open Client

(* -------------------------------------------------------------------------- *)

(* Shrinker. *)

module Shrinker = struct
  module Shrink = QCheck.Shrink
  module Iter = QCheck.Iter

  let rec bv_pat = function
    | ML.PVar (_, y) -> [y]
    | ML.PWildcard _ | ML.PVariant (_, _, None) -> []
    | ML.PAnnot (_, pat, _)
    | ML.PVariant (_, _, Some pat) ->
       bv_pat pat
    | ML.PTuple (_, ps) ->
       List.(concat (map bv_pat ps))

  (* t[u/x] *)
  let rec subst t x u =
    match t with
    | ML.Var (pos, y) ->
      if x = y then u
      else ML.Var (pos, y)
    | ML.Abs (pos, y, t) ->
      ML.Abs (pos, y, subst_under [y] t x u)
    | ML.App (pos, t1, t2) ->
      ML.App (pos, subst t1 x u, subst t2 x u)
    | ML.Let (pos, r, y, t1, t2) ->
      ML.Let (pos, r, y, subst t1 x u, subst_under [y] t2 x u)
    | ML.Tuple (pos, ts) ->
      ML.Tuple (pos, List.map (fun t -> subst t x u) ts)
    | ML.Hole (pos, ts) ->
      ML.Hole (pos, List.map (fun t -> subst t x u) ts)
    | ML.LetProd (pos, ys, t1, t2) ->
      ML.LetProd (pos, ys, subst t1 x u, subst_under ys t2 x u)
    | ML.Annot (pos, t, ty) ->
      ML.Annot (pos, subst t x u, ty)
    | ML.Variant (pos, ty, t) ->
      ML.Variant (pos, ty, Option.map (fun t -> subst t x u) t)
    | ML.Match (pos, t, brs) ->
      ML.Match (pos, subst t x u, List.map (fun br -> subst_branch br x u) brs)

  (* (y.t)[u/x] *)
  and subst_under ys t x u =
    if List.mem x ys then t
    else subst t x u

  and subst_under_pat p t x u =
    subst_under (bv_pat p) t x u

  and subst_branch (p, t) x u =
    (p, subst_under_pat p t x u)

  let remove_variable t x =
    subst t x (ML.Hole (None, []))

  let remove_variables t xs =
    List.fold_left remove_variable t xs

  let rec shrink_term t = Iter.(
    (* The Iter product is not suitable for shrinking:
         (and+) (shrink a) (shrink b)
       will try to shrink *both* a and b simultaneously,
       but never try to shrink just one of them.

       We shadow this unsuitable operator and use a "pointed product" (and++),
       which tries to shrink a (with b constant) and then b (with a constant).

       This corresponds to the behavior of Shrink.pair, but Shrink.pair works
       on function types ('a -> 'a Iter.t), which is inconvenient
       to write shrinkers directly -- no 'map' function. *)
    let (and+) = () in ignore ((and+));
    let (let++) (_a, it) f = Iter.map f it in
    let (and++) (a, ita) (b, itb) =
      (a, b),
      Iter.append
        (let+ a' = ita in (a', b))
        (let+ b' = itb in (a, b'))
    in
    let subterms ts =
      (* ...[t1, t2] is not always a desirable shrinking choice for a term
         containing [t1, t2] as subterms, because it breaks the property that
         the types of t1 and t2 appear in the resulting type, which is sometimes
         important to reproduce typing bugs.
         So we start with just (t1) and (t2) as shrinking choices,
         even though they typically do not preserve typability. *)
      of_list ts <+> return (ML.Hole (None, ts)) in
    (match t with
     | ML.Hole (_, []) ->
        empty
     | _ ->
       return (ML.Hole (None, []))
    ) <+> (
      match t with
      | ML.Var _ ->
         empty

      | ML.Hole (pos, ts) ->
        (match ts with [t] -> return t | _ -> empty)
        <+> (
         let+ ts' = Shrink.list ~shrink:shrink_term ts
         in ML.Hole (pos, ts')
       )

      | ML.Abs (pos, x, t) ->
         subterms [remove_variable t x]
         <+> (
           let+ t' = shrink_term t in
           ML.Abs (pos, x, t')
         )

      | ML.App (pos, t1, t2) ->
        subterms [t1; t2]
        <+> (
         let++ t1' = t1, shrink_term t1
         and++ t2' = t2, shrink_term t2
         in ML.App (pos, t1',t2')
       )

      | ML.Let (pos, r, x, t, u) ->
        subterms [t; remove_variable u x]
        <+> (
         let++ t' = t, shrink_term t
         and++ u' = u, shrink_term u
         in ML.Let (pos, r, x, t', u')
       )

      | ML.LetProd (pos, xs, t, u) ->
        subterms [t; remove_variables u xs]
        <+> (match t with
          | ML.Hole _ ->
            let+ xs' = Shrink.list_spine xs in
            let u =
              List.filter (fun x -> not (List.mem x xs')) xs
              |> remove_variables u
            in
            if xs' = [] then u
            else ML.LetProd (pos, xs', t, u)
          | _ -> empty
        )
        <+> (
         let++ t' = t, shrink_term t
         and++ u' = u, shrink_term u
         in ML.LetProd (pos, xs, t', u')
       )

      | ML.Tuple (pos, ts) ->
        subterms ts
         <+> (
           let+ ts' = Shrink.list ~shrink:shrink_term ts
           in ML.Tuple (pos, ts')
         )

      | ML.Annot (_, t, _ty) ->
        subterms [t]

      | ML.Variant (pos, lab, t) ->
        subterms (Option.to_list t)
        <+> (
          match t with
          | None -> empty
          | Some t ->
            let+ t' = shrink_term t
            in ML.Variant (pos, lab, Some t')
        )

      | ML.Match (_, _t, _branches) ->
        failwith "unsupported"
    )
  )
end

(* -------------------------------------------------------------------------- *)

(* Random testing. *)

(* A list of pairs [m, n], where [m] is the number of tests and [n] is the
   size of the randomly generated terms. *)

(* The percentages of well-typed terms have been empirically measured
   with [rectypes] turned off. There are more well-typed terms when
   [rectypes] is on. *)

let slow_tests =
  (* We enable slow tests by default, so that unaware users run the
     full thing. *)
  match Sys.getenv_opt "INFERNO_SLOW_TESTS" with
  | Some ("0" | "false" | "") -> false
  | Some _ | None -> true

let pairs k = [
    1 * k, 10; (* about 26% of well-typed terms *)
] @ if not slow_tests then [] else [
    2 * k, 15; (* about 12% of well-typed terms *)
    4 * k, 20; (* about  5% of well-typed terms *)
    3 * k, 25; (* about  2% of well-typed terms *)
    3 * k, 30; (* about  1% of well-typed terms *)
    3 * k, 35; (* about .5% of well-typed terms *)
    2 * k, 40; (* about .1% of well-typed terms *)
  ]

let () =
  Printf.printf "Preparing to type-check a bunch of randomly-generated terms...\n%!";
  let count_success = ref 0 in
  let count_total = ref 0 in
  let tests rectypes k =
    List.map (fun (m, n) ->
      let arb =
        QCheck.make
          ~print:MLPrinter.to_string
          ~shrink:Shrinker.shrink_term
          (Test.RandomML.term (0, n))
      in
      let prop t =
        Test.CheckML.test_with_args
          ~rectypes
          ~success:count_success
          ~total:count_total
          Datatype.Env.empty
          t
      in
      QCheck.Test.make
        ~name:(Printf.sprintf "Type checking (size %d)" n)
        ~count:m
        arb
        prop
  ) (pairs k) in

  (* Test both settings of [rectypes]. *)
  let tests = tests false 10_000 @ tests true 2_000 in

  (* Note that we need to initialize the random state on each test. *)
  let suite () =
    QCheck_runner.set_seed 0;
    let outcome = QCheck_runner.run_tests
                    ~debug_shrink:
                      (* use (Some stdout) to see intermediate shrinking steps *)
                      None
                    tests
    in
    if outcome <> 0 then
      failwith "Problem detected !"
    else begin
        Printf.printf
          "\nIn total, %d out of %d terms (%.1f%%) were considered well-typed.\n%!"
          !count_success !count_total
          (float !count_success /. float !count_total *. 100.);
        Printf.printf "No problem detected.\n%!"
      end
  in
  Alcotest.run "random_suite" [ ("random_suite",
                                 [ Alcotest.test_case "random_suite" `Quick suite ] ) ]
    ~and_exit:false ~verbose:false
