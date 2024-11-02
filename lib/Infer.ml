(* This sample client performs type inference for a fragment of ML and
   translates it down to a fragment of System F. *)

(* The unifier uses the type structure provided by our module [Structure].
   We define [S] as a local name for this module. *)

module S =
  Structure

(* -------------------------------------------------------------------------- *)

(* The unifier type structure is decoded into the target calculus type
   structure as follows. *)

module O = struct

  type tyvar =
    int


  (* See also [fresh_tyvar] *)
  let inject n =
    2 * n

  type 'a structure = 'a S.structure
  let pprint = S.pprint

  type ty =
    F.nominal_type

  let variable x =
    F.TyVar x

  let structure t =
    match t with
    | S.TyArrow (t1, t2) ->
        F.TyArrow (t1, t2)
    | S.TyProduct ts ->
        F.TyProduct ts
    | S.TyConstr (tyconstr, ts) ->
        F.TyConstr(tyconstr, ts)
    | S.TyEq (t1, t2) ->
        F.TyEq (t1, t2)

  let mu x t =
    F.TyMu (x, t)

end

(* -------------------------------------------------------------------------- *)

(* Instantiate the solver. *)

module X = struct
  (* The module X (following the naming convention of Solver.Make)
     provides a type of variables that will be assigned polymorphic
     schemes by the solver.

     In a toy ML language, the syntact constructs that introduce
     polymorphic schemes always correspond to binding constructs for
     term variables: (let x = t in u) in particular, or (fun x -> t)
     which can be considered to give a "trivial" (non-polymorphic)
     scheme to x.

     In our richer language, we also compute polymorphic schemes for
     type annotations containing rigid variables:

       (t : for 'a 'b. 'a * 'b -> 'a)

     For this construct there is no term variable associated to the
     scheme, instead we create a "symbolic" variable (a fresh integer)
     to pass to the solver.
   *)
  type t =
    | Var of ML.tevar
    | Sym of int

  let fresh : unit -> t =
    let gensym = Inferno.Utils.gensym() in
    fun () -> Sym (gensym ())

  let hash = Hashtbl.hash

  let compare v1 v2 = Stdlib.compare v1 v2

  let equal v1 v2 = compare v1 v2 = 0

  let to_string v =
    match v with
    | Var v ->
       v
    | Sym n ->
       string_of_int n
end

module Solver = Inferno.Solver.Make(X)(S)(O)
open Solver

(* Errors *)

type error =
  | Unbound of ML.tevar
  | Unify of F.nominal_type * F.nominal_type
  | Cycle of F.nominal_type
  | VariableConflict of ML.tevar
  | VariableScopeEscape
  | Unsupported of string

exception Error of Utils.loc * error

(* -------------------------------------------------------------------------- *)

let arrow x y =
  S.TyArrow (x, y)

let product xs =
  S.TyProduct xs

let constr c xs =
  S.TyConstr (c, xs)

(* Should we use smart constructors to eliminate redundant coercions when
   possible? *)

let smart =
  true

let flet ~loc (x, ty, t, u) =
  match t with
  | F.Var (_, y) when smart && x = y ->
      u
  | t ->
      F.Let (loc, F.Non_recursive, x, ty, t, u)

(* -------------------------------------------------------------------------- *)

(* The coercion [coerce vs1 vs2] converts a type of the form [forall vs1, _]
   to a type of the form [forall vs2, _], where [vs2] forms a subset of [vs1].
   This coercion allows getting rid of unused quantifiers and/or re-ordering
   quantifiers. *)

type coercion =
  F.nominal_term -> F.nominal_term

let bottom : F.nominal_type =
  let a : F.tyvar = 0 (* arbitrary *) in
  F.TyForall (a, F.TyVar a)

(* [ftyabs1 v t] builds a (capital-Lambda) abstraction of the type variable
   [v] in the term [t]. It is a smart constructor: if it recognizes an
   eta-redex, it contracts it on the fly. We are in a special case where, if
   [v] and [w] are the same variable, then this variable does not occur free
   in [t], so we don't need to perform this costly check at runtime. This
   eta-contraction is not essential anyway; it's just a way of avoiding
   coercion clutter in the common case where the coercion actually has no
   effect. *)

let ftyabs1 ~loc v t =
  match t with
  | F.TyApp (_, t, F.TyVar w) when smart && v = w ->
      t
  | t ->
      F.TyAbs (loc, v, t)

(* TEMPORARY find a better name for [coerce] *)

let coerce ~loc (vs1 : O.tyvar list) (vs2 : O.tyvar list) : coercion =
  (* Assume the term [t] has type [forall vs1, _]. *)
  fun t ->
    (* Introduce the desired quantifiers. *)
    List.fold_right (ftyabs1 ~loc) vs2 (
      (* Now, specialize the term [t]. For each member of [vs1],
         we must provide a suitable instantiation. *)
      F.ftyapp ~loc t (
        (* [vs1] is a superset of [vs2]. For each member of [vs1], if it is a
           member of [vs2], then we keep it (by instantiating it with itself),
           otherwise we get rid of it (by instantiating it with an arbitrary
           closed type, say [bottom]). *)
        let suitable (v : O.tyvar) : O.ty =
          if List.mem v vs2 then F.TyVar v else bottom
          (* TEMPORARY need an efficient membership test in [vs2] *)
        in
        List.map suitable vs1
      )
    )

(* -------------------------------------------------------------------------- *)

(* The mapM_* functions are monadic maps of the form

       ('a -> (..., 'r) binder) -> 'a list -> (... list, 'r) binder

   (Reminder: a ('b, 'r) binder computes a 'b but can create new inference
    variables in the process, and return them as part of the constraint.)

   For mapM_now, the mapped function has type ('a -> ('b, 'r) binder),
   where we expect to use the 'b during the rest of the constraint construction.
   We get back a ('b list).

   For mapM_later, the mapped function has type ('a -> ('c co, 'r) binder),
   where the 'c will be available "later", after the constraint is solved.
   We get back a ('c list co) -- a ('c list), later.

   For mapM_both, the mapped function has type ('a -> ('b * 'c co, 'r) binder),
   where the 'b is available "now" and the 'c "later".
   We get back a ('b list * 'c list co) -- a ('b list) now and a ('c list) later.
 *)

let rec mapM_now (f : ('a -> ('b, 'r) binder)) (xs : 'a list)
  : ('b list, 'r) binder
  = fun k ->
  match xs with
  | [] ->
     k []
  | x :: xs ->
     let@ y = f x in
     let@ ys = mapM_now f xs in
     k (y :: ys)

let rec mapM_later (f : ('a -> ('c co, 'r) binder)) (xs : 'a list)
  : ('c list co, 'r) binder
  = fun k ->
  match xs with
  | [] ->
     k (pure [])
  | x::xs ->
     let@ y = f x in
     let@ ys = mapM_later f xs in
     k(let+ y = y
       and+ ys = ys
       in y :: ys)

let rec mapM_both (f : ('a -> ('b * 'c co, 'r) binder)) (xs : 'a list)
  : ('b list * 'c list co, 'r) binder
  = fun k ->
  match xs with
  | [] ->
     k ([], pure [])
  | x :: xs ->
     let@ (y, z) = f x in
     let@ (ys, zs) = mapM_both f xs in
     k (y::ys,
        let+z = z
        and+ zs = zs
        in z :: zs
       )

let rec map_co (f : 'a -> 'b co) : 'a list -> 'b list co
  = function
    | [] -> pure []
    | x :: xs ->
      let+ y = f x
      and+ ys = map_co f xs
      in y :: ys

let rec convert_deep (env : ML.datatype_env) (params : (ML.tyvar * variable) list) (ty : ML.typ) : deep_ty =
  let conv ty = convert_deep env params ty in
  match ty with
  | ML.TyVar (_, tx) ->
     let tx' = List.assoc tx params in
     DeepVar tx'

  | ML.TyArrow (_, ty1, ty2) ->
     DeepStructure (S.TyArrow(conv ty1, conv ty2))

  | ML.TyProduct (_, tys) ->
     DeepStructure (S.TyProduct (List.map conv tys))

  | ML.TyConstr (_, tid, tys) ->
     DeepStructure (S.TyConstr(tid, List.map conv tys))

let convert env params ty =
  let deep_ty = convert_deep env params ty in
  deep deep_ty

(* -------------------------------------------------------------------------- *)

(* [get_loc t] returns the location of [t]. *)
let get_loc t =
  match t with
  | ML.Var (pos, _) | ML.Hole (pos, _) | ML.Abs (pos, _, _)
  | ML.App (pos, _, _) | ML.Let (pos, _, _, _, _) | ML.Annot (pos, _, _)
  | ML.Tuple (pos, _) | ML.LetProd (pos, _, _, _)
  | ML.Variant (pos, _, _) | ML.Match (pos, _, _)
    -> pos

let correlate loc c =
  (* We (the client) use optional locations,
     whereas the solver uses non-optional locations. *)
  match loc with
  | None -> c
  | Some loc -> Solver.correlate loc c

(* -------------------------------------------------------------------------- *)

(* We will need a type environment to keep trace of term variables that must
   be bound to solver variables during typechecking of patterns *)

type type_env = (ML.tevar * variable) list

(* -------------------------------------------------------------------------- *)

(* The client uses the combinators provided by the solver so as to
   transparently 1- analyse the source term and produce constraints; and 2-
   decode the solution of the constraints and produce a term in the target
   calculus. These two steps take place in different phases, but the code is
   written as if there was just one phase. *)

(* The function [hastype] takes a source term [t] and an expected type [w]. No
   type environment is required, as everything is built into the constraint
   via suitable combinators, such as [def]. *)

let hastype (typedecl_env : ML.datatype_env) (t : ML.term) (w : variable) : F.nominal_term co
  =
  let rec hastype t w =
    let loc = get_loc t in
    correlate loc @@
    match t with
    (* Variable. *)
    | ML.Var (loc, x) ->

      (* [w] must be an instance of the type scheme associated with [x]. *)
      let+ tys = instance (X.Var x) w in
      (* The translation makes the type application explicit. *)
      F.ftyapp ~loc (F.Var (loc, x)) tys

    (* Abstraction. *)
    | ML.Abs (loc, x, u) ->

      (* We do not know a priori what the domain and codomain of this function
         are, so we must infer them. We introduce two type variables to stand
         for these unknowns. *)
      let@ v1 = exist in
      let@ v2 = exist in
      (* [w] must be the function type [v1 -> v2]. *)
      let+ () = w --- arrow v1 v2
      (* Under the assumption that [x] has type [domain], the term [u] must
         have type [codomain]. *)
      and+ u' = def (X.Var x) v1 (hastype u v2)
      and+ ty1 = decode v1
      in
      (* Once these constraints are solved, we obtain the translated function
         body [u']. There remains to construct an explicitly-typed abstraction
         in the target calculus. *)
      F.Abs (loc, x, ty1, u')

    (* Application. *)
    | ML.App (loc, t1, t2) ->

      (* Introduce a type variable to stand for the unknown argument type. *)
      let@ v = exist in
      let+ t1' = lift hastype t1 (arrow v w)
      and+ t2' = hastype t2 v
      in F.App (loc, t1', t2')

      (* Generalization. *)
    | ML.Let (loc, rec_, x, t, u) ->
      let hastype_def x t v =
        match rec_ with
        | ML.Non_recursive -> hastype t v
        | ML.Recursive ->
          (* For recursive definitions [let rec x = t], we bind the
             variable [x] to the monomorphic expected type of [t] when
             inferring the type of [t] itself. *)
          def (X.Var x) v (hastype t v)
      in
      (* Construct a ``let'' constraint. *)
      let+ (a, (b, ty), t', u') =
        let1 (X.Var x) (hastype_def x t) (hastype u w) in
      (* [a] are the type variables that we must bind (via Lambda abstractions)
         while type-checking [t]. [(b, _)] is the type scheme that [x] must
         receive while type-checking [u]. Its quantifiers [b] are guaranteed to
         form a subset of [a]. Hence, in general, we must re-bind [x] to an
         application of a suitable coercion to [x]. We use smart constructors so
         that, if the lists [a] and [b] happen to be equal, no extra code is
         produced. *)
      let sch tyvars =
        List.fold_right (fun alpha sch -> F.TyForall (alpha, sch)) tyvars ty in
      let rec_ = match rec_ with
        | ML.Recursive -> F.Recursive
        | ML.Non_recursive -> F.Non_recursive
      in
      let t'' = match rec_ with
        | F.Non_recursive -> t'
        | F.Recursive ->
          (* For recursive definitions, the defined variable is used monomorphically
             within the definition, so we must instantiate the type scheme.

             Consider for example:
               let rec loop x = loop x
             Which gets inferred at type ([a] [b] a -> b).

             We do not want to get

               let rec (loop : [a] [b] a -> b) =
                 Fun a b ->
                   fun (x : a) -> loop x

             which is ill-typed: the recursive occurrence of 'loop' in its body
             is applied as a monomorphic function, but it is bound to the polymorphic
             (loop : [a] [b] a -> b).

             Instead we elaborate into the following:

               let rec (loop : [a] [b] a -> b) =
                 Fun a b ->
                   let loop = loop [a] [b] in
                   fun (x : a) -> loop x
          *)
          flet ~loc (x, ty,
                     F.ftyapp ~loc (F.Var (loc, x)) (List.map (fun v -> F.TyVar v) a),
                     t')
      in
      F.Let (loc, rec_, x, sch a,
             F.ftyabs ~loc a t'',
             flet ~loc (x, sch b, coerce ~loc a b (F.Var (loc, x)),
                        u'))

    | ML.Annot (loc, t, annot) ->

      let convert_annot typedecl_env params w t ty =
        let@ v = convert typedecl_env params ty in
        let+ () = v -- w
        and+ t' = hastype t v
        and+ ty' = decode v
        in F.Annot (loc, t', ty')
      in

      begin match annot with
        | (_, [], ty) ->
          convert_annot typedecl_env [] w t ty
        | (ML.Flexible, vs, ty) ->
          let@ params =
            vs |> mapM_now (fun alpha k -> let@ v = exist in k (alpha, v)) in
          convert_annot typedecl_env params w t ty
        | (ML.Rigid, vs, ty) ->
          (* See "The Essence of ML type inference", long version, exercise 1.10.8 page 112:
               <<(t : forall 'a 'b. ty) : 'w>>
             is elaborated into a rigid constraint
               let x: forall ('a 'b) exists 'z [<<(t : ty) : 'z>>]. 'z in (x <= 'w)

             After constraint solving, the witness we generate looks like
               (Lambda 'a 'b. (t : ty)) [ty1] [ty2]
             where ty1, ty2 are the witnesses of the instance
             constraint between the polymorphic scheme of x and the
             result type 'w. This enforces that 'a, 'b are used polymorphically
             by t, but they can still be instantiated in the rest of the term.
          *)
          let x = X.fresh () in
          let+ (alphas, (betas, _), t', tys) =
            letr1 (List.length vs) x
              (fun tys z ->
                 let tyvs = List.combine vs tys in
                 convert_annot typedecl_env tyvs z t ty)
              (instance x w)
          in
          F.ftyapp ~loc (coerce ~loc alphas betas (F.ftyabs ~loc alphas t')) tys
      end

    | ML.Tuple (loc, ts) ->
      let on_term (t:ML.term) : ('b * 'c co, 'r) binder =
        fun (k : ('b * 'c co) -> 'r co) : 'r co ->
          let@ v : 'b = exist in
          let t = hastype t v in
          k (v, t)
      in

      let@ (vs, ts') = mapM_both on_term ts in
      let+ () = w --- product vs
      and+ ts' = ts'
      in F.Tuple (loc, ts')

    | ML.LetProd (loc, xs, t, u) ->
      let on_var (x:ML.tevar) : ('a, 'r) binder =
        fun (k : 'b -> 'r co) : 'r co ->
          let@ v = exist in
          def (X.Var x) v (k v)
      in

      let@ vs = mapM_now on_var xs in
      let+ t' = lift hastype t (product vs)
      and+ u' = hastype u w
      in F.LetProd(loc, xs, t', u')

    | ML.Variant (loc, c, t) ->
      let@ (dty, v) = hastype_variant typedecl_env ~loc c w in

      let+ dty = dty
      and+ t' =
        match t with
        | None ->
          pure (F.Tuple (loc, []))
        | Some t ->
          hastype t v
      in F.Variant (loc, c, dty, t')

    | ML.Match (loc, t, branches) ->
      (* Inference variable for the type of the scrutinee
         (and of the patterns) *)
      let@ v = exist in

      let@ branches' = hastype_branches typedecl_env branches w v in

      let+ t = hastype t v
      and+ branches' = branches'
      and+ ty = decode w
      in F.Match (loc, ty, t, branches')

    | ML.Hole (loc, ts) ->
      (* A hole ...[t1, t2, .., tn] has any type, and its subterms
         [t1, .., tn] can themselves have any type; our return type
         w is unconstrained and we type each ti at a new inference
         variable. *)
      let on_subterm t k =
        let@ v = exist in
        k (hastype t v) in
      let@ ts' = mapM_later on_subterm ts in
      let+ ts' = ts'
      and+ ty = decode w
      in F.Hole (loc, ty, ts')

  and hastype_variant typedecl_env ~loc c w
    : (F.nominal_datatype co * variable, 'r) binder
    = fun k ->
      let Datatype.{ type_name ; arg_type ; _ } =
        Datatype.Env.find_label typedecl_env c in
      let Datatype.{ type_params ; data_kind ; _ } =
        Datatype.Env.find_decl typedecl_env type_name in
      begin
        match data_kind with
        | Datatype.Variant ->
          ()
        | Datatype.Record ->
          (* TODO: this error should be turned into a proper 'error'
             constructor like the others, but we probably need to
             figure out how to deal with all Datatype exceptions at
             once. *)
          raise Datatype.Env.UnexpectedRecord
      end;

      let arg_type =
        match arg_type with
        | None ->
          ML.TyProduct (loc, [])
        | Some ty ->
          ty
      in

      let@ type_param_vars = mapM_now (fun _x -> exist) type_params in
      let type_param_dict = List.combine type_params type_param_vars in

      let dty =
        let+ param_types = map_co decode type_param_vars in
        (type_name, param_types) in

      let sum_type = constr type_name type_param_vars in

      let@ argument_v = convert typedecl_env type_param_dict arg_type in

      let+ () = w --- sum_type
      and+ r = k (dty, argument_v)
      in r

  and hastype_branches typedecl_env branches v_return v_scrutinee
    : (F.nominal_branch list co, 'r) binder
    =

    (* Translate the ML term [u] into System F and bind the pattern
       variables in [pat_env] *)
    let rec bind_pattern_vars pat_env u
      : F.nominal_term co
      = match pat_env with
      | [] ->
        (* Here we use [v_return] because [t] should have the same type
           as the whole match statement *)
        hastype u v_return
      | (x, v1) :: pat_env ->
        def (X.Var x) v1 @@ bind_pattern_vars pat_env u
    in

    let on_branch ((pat,u) : ML.branch)
      : (F.nominal_branch co, 'r) binder
      = fun k ->
        let@ (pat_env, pat) = hastype_pat typedecl_env pat v_scrutinee in

        let u = bind_pattern_vars pat_env u in

        k (
          let+ pat = pat and+ u = u
          in (pat, u)
        )
    in

    mapM_later on_branch branches

  (* [hastype_pat pat v] returns a type environment, containing term variables
     associated with solver variables, and a System F pattern *)
  and hastype_pat typedecl_env pat w
    : (type_env * F.nominal_pattern co, 'r) binder
    = fun k ->
      match pat with
      | ML.PVar (loc, x) ->
        let pat_env = [(x, w)] in
        k (pat_env, pure (F.PVar (loc, x)))

      | ML.PWildcard loc ->
        k ([], pure (F.PWildcard loc))

      | ML.PAnnot (loc, pat, (rigidity, vars, ty)) ->
        begin match rigidity with
          | ML.Rigid ->
            failwith "Rigid variables are not supported in pattern annotation"
          | ML.Flexible ->
            let@ params =
              vars |> mapM_now (fun alpha k ->
                let@ v = exist in k(alpha,v)
              )
            in
            let@ v = convert typedecl_env params ty in
            let@ (pat_env, pat) = hastype_pat typedecl_env pat v in
            let+ () = v -- w
            and+ res = k (pat_env,
                          let+ pat = pat
                          and+ ty' = decode v
                          in F.PAnnot(loc, pat, ty'))
            in res
        end

      | ML.PTuple (loc, pats) ->

        let check_no_duplicate accu env =
          List.iter (fun (x,_) ->
            if List.mem_assoc x accu then
              raise (Error (loc, VariableConflict x))
          ) env
        in

        let union_ accu env =
          check_no_duplicate accu env;
          List.append accu env
        in

        let union envs =
          List.fold_left union_ [] envs in

        let on_pattern pat
          : ((variable * (ML.tevar * variable) list)
             * F.nominal_pattern co, 'r) binder
          = fun k ->
            let@ v = exist in
            let@ (pat_env, pat) = hastype_pat typedecl_env pat v in
            k ((v,pat_env), pat)
        in

        let@ (l, pats) = mapM_both on_pattern pats in
        let (vs, pat_envs) = List.split l in
        let pat_env = union pat_envs in

        k (pat_env,
           let+ () = w --- product vs
           and+ pats = pats
           in F.PTuple (loc, pats))

      | ML.PVariant (loc, c, pat) ->
        let@ (dty, v) = hastype_variant typedecl_env ~loc c w in

        let@ (pat_env, pat') =
          match pat with
          | None ->
            (fun k ->
               k ([], pure (F.PTuple (loc, []))))
          | Some pat ->
            hastype_pat typedecl_env pat v
        in
        k(pat_env,
          let+ dty = dty
          and+ pat' = pat'
          in F.PVariant (loc, c, dty, pat'))
  in
  hastype t w

(* The top-level wrapper uses [let0]. It does not require an expected
   type; it creates its own using [exist]. And it runs the solver. *)

let hastype (env : ML.datatype_env) (t : ML.term) : F.nominal_term co =
  let loc = get_loc t in
  let+ (vs, t) =
    correlate loc (let0 (exist (hastype env t))) in
  (* [vs] are the binders that we must introduce *)
  F.ftyabs ~loc vs t

let hastype_with_hook ~(hook : unit -> 'a) (env : ML.datatype_env) (t : ML.term)
: ('a * F.nominal_term) co
=
  let+ a = (let+ () = pure () in hook())
  and+ u = hastype env t in
  a, u

let get_tevar x =
  match x with
  | X.Sym _ -> assert false
  | X.Var x -> x

let translate_with_hook ~hook ~rectypes env t =
  try Solver.solve ~rectypes (hastype_with_hook ~hook env t) with
  | Error (loc, solver_error) ->
    (* TODO: it would be nice to be able to share the definition
       of errors of the solver, instead of duplicating them
       in a separate type.

       This is not obvious to do, because the Solver error type is
       defined inside the functor, and the functor application is no
       mentioned at all in the Infer interface currently.
    *)
    let error : error = match solver_error with
      | Unbound x -> Unbound x
      | Unify (t1, t2) -> Unify (t1, t2)
      | Cycle (ty) -> Cycle (ty)
      | VariableScopeEscape -> VariableScopeEscape
      | _ -> failwith "unmatched solver_error"
    in
    raise (Error (loc, error))

let translate ~rectypes env t =
  let ((), res) = translate_with_hook ~hook:ignore ~rectypes env t in
  res

let emit_error loc (error : error) =
  let emit_type ty =
    Utils.emit_endline (FPrinter.print_type ty)
  in
  Utils.emit_loc loc;
  begin match error with
  | Unbound (s) ->
      Printf.printf "Type error: unbound variable \"%s\".\n"
        s
  | Cycle (ty) ->
      Printf.printf "Type error: a cyclic type arose.\n";
      emit_type ty
  | Unify (ty1, ty2) ->
      Printf.printf "Type error: mismatch between the type:\n";
      emit_type ty1;
      Printf.printf "and the type:\n";
      emit_type ty2;
  | VariableScopeEscape ->
      Printf.printf
        "A rigid variable escapes its scope.\n"
  | VariableConflict (x) ->
      Printf.printf
        "Scope error: variable %s is already bound in this pattern."
        x
  | Unsupported (feature) ->
      Printf.printf
        "Type inference does not yet support %S."
        feature
  end;
  flush stdout
