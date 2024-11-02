open Client

(* -------------------------------------------------------------------------- *)

(* AST helper functions *)

let (-->) ty1 ty2 =
  F.TyArrow (ty1, ty2)

let unit =
  F.Tuple (None, [])

let unit_type =
  F.TyProduct []

let unit_pattern =
  F.PTuple (None, [])

let var x =
  F.(Var (None, x))

let annot ty t =
  F.(Annot (None, ty, t))

let abs x ty t =
  F.(Abs (None, x, ty, t))

let app t u =
  F.(App (None, t, u))

let tyabs x t =
  F.(TyAbs (None, x, t))

let tyapp t ty =
  F.(TyApp (None, t, ty))

let tuple ts =
  F.(Tuple (None, ts))

let letprod xs t u =
  F.(LetProd (None, xs, t, u))

let variant lbl datatype t =
  F.(Variant (None, lbl, datatype, t))

let match_ ty scrutinee branches =
  F.(Match (None, ty, scrutinee, branches))

let absurd ty =
  F.(Absurd (None, ty))

let refl ty =
  F.(Refl (None, ty))

let use t u =
  F.(Use (None, t, u))

let pvar x =
  F.(PVar (None, x))

let pwildcard =
  F.(PWildcard None)

let ptuple ps =
  F.(PTuple (None, ps))

let pvariant lbl datatype t =
  F.(PVariant (None, lbl, datatype, t))

(* -------------------------------------------------------------------------- *)

(* ∀a b. ({} -> (a * (a -> b))) -> b
   Λa b. fun (p : {} -> (a * (a -> b))) ->
     let (x, f) = p () in f x
*)
let let_prod =
  let alpha, beta = 0, 1 in
  let p, f, x = "p", "f", "x" in
  tyabs alpha @@
  tyabs beta @@
  abs p (unit_type --> F.(TyProduct [TyVar alpha; TyVar alpha --> TyVar beta])) @@
  letprod [x; f]
    (app (var p) (tuple []))
    (app (var f) (var x))

(* Λαβ. λx:{α*β}. match x with (_, y) -> y end *)
let match_with_prod =
  let alpha, beta = 1, 0 in
    tyabs alpha @@
    tyabs beta @@
    abs "x" (F.TyProduct [ F.TyVar alpha ; F.TyVar beta ]) @@
    match_ (F.TyVar beta) (var "x") [
        (ptuple [ pwildcard ; pvar "y" ]) , var"y"
      ]

(* Λα. λx:{α*α}. match x with (y, y) -> y end *)
let match_variable_bound_twice =
  let alpha = 0 in
    tyabs alpha @@
    abs "x" (F.TyProduct [ F.TyVar alpha ; F.TyVar alpha ]) @@
    match_ (F.TyVar alpha) (var "x") [
        (ptuple [ pvar "y" ; pvar "y" ]) , var"y"
      ]

(* option *)
let option_env =
  let option_typedecl =
    let open Datatype in {
      name = Type "option";
      type_params = [ 0 ];
      data_kind = Variant;
      labels_descr = [
        {
          label_name = Label "None";
          type_name = Type "option";
          arg_type = F.TyProduct [];
        } ; {
          label_name = Label "Some";
          type_name = Type "option";
          arg_type = F.TyVar 0;
        }
      ];
    }
  in
  Datatype.Env.add_decl Datatype.Env.empty option_typedecl

(* We test this example in an empty datatype environment. It should raise
   an error indicating that it did not find the label. *)
let not_in_env =
  let alpha = 0 in
  let label = Datatype.Label "None" in
  let datatype = Datatype.Type "option", [F.TyForall (alpha, F.TyVar alpha)] in
  variant label datatype unit

(* None *)
let none =
  let alpha = 0 in
  let label = Datatype.Label "None" in
  let datatype = Datatype.Type "option", [F.TyForall (alpha, F.TyVar alpha)] in
  variant label datatype unit

let none_pattern =
  let alpha = 0 in
  let label = Datatype.Label "None" in
  let datatype = Datatype.Type "option", [F.TyForall (alpha, F.TyVar alpha)] in
  pvariant label datatype unit_pattern

(* Some Λα.λx:α.x *)
let some =
  let alpha = 0 in
  let label = Datatype.Label "Some" in
  let datatype = Datatype.Type "option",
                 [ F.TyForall (alpha, F.TyVar alpha --> F.TyVar alpha) ] in
  variant label datatype @@
  tyabs alpha @@
  abs "x" (F.TyVar alpha) @@
  var "x"

let some_pattern =
  let alpha = 0 in
  let label = Datatype.Label "Some" in
  let datatype = Datatype.Type "option", [ F.TyForall (alpha, F.TyVar alpha) ] in
  pvariant label datatype pwildcard

(* Λα. match None with
       | None     -> ()
       | Some (_) -> ()
 *)
let match_none =
  let alpha = 0 in
  tyabs alpha @@
  match_ unit_type none @@ [
    (none_pattern , unit);
    (some_pattern , unit);
  ]

(* Λα. λx:α.
   match (x,Some x) with
   | (y, None)  -> y
   | (y,Some y) -> y
   end
 *)
let match_variable_bound_twice_under_tuple =
  let alpha = 0 in
  let none_label = Datatype.Label "None" in
  let some_label = Datatype.Label "Some" in
  let datatype = Datatype.Type "option", [ F.TyVar alpha ] in
  tyabs alpha @@
  abs "x" (F.TyVar alpha) @@
  match_ (F.TyVar alpha)
    (tuple [var "x"; variant some_label datatype (var "x")]) [
      (ptuple [ pvar "y" ; pvariant none_label datatype unit_pattern ]) , var"y" ;
      (ptuple [ pvar "y" ; pvariant some_label datatype (pvar "y") ]) , var"y"
      ]

(* ( refl_{} : Eq(∀α.{} , {}) ) *)
let type_eq =
  let alpha = 0 in
  annot (refl unit_type) @@
  F.TyEq (F.TyForall (alpha, unit_type),
          unit_type)

(* Λ α. use (Refl_α : eq (α,α)) in λ (x:α). x *)
let introduce_type_eq =
  let alpha = 0 in
  let x = "x" in
  tyabs alpha @@
  use
    (annot (refl (F.TyVar alpha)) (F.TyEq (F.TyVar alpha, F.TyVar alpha))) @@
    abs x (F.TyVar alpha) (var x)

(* Λ αβ. λ (x : eq (α,β)). use x in (Refl_β : eq (β,α))
 * ∀ αβ. eq (α,β) -> eq (β,α) *)
let sym =
  let alpha = 1 in
  let beta = 0 in
  let x = "x" in
  annot
    (tyabs alpha @@
     tyabs beta @@
     abs x (F.TyEq (F.TyVar alpha, F.TyVar beta)) @@
     use (var x) @@
     annot (refl (F.TyVar beta)) (F.TyEq (F.TyVar beta, F.TyVar alpha)))
    @@
    F.TyForall (alpha,
    F.TyForall (beta,
    F.TyEq (F.TyVar alpha, F.TyVar beta)
    --> F.TyEq (F.TyVar beta, F.TyVar alpha)))


(* Λ αβγ.
   λ (x : eq (α,β)).
   λ (y : eq (β,γ)).
   use x in
   use y in
   (Refl_γ : eq (α,γ))

   ∀αβγ. eq (α,β) -> eq (β,γ) -> eq (α,γ) *)
let trans =
  let alpha = 2 in
  let beta = 1 in
  let gamma = 0 in
  let x = "x" in
  let y = "y" in
  annot
    (tyabs alpha @@
     tyabs beta @@
     tyabs gamma @@
     abs x (F.TyEq (F.TyVar alpha, F.TyVar beta)) @@
     abs y (F.TyEq (F.TyVar beta, F.TyVar gamma)) @@
     use (var x) @@
     use (var y) @@
     annot (refl (F.TyVar gamma)) (F.TyEq (F.TyVar alpha, F.TyVar gamma)))

     @@
     F.TyForall (alpha,
     F.TyForall (beta,
     F.TyForall (gamma,
     F.TyEq (F.TyVar alpha, F.TyVar beta)
     --> (F.TyEq (F.TyVar beta, F.TyVar gamma)
         --> F.TyEq (F.TyVar alpha, F.TyVar gamma)))))

let bool_env =
  let bool_typedecl =
    let open Datatype in {
      name = Type "bool";
      type_params = [];
      data_kind = Variant;
      labels_descr = [
        {
          label_name = Label "True";
          type_name = Type "bool";
          arg_type = F.TyProduct [];
        } ; {
          label_name = Label "False";
          type_name = Type "bool";
          arg_type = F.TyProduct [];
        }
      ]
    }
  in
  Datatype.Env.add_decl option_env bool_typedecl

let bool_datatype =
  Datatype.Type "bool", []

let nat_env =
  let nat_typedecl =
    let open Datatype in {
      name = Type "nat";
      type_params = [];
      data_kind = Variant;
      labels_descr = [
        {
          label_name = Label "O";
          type_name = Type "nat";
          arg_type = F.TyProduct [];
        } ; {
          label_name = Label "S";
          type_name = Type "nat";
          arg_type = F.TyConstr (Type "nat", []);
        }
      ]
    }
  in
  Datatype.Env.add_decl bool_env nat_typedecl

let nat_datatype =
  Datatype.Type "nat", []

(* small gadt *)
let small_gadt_env =
  let small_gadt_typedecl =
    let alpha = 0 in
    let open Datatype in {
      name = Type "ty";
      type_params = [ alpha ];
      data_kind = Variant;
      labels_descr = [
        {
          label_name = Label "Nat";
          type_name = Type "ty";
          arg_type = F.TyEq (F.TyVar alpha, F.TyConstr nat_datatype);
        } ; {
          label_name = Label "Bool";
          type_name = Type "ty";
          arg_type = F.TyEq (F.TyVar alpha, F.TyConstr bool_datatype);
        }
      ];
    }
  in
  Datatype.Env.add_decl nat_env small_gadt_typedecl

let nat_pattern arg_type pat =
  pvariant
    (Datatype.Label "Nat")
    (Datatype.Type "ty", arg_type)
    pat

let bool_pattern arg_type pat =
  pvariant
    (Datatype.Label "Bool")
    (Datatype.Type "ty", arg_type)
    pat

(*
Λα.
  λ(x : μβ. {} * β).
  x
 *)
let mu_under_forall =
  let alpha = 1 in
  let beta = 0 in
  let x = "x" in
  tyabs alpha @@
  abs x (F.TyMu (beta, F.TyProduct [unit_type ; F.TyVar beta])) @@
  var x

(*
Λα.
  λ(w : Eq(α,nat)).
    use w in
    ( O : α )
 *)
let cast =
  let alpha = 0 in
  tyabs alpha @@
  abs "w" (F.TyEq (F.TyVar alpha, F.TyConstr nat_datatype)) @@
  use (var "w") @@
  annot (variant (Datatype.Label "O") nat_datatype unit) (F.TyVar alpha)

(*
Λα.
  λ(n : α ty).
    match_α n with
    | Nat p ->
        use (p : Eq(α,nat)) in (O : α)
    | Bool p ->
        use (p : Eq(α,bool)) in (True : α)
 *)
let match_gadt_default =
  let alpha = 0 in

  let nat_pat =
    nat_pattern [F.TyVar alpha] (pvar "p")
  in

  let nat_payoff =
    use
      (annot
         (var "p")
         (F.TyEq (F.TyVar alpha, F.TyConstr nat_datatype)))
      (annot
         (variant
            (Datatype.Label "O")
            nat_datatype
            unit)
         (F.TyVar alpha))
  in

  let bool_pat =
    bool_pattern [F.TyVar alpha] (pvar "p")
  in

  let bool_payoff =
    use
      (annot
         (var "p")
         (F.TyEq (F.TyVar alpha, F.TyConstr bool_datatype)))
      (annot
         (variant
            (Datatype.Label "True")
            bool_datatype
            unit)
         (F.TyVar alpha))
  in
  tyabs alpha @@
  abs "n" (F.TyConstr (Datatype.Type "ty", [F.TyVar alpha])) @@
  match_ (F.TyVar alpha) (var "n") [
    (nat_pat , nat_payoff);
    (bool_pat , bool_payoff)
  ]

(*
(Λα.
  λ(n : α ty).
    match_α n with
    | Nat p ->
        use (p : Eq(α,nat)) in (O : α)
    | Bool p ->
        use (p : Eq(α,bool)) in (True : α))
nat
(Nat (refl_nat))
 *)
let default_nat =
  app
    (tyapp match_gadt_default (F.TyConstr nat_datatype))
    (variant
       (Datatype.Label "Nat")
       (Datatype.Type "ty", [F.TyConstr nat_datatype])
       (refl (F.TyConstr nat_datatype)))

(*
(Λα.
  λ(n : α ty).
    match_α n with
    | Nat p ->
        use (p : Eq(α,nat)) in (O : α)
    | Bool p ->
        use (p : Eq(α,bool)) in (True : α))
bool
(Bool (refl_bool))
 *)
let default_bool =
    app
      (tyapp match_gadt_default (F.TyConstr bool_datatype))
      (variant
         (Datatype.Label "Bool")
         (Datatype.Type "ty", [F.TyConstr bool_datatype])
         (refl (F.TyConstr bool_datatype)))

(*
Λα.
  λ(n : α ty).
    match_α n with
    | Nat p ->
        use (p : Eq(α,nat)) in (O (. : unit) : α)
    | Bool p ->
        use (p : Eq(α,bool)) in (True (. : unit) : α)
 *)
let default_absurd_wrong =
  let alpha = 0 in

  let nat_pat =
    nat_pattern [F.TyVar alpha] (pvar "p")
  in

  let nat_payoff =
    use (annot (var "p") (F.TyEq (F.TyVar alpha, F.TyConstr nat_datatype))) @@
    annot
      (variant
         (Datatype.Label "O")
         nat_datatype
         (absurd unit_type))
      (F.TyVar alpha)
  in

  let bool_pat =
    bool_pattern [F.TyVar alpha] (pvar "p")
  in

  let bool_payoff =
    use (annot (var "p") (F.TyEq (F.TyVar alpha, F.TyConstr bool_datatype))) @@
    annot
      (variant
         (Datatype.Label "True")
         bool_datatype
         (absurd unit_type))
      (F.TyVar alpha)
  in

  tyabs alpha @@
  abs "n" (F.TyConstr (Datatype.Type "ty", [F.TyVar alpha])) @@
  match_ (F.TyVar alpha) (var "n") [
    (nat_pat , nat_payoff);
    (bool_pat , bool_payoff)
  ]

(*
Λα.
  λ(x : α ty).
    λ(y : α ty).
      match (x, y) with
      | (Nat p1, Nat p2) ->
          payoff1
      | (Bool p1, Bool p2) ->
          payoff2
      | (Nat p1, Bool p2) ->
          payoff3
      | (Bool p1, Nat p2) ->
          payoff4
*)
let test_absurd payoff1 payoff2 payoff3 payoff4 =
    let alpha = 0 in

    let variant_ty lbl pat =
      pvariant
          (Datatype.Label lbl)
          (Datatype.Type "ty", [F.TyVar alpha])
          pat
    in

    (* Helper functions for payoff *)

    (* use (p1 : Eq(α,dt1)) in use (p2 : Eq(α,dt2)) in payoff *)
    let double_use datatype1 datatype2 payoff=
      use (annot (var "p1") (F.TyEq (F.TyVar alpha, F.TyConstr datatype1))) @@
      use (annot (var "p2") (F.TyEq (F.TyVar alpha, F.TyConstr datatype2))) @@
      payoff
    in

    (*
      (Nat p1, Nat p2) ->
          use (p1 : Eq(α,nat)) in use (p2 : Eq(α,nat)) in payoff1
     *)
    let nat_nat_branch =
      ptuple [
          (variant_ty "Nat" (pvar "p1"));
          (variant_ty "Nat" (pvar "p2"));
      ] ,
      double_use nat_datatype nat_datatype payoff1

    (*
      (Bool p1, Bool p2) ->
          use (p1 : Eq(α,bool)) in use (p2 : Eq(α,bool)) in payoff2
     *)
    and bool_bool_branch =
      ptuple [
          (variant_ty "Bool" (pvar "p1"));
          (variant_ty "Bool" (pvar "p2"));
      ] ,
      double_use bool_datatype bool_datatype payoff2

    (*
      (Nat p1, Bool p2) ->
          use (p1 : Eq(α,nat)) in use (p2 : Eq(α,bool)) in payoff3
     *)
    and nat_bool_branch =
      ptuple [
          (variant_ty "Nat" (pvar "p1"));
          (variant_ty "Bool" (pvar "p2"));
      ] ,
      double_use nat_datatype bool_datatype payoff3

    (*
      (Bool p1, Nat p2) ->
          use (p1 : Eq(α,bool)) in use (p2 : Eq(α,nat)) in payoff4
     *)
    and bool_nat_branch =
      ptuple [
          (variant_ty "Bool" (pvar "p1"));
          (variant_ty "Nat" (pvar "p2"));
      ] ,
      double_use bool_datatype nat_datatype payoff4
    in

    tyabs alpha @@
    abs "x" (F.TyConstr (Datatype.Type "ty", [F.TyVar alpha])) @@
    abs "y" (F.TyConstr (Datatype.Type "ty", [F.TyVar alpha])) @@
    match_ unit_type (tuple [ var "x"; var "y" ]) [
      nat_nat_branch ;
      bool_bool_branch;
      nat_bool_branch;
      bool_nat_branch;
    ]

(*
Λα.
  λ(x : α ty).
    λ(y : α ty).
      match (x, y) with
      | (Nat p1, Nat p2) ->
          ()
      | (Bool p1, Bool p2) ->
          ()
      | (Nat p1, Bool p2) ->
          .
      | (Bool p1, Nat p2) ->
          .
*)
(* This example is ok : the two last branches are unreachable. *)
let test_absurd_ok =
  test_absurd
    unit
    unit
    (absurd unit_type)
    (absurd unit_type)


(*
Λα.
  λ(x : α ty).
    λ(y : α ty).
      match (x, y) with
      | (Nat p1, Nat p2) ->
          ()
      | (Bool p1, Bool p2) ->
          ()
      | (Nat p1, Bool p2) ->
          ()
      | (Bool p1, Nat p2) ->
          ()
*)
(* This example is ok : the two last branches are unreachable, but it is not
   mandatory to declare them as such. *)
let test_absurd_ok2 =
  test_absurd
    unit
    unit
    unit
    unit

(*
Λα.
  λ(x : α ty).
    λ(y : α ty).
      match (x, y) with
      | (Nat p1, Nat p2) ->
          .
      | (Bool p1, Bool p2) ->
          .
      | (Nat p1, Bool p2) ->
          .
      | (Bool p1, Nat p2) ->
          .
*)
(* This example is wrong : the first two branches are reachable, i.e. they
   don't introduce type inconsistencies in the environment *)
let test_absurd_wrong =
  test_absurd
    (absurd unit_type)
    (absurd unit_type)
    (absurd unit_type)
    (absurd unit_type)

let test_ok_from_ast msg datatype_env t =
  let test_ok () =
    Alcotest.(check unit) "type inference" (Test.CheckF.test datatype_env t) ()
  in
  Alcotest.(test_case msg `Quick test_ok)

let test_type_error msg datatype_env t =
  let test_error () =
    Alcotest.(check unit) "type inference"
      (Test.CheckF.test_error datatype_env t) ()
  in
  Alcotest.(test_case msg `Quick test_error)

let test_suite =
  [(
    "test F ast",
    [ test_ok_from_ast "let prod" Datatype.Env.empty let_prod;
      test_ok_from_ast "match with prod" Datatype.Env.empty match_with_prod;
      test_type_error "match variable bound twice" Datatype.Env.empty
        match_variable_bound_twice;
      test_type_error "not in env" Datatype.Env.empty not_in_env;
      test_ok_from_ast "unit" option_env unit;
      test_ok_from_ast "none" option_env none;
      test_ok_from_ast "some" option_env some;
      test_ok_from_ast "match none" option_env match_none;
      test_type_error "match deep variable bound twice" option_env
        match_variable_bound_twice_under_tuple;
      test_type_error "type equality" Datatype.Env.empty type_eq;
      test_ok_from_ast "introduce type equality" Datatype.Env.empty
        introduce_type_eq;
      test_ok_from_ast "symmetry" Datatype.Env.empty sym;
      test_ok_from_ast "transitivity" Datatype.Env.empty trans;
      test_ok_from_ast "mu under forall" Datatype.Env.empty mu_under_forall;
      test_ok_from_ast "cast" nat_env cast;
      test_ok_from_ast "default" small_gadt_env match_gadt_default;
      test_ok_from_ast "default nat" small_gadt_env default_nat;
      test_ok_from_ast "default bool" small_gadt_env default_bool;
      test_type_error "default absurd wrong" small_gadt_env default_absurd_wrong;
      test_ok_from_ast "pair of gadt" small_gadt_env test_absurd_ok;
      test_ok_from_ast "pair of gadt" small_gadt_env test_absurd_ok2;
      test_type_error "pair of gadt" small_gadt_env test_absurd_wrong;
    ]
  )]

let () =
  Alcotest.run "F test suite" test_suite
