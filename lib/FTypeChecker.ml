open F

type type_error =
  | TypeMismatch of debruijn_type * debruijn_type
  | ArityMismatch of arity_requirement * debruijn_type
  | NotAnArrow of debruijn_type
  | NotAProduct of debruijn_type
  | NotAForall of debruijn_type
  | NotAnEqual of debruijn_type
  | UnboundTermVariable of tevar
  | UnboundTypeVariable of tyvar
  | TwoOccurencesOfSameVariable of string
  | ContextNotAbsurd
  | UnexpectedRecord
  | DeclarationNotFound of Datatype.tyconstr_id
  | LabelNotFound of Datatype.label_id


and arity_requirement = Index of int | Total of int

exception TypeError of loc * type_error

(* -------------------------------------------------------------------------- *)

(* A type environment maps term variables to types in de Bruijn's representation. *)

(* Our term variables are in nominal representation, which allows us to represent
   the environment as a binary search tree. One difficulty is that when we enter a
   new type variable binder [TyAbs], we must (conceptually) shift every type in
   the range of the environment up by one. When term variables are in de Bruijn
   notation and the environment is a list, this is easily done by inserting a mark
   in front of the environment. Here, we must be more clever. We maintain an [N2DB]
   environment that tells us, for every *term* variable, how long ago it was bound,
   that is, how many *type* variables were introduced since then. Hence, this tells
   us by how much we must shift its type. It's really a bit too clever, but let's
   do this for fun. *)

module TermVar =
  String

module TermVarMap =
  Map.Make(TermVar)

module N2DB =
  DeBruijn.Nominal2deBruijn(TermVar)

(* We use a union-find data structure to represent equalities between rigid
   variables and types. We need the ability to snapshot and rollback changes, to
   undo the addition of an equality to the environment. *)
module UF = struct
  include UnionFind.Make(UnionFind.StoreVector)
  type 'a elem = 'a rref
end

module S =
  Structure

(* We translate types into union-find graphs to check equality.
   μ-types create cyclic graphs. Each vertex represents a type expression.
   GADTs can add type equalities in the context and we represent
   this by unifying their vertices in the union-find graph. This is
   possible only when they have compatible structures (or one of the
   side has no structure), otherwise the equality is inconsistent. *)
type vertex =
  structure option UF.elem

and structure =
  (* Corresponds to types from the source language (arrow, product, ...). *)
  | SStruct of vertex S.structure
  (* Represents ∀α.τ. We use De Bruijn levels, so we don't need to name
     explicitly the bound variable α. *)
  | SForall of vertex
  (* A De Bruijn level corresponding to a ∀-bound variable. Using levels
     instead of indices makes the equality test easier. *)
  | SForallLevel of int

(* The global store of the union-find. *)
type uf_store = structure option UF.store

(* A mapping from rigid variables to union-find vertices. *)
type uf_tyvars = structure option UF.elem list

(* If the type equations introduced are inconsistent, then no need for
   [store] and [tyvars] *)
type equations_env =
  | Equations of { store: uf_store ; tyvars: uf_tyvars }
  | Inconsistent

type env = {
  (* A mapping of term variables to types. *)
  types: debruijn_type TermVarMap.t;
  (* A translation environment of TERM variables to TYPE indices. *)
  names: N2DB.env;
  (* We keep trace of whether or not the typing equations is consistent *)
  equations: equations_env;
}

let empty = {
  types = TermVarMap.empty;
  names = N2DB.empty;
  equations = Equations { store = UF.new_store() ; tyvars = [] };
}

let lookup ~loc { types; names; _ } x =
  (* Obtain the type associated with [x]. *)
  match TermVarMap.find x types with
  | exception Not_found ->
    raise (TypeError (loc, UnboundTermVariable x))
  | ty ->
    (* Find how long ago [x] was bound. *)
    let w = N2DB.lookup names x in
    (* Shift the type [ty] by this amount, so that it makes sense in the
       current scope. *)
    Type.lift w 0 ty

let extend_with_tevar { types; names; equations } x ty =
  (* Map the name [x] to [ty], and record when it was bound, without
     incrementing the time. *)
  { types = TermVarMap.add x ty types;
    names = N2DB.slide names x;
    equations; }

let extend_with_tevar_no_dup ~loc ({ types; _ } as env) x ty =
  if TermVarMap.mem x types then
    raise (TypeError (loc, TwoOccurencesOfSameVariable x));
  extend_with_tevar env x ty

let extend_with_tyvar { types; names; equations } =
  match equations with
  | Inconsistent ->
     { types; names; equations }
  | Equations { store; tyvars } ->
     (* Create a fresh vertex for the new type variable *)
     let v = UF.make store None in
     (* Extend the environment of type variables *)
     let tyvars = v :: tyvars in
     (* Increment the time. *)
     let names = N2DB.bump names in
     { types; names ; equations = Equations { store ; tyvars } }

(* -------------------------------------------------------------------------- *)

(* Destructors. *)

let unfold ty =
  match ty with
  | TyMu ((), body) ->
      Type.subst ty 0 body
  | _ ->
      assert false

let rec as_arrow ~loc ty =
  match ty with
  | TyArrow (ty1, ty2) ->
      ty1, ty2
  | TyMu _ ->
      as_arrow ~loc (unfold ty)
  | _ ->
      raise (TypeError (loc, NotAnArrow ty))

let rec as_product ~loc ty =
  match ty with
  | TyProduct tys ->
      tys
  | TyMu _ ->
      as_product ~loc (unfold ty)
  | _ ->
      raise (TypeError (loc, NotAProduct ty))

let rec as_forall ~loc ty =
  match ty with
  | TyForall ((), ty) ->
      ty
  | TyMu _ ->
      as_forall ~loc (unfold ty)
  | _ ->
      raise (TypeError (loc, NotAForall ty))

(* -------------------------------------------------------------------------- *)

(* A sound approximation of the equality test. *)

(* The System F types produced by an ML type inference algorithm cannot
   contain [TyForall] under [TyMu]. In this restricted setting, deciding
   type equality is relatively easy. We map each type to a graph of
   unification variables (where every variable has rigid structure),
   then we check that the two graphs can be unified. *)

exception Clash =
  Structure.Iter2

(* This function assumes no universal quantification inside a μ-type, because
   it would be difficult to check type equality otherwise. The boolean
   [inside_mu] tracks whether we are already under a μ quantifier. *)
let rec translate ~loc ~inside_mu store (env : vertex list) (ty : F.debruijn_type)
  : vertex
  = match ty with

  | TyVar x ->
      begin
        (* If the type is closed, then [x] was bound by a quantifier before and
           was added to the environment. *)
        try
          List.nth env x
        with Not_found ->
          raise (TypeError (loc, UnboundTypeVariable x))
      end

  | TyMu ((), ty) ->
      (* Extend the environment with a mapping of this μ-bound variable
         to a fresh vertex. *)
      let v1 = UF.make store None in
      let env = v1 :: env in
      (* Translate the body. *)
      let v2 = translate ~loc ~inside_mu:true store env ty in
      (* Unify the vertices [v1] and [v2], keeping [v2]'s structure. *)
      let v = UF.merge store (fun _ s2 -> s2) v1 v2 in
      v

  | TyForall ((), ty) ->
      assert (not inside_mu);
      (* Extend the environment with a mapping of this forall-bound variable
         to a fresh vertex. *)
      let v1 = UF.make store (Some (SForallLevel (List.length env))) in
      let env = v1 :: env in
      (* Translate the body. *)
      let v2 = translate ~loc ~inside_mu store env ty in
      UF.make store (Some (SForall v2))

  | TyArrow (ty1, ty2) ->
      let v1 = translate ~loc ~inside_mu store env ty1
      and v2 = translate ~loc ~inside_mu store env ty2 in
      UF.make store (Some (SStruct (S.TyArrow (v1, v2))))

  | TyProduct tys ->
      let vs = translate_list ~loc ~inside_mu store env tys in
      UF.make store (Some (SStruct (S.TyProduct vs)))

  | TyConstr (id, tys) ->
      let vs = translate_list ~loc ~inside_mu store env tys in
      UF.make store (Some (SStruct (S.TyConstr (id, vs))))

  | TyEq (ty1, ty2) ->
      let v1 = translate ~loc ~inside_mu store env ty1
      and v2 = translate ~loc ~inside_mu store env ty2 in
      UF.make store (Some (SStruct (S.TyEq (v1, v2))))

and translate_list ~loc ~inside_mu store env tys =
  List.map (translate ~loc ~inside_mu store env) tys

let insert q v1 v2 =
  Stack.push (v1, v2) q

let unify_struct q s1 s2 =
  match s1, s2 with
  | SForallLevel x1, SForallLevel x2 ->
      if x1 <> x2 then raise Clash
  | SStruct s1, SStruct s2 ->
      Structure.iter2 (insert q) s1 s2
  | SForall s1, SForall s2 ->
      insert q s1 s2
  | SForallLevel _, _
  | SStruct _, _
  | SForall _, _ ->
      raise Clash


(* We need two operations on equalities between types:
   - add an equality to the equations in the environment
   - check if a given equality holds modulo the equations in the environment *)

(* Both operations can be described as first decomposing a given equality
   "ty1 = ty2" into "simple equalities" between a rigid variable and a type.
   In fact, the union-find data structure that we use to represent an
   environment of equations store exactly those simple equalities. *)

(* Then:
   - to add an equality, we modify our environment by unifying the type
     variables with the equated type
   - to check an equality, we check that the simple equalities are already
     valid in the equations of the environment, and fail otherwise *)

(* The decomposition process does not produce simple equalities if the
   provided equality is absurd ("int * int = int * bool").
   Then:
   - if we are adding this equality to the environment, we record that the
     environment is now Inconsistent
   - if we are checking the equality (in a consistent environment), we fail *)

(* The functions below implement a unification procedure that implements both
   these operations, depending on a [mode] parameter:
   - in [Input] mode, they add an equality to the environment
   - in [Check] mode, they check that the equality holds modulo the equations
   in the environment *)

type mode = Input | Check

let merge_struct mode q so1 so2 : structure option =
  match so1, so2 with
  | Some s1, Some s2 ->
     unify_struct q s1 s2;
     so1
  | None, so | so, None ->
     match mode with
     | Input ->
        so
     | Check ->
        raise Clash

let rec unify mode store q (v1 : vertex) (v2 : vertex) =
  let (_ : vertex) = UF.merge store (merge_struct mode q) v1 v2 in
  unify_pending mode store q

and unify_pending mode store q =
  match Stack.pop q with
  | v1, v2 ->
      unify mode store q v1 v2
  | exception Stack.Empty ->
      ()

let unify mode store v1 v2 =
  let q = Stack.create() in
  unify mode store q v1 v2

let unify_types ~loc mode env ty1 ty2 =
  match env.equations with
  | Inconsistent ->
     true
  | Equations { store ; tyvars } ->
     try
       let v1 = translate ~loc ~inside_mu:false store tyvars ty1
       and v2 = translate ~loc ~inside_mu:false store tyvars ty2 in
       unify mode store v1 v2;
       true
     with Clash ->
       false

(* -------------------------------------------------------------------------- *)

(* Re-package the type unification as a type equality check. *)
let enforce_equal ~loc env ty1 ty2 : unit =
  if not (unify_types ~loc Check env ty1 ty2) then
    raise (TypeError (loc, TypeMismatch (ty1, ty2)))

(* Re-package the type unification as an addition in the environment. *)
let add_equation ~loc env ty1 ty2 : env =
  if unify_types ~loc Input env ty1 ty2 then
    env
  else
    { env with equations = Inconsistent }

let copy_env env store tyvars =
  let store_copy = UF.copy store in
  let equations = Equations { store = store_copy; tyvars } in
  { env with equations }

(* -------------------------------------------------------------------------- *)

(* The type-checker. *)

let nth_type ~loc ty tys i =
  if i < 0 || i >= List.length tys then
    raise (TypeError (loc, ArityMismatch (Index i, ty)))
  else
    List.nth tys i

let rec typeof datatype_env env (t : debruijn_term) : debruijn_type =
  let typeof = typeof datatype_env in
  match t with
  | Var (loc, x) ->
      lookup ~loc env x
  | Hole (_, ty, ts) ->
      let on_subterm t =
        ignore (typeof env t) in
      List.iter on_subterm ts;
      ty
  | Annot (loc, t, ty) ->
      enforce_equal ~loc env (typeof env t) ty;
      ty
  | Abs (_, x, ty1, t) ->
      let ty2 = typeof (extend_with_tevar env x ty1) t in
      TyArrow (ty1, ty2)
  | App (loc, t, u) ->
      let ty1, ty2 = as_arrow ~loc (typeof env t) in
      enforce_equal ~loc env (typeof env u) ty1;
      ty2
  | Let (loc, rec_, x, ty, t, u) ->
      let env_with_x = extend_with_tevar env x ty in
      let def_env = match rec_ with
        | Non_recursive -> env
        | Recursive -> env_with_x
      in
      enforce_equal ~loc def_env (typeof def_env t) ty;
      typeof env_with_x u
  | TyAbs (_, (), t) ->
      TyForall ((), typeof (extend_with_tyvar env) t)
  | TyApp (loc, t, ty2) ->
      Type.subst ty2 0 (as_forall ~loc (typeof env t))
  | Tuple (_, ts) ->
      let tys = List.map (typeof env) ts in
      TyProduct tys
  | Proj (loc, i, t) ->
      let ty = typeof env t in
      let tys = as_product ~loc ty in
      nth_type ~loc ty tys i
  | Variant (loc, lbl, dty, t) ->
      let arg_type = typeof_variant datatype_env ~loc lbl dty in
      let ty = typeof env t in
      enforce_equal ~loc env ty arg_type;
      TyConstr dty
  | LetProd (loc, xs, t, u) ->
      let ty = typeof env t in
      let tys = as_product ~loc ty in
      if List.length xs <> List.length tys then
        raise (TypeError (loc, ArityMismatch (Total (List.length xs), ty)));
      let env = List.fold_left2 extend_with_tevar env xs tys in
      typeof env u
  | Match (loc, ty, t, brs) ->
      let scrutinee_ty = typeof env t in
      let tys = List.map (typeof_branch datatype_env env scrutinee_ty) brs in
      List.iter (fun ty2 -> enforce_equal ~loc env ty ty2) tys;
      ty
  | Absurd (loc, ty) ->
      begin
        match env.equations with
        | Inconsistent ->
           ty
        | Equations _ ->
           raise (TypeError (loc, ContextNotAbsurd))
      end
  | Refl (_, ty) ->
      TyEq (ty, ty)
  | Use (loc, t, u) ->
     begin
       match env.equations with
       | Inconsistent ->
          typeof env u
       | Equations { store ; tyvars } ->
          let env = copy_env env store tyvars in
          match typeof env t with
          | TyEq (ty1, ty2) ->
             let env = add_equation ~loc env ty1 ty2 in
             typeof env u
          | ty ->
             raise (TypeError (loc, NotAnEqual ty))
     end

and typeof_variant datatype_env ~loc lbl (tid, tyargs) =
  let Datatype.{ data_kind ; type_params ; labels_descr; _ } =
    try
      Datatype.Env.find_decl datatype_env tid
    with Datatype.Env.DeclarationNotFound _ ->
      raise (TypeError (loc, DeclarationNotFound tid))
  in
  let Datatype.{ arg_type; _ } =
    try
      List.find (fun l -> l.Datatype.label_name = lbl) labels_descr
    with Datatype.Env.LabelNotFound _ ->
      raise (TypeError (loc, LabelNotFound lbl))
  in
  begin
    match data_kind with
    | Datatype.Variant ->
        ()
    | Datatype.Record ->
        raise Datatype.Env.UnexpectedRecord
  end;
  List.fold_right2 (fun ty () arg_type ->
    Type.subst ty 0 arg_type
  ) tyargs type_params arg_type

and typeof_branch datatype_env env scrutinee_ty (pat, rhs) : debruijn_type =
  let new_env = binding_pattern datatype_env env scrutinee_ty pat in
  typeof datatype_env new_env rhs

and binding_pattern datatype_env env scrutinee_ty pat : env =
  let binding_pattern = binding_pattern datatype_env in
  match pat with
  | PVar (loc, x) ->
      extend_with_tevar_no_dup ~loc env x scrutinee_ty
  | PWildcard _ ->
      env
  | PAnnot (loc, pat, ty) ->
      enforce_equal ~loc env scrutinee_ty ty;
      binding_pattern env ty pat
  | PTuple (loc, ps) ->
      let tys = as_product ~loc scrutinee_ty in
      if List.length ps <> List.length tys then
        raise
          (TypeError (loc, ArityMismatch (Total (List.length ps), scrutinee_ty)));
      List.fold_left2 binding_pattern env tys ps
  | PVariant (loc, lbl, dty, pat) ->
      let arg_type = typeof_variant datatype_env ~loc lbl dty in
      enforce_equal ~loc env scrutinee_ty (TyConstr dty);
      binding_pattern env arg_type pat

let typeof datatype_env t =
  typeof datatype_env empty t

let typeof_result datatype_env u =
  match typeof datatype_env u with
  | v ->
      Ok v
  | exception TypeError (loc, e) ->
      Error (loc, e)
