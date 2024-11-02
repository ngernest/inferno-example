(* This is the target calculus of the sample client. It is a core System F. *)

(* -------------------------------------------------------------------------- *)

(* Types. *)

(* We include recursive types [TyMu] in the target calculus, not only because
   we might wish to support them, but also because even if we disallow them,
   they can still arise during unification (the occurs check is run late), so
   we must be able to display them as part of a type error message. *)

(* Types mixing ∀ and μ are difficult to compare in general. To simplify
   equality checking, we do not allow ∀ under μ.
   For instance :
           ∀ a. μ t. a -> t is allowed
           μ t . ∀ a . (a -> t) is not allowed
           μ t . (∀ a . a) -> t is not allowed *)

(* We also include a type equality witness [TyEq]. *)

(* Nominal or de Bruijn representation of type variables and binders. The
   nominal representation is more convenient when translating from ML to F,
   while the de Bruijn representation is more convenient when type-checking
   F. *)

type loc = Utils.loc

type ('a, 'b) typ =
  | TyVar of 'a
  | TyArrow of ('a, 'b) typ * ('a, 'b) typ
  | TyProduct of ('a, 'b) typ list
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyConstr of ('a, 'b) datatype
  | TyEq of ('a, 'b) typ * ('a, 'b) typ

and ('a, 'b) datatype = Datatype.tyconstr_id * ('a, 'b) typ list

type tyvar = int

type nominal_type =
    (tyvar, tyvar) typ

type nominal_datatype =
    (tyvar, tyvar) datatype

type debruijn_type =
    (DeBruijn.index, unit) typ

type nominal_datatype_env =
    (tyvar, nominal_type) Datatype.Env.t

type debruijn_datatype_env =
    (unit, debruijn_type) Datatype.Env.t

(* -------------------------------------------------------------------------- *)

(* Terms. *)

(* Nominal representation of term variables and binders. *)

(* Nominal or de Bruijn representation of type variables and binders. *)

(* We include a term [Refl] that represents a type equality witness.
   Note that it has only one type argument but is typed as a witness for
   an equality between two possibly distinct types (see [TyEq] above).

   [Use] is a construct that "opens" a type equality. That is, it allows us to
   reason in a context where two types are assumed to be equals.
   It is supposed to be used with a type equality witness as a left-hand side :

           use (eq : TyEq (ty1, ty2)) in
           ... (* here ty1 and ty2 are assumed to be equal *)

   Doing this might introduce inconsistent assumptions about types (this can
   occur for example inside a pattern matching). That is why we introduce
   a construct [Absurd], that can be used as a placeholder in pieces of code
   with inconsistent equations in the environment and that are thus
   unreachable. *)

type tevar =
  string

type ('a, 'b) term =
  | Var of loc *  tevar
  | Hole of loc * ('a, 'b) typ * ('a, 'b) term list
  | Annot of loc * ('a, 'b) term * ('a, 'b) typ
  | Abs of loc * tevar * ('a, 'b) typ * ('a, 'b) term
  | App of loc * ('a, 'b) term * ('a, 'b) term
  | Let of loc * rec_status * tevar * ('a, 'b) typ * ('a, 'b) term * ('a, 'b) term
  | TyAbs of loc * 'b * ('a, 'b) term
  | TyApp of loc * ('a, 'b) term * ('a, 'b) typ
  | Tuple of loc * ('a, 'b) term list
  | Proj of loc * int * ('a, 'b) term
  | LetProd of loc * tevar list * ('a, 'b) term * ('a, 'b) term
  | Variant of loc * Datatype.label_id * ('a, 'b) datatype * ('a,'b) term
  | Match of loc * ('a,'b) typ * ('a,'b) term * ('a,'b) branch list
  | Absurd of loc * ('a,'b) typ
  | Refl of loc * ('a,'b) typ
  | Use of loc * ('a,'b) term * ('a,'b) term

and rec_status = Recursive | Non_recursive

and ('a,'b) branch = ('a,'b) pattern * ('a,'b) term

and ('a,'b) pattern =
  | PVar of loc * tevar
  | PAnnot of loc * ('a, 'b) pattern * ('a, 'b) typ
  | PWildcard of loc
  | PTuple of loc * ('a,'b) pattern list
  | PVariant of loc * Datatype.label_id * ('a, 'b) datatype * ('a,'b) pattern

type nominal_term = (tyvar, tyvar) term
type nominal_pattern = (tyvar, tyvar) pattern
type nominal_branch = nominal_pattern * nominal_term

type debruijn_term =
    (DeBruijn.index, unit) term

(* -------------------------------------------------------------------------- *)

(* Constructors. *)

let ftyabs ~loc vs t =
  List.fold_right (fun v t -> TyAbs (loc, v, t)) vs t
let ftyapp ~loc t tys =
  List.fold_left (fun t ty -> TyApp (loc, t, ty)) t tys

(* -------------------------------------------------------------------------- *)

(* Boilerplate code for type-in-type substitutions. *)

module TypeVar : DeBruijn.VAR
  with type ('a, 'b) v = ('a, 'b) typ
= struct

  type ('v, 'b) v =
      ('v, 'b) typ

  let var x =
    TyVar x

end

module TypeInType : DeBruijn.TRAVERSE
  with type ('v, 'b) v = ('v, 'b) typ
   and type ('v, 'b) t = ('v, 'b) typ
= struct

  type ('v, 'b) v =
      ('v, 'b) typ

  type ('v, 'b) t =
      ('v, 'b) typ

  (* I note that we could perform physical equality tests in [traverse]
     so as to preserve sharing when possible, but that would require use
     of [Obj.magic]. Let's just not do it in this demo. *)

  let rec traverse lookup extend env ty =
    let trav env = traverse lookup extend env in
    match ty with
    | TyVar x ->
        lookup env x
    | TyArrow (ty1, ty2) ->
        let ty1' = trav env ty1
        and ty2' = trav env ty2 in
        TyArrow (ty1', ty2')
    | TyProduct tys ->
        let tys' = List.map (trav env) tys in
        TyProduct tys'
    | TyConstr (tyconstr, tys) ->
        let tys' = List.map (trav env) tys in
        TyConstr (tyconstr, tys')
    | TyForall (x, ty1) ->
        let env, x = extend env x in
        let ty1' = trav env ty1 in
        TyForall (x, ty1')
    | TyMu (x, ty1) ->
        let env, x = extend env x in
        let ty1' = trav env ty1 in
        TyMu (x, ty1')
    | TyEq (ty1, ty2) ->
        let ty1' = trav env ty1 in
        let ty2' = trav env ty2 in
        TyEq (ty1', ty2')
end

(* -------------------------------------------------------------------------- *)

(* Boilerplate code for type-in-term substitutions. *)

module TypeInTerm : DeBruijn.TRAVERSE
  with type ('v, 'b) v = ('v, 'b) typ
  with type ('v, 'b) t = ('v, 'b) term
= struct

  type ('v, 'b) v =
      ('v, 'b) typ

  type ('v, 'b) t =
      ('v, 'b) term

  let rec traverse lookup extend env t =
    let trav env = traverse lookup extend env in
    let trav_ty env ty =
      TypeInType.traverse lookup extend env ty in
    match t with
    | Var (pos, x) ->
        Var (pos, x)
    | Hole (pos, ty, ts) ->
      let ty' = trav_ty env ty in
      let ts' = List.map (trav env) ts in
      Hole (pos, ty', ts')
    | Annot (pos, t, ty) ->
        let t' = trav env t
        and ty' = trav_ty env ty in
        Annot (pos, t', ty')
    | Abs (pos, x, ty, t) ->
        let ty' = trav_ty env ty
        and t' = trav env t in
        Abs (pos, x, ty', t')
    | App (pos, t1, t2) ->
        let t1' = trav env t1
        and t2' = trav env t2 in
        App (pos, t1', t2')
    | Let (pos, rec_, x, ty, t1, t2) ->
        let ty' = trav_ty env ty in
        let t1' = trav env t1
        and t2' = trav env t2 in
        Let (pos, rec_, x, ty', t1', t2')
    | TyAbs (pos, x, t) ->
        let env, x = extend env x in
        let t' = trav env t in
        TyAbs (pos, x, t')
    | TyApp (pos, t, ty) ->
        let t' = trav env t
        and ty' = trav_ty env ty in
        TyApp (pos, t', ty')
    | Tuple (pos, ts) ->
        let ts' = List.map (trav env) ts in
        Tuple (pos, ts')
    | Proj (pos, i, t) ->
        let t' = trav env t in
        Proj (pos, i, t')
    | LetProd (pos, xs, t1, t2) ->
        let t1' = trav env t1
        and t2' = trav env t2 in
        LetProd (pos, xs, t1', t2')
    | Variant (pos, lbl, dty, t) ->
        let dty' = traverse_datatype lookup extend env dty
        and t' = trav env t in
        Variant (pos, lbl, dty', t')
    | Match (pos, ty, t, brs) ->
        let ty' = trav_ty env ty in
        let t' = trav env t
        and brs' = List.map (traverse_branch lookup extend env) brs in
        Match (pos, ty', t', brs')
    | Absurd (pos, ty) ->
        let ty' = trav_ty env ty in
        Absurd (pos, ty')
    | Refl (pos, ty) ->
        let ty' = trav_ty env ty in
        Refl (pos, ty')
    | Use (pos, t, u) ->
        let t' = trav env t in
        let u' = trav env u in
        Use (pos, t', u')

  and traverse_datatype lookup extend env (tid, tyargs) =
    (tid, List.map (TypeInType.traverse lookup extend env) tyargs)

  and traverse_branch lookup extend env (pat,t) =
    (traverse_pattern lookup extend env pat,
     traverse lookup extend env t)

  and traverse_pattern lookup extend env pat =
    let trav env = traverse_pattern lookup extend env in
    match pat with
    | PVar (pos, x) ->
        PVar (pos, x)
    | PWildcard pos ->
        PWildcard pos
    | PAnnot (pos, p, ty) ->
        let p' = trav env p
        and ty' = TypeInType.traverse lookup extend env ty in
        PAnnot (pos, p', ty')
    | PTuple (pos, ps) ->
        let ps' = List.map (trav env) ps in
        PTuple (pos, ps')
    | PVariant (pos, lbl, dty, pat) ->
        let dty' = traverse_datatype lookup extend env dty
        and pat' = trav env pat in
        PVariant (pos, lbl, dty', pat')

end

(* -------------------------------------------------------------------------- *)

(* Type-in-type weakening and substitution. *)

module Type = struct
  include DeBruijn.MakeLift(TypeVar)(TypeInType)

  include DeBruijn.MakeSubst(TypeVar)(TypeInType)(TypeInType)

  include DeBruijn.MakeTranslate(TypeVar)(TypeInType)(Int)
end

(* -------------------------------------------------------------------------- *)

(* Translation of nominal terms to de Bruijn terms. *)

module Term = struct
  include DeBruijn.MakeTranslate(TypeVar)(TypeInTerm)(Int)
end


module N2DB = DeBruijn.Nominal2deBruijn(Int)

(* Translate a nominal-F datatype description into a De Bruijn version *)
let translate_datatype tdescr =

  (* We create a De Bruijn environemnt from the nominal type-parameters *)
  let params_env : N2DB.env =
    List.fold_left N2DB.extend N2DB.empty tdescr.Datatype.type_params
  in

  let translate_label ldescr =
    let new_arg_type =
      Type.translate_open params_env ldescr.Datatype.arg_type
    in
    Datatype.{
      label_name = ldescr.label_name;
      type_name = ldescr.type_name;
      arg_type = new_arg_type;
    }
  in

  let new_type_params =
    List.map (fun _param -> ()) tdescr.Datatype.type_params
  in
  let new_labels_descr =
    List.map translate_label tdescr.Datatype.labels_descr
  in

  (* The name and kind of data stay the same, only the type parameters and
     labels description need to change. *)
  Datatype.{
      name = tdescr.name;
      type_params = new_type_params;
      data_kind = tdescr.data_kind;
      labels_descr = new_labels_descr;
  }

let translate_env (env : nominal_datatype_env)
    : debruijn_datatype_env =
  Datatype.Env.map translate_datatype env
