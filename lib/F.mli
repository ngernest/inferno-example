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
  | TyProduct of ('a,'b) typ list
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyConstr of ('a, 'b) datatype
  | TyEq of ('a, 'b) typ * ('a, 'b) typ

and ('a, 'b) datatype = Datatype.tyconstr_id * ('a, 'b) typ list

type tyvar =
    int

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
  | Var of loc * tevar
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

type nominal_term =
    (tyvar, tyvar) term

type nominal_pattern =
    (tyvar, tyvar) pattern

type nominal_branch =
    nominal_pattern * nominal_term

type debruijn_term =
    (DeBruijn.index, unit) term

(* -------------------------------------------------------------------------- *)

(* Constructors. *)

val ftyabs: loc:loc -> 'b list -> ('a, 'b) term -> ('a, 'b) term
val ftyapp: loc:loc -> ('a, 'b) term -> ('a, 'b) typ list -> ('a, 'b) term

(* -------------------------------------------------------------------------- *)

module Type : sig
  (* Type-in-type weakening and substitution. *)

  (* [lift w k ty] is the type [ty] where the variables at or above index [k]
     are lifted up by [w]. *)
  val lift: int -> DeBruijn.index -> debruijn_type -> debruijn_type

  (* [subst xty x ty] is the type [ty] where the type variable [x] has been
     replaced with the type [xty]. *)
  val subst: debruijn_type -> DeBruijn.index -> debruijn_type -> debruijn_type

  (* Translation of nominal types to de Bruijn types. *)
  val translate: nominal_type -> debruijn_type
  val translate_open: DeBruijn.Nominal2deBruijn(Int).env -> nominal_type -> debruijn_type
end

(* -------------------------------------------------------------------------- *)

module Term : sig

  (* Translation of nominal terms to de Bruijn terms. *)
  val translate: nominal_term -> debruijn_term
end

val translate_env: nominal_datatype_env -> debruijn_datatype_env
