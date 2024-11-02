(* This is the source calculus of the sample client. It is a core ML. *)

(* Nominal representation of term variables, type variables and binders. *)

type 'a list = 'a List.t =
  | []
  | (::) of 'a * 'a list
  [@@deriving compare]

type loc = Utils.loc

(* We generate a comparison function [compare_loc] that ignores all locations.
   This is useful while testing. *)
let compare_loc _ _ = 0

type tevar = String.t [@@deriving compare]
type tyvar = String.t [@@deriving compare]

type typ =
  | TyVar of loc * tyvar
  | TyArrow of loc * typ * typ
  | TyProduct of loc * typ list
  | TyConstr of loc * Datatype.TyConstrId.t * typ list
 [@@deriving compare]

type rigidity = Flexible | Rigid
  [@@deriving compare]

type type_annotation = rigidity * tyvar list * typ [@@deriving compare]
  (* some <flexible vars> . <ty> *)

type recursive_status = Recursive | Non_recursive
  [@@deriving compare]

type term =
  | Var of loc * tevar
  | Hole of loc * term list
  | Abs of loc * tevar * term
  | App of loc * term * term
  | Let of loc * recursive_status * tevar * term * term
  | Annot of loc * term * type_annotation
  | Tuple of loc * term list
  | LetProd of loc * tevar list * term * term
  | Variant of loc * Datatype.LabelId.t * term Option.t
  | Match of loc * term * branch list

and branch = pattern * term

and pattern =
  | PVar of loc * tevar
  | PWildcard of loc
  | PAnnot of loc * pattern * type_annotation
  | PVariant of loc * Datatype.LabelId.t * pattern Option.t
  | PTuple of loc * pattern list
  [@@deriving compare]

type datatype_env = (tyvar, typ option) Datatype.Env.t
