(* P is a superset of both ML and F. It is intended only for printing *)

type tyvar = string

type typ =
  | TyVar of tyvar
  | TyArrow of typ * typ
  | TyProduct of typ list
  | TyForall of tyvar * typ
  | TyMu of tyvar * typ
  | TyConstr of datatype
  | TyEq of typ * typ

and datatype = Datatype.tyconstr_id * typ list

type rigidity = Flexible | Rigid

type recursive_status = ML.recursive_status = Recursive | Non_recursive

type type_annotation = rigidity * tyvar list * typ
  (* some <flexible vars> . <ty> *)

type tevar = string

type term =
  | Var of tevar
  | Hole of typ option * term list
  | Abs of pattern * term
  | App of term * term
  | Let of recursive_status * pattern * term * term
  | Annot of term * type_annotation
  | TyAbs of tyvar * term
  | TyApp of term * typ
  | Tuple of term list
  | Proj of int * term
  | Inj of (typ list) option * int * term
  | Variant of Datatype.label_id * datatype option * term option
  | Match of typ option * term * branch list
  | Absurd of typ
  | Refl of typ
  | Use of term * term

and branch = pattern * term

and pattern =
  | PVar of tevar
  | PWildcard
  | PInj of (typ list) option * int * pattern
  | PTuple of pattern list
  | PVariant of Datatype.label_id * datatype option * pattern option
  | PAnnot of pattern * type_annotation
