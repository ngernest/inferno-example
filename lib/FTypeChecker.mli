open F

(* A type-checker for System F. *)

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

(* An arity-related requirement on a certain (sum or product) type
   arising during type-checking:
   - [Index i]: [i] should be a valid index within the type
   - [Total n]: the type should have [n] components.
*)
and arity_requirement = Index of int | Total of int

exception TypeError of loc * type_error

(* [typeof env t] type-checks the closed term [t] in datatype environment [env]
   and constructs its type.

   @raise [TypeError] if a type error occurs during type-checking. *)
val typeof: debruijn_datatype_env -> debruijn_term -> debruijn_type

(* Similar to {!typeof}, but returns a [result] type instead of raising an exception. *)
val typeof_result:
  debruijn_datatype_env -> debruijn_term -> (debruijn_type, loc * type_error) result
