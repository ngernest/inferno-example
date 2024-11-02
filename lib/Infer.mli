type error =
  | Unbound of ML.tevar
  | Unify of F.nominal_type * F.nominal_type
  | Cycle of F.nominal_type
  | VariableConflict of ML.tevar
  | VariableScopeEscape
  | Unsupported of string

exception Error of Utils.loc * error

(* Contraint generation, constraint solving and elaboration, combined. *)
val translate: rectypes:bool -> ML.datatype_env -> ML.term -> F.nominal_term

(* [translate_with_hook] is identical to [translate], except it takes a user
   hook that is invoked at the end of the constraint solving phase, before
   the elaboration phase. A pair of the hook's result and of the elaborated
   term is returned in the end. *)
val translate_with_hook:
  hook:(unit -> 'a) ->
  rectypes:bool -> ML.datatype_env -> ML.term -> 'a * F.nominal_term

val emit_error : Utils.loc -> error -> unit
