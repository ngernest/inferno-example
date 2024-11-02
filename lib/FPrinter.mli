(* A pretty-printer for F. *)

open PPrint

val print_type: F.nominal_type -> document
val print_term: F.nominal_term -> document
val print_type_error: FTypeChecker.type_error -> document
