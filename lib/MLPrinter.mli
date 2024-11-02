(* A pretty-printer for ML. *)

val print_type: ML.typ -> PPrint.document
val print_term: ML.term -> PPrint.document
val to_string: ML.term -> string
