open Client

(* A random generator of ML terms. *)

(* The following functions expect a pair [(k, n)] where [k] is the number of
   variables that are currently in scope and [n] is the goal size, that is,
   the desired number of internal nodes. *)

(* [term] generates an arbitrary ML term, which may be ill-typed. *)

val term: int * int -> Random.State.t -> ML.term

(* [pure_lambda_term] generates a term that is guaranteed to be well-typed,
   provided [rectypes] is [true]. *)

val pure_lambda_term: int * int -> Random.State.t -> ML.term
