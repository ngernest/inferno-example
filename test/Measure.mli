(**[time f] measures the time required by one execution of [f()],
   in seconds. For better accuracy, the GC is stabilized first, and
   the function call [f()] is executed several times in succession;
   [repetitions] controls the number of repetitions. The result of
   the first execution of [f()] is returned as well. *)
val time: repetitions:int -> (unit -> 'a) -> float * 'a

(**[space f] measure how many words are allocated during one execution
   of [f()]. The result of [f()] is returned as well. *)
val space: (unit -> 'a) -> int * 'a

(**[allocated()] returns the number of words that have been allocated
   since the start of this process. The distinction between the minor
   heap and the major heap is abstracted away; one word is counted as
   one word, regardless of whether it has been allocated in the minor
   heap and later moved to the major heap, or allocated in the minor
   heap and never moved to the major heap, or allocated directly in
   the major heap. *)
val allocated: unit -> int
