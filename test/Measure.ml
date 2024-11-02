open Gc

let time ~repetitions f =
  assert (repetitions > 0);
  Gc.compact();
  let t1 = Unix.gettimeofday() in
  let result = f() in
  for _ = 1 to repetitions-1 do
    ignore (f())
  done;
  let t2 = Unix.gettimeofday() in
  (t2 -. t1) /. float_of_int repetitions,
  result

let allocated () =
  let stat = Gc.stat() in
  int_of_float (stat.major_words +. stat.minor_words -. stat.promoted_words)

let space f =
  let space1 = allocated() in
  let result = f() in
  let space2 = allocated() in
  space2 - space1,
  result
