open Printf
open Client
open Test
open Colors

let () =

  (* Parse the command line. *)
  let default = 23 in
  let seed = ref default in
  let usage = sprintf "Usage: %s --seed <seed>" Sys.argv.(0) in
  Arg.parse [
    "--seed", Arg.Int (fun s -> seed := s), "<int> Set the random seed";
  ] (fun _ -> ()) usage;

  (* Initialize the random state. *)
  Random.init !seed;
  let state = Random.get_state() in

  (* Generate a large closed lambda-term. *)
  let n = 100_000 in
  printf "Generating a term of size %d (seed = %d)...\n%!" n !seed;
  let repetitions = 1 in
  let time, (t : ML.term) = Measure.time ~repetitions begin fun () ->
      RandomML.pure_lambda_term (0, n) state
    end in
  Printf.printf "Random generation:                      %.3f seconds.\n%!"
    time;
  Printf.printf "Size of the term:                       %d words.\n%!"
    (Obj.reachable_words (Obj.repr t));

  (* Infer its type and translate it to System F. *)
  printf "Inference and elaboration (one run)...\n%!";
  let rectypes = true in
  let env = Datatype.Env.empty in
  let space0 = Measure.allocated() in
  let space1, (u : F.nominal_term) =
    Infer.translate_with_hook ~hook:Measure.allocated ~rectypes env t
  in
  let space2 = Measure.allocated() in
  Printf.printf "Type inference and elaboration:         %s%d words.%s\n"
    green (space2 - space0) normal;
  Printf.printf "    Type inference alone:               %s%d words.%s\n"
    blue (space1 - space0) normal;
  Printf.printf "    Elaboration alone:                  %s%d words.%s\n"
    blue (space2 - space1) normal;

  (* Translate the System F term from nominal to de Bruijn. *)
  printf "Translating...\n%!";
  let repetitions = 1 in
  let time, v = Measure.time ~repetitions
      (fun () -> F.Term.translate u) in
  Printf.printf "Translating from nominal to de Bruijn:  %.3f seconds.\n%!" time;
  Printf.printf "Size of the elaborated term (nominal):  %d words.\n%!"
    (Obj.reachable_words (Obj.repr u));
  Printf.printf "Size of the elaborated term (deBruijn): %d words.\n%!"
    (Obj.reachable_words (Obj.repr v));

  (* Type-check. This is sanity check; we do not expect a type error. *)
  printf "Type-checking...\n%!";
  let repetitions = 1 in
  let time, () =
    Measure.time ~repetitions @@ fun () ->
    match FTypeChecker.typeof_result env v with
    | Error (range, e) ->
      Utils.emit_error range (FPrinter.print_type_error e);
      failwith "Sanity check failed."
    | Ok _v -> ()
  in
  Printf.printf "Type-checking:                          %.3f seconds.\n%!" time;

  (* Start the benchmark. Measure how long it takes to perform type inference
     and elaboration. *)
  (* We perform a global measurement (inference + elaboration), and we perform
     separate measurements as well. These separate measurements do not
     necessarily make sense, as we do not control when garbage collection
     takes place. The cost of reclaiming memory allocated during inference
     could be charged to elaboration, or vice-versa. *)
  (* Note that performance depends on the GC settings; e.g., setting
     OCAMLRUNPARAM="s=1G" can improve performance by 30%. *)
  Gc.compact();
  let repetitions = 20 in
  printf "Inference and elaboration (%d runs)...\n%!" repetitions;
  let inference, elaboration = ref 0.0, ref 0.0 in
  let start = Unix.gettimeofday() in
  for _ = 1 to repetitions do
    let time0 = Unix.gettimeofday() in
    let time1, (_ : F.nominal_term) =
      Infer.translate_with_hook ~hook:Unix.gettimeofday ~rectypes env t in
    let time2 = Unix.gettimeofday() in
    inference := !inference +. time1 -. time0;
    elaboration := !elaboration +. time2 -. time1
  done;
  let finish = Unix.gettimeofday() in
  let normalize time = time /. float_of_int repetitions in
  let time = normalize (finish -. start)
  and inference = normalize !inference
  and elaboration = normalize !elaboration in
  Printf.printf "Type inference and elaboration:         %s%.3f seconds.%s\n"
    green time normal;
  Printf.printf "    Type inference alone:               %s%.3f seconds.%s\n"
    blue inference normal;
  Printf.printf "    Elaboration alone:                  %s%.3f seconds.%s\n"
    blue elaboration normal;

  Printf.printf "Done.\n%!"
