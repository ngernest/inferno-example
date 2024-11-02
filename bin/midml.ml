open Printf
open Test.CheckML

let rectypes =
  ref false

let test_ok filename =
  match from_file filename with
  | exception (ParsingError loc) ->
    loc |> Option.iter (fun range ->
      prerr_string (LexUtil.range range));
    prerr_endline "Syntax error."
  | (datatype_env, t) ->
  let rectypes = !rectypes in
  let _ = Test.CheckML.test ~verbose:true ~rectypes datatype_env t in ()

let parse_args () =
  let usage = sprintf "Usage: %s [-rectypes] <filename>" Sys.argv.(0) in
  let spec = Arg.align [
    "-rectypes", Arg.Set rectypes, " Enable equirecursive types";
  ] in
  Arg.parse spec test_ok usage

let () =
  parse_args ()
