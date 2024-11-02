open Client

module LexUtil = MenhirLib.LexerUtil

(* -------------------------------------------------------------------------- *)

(* A wrapper over the client's [translate] function. We consider ill-typedness
   as normal, since our terms are randomly generated, so we translate the client
   exceptions to [None]. *)

let translate ~verbose ~rectypes e t =
  match Infer.translate ~rectypes e t with
  | x -> Some x
  | exception Infer.Error(range, error) ->
    if verbose then Infer.emit_error range error;
    None

let equal_term t1 t2 =
  ML.compare_term t1 t2 = 0


(* -------------------------------------------------------------------------- *)

exception ParsingError of Utils.loc

let wrap parser lexbuf =
  let lexbuf = LexUtil.init "test" lexbuf in
  try parser MLLexer.read lexbuf
  with MLParser.Error ->
    let range = Lexing.(lexbuf.lex_start_p, lexbuf.lex_curr_p) in
    raise (ParsingError (Some range))

(* Main parsing function *)
let parse_term lexbuf = wrap MLParser.self_contained_term lexbuf
let parse_program lexbuf = wrap MLParser.prog lexbuf
let parse_type_decls lexbuf = wrap MLParser.self_contained_type_decls lexbuf


let ast_from_string s =
  let lexbuf = Lexing.from_string s in
  parse_program lexbuf

let letify xts =
  let rec aux xts =
    match xts with
    | [] ->
        assert false
    | [(_loc, _last_var, t)] ->
        t
    | (loc, x, t) :: xts ->
        ML.Let (loc, ML.Non_recursive, x, t, aux xts)
  in
  aux xts

let open_uses filenames =
  let on_file typedecl_env filename =
    let ch = open_in filename in
    let lexbuf = Lexing.from_channel ch in
    let typedecl_env' = parse_type_decls lexbuf in
    close_in ch;
    Datatype.Env.union typedecl_env typedecl_env'
  in
  List.fold_left on_file Datatype.Env.empty filenames

let from_string typedecl s =
  let s = typedecl ^ "\nlet _ = " ^ s in
  let (uses, typedecl_env, xts) = ast_from_string s in
  let typedecl_env' = open_uses uses in
  let ast = letify xts in
  (Datatype.Env.union typedecl_env typedecl_env', ast)

let from_file filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let (uses, typedecl_env, xts) = parse_program lexbuf in
  close_in ch;
  let typedecl_env' = open_uses uses in
  let ast = letify xts in
  (Datatype.Env.union typedecl_env typedecl_env', ast)

(* -------------------------------------------------------------------------- *)

(* Running all passes over a single ML term. *)

let test_with_args
  ?(verbose=Config.verbose)
  ~rectypes
  ~(success:int ref) ~(total:int ref) (env : ML.datatype_env) (t : ML.term)
  : bool
  =
  incr total;
  (* We print the term, parse it and compare with the given term *)
  let s = MLPrinter.to_string t in
  let lexbuf = Lexing.from_string s in
  match MLParser.self_contained_term MLLexer.read lexbuf with
  | exception (ParsingError loc) ->
    loc |> Option.iter (fun range ->
      prerr_string (LexUtil.range range)
    );
    prerr_endline "Syntax error on re-parsing.";
    false
  | t' ->
     assert (equal_term t t');
  (* now we check typability; inference should not fail *)
  let outcome_env =
    ML2F.translate_env env in
  print_endline "Type inference and translation to System F...";
  let outcome =
    translate ~verbose ~rectypes env t
  in
  match outcome with
  | None ->
      (* This term is ill-typed. This is considered a normal outcome, since
         our terms can be randomly generated. *)
      true
  | Some (t : F.nominal_term) ->
      CheckF.test outcome_env t;
      (* Everything seems to be OK. *)
      incr success;
      true

let test ?(verbose=Config.verbose) env t =
  test_with_args ~verbose ~success:(ref 0) ~total:(ref 0) env t
