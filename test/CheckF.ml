open Client

(* Typecheck a System F term after a bunch of debugging printing.
   FTypechecker returns a [result] that is treated by the user-supplied
   [on_error] and [on_ok] functions. *)
let check (env : F.nominal_datatype_env) (t : F.nominal_term)
  : (F.debruijn_type, Utils.loc * FTypeChecker.type_error) result
  =
  Printf.printf "Formatting the System F term...\n%!";
  let doc = FPrinter.print_term t in
  Printf.printf "Pretty-printing the System F term...\n%!";
  Utils.emit_endline doc;
  let env : F.debruijn_datatype_env =
    F.translate_env env in
  print_string "Converting the System F term to de Bruijn style...\n";
  let t : F.debruijn_term =
    F.Term.translate t in
  print_string "Type-checking the System F term...\n";
  FTypeChecker.typeof_result env t

(* Test a term that is expected to pass type checking. *)
let test (env : F.nominal_datatype_env) (t : F.nominal_term) =
  match check env t with
  | Ok _ ->
     ()
  | Error (range, e) ->
     Utils.emit_error range (FPrinter.print_type_error e);
     failwith "Type-checking error."

(* Test a term that is expected to fail type checking. *)
let test_error (env : F.nominal_datatype_env) (t : F.nominal_term) =
  match check env t with
  | Error _ ->
     ()
  | Ok _ ->
    failwith "Type-checking error."
