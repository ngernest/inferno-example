(******************************************************************************)
(*                                                                            *)
(*                                  Inferno                                   *)
(*                                                                            *)
(*                       Gabriel Scherer, Inria Saclay                        *)
(*                                                                            *)
(*  Copyright Inria. All rights reserved. This file is distributed under the  *)
(*  terms of the MIT License, as described in the file LICENSE.               *)
(*                                                                            *)
(******************************************************************************)

let emit doc =
  PPrint.ToChannel.pretty 0.9 80 stdout doc

let emit_endline doc =
  emit PPrint.(doc ^^ hardline);
  flush stdout

type loc = (Lexing.position * Lexing.position) option

let emit_loc = function
  | None -> ()
  | Some range ->
    print_string (MenhirLib.LexerUtil.range range);
    flush stdout

let emit_error loc doc =
  emit_loc loc;
  emit_endline doc
