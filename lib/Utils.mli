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

(* Emits a PPrint document to stdout with 80-column width. *)
val emit : PPrint.document -> unit

(* Similar to {!emit}; [emit_endline] also includes a newline at the
   end and flushes [stdout]. *)
val emit_endline : PPrint.document -> unit

type loc = (Lexing.position * Lexing.position) option
val emit_loc : loc -> unit

(* Similar to {!emit_endline}, but starts by printing
   a source location. *)
val emit_error : loc -> PPrint.document -> unit
