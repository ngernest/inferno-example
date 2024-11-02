{
  open MLParser

  let keyword_table =
    Hashtbl.create 53

  let keywords = [
      "let", LET;
      "rec", REC;
      "in", IN;
      "fun", FUN;
      "let", LET;
      "with", WITH;
      "match", MATCH;
      "end", END;
      "type", TYPE;
      "of", OF;
      "some", SOME;
      "#use", USE;
      "for", FOR;
    ]

  let _ =
    List.iter
      (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      keywords

  let next_line lexbuf =
    Lexing.new_line lexbuf
}

let identchar = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let lident = ['a'-'z'] identchar*
let uident = ['A'-'Z'] identchar*
let filename = lident '.' lident

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read =
  parse
  | newline     { next_line lexbuf; read lexbuf }
  | white       { read lexbuf }
  | lident as id { try Hashtbl.find keyword_table id
                    with Not_found ->  LIDENT id }
  | uident as id { UIDENT id }
  | filename as fname { FILENAME fname }
  | "'" lident as id { QIDENT id }
  | "->"        { ARROW }
  | '('		{ LPAR }
  | ')'		{ RPAR }
  | '{'		{ LBRACE }
  | '}'		{ RBRACE }
  | '['		{ LBRACKET }
  | ']'		{ RBRACKET }
  | '*'		{ STAR }
  | ','		{ COMMA }
  | '_'		{ WILDCARD }
  | '|'		{ PIPE }
  | '='		{ EQ }
  | ":"		{ COLON }
  | '.'		{ PERIOD }
  | "..."       { DOTS }
  | "#use"      { USE }
  | eof		{ EOF }
  | "(*"        { ocamlcomment lexbuf; read lexbuf }
  | _ as c	{ failwith (Printf.sprintf "Unexpected character during lexing: %c" c) }

(* Skip comments. Comments can be nested. Note that we do not recognize
   string or character literals inside comments. *)

and ocamlcomment = parse
| "*)"
    { () }
| "(*"
    { ocamlcomment lexbuf; ocamlcomment lexbuf }
| newline
    { next_line lexbuf; ocamlcomment lexbuf }
| eof
    { failwith "Unterminated OCaml comment." }
| _
    { ocamlcomment lexbuf }
