%{
  open ML
%}

%token <string> LIDENT
%token <string> UIDENT
%token <string> QIDENT

%token FUN
%token ARROW "->"
%token LET IN
%token REC "rec"
%token EQ "="

%token LPAR "("
%token RPAR ")"

%token TYPE
%token OF
%token LBRACE "{"
%token RBRACE "}"
%token STAR "*"

%token DOTS "..."
%token LBRACKET "["
%token RBRACKET "]"

%token COMMA
%token WILDCARD
%token PIPE
%token MATCH WITH END

%token COLON ":"
%token PERIOD "."
%token SOME
%token FOR

%token USE "#use"
%token <string> FILENAME

%token EOF

%type<(string list * ML.datatype_env * (Utils.loc * string * ML.term) list)> prog
%type<ML.term> self_contained_term
%type<ML.datatype_env> self_contained_type_decls

%start prog self_contained_term self_contained_type_decls

%%

let prog :=
  | filenames = use_directives ;
    datatype_env = type_decls ;
    xts = nonempty_list (toplevel_term_decl) ; EOF ;
                                          { (filenames, datatype_env, xts) }

let self_contained_term :=
  | ~ = term ; EOF ; <>

let self_contained_type_decls :=
  | ~ = type_decls ; EOF ; <>

(***************** TERMS ***************)
let toplevel_term_decl :=
  | LET ; x = tevar_ ; "=" ; t = term ;   { (Some $loc, x, t) }

let term :=
  | ~ = term_abs ; <>

let term_abs :=
  | FUN ; xs = list (tevar_) ; "->" ; t = term_abs ;
    {
      List.fold_right (fun x t -> Abs (Some $loc, x, t)) xs t
    }

  | (x, t1, t2) = letin(tevar) ;          { Let (Some $loc, Non_recursive, x, t1, t2) }

  | (x, t1, t2) = letrecin(tevar) ;       { Let (Some $loc, Recursive, x, t1, t2) }

  | (xs, t1, t2) = letin(tuple(tevar)) ;  { LetProd (Some $loc, xs, t1, t2) }

  | ~ = term_app ; <>

let term_app :=
  | t1 = term_app ; t2 = term_atom ;
    {
      match t1 with
      | Variant (loc, l, None) ->
         let loc = match loc with
           | None -> Some $loc
           | Some (start_pos, _end_pos) ->
              Some (start_pos, $endpos)
         in
	 Variant (loc, l, Some t2)
      | _ ->
	 App (Some $loc, t1, t2)
    }

  | ~ = term_atom ; <>

let term_atom :=
  | x = tevar ;                           { Var (Some $loc, x) }

  | l = UIDENT ;                          { Variant (Some $loc, Datatype.Label l, None) }

  | ts = tuple (term) ;                   { Tuple (Some $loc, ts) }

  | MATCH ; t = term ; WITH ;
    brs = branches ;
    END ;                                 { Match (Some $loc, t, brs) }

  | "..."; "["; ts = item_sequence(term, COMMA); "]";
                                          { Hole (Some $loc, ts) }

  | "(" ; t = term ; ":" ; tyannot = type_annotation ; ")" ;
                                          { Annot (Some $loc, t, tyannot) }

  | "(" ; ~ = term ; ")" ; <>

let branches :=
  | ~ = pipe_separated_list (branch) ; <>

let branch :=
  | pat = pattern ; "->" ; t = term ;     { (pat, t) }

let pattern :=
  | l = UIDENT ; pat = pattern_atom ;     { PVariant (Some $loc, Datatype.Label l, Some pat) }

  | ~ = pattern_atom ; <>

let pattern_atom :=
  | x = tevar ;                           { PVar (Some $loc, x) }

  | l = UIDENT;                           { PVariant (Some $loc, Datatype.Label l, None) }

  | WILDCARD ;                            { PWildcard (Some $loc) }

  | ps = tuple (pattern) ;                { PTuple (Some $loc, ps) }

  | "(" ; p = pattern ; ":" ; tyannot = type_annotation ; ")" ;
                                          { PAnnot (Some $loc, p, tyannot) }

let tevar :=
  | ~ = LIDENT ; <>

let tevar_ :=
  | ~ = LIDENT ; <>
  | WILDCARD ;   { "_" }

(*************** TYPES ***************)

let typ :=
  | ~ = type_arrow ; <>

let type_arrow :=
  | ty1 = type_tyconstr ; "->" ; ty2 = type_arrow ;
                                          { TyArrow (Some $loc, ty1, ty2) }

  | ~ = type_tyconstr ; <>


let type_tyconstr :=
  | ~ = tyname ; typarams = list (type_atom) ;
                                          { TyConstr (Some $loc, tyname, typarams)}

  | ~ = type_atom ; <>

let type_atom :=
  | x = tyvar ;                           { TyVar (Some $loc, x) }

  | "{" ; tys = separated_list ("*", typ) ; "}" ;
                                          { TyProduct (Some $loc, tys) }

  | "(" ; ~ = typ ; ")" ;                 <>


let type_annotation :=
  | ty = typ;                             { (Flexible, [], ty) }
  | SOME ; xs = list(tyvar) ; "." ; ty = typ ;
                                          { (Flexible, xs, ty) }
  | FOR ; xs = list(tyvar) ; "." ; ty = typ ;
                                          { (Rigid, xs, ty) }

let tyconstr_decl :=
  | l = UIDENT ; arg_type = option (OF ; ~ = typ ; <>) ;
    { (Datatype.Label l, arg_type) }

let type_decls :=
  | decls = list (type_decl) ;
    { List.fold_left Datatype.Env.add_decl Datatype.Env.empty decls }

let type_decl :=
  | TYPE ; ~ = tyname ; type_params = list (tyvar) ; "=" ;
    arg_types = pipe_separated_list (tyconstr_decl) ;
    {
      let name = tyname in
      let data_kind = Datatype.Variant in
      let labels_descr = List.map (fun (label_name, arg_type) ->
          Datatype.{ label_name ; type_name = name ; arg_type } )
        arg_types
      in
      Datatype.{ name ; type_params ; data_kind ; labels_descr }
    }

let use_directives :=
  | ~ = list (use_directive) ;            <>

let use_directive :=
  | "#use" ; filename = FILENAME ;          { filename }

let tyname :=
  | lid = LIDENT ; { Datatype.Type lid }

let tyvar :=
  | ~ = QIDENT ; <>

let tuple (X) :=
  | "(" ; ")" ;                                                { [] }
  (* note: the rule below enforces that one-element lists always
     end with a trailing comma *)
  | "(" ; x = X ; COMMA ; xs = item_sequence(X, COMMA) ; ")";  { x :: xs }

(* item sequence with optional trailing separator *)
let item_sequence(X, Sep) :=
  |                                                { [] }
  | x = X ;                                        { [x] }
  | x = X ; () = Sep ; xs = item_sequence(X, Sep); { x :: xs }

let letin (X) :=
  | LET ; x = X ; EQ ;
      t1 = term ; IN ;
      t2 = term_abs ;                     { (x, t1, t2) }

let letrecin (X) :=
  | LET ; REC; x = X ; EQ ;
      t1 = term ; IN ;
      t2 = term_abs ;                     { (x, t1, t2) }

let pipe_separated_list (X) :=
  | option (PIPE) ; ~ = separated_list (PIPE, X) ; <>
