(* A pretty-printer for the generic language P. *)

open PPrint
open P

(* -------------------------------------------------------------------------- *)

(* Types. *)

let print_tyvar x =
  string x

let rec print_type ty =
  print_type_quant ty

and print_type_quant ty =
  group @@ match ty with
  | TyMu (x, ty) ->
      group (
        string "mu " ^^
        space ^^
        print_tyvar x  ^^
        dot
      ) ^//^ print_type_quant ty
  | TyForall (x, ty) ->
      group (
        lbracket ^^
        print_tyvar x ^^
        rbracket
      ) ^//^ print_type_quant ty
  | ty ->
      print_type_arrow ty


and print_type_arrow ty =
  group @@ match ty with
  | TyArrow (ty1, ty2) ->
      print_type_tyconstr ty1
      ^^ space ^^ string "->"
      ^//^ print_type_arrow ty2
  | TyEq (ty1, ty2) ->
      print_type_tyconstr ty1
      ^^ space ^^ string "="
      ^//^ print_type_arrow ty2
  | ty ->
      print_type_tyconstr ty

and print_type_tyconstr ty =
  group @@ match ty with
  | TyConstr datatype ->
      print_datatype datatype
  | ty ->
      print_type_atom ty

and print_type_atom ty =
  group @@ match ty with
  | TyVar x ->
      print_tyvar x
  | TyProduct tys ->
      surround_separate_map 2 0 (lbrace ^^ rbrace)
        lbrace star rbrace print_type tys
  | TyMu _ | TyForall _ | TyArrow _ | TyConstr _ | TyEq _ as ty ->
      parens (print_type ty)

and print_datatype (Datatype.Type tyconstr, tyargs) =
  string tyconstr
  ^//^ separate_map space print_type_atom tyargs

let print_angle elem =
  surround 2 0 langle elem rangle

let print_angle_type ty =
  print_angle @@ print_type ty

let print_angle_datatype dty =
  print_angle @@ print_datatype dty

(* -------------------------------------------------------------------------- *)

(* Terms. *)

let print_tevar x =
  string x

let print_variant (Datatype.Label lbl) dty print_arg arg =
  group (
    string lbl
    ^^ optional print_angle_datatype dty
    ^^ (match arg with
        | None ->
           empty
        | Some arg -> space ^^ print_arg arg)
  )

let print_tuple print_elem elems =
  match elems with
  | [] -> lparen ^^ rparen
  | _ ->
    let contents =
      match elems with
      | [elem] ->
          (* For arity-1 tuples we print (foo,)
             instead of (foo) which would be ambiguous. *)
          print_elem elem ^^ comma
      | _ ->
          separate_map (comma ^^ break 1) print_elem elems in
    surround 2 0 lparen contents rparen

let print_let_in rec_ lhs rhs body =
  string "let"
  ^^ (match rec_ with
      | Recursive -> space ^^ string "rec"
      | Non_recursive -> empty)
  ^^ surround 2 1 empty lhs empty
  ^^ string "="
  ^^ surround 2 1 empty rhs empty
  ^^ string "in"
  ^^ prefix 0 1 empty body

let rec flatten_tyabs t =
  match t with
  | TyAbs (x, t) ->
      let (xs, t) = flatten_tyabs t in
      (x::xs, t)
  | t ->
      ([], t)

let rec flatten_abs t =
  match t with
  | Abs (p, t) ->
      let (ps, t) = flatten_abs t in
      (p::ps, t)
  | t ->
      ([], t)

let print_nary_abstraction abs print_arg args rhs =
  string abs
  ^^ space
  ^^ separate_map space print_arg args
  ^^ space
  ^^ string "->"
  ^//^ rhs

let print_annot print_elem (rigidity, tyvars, typ) =
  let rigidity_kwd =
    string @@ match rigidity with
             | Flexible ->
                "some"
             | Rigid ->
                "for"
  in
  surround 2 0 lparen (
    print_elem ^^ break 1 ^^ string ":"
    ^^ (if tyvars = [] then empty
        else prefix 2 1 empty
               (rigidity_kwd ^^ space ^^
                separate_map space print_tyvar tyvars ^^ dot))
    ^//^ print_type typ
  ) rparen

let rec print_term t =
  print_term_abs t

and print_term_abs t =
  group @@ match t with
  | TyAbs _ ->
      let (xs, t) = flatten_tyabs t in
      print_nary_abstraction "FUN" print_tyvar xs (print_term_abs t)
  | Let (rec_, p, t1, t2) ->
      print_let_in rec_
        (print_pattern p)
        (print_term t1)
        (print_term_abs t2)
  | Abs _ ->
      let (ps, t) = flatten_abs t in
      print_nary_abstraction "fun" print_pattern ps (print_term_abs t)
  | Use (t, u) ->
      string "use" ^^ space
      ^^ print_term t
      ^^ space ^^ string "in" ^^ hardline
      ^^ print_term u
  | t ->
      print_term_app t

and print_term_app t =
  group @@ match t with
  | TyApp (t1, ty2) ->
      print_term_app t1
      ^//^ lbracket ^^ print_type ty2 ^^ rbracket
  | App (t1, t2) ->
      print_term_app t1
      ^//^ print_term_atom t2
  | Proj (i, t) ->
      string "proj" ^^ print_angle (OCaml.int i)
      ^^ space ^^ print_term_atom t
  | Variant (lbl, dty, t) ->
      print_variant lbl dty print_term_atom t
  | Refl ty ->
     group (
       string "Refl"
       ^^ print_angle_type ty
     )
  | t ->
      print_term_atom t

and print_term_atom t =
  group @@ match t with
  | Var x ->
      print_tevar x
  | Hole (ty, ts) ->
      optional print_angle_type ty
      ^^ string "..."
      ^^ surround_separate_map 2 0 (lbracket ^^ rbracket) lbracket (comma ^^ break 1) rbracket print_term ts
  | Tuple (ts) ->
      print_tuple print_term ts
  | Match (ty, t, brs) ->
      print_match ty t brs
  | Annot (t, tyannot) ->
      print_annot (print_term t) tyannot
  | Absurd _ ->
      dot
  | TyAbs _ | Let _ | Abs _ | Use _
  | TyApp _ | App _ | Proj _ | Inj _ | Variant _  | Refl _ as t ->
      parens (print_term t)

and print_match ty scrutinee brs =
  string "match" ^^ optional print_angle_type ty
  ^^ surround 2 1 empty (print_term scrutinee) empty
  ^^ string "with" ^^ hardline
  ^^ print_branches brs ^^ hardline
  ^^ string "end"

and print_branches brs =
  separate_map hardline print_branch brs

and print_branch (pat,t) =
  group (
    bar ^^ space ^^ nest 2 (print_pattern pat)
    ^^ space ^^ string "->"
    ^//^ print_term t
  )

and print_pattern pat =
  print_pattern_inj pat

and print_pattern_inj pat =
  group @@ match pat with
  | PVariant (lbl, dty, pat) ->
      print_variant lbl dty
        print_pattern_atom pat
  | pat ->
      print_pattern_atom pat

and print_pattern_atom pat =
  group @@ match pat with
  | PVar x ->
      print_tevar x
  | PWildcard ->
      underscore
  | PTuple ps ->
      print_tuple print_pattern ps
  | PAnnot (pat, typ_annot) ->
       print_annot (print_pattern pat) typ_annot
  | PInj _ | PVariant _ as pat ->
      group (parens (print_pattern pat))
