(* A pretty-printer for ML. *)

(* We translate from System F to P and then print the P term (resp. type). *)

let rec translate_type (ty : ML.typ) : P.typ =
  let self = translate_type in
  match ty with
  | ML.TyVar (_, x) ->
      P.TyVar x
  | ML.TyArrow (_, ty1, ty2) ->
      P.TyArrow (self ty1, self ty2)
  | ML.TyProduct (_, tys) ->
      P.TyProduct (List.map self tys)
  | ML.TyConstr (_, lbl, tys) ->
      P.TyConstr (lbl, List.map self tys)

let print_type (ty : ML.typ) =
  Printer.print_type (translate_type ty)

let translate_rigidity = function
  | ML.Flexible ->
     P.Flexible
  | ML.Rigid ->
     P.Rigid

let translate_annot (rigidity, vars, ty) =
  (translate_rigidity rigidity, vars, translate_type ty)

let rec translate_term (t : ML.term) : P.term =
  let self = translate_term in
  match t with
  | ML.Var (_, x) ->
      P.Var x
  | ML.Hole (_, ts) ->
      P.Hole (None, List.map self ts)
  | ML.Abs (_, x, t) ->
      P.Abs (P.PVar x, self t)
  | ML.App (_, t1, t2) ->
      P.App (self t1, self t2)
  | ML.Let (_, r, x, t, u) ->
      P.Let (r, P.PVar x, self t, self u)
  | ML.Annot (_, t, tyannot) ->
      P.Annot (self t, translate_annot tyannot)
  | ML.Tuple (_, ts) ->
      P.Tuple (List.map translate_term ts)
  | ML.LetProd (_, xs, t, u) ->
      let pat = P.PTuple (List.map (fun x -> P.PVar x) xs) in
      P.Let (P.Non_recursive, pat, self t, self u)
  | ML.Variant (_, lbl, t) ->
      P.Variant (lbl, None, Option.map self t)
  | ML.Match (_, t, brs) ->
      P.Match (None, self t, List.map translate_branch brs)

and translate_branch (pat, t) =
  (translate_pattern pat, translate_term t)

and translate_pattern p =
  let self = translate_pattern in
  match p with
  | ML.PVar (_, x) ->
      P.PVar x
  | ML.PWildcard _ ->
      P.PWildcard
  | ML.PAnnot (_, p, tyannot) ->
      P.PAnnot (self p, translate_annot tyannot)
  | ML.PVariant (_, lbl, p) ->
      P.PVariant (lbl, None, Option.map self p)
  | ML.PTuple (_, ps) ->
      P.PTuple (List.map self ps)

let print_term t =
  Printer.print_term (translate_term t)

let to_string t =
  let b = Buffer.create 128 in
  PPrint.ToBuffer.pretty 0.9 80 b (print_term t);
  Buffer.contents b
