(* A pretty-printer for F. *)

(* We translate from System F to P and then print the P term (resp. type). *)

let new_id : unit -> int =
  Inferno.Utils.gensym()

let new_tyvar () =
  Printf.sprintf "a%d" (new_id())

let translate_old_var (x : F.tyvar) =
  Printf.sprintf "r%d" x

let translate_tyvar env x =
  try
    (* if the type variable [x] is locally bound in the type that we are
       presently printing, then it is mapped by [env] to a name that we have
       generated when we have entered this binder. *)
    List.assoc x env
  with Not_found ->
    (* If [x] is not bound in [env], then we have been asked to print
       a type that has free variables. This can happen, for instance,
       when printing a type as part of a type error message. *)
    translate_old_var x

let rec translate_type (env : (F.tyvar * P.tyvar) list) (ty : F.nominal_type) : P.typ =
  let self = translate_type in
  match ty with
  | F.TyVar x ->
      P.TyVar (translate_tyvar env x)
  | F.TyArrow (ty1, ty2) ->
      P.TyArrow (self env ty1, self env ty2)
  | F.TyProduct tys ->
      P.TyProduct (List.map (self env) tys)
  | F.TyForall (x, ty) ->
      let alpha = new_tyvar () in
      P.TyForall (alpha, self ((x, alpha) :: env) ty)
  | F.TyMu (x, ty) ->
      let alpha = new_tyvar () in
      P.TyMu (alpha, self ((x, alpha) :: env) ty)
  | F.TyConstr (constr, tys) ->
      P.TyConstr (constr, List.map (self env) tys)
  | F.TyEq (ty1, ty2) ->
      P.TyEq (self env ty1, self env ty2)

let print_type ty =
  Printer.print_type (translate_type [] ty)

let rec translate_term env (t : F.nominal_term) : P.term =
  let self = translate_term in
  let annot env ty = (P.Flexible, [], translate_type env ty) in
  match t with
  | F.Var (_, x) ->
      P.Var x
  | F.Hole (_, ty, ts) ->
      P.Hole (Some (translate_type env ty), List.map (self env) ts)
  | F.Annot (_, t, ty) ->
      P.Annot (self env t, annot env ty)
  | F.Abs (_, x, ty, t) ->
      let x_annot = P.PAnnot (P.PVar x, annot env ty) in
      P.Abs (x_annot, self env t)
  | F.App (_, t1, t2) ->
      P.App (self env t1, self env t2)
  | F.Let (_, rec_, x, ty, t, u) ->
      let rec_ = match rec_ with
      | F.Recursive -> P.Recursive
      | F.Non_recursive -> P.Non_recursive
      in
      let x_annot = P.PAnnot (P.PVar x, annot env ty) in
      P.Let (rec_, x_annot, self env t, self env u)
  | F.TyAbs (_, x, t) ->
      let alpha = new_tyvar () in
      P.TyAbs (alpha, self ((x, alpha) :: env) t)
  | F.TyApp (_, t, ty) ->
      P.TyApp (self env t, translate_type env ty)
  | F.Tuple (_, ts) ->
      P.Tuple (List.map (self env) ts)
  | F.Proj (_, i, t) ->
      P.Proj (i, self env t)
  | F.LetProd (_, xs, t, u) ->
      let pat = P.PTuple (List.map (fun x -> P.PVar x) xs) in
      P.Let (P.Non_recursive, pat, self env t, self env u)
  | F.Variant (_, lbl, (tid, tys) , t) ->
      P.Variant (
          lbl,
          Some (tid, List.map (translate_type env) tys),
          Some (self env t)
        )
  | F.Match (_, ty, t, brs) ->
      P.Match (
        Some (translate_type env ty),
        self env t,
        List.map (translate_branch env) brs
      )
  | F.Absurd (_, ty) ->
      P.Absurd (translate_type env ty)
  | F.Refl (_, ty) ->
      P.Refl (translate_type env ty)
  | F.Use (_, t, u) ->
      let t' = self env t in
      let u' = self env u in
      P.Use (t', u')

and translate_branch env (pat, t) =
  (translate_pattern env pat, translate_term env t)

and translate_pattern env pat =
  let self = translate_pattern in
  match pat with
  | F.PVar (_, x) ->
      P.PVar x
  | F.PWildcard _ ->
      P.PWildcard
  | F.PAnnot (_, p, ty) ->
      P.PAnnot (self env p, (P.Flexible, [], translate_type env ty))
  | F.PTuple (_, ps) ->
      P.PTuple (List.map (self env) ps)
  | F.PVariant (_, lbl, (tid, tys), p) ->
      P.PVariant (
          lbl,
          Some (tid, List.map (translate_type env) tys),
          Some (self env p)
        )

let print_term t =
  Printer.print_term (translate_term [] t)

open PPrint
open FTypeChecker

let str =
  utf8format

let (++) d1 d2 =
  d1 ^^ hardline ^^ d2

let new_id : unit -> F.tyvar =
  Inferno.Utils.gensym()

let new_tyvar () : P.tyvar =
  Printf.sprintf "a%d" (new_id())

let translate_old_db_var (x : DeBruijn.index) =
  Printf.sprintf "r%d" x

let rec translate_db_type (env : P.tyvar list) (ty : F.debruijn_type) : P.typ =
  let self = translate_db_type in
  match ty with
  | F.TyVar x ->
      let n = List.length env in
      if x < n then
        (* The type variable [x] is locally bound in the type that we are
           presently printing. It is mapped by [env] to a name that we have
           generated when we have entered this binder. *)
        P.TyVar (List.nth env x)
      else
        (* The type variable [x] is not bound. We have been asked to print
           a type that has free variables. We print these free variables
           as de Bruijn indices (adjusted by subtracting [n]), because we
           have no better way. *)
        P.TyVar (translate_old_db_var (x - n))
  | F.TyArrow (ty1, ty2) ->
      P.TyArrow (self env ty1, self env ty2)
  | F.TyProduct tys ->
      P.TyProduct (List.map (self env) tys)
  | F.TyForall ((), ty) ->
      let alpha = new_tyvar () in
      P.TyForall (alpha, self (alpha :: env) ty)
  | F.TyMu ((), ty) ->
      let alpha = new_tyvar () in
      P.TyMu (alpha, self (alpha :: env) ty)
  | F.TyConstr (constr, tys) ->
      P.TyConstr (constr, List.map (self env) tys)
  | F.TyEq (ty1, ty2) ->
      P.TyEq (self env ty1, self env ty2)

let print_db_type ty =
  Printer.print_type (translate_db_type [] ty)

let print_type_error e =
  match e with
  | TypeMismatch (ty1, ty2) ->
      str "Type mismatch. The following types should be equal." ++
      str "Left-hand type:" ++
      print_db_type ty1 ++
      str "Right-hand type:" ++
      print_db_type ty2 ++
      empty
  | ArityMismatch (Index i, ty) ->
      str "Arity mismatch." ++
      str "This product type should have at least %d components:" (i+1) ++
      print_db_type ty ++
      empty
  | ArityMismatch (Total n, ty) ->
      str "Arity mismatch." ++
      str "This product type should have exactly %d components:" n ++
      print_db_type ty ++
      empty
  | NotAnArrow ty ->
      str "Type error." ++
      str "This type should be an arrow type:" ++
      print_db_type ty
  | NotAProduct ty ->
      str "Type error." ++
      str "This type should be a product type:" ++
      print_db_type ty
  | NotAForall ty ->
      str "Type error." ++
      str "This type should be a universal type:" ++
      print_db_type ty
  | NotAnEqual ty ->
      str "Type error." ++
      str "This type should be an equality type:" ++
      print_db_type ty
  | UnboundTermVariable x ->
      str "Scope error." ++
      str "The variable %s is unbound." x
  | UnboundTypeVariable x ->
      str "Scope error." ++
      str "The type variable %d is unbound." x
  | TwoOccurencesOfSameVariable x ->
      str "Scope error." ++
      str "The variable %s is bound twice in a pattern." x
  | ContextNotAbsurd ->
      str "Type error." ++
      str "The type equations in the typing environment are not contradictory."
  | UnexpectedRecord ->
      str "Type error." ++
      str "A record was expected."
  | DeclarationNotFound (Datatype.Type tid) ->
      str "Scope error." ++
      str "Unknown type declaration : %s." tid
  | LabelNotFound (Datatype.Label lid) ->
      str "Scope error." ++
      str "Unknown variant constructor : %s." lid
