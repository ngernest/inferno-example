(* Translation from ML types to F types *)

let fresh_tyvar =
  let cpt = ref 0 in

  (* We generate odd number for the user and even number for the solver *)
  fun () -> incr cpt; 2 * !cpt + 1

(* Translation of ML datatype environment into System F datatype environment. *)

(* Given a way to translate ML type variables into System F type,
   this function translates an ML type into a System F type. *)
let rec translate_type (translate_tyvar : ML.tyvar -> F.nominal_type) (ty : ML.typ)
    : F.nominal_type =
  let trans ty = translate_type translate_tyvar ty in
  match ty with
  | ML.TyVar (_, tv) ->
      translate_tyvar tv
  | ML.TyArrow (_, ty1, ty2) ->
      F.TyArrow (trans ty1, trans ty2)
  | ML.TyProduct (_, tys) ->
      F.TyProduct (List.map trans tys)
  | ML.TyConstr (_, tyconstr, tys) ->
      F.TyConstr (tyconstr, List.map trans tys)

(* Translate a ML datatype description into a nominal System F version *)
let translate_datatype tdescr =

  (* We create an association list between ML and System F type variables.
     We'll use this association list to translate type parameters and
     type arguments containing those type parameters. *)
  let assoc =
    List.map (fun tyvar -> (tyvar, fresh_tyvar ()))
      tdescr.Datatype.type_params
  in

  let translate_label ldescr =
    let arg_type =
      match ldescr.Datatype.arg_type with
      | None ->
         ML.TyProduct (None, [])
      | Some ty ->
         ty
    in
    let new_arg_type =
      translate_type (fun tv -> F.TyVar (List.assoc tv assoc)) arg_type
    in
    Datatype.{
      label_name = ldescr.label_name;
      type_name = ldescr.type_name;
      arg_type = new_arg_type;
    }
  in

  let new_type_params =
    List.map (fun param -> List.assoc param assoc) tdescr.Datatype.type_params
  in
  let new_labels_descr =
    List.map translate_label tdescr.Datatype.labels_descr
  in

  (* The name and kind of data stay the same, only the type parameters and
     labels description need to change. *)
  Datatype.{
      name = tdescr.name;
      type_params = new_type_params;
      data_kind = tdescr.data_kind;
      labels_descr = new_labels_descr;
  }

let translate_env (env : ML.datatype_env)
    : F.nominal_datatype_env =
  Datatype.Env.map translate_datatype env
