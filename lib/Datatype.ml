(* [tyconstr_id] is the name of an datatype constructor.
   [label_id] is the name of a field label or data constructor. *)
type tyconstr_id = Type of string
type label_id = Label of string

type kind = Variant | Record

type ('b,'t) decl = {
    name : tyconstr_id ;
    type_params : 'b list ;
    data_kind : kind ;
    labels_descr : 't label list ;
  }

and 't label = {
    label_name : label_id ;
    type_name : tyconstr_id ;
    arg_type : 't ;
  }

(* During inference, we will need an environment to keep track of
 * the user defined types *)

module LabelId = struct
  type t = label_id
  let compare = Stdlib.compare
end

module LabelMap =
  Map.Make(LabelId)

module TyConstrId = struct
  type t = tyconstr_id
  let compare = Stdlib.compare
end

module TyConstrMap =
  Map.Make(TyConstrId)

module Env = struct

  (* Environment for user defined data types *)
  type ('b,'t) t = {
      datatypes :  ('b,'t) decl TyConstrMap.t;
      labels : 't label LabelMap.t;
    }

  exception UnexpectedRecord
  exception DeclarationNotFound of tyconstr_id
  exception LabelNotFound of label_id

  let empty = {
      datatypes = TyConstrMap.empty;
      labels = LabelMap.empty;
    }

  let add_decl e tdescr =
    let add_datatype m tdescr =
      TyConstrMap.add tdescr.name tdescr m in
    let add_labels m ldescrs =
      List.fold_left (fun m ldescr ->
          LabelMap.add ldescr.label_name ldescr m
        ) m ldescrs
    in {
      datatypes = add_datatype e.datatypes tdescr;
      labels = add_labels e.labels tdescr.labels_descr;
    }

  let find_label { labels ; _ } label =
    try
      LabelMap.find label labels
    with Not_found ->
       raise (LabelNotFound label)

  let find_decl { datatypes ; _ } tid =
    try
      TyConstrMap.find tid datatypes
    with Not_found ->
       raise (DeclarationNotFound tid)

  let map (type b1 b2 t1 t2)
    (f : (b1, t1) decl -> (b2, t2) decl)
    (env : (b1, t1) t) : (b2, t2) t
  =
    TyConstrMap.to_seq env.datatypes
    |> Seq.map snd
    |> Seq.map f
    |> Seq.fold_left add_decl empty

  let union env1 env2 =
    let shadow_old_key _ _ m2 = Some m2
    in {
      datatypes =
        TyConstrMap.union shadow_old_key env1.datatypes env2.datatypes;
      labels =
        LabelMap.union shadow_old_key env1.labels env2.labels;
    }

end
