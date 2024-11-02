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

module LabelId : sig
  type t = label_id
  val compare: t -> t -> int
end

module TyConstrId : sig
  type t = tyconstr_id
  val compare: t -> t -> int
end


(* Environment for user defined data types *)
module Env : sig
  type ('b, 't) t

  exception UnexpectedRecord
  exception DeclarationNotFound of tyconstr_id
  exception LabelNotFound of label_id

  val empty: ('b, 't) t
  val add_decl: ('b, 't) t -> ('b, 't) decl -> ('b, 't) t

  val find_label: ('b, 't) t -> label_id -> 't label
  val find_decl: ('b, 't) t -> tyconstr_id -> ('b, 't) decl

  val map: (('b1, 't1) decl -> ('b2, 't2) decl) -> ('b1, 't1) t -> ('b2, 't2) t

  val union: ('b, 't) t -> ('b, 't) t -> ('b, 't) t
end
