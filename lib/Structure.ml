(* This is an open-ended (non-recursive) version of the algebraic data type of
   System F types. The ordinary, recursive version of this type is defined in
   the module [F]. *)

type 'a structure =
  | TyArrow of 'a * 'a
  | TyProduct of 'a list
  | TyConstr of Datatype.tyconstr_id * 'a list
  | TyEq of 'a * 'a

(* -------------------------------------------------------------------------- *)

(* Traversals at arity 1. *)

(* We enforce the same traversal order for [iter], [fold], and [map].
   In principle, this is not necessary. *)

let iter f t =
  match t with
  | TyArrow (t1, t2)
  | TyEq (t1, t2) ->
      f t1; f t2
  | TyProduct ts
  | TyConstr (_, ts) ->
      List.iter f ts

let fold f t accu =
  match t with
  | TyArrow (t1, t2)
  | TyEq (t1, t2) ->
      let accu = f t1 accu in
      let accu = f t2 accu in
      accu
  | TyProduct ts
  | TyConstr (_, ts) ->
      List.fold_left (fun accu t -> f t accu) accu ts

let map f t =
  match t with
  | TyArrow (t1, t2)
  | TyEq (t1, t2) ->
      let t1 = f t1 in
      let t2 = f t2 in
      TyArrow (t1, t2)
  | TyProduct ts ->
      let ts = List.map f ts in
      TyProduct ts
  | TyConstr (tid, ts) ->
      let ts = List.map f ts in
      TyConstr (tid, ts)

(* -------------------------------------------------------------------------- *)

(* Traversals at arity 2. *)

exception Iter2

let list_iter2 f ts us =
  if List.length ts <> List.length us then raise Iter2;
  List.iter2 f ts us

let iter2 f t u =
  match t, u with
  | TyArrow (t1, t2), TyArrow (u1, u2)
  | TyEq (t1, t2), TyEq (u1, u2) ->
      f t1 u1;
      f t2 u2
  | TyProduct ts1, TyProduct ts2 ->
      list_iter2 f ts1 ts2
  | TyConstr (tid1, ts1), TyConstr (tid2, ts2) ->
      if tid1 <> tid2 then raise Iter2;
      list_iter2 f ts1 ts2
  | TyArrow _, _
  | TyProduct _, _
  | TyConstr _, _
  | TyEq _, _->
      raise Iter2

(* The function [conjunction] that is expected by the solver is essentially
   [iter2], except it must return a structure, as opposed to a unit value. *)

exception InconsistentConjunction =
  Iter2

let conjunction f t u =
  iter2 f t u;
  t

(* -------------------------------------------------------------------------- *)

(* Printing. *)

open PPrint

let pprint leaf s =
  match s with
  | TyArrow (t1, t2) ->
      parens (leaf t1) ^^ string " -> " ^^ leaf t2
  | TyProduct ts ->
      braces (separate_map (string " * ") leaf ts)
  | TyConstr (Datatype.Type c, ts) ->
      string c ^^ parens (separate_map (string ", ") leaf ts)
  | TyEq (t1, t2) ->
      parens (leaf t1 ^^ string " = " ^^ leaf t2)
