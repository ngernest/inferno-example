# Basics

  $ cat id.midml
  let id =
    fun x -> x

  $ midml id.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> fun (x : a0) -> x
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat idid.midml
  let idid =
    (fun x -> x) (fun x -> x)

  $ midml idid.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> (fun (x : a0 -> a0) -> x) (fun (x : a0) -> x)
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat wrong-id.midml
  let id =
    fun x -> y

  $ midml wrong-id.midml
  Type inference and translation to System F...
  File "test", line 2, characters 11-12:
  Type error: unbound variable "y".

  $ cat wrong-id2.midml
  let id =
    (fun x -> x : some 'a. 'a -> 'a -> 'a)

  $ midml wrong-id2.midml
  Type inference and translation to System F...
  File "test", line 2, characters 2-40:
  Type error: a cyclic type arose.
  mu  a0. a0 -> a0

  $ cat hole.midml
  let hole =
    ... []

  $ midml hole.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> <a0>...[]
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat error-parsing.midml
  let y =
    fun x ->

  $ midml error-parsing.midml
  File "test", line 2, characters 10-10:
  Syntax error.

# Errors

Unbound variables.

  $ cat error-unbound.midml
  let x = (fun y -> z)

  $ midml error-unbound.midml
  Type inference and translation to System F...
  File "test", line 1, characters 18-19:
  Type error: unbound variable "z".

Some unification errors (not exhaustive!)

  $ cat error-unify-letprod.midml
  let letprod_error =
    let (x, y) = (fun z -> z) in x

  $ midml error-unify-letprod.midml
  Type inference and translation to System F...
  File "test", line 2, characters 16-26:
  Type error: mismatch between the type:
  {r2*r4}
  and the type:
  r8 -> r10

  $ cat error-unify-app-fun.midml
  let app_error = fun x ->
    (x, x) (fun y -> y)

  $ midml error-unify-app-fun.midml
  Type inference and translation to System F...
  File "test", line 2, characters 2-8:
  Type error: mismatch between the type:
  r8 -> r4
  and the type:
  {r12*r14}

  $ cat error-unify-app-arg.midml
  let x =
    (fun y z -> y z) ()

  $ midml error-unify-app-arg.midml
  Type inference and translation to System F...
  File "test", line 2, characters 19-21:
  Type error: mismatch between the type:
  r12 -> r14
  and the type:
  {}

Cycles

  $ cat error-cycle.midml
  let self_app = fun x -> x x

  $ midml error-cycle.midml
  Type inference and translation to System F...
  File "test", line 1, characters 15-27:
  Type error: a cyclic type arose.
  mu  a0. a0 -> r4

Variable scope escape

  $ cat error-variable-scope-escape.midml
  let rigid_escape = fun f ->
    (fun x -> f x : for 'a . 'a -> 'a)

  $ midml error-variable-scope-escape.midml
  Type inference and translation to System F...
  File "test", line 2, characters 2-36:
  A rigid variable escapes its scope.

# Option type

  $ cat none.midml
  #use option.midml
  
  let _ =
    None

  $ midml none.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> None<option a0> ()
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat some.midml
  #use option.midml
  
  let _ =
    Some (fun x -> x)

  $ midml some.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> Some<option (a0 -> a0)> (fun (x : a0) -> x)
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat some-pair.midml
  #use option.midml
  
  let _ =
    Some (fun x -> x, fun x -> x)

  $ midml some-pair.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 a1 ->
    Some<option {a1 -> a1*a0 -> a0}> (fun (x : a1) -> x, fun (x : a0) -> x)
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

# List type

  $ cat nil.midml
  #use list.midml
  
  let _ =
    Nil

  $ midml nil.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> Nil<list a0> ()
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat cons.midml
  #use list.midml
  
  let _ =
    Cons (fun x -> x, Nil)

  $ midml cons.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 ->
    Cons<list (a0 -> a0)> (fun (x : a0) -> x, Nil<list (a0 -> a0)> ())
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat conscons.midml
  #use list.midml
  
  let _ =
    Cons (
      fun x -> x,
      Cons (
        fun x -> x,
        Nil
      )
    )

  $ midml conscons.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 ->
    Cons<list (a0 -> a0)> (
      fun (x : a0) -> x,
      Cons<list (a0 -> a0)> (fun (x : a0) -> x, Nil<list (a0 -> a0)> ())
    )
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat some-nil.midml
  #use option.midml
  #use list.midml
  
  let _ =
    Some Nil

  $ midml some-nil.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> Some<option (list a0)> (Nil<list a0> ())
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

# Annotations

  $ cat nat-annot.midml
  #use nat.midml
  let f = (fun x -> x : nat -> nat)

  $ midml nat-annot.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  (fun (x : nat ) -> x : nat  -> nat )
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

# Pattern-matching

  $ cat match-tuple.midml
  let _ =
    match (fun x -> x, ()) with (f, ()) -> f end

  $ midml match-tuple.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 ->
    match<a0 -> a0> (fun (x : a0) -> x, ()) with
    | (f, ()) -> f
    end
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat match-some-annotated.midml
  #use option.midml
  
  let _ =
    match Some (fun x -> x) with
    | None -> None
    | (Some _ : some 'a. option 'a) -> None
    end

  $ midml match-some-annotated.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 a1 ->
    match<option a0> Some<option (a1 -> a1)> (fun (x : a1) -> x) with
    | None<option (a1 -> a1)> () -> None<option a0> ()
    | (Some<option (a1 -> a1)> _ : option (a1 -> a1)) -> None<option a0> ()
    end
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

# Recursion

For now there is only support in the parser, so the examples below
parse correctly but fail to type-check.

Mutual recursion is not yet supported.

Polymorphic recursion is not yet supported.

A simple let-rec function: addition of natural numbers.

  $ cat letrec-add.midml
  #use nat.midml
  
  (* toplevel recursion is currently not supported,
     so we wrap a "let rec .. in .." *)
  let add =
    let rec add = fun m n ->
      match m with
      | Zero -> n
      | Succ m1 -> add m1 (Succ n)
      end
    in add

  $ midml letrec-add.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  let rec (add : nat  -> nat  -> nat ) =
    fun (m : nat ) (n : nat ) ->
      match<nat > m with
      | Zero<nat > () -> n
      | Succ<nat > m1 -> add m1 (Succ<nat > n)
      end
  in add
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

A classic let-rec function: List.length

  $ cat letrec-list-length.midml
  #use nat.midml
  #use list.midml
  
  (* toplevel recursion is currently not supported,
     so we wrap a "let rec .. in .." *)
  let length =
    let rec length = fun xs ->
      match xs with
      | Nil -> Zero
      | Cons (_, rest) -> Succ (length rest)
      end
    in length

  $ midml letrec-list-length.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 ->
    let rec (length : [a1] list a1 -> nat ) =
      FUN a2 ->
        let (length : list a2 -> nat ) = length [a2] in
        fun (xs : list a2) ->
          match<nat > xs with
          | Nil<list a2> () -> Zero<nat > ()
          | Cons<list a2> (_, rest) -> Succ<nat > (length rest)
          end
    in length [a0]
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

Using recursion to define (loop : 'a -> 'b)

  $ cat letrec-loop.midml
  (* expected type: 'a 'b. 'a -> 'b *)
  let loop =
    let rec loop = fun x -> loop x in
    loop

  $ midml letrec-loop.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 a1 ->
    let rec (loop : [a2] [a3] a3 -> a2) =
      FUN a4 a5 ->
        let (loop : a5 -> a4) = loop [a4] [a5] in fun (x : a5) -> loop x
    in loop [a1] [a0]
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

# Rigid, flexible variables.

Flexible variables can be unified with some structure
or with each other.

  $ cat id-annot-flexible.midml
  let _ =
    (fun x -> x : some 'a 'b. 'a -> 'b)

  $ midml id-annot-flexible.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> (fun (x : a0) -> x : a0 -> a0)
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

  $ cat id-annot-flexible2.midml
  let _ =
    (fun x -> () : some 'a. 'a -> 'a)

  $ midml id-annot-flexible2.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  (fun (x : {}) -> () : {} -> {})
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

Rigid variables enforce polymorphism.
The identity function below is correct.

  $ cat id-rigid.midml
  let _ =
    (fun x -> x : for 'a. 'a -> 'a)

  $ midml id-rigid.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  FUN a0 -> (FUN a1 -> (fun (x : a1) -> x : a1 -> a1)) [a0]
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

The elaborated term is a bit strange, there is one variable a0
corresponding to the outer polymorphism, and a1 for the rigid variable
'a. It is easier to look at the elaboration of the simpler example below:

  $ cat id-rigid2.midml
  let _ =
    (fun x -> x : for 'a. 'a -> 'a) ()

  $ midml id-rigid2.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  (FUN a0 -> (fun (x : a0) -> x : a0 -> a0)) [{}] ()
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

Here we see that the variable 'a is rigid inside the annotated term
(translated to a System F type abstraction), but can be used at any
instantiation type from the outside -- here the unit type {}.

This example is correct as well.
It involves a useless universal quantifier.

  $ cat rigid-redundant.midml
  (* We have a redundant quantifier here: 'b is not used in the type
     annotation. *)
  let _ =
    (fun x -> x : for 'a 'b. 'a -> 'a) ()

  $ midml rigid-redundant.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  (FUN a1 a2 -> (fun (x : a2) -> x : a2 -> a2)) [[a0] a0] [{}] ()
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

This example is also correct.
It involves unreachable generalizable type variables,
that is, type variables that are both unconstrained
and unreachable from the entry point of a type scheme.

  $ cat rigid-unreachable.midml
  (* We have unreachable generalizable variables inside the left-hand
     side of a [letr] combinator. *)
  let _ =
    ((fun x -> fun y -> y) (fun x -> x) : for 'a. 'a -> 'a) ()

  $ midml rigid-unreachable.midml
  Type inference and translation to System F...
  Formatting the System F term...
  Pretty-printing the System F term...
  (FUN a1 a2 ->
    ((fun (x : a1 -> a1) (y : a2) -> y) (fun (x : a1) -> x) : a2 -> a2))
    [[a0] a0]
    [{}]
    ()
  Converting the System F term to de Bruijn style...
  Type-checking the System F term...

The example below is incorrect, it tries to unify two distinct rigid
variables.

  $ cat id-rigid-wrong.midml
  let _ =
    (fun x -> x : for 'a 'b. 'a -> 'b)

  $ midml id-rigid-wrong.midml
  Type inference and translation to System F...
  File "test", line 2, characters 12-13:
  Type error: mismatch between the type:
  r2
  and the type:
  r4

The example below is incorrect, it tries to unify a rigid variable
with some structure.

  $ cat unit-rigid-wrong.midml
  let _ =
    (() : for 'a. 'a)

  $ midml unit-rigid-wrong.midml
  Type inference and translation to System F...
  File "test", line 2, characters 3-5:
  Type error: mismatch between the type:
  r2
  and the type:
  {}

The example below is incorrect, a rigid variable tries to escape
its binding scope.

  $ cat rigid-level-escape-wrong.midml
  let f =
    fun x -> (x : for 'a. 'a)

  $ midml rigid-level-escape-wrong.midml
  Type inference and translation to System F...
  File "test", line 2, characters 12-13:
  A rigid variable escapes its scope.


The example below is incorrect, a rigid variable tries to escape
its binding scope. The escape is only noticed at generalization
time when adjusting levels.

  $ cat rigid-level-escape-later-wrong.midml
  let g = fun f ->
    (f : for 'a. 'a -> 'a)

In the example above,* the type of f is "old" relative to the
rigid-introducing annotation, but we don't notice during the
unification itself which only touches the arrow type ->, not the rigid
variable 'a. The escape will be noticed at generalization time, when
adjusting the level of the type nodes below the arrow.

  $ midml rigid-level-escape-later-wrong.midml
  Type inference and translation to System F...
  File "test", line 2, characters 2-24:
  A rigid variable escapes its scope.
