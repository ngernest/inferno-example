open Client

(* A few manually constructed terms. *)

let hole =
  ML.Hole (None, [])

let x =
  ML.Var (None, "x")

let y =
  ML.Var (None, "y")

let id =
  ML.Abs (None, "x", x)

let delta =
  ML.Abs (None, "x", ML.App (None, x, x))

(* unused *)
let _deltadelta =
  ML.App (None, delta, delta)

let idid =
  ML.App (None, id, id)

let k =
  ML.Abs (None, "x", ML.Abs (None, "y", x))

let genid =
  ML.Let (None, ML.Non_recursive,
          "x", id, x)

let genidid =
  ML.Let (None, ML.Non_recursive,
          "x", id, ML.App (None, x, x))

let genkidid =
  ML.Let (None, ML.Non_recursive,
          "x", ML.App (None, k, id), ML.App (None, x, id))

let genkidid2 =
  ML.Let (None, ML.Non_recursive,
          "x", ML.App (None, ML.App (None, k, id), id), x)

(* unused *)
let _app_pair = (* ill-typed *)
  ML.App (None, ML.Tuple (None, [id; id]), id)

let unit =
  ML.Tuple (None, [])

(* "let x1 = (...[], ...[]) in ...[] x1" *)
let regression1 =
  ML.Let (None, ML.Non_recursive,
          "x1", ML.Tuple (None, [ ML.Hole (None, []) ;
                                       ML.Hole (None, []) ]),
          ML.App (None, ML.Hole (None, []), ML.Var (None, "x1")))

(* "let f = fun x ->
              let g = fun y -> (x, y) in
              g
            in
            fun x -> fun y -> f" *)
let regression2 =
  ML.(
    Let (None, Non_recursive,
      "f",
      Abs (None,
        "x",
        Let (None, Non_recursive,
          "g",
          Abs (None,
            "y",
            Tuple (None, [x; y])
          ),
          Var (None, "g")
        )),
        Abs(None,
          "x",
          Abs(None,
            "y",
            Var (None, "f"))))
  )

let abs_match_with =
  ML.(
    Abs(
      None,
      "x",
      Match(
        None,
        Tuple (None, []),
        [ (PTuple (None, []), Tuple (None, [])) ]
      )
    )
  )

(* option *)
let option_env =

  (* type 'a option = None | Some of 'a *)
  let option_typedecl =
    let open Datatype in {
    name = Type "option";
    type_params = [ "'a" ];
    data_kind = Variant;
    labels_descr = [
      {
        label_name = Label"None";
        type_name = Type "option";
        arg_type = None;
      } ; {
        label_name = Label "Some";
        type_name = Type "option";
        arg_type = Some (ML.TyVar (None,"'a"));
      }
    ]
  } in
  Datatype.Env.add_decl Datatype.Env.empty option_typedecl

let none = ML.Variant (None, Datatype.Label "None" , None )

let some =
  ML.Variant (
    None,
    Datatype.Label "Some",
    Some id
  )

let match_none = ML.(
    Match (None, none, [
      PVariant (None, Datatype.Label "None", None), none ;
      PVariant (None, Datatype.Label "Some", Some (PVar (None, "x"))), x ;
    ])
  )

let match_some = ML.(
    Match (None, some, [
      PVariant (None, Datatype.Label "None", None), none ;
      PVariant (None, Datatype.Label "Some", Some (PWildcard None)), none
    ])
  )

let match_some_annotated = ML.(
    Match (None, some, [
      ( PVariant (None, Datatype.Label "None", None), none );
      ( PAnnot (None,
                PVariant (None, Datatype.Label "Some",
                          Some (PWildcard None)),
                (Flexible, ["'a"], TyConstr (None, Datatype.Type "option",
                                   [ TyVar (None, "'a") ]))),
        none );
    ])
  )

(* list *)
let list_env =

  (* type 'a list = Nil | Cons of 'a * 'a list *)
  let list_typedecl =
    let open Datatype in {
    name = Type "list";
    type_params = [ "'a" ];
    data_kind = Variant;
    labels_descr = [
      {
        label_name = Label "Nil";
        type_name = Type "list";
        arg_type = None;
      } ; {
        label_name = Label "Cons";
        type_name = Type "list";
        arg_type = Some (ML.(TyProduct (None,
                                        [ TyVar (None, "'a") ;
                                          TyConstr (None,
                                                    Type "list",
                                                    [ TyVar (None, "'a") ])
                                        ]
                     )));
      }
    ]
  } in

  Datatype.Env.add_decl option_env list_typedecl

let nil = ML.Variant (None, Datatype.Label "Nil" , None )

let cons =
  ML.Variant (
    None,
    Datatype.Label "Cons",
    Some (ML.Tuple (None, [ id ; nil ]))
  )

(* unused *)
let _list_annotated =
  let open ML in
  Annot (
    None,
    Variant (
      None,
      Datatype.Label "Cons",
      Some (Tuple (None, [
                  Annot (None, id,
                         (Flexible, ["'a"], TyArrow (None,
                                           TyVar (None, "'a"),
                                           TyVar (None, "'a"))));
                  nil ]))
    ),
    (Flexible, ["'a"; "'b"], TyConstr (None,
                             Datatype.Type "list",
                             [TyArrow (None,
                                       TyVar (None, "'a"),
                                       TyVar (None, "'b"))]))
  )

(* tree *)
let tree_env =

  (* type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree *)
  let tree_typedecl =
    let open Datatype in {
    name = Type "tree";
    type_params = [ "'a" ];
    data_kind = Variant;
    labels_descr = [
      {
        label_name = Label "Leaf";
        type_name = Type "tree";
        arg_type = None
      } ; {
        label_name = Label "Node";
        type_name = Type "tree";
        arg_type = Some (ML.(TyProduct (None, [
          TyConstr (None, Type "tree", [ TyVar (None, "'a") ]);
          TyVar (None, "'a");
          TyConstr (None, Type "tree", [ TyVar (None, "'a") ]);
        ])))
      }
    ];
  } in

  Datatype.Env.add_decl list_env tree_typedecl

let leaf = ML.Variant (None, Datatype.Label "Leaf" , None )

let node =
  ML.Variant (
    None,
    Datatype.Label "Node",
    Some (ML.Tuple (None, [
      leaf ;
      id ;
      leaf ;
    ]))
  )

(* Families of terms of increasing size. *)

let rec boom n =
  if n = 0 then
    "let f = fun x -> fun f -> f x x in "
  else
    boom (n - 1) ^
    "let f = fun x -> f (f x) in "

let boom n =
  boom n ^ "f"

let parse (s : string) : ML.term =
  let lexbuf = Lexing.from_string s in
  MLParser.self_contained_term MLLexer.read lexbuf

let boom n =
  parse (boom n)

(* Infrastructure. *)

let test_ok_from_ast datatype_env t () =
  Alcotest.(check bool) "type inference"
    (Test.CheckML.test ~rectypes:false datatype_env t)
    true

let test_case msg datatype_env t =
  Alcotest.(test_case msg `Quick (test_ok_from_ast datatype_env t))
  (* TODO: there is also a function named [test_case] in core.ml,
     this is confusing! *)

let test_suite =
  let empty = Datatype.Env.empty in
  (
    "test ML ast",
    [ test_case "hole" empty hole ;
      test_case "id" empty id ;
      test_case "id id" empty idid ;
      test_case "gen id" empty genid ;
      test_case "gen id id" empty genidid ;
      test_case "gen k id id" empty genkidid ;
      test_case "gen k id id 2" empty genkidid2 ;
      test_case "none" option_env none ;
      test_case "some" option_env some ;
      test_case "nil" list_env nil ;
      test_case "list" list_env cons ;
      test_case "leaf" tree_env leaf ;
      test_case "node" tree_env node ;
      test_case "abs match with" empty abs_match_with ;
      test_case "match none" option_env match_none ;
      test_case "match some" option_env match_some ;
      test_case "boom 0" empty (boom 0);
      test_case "boom 1" empty (boom 1);
      test_case "boom 2" empty (boom 2);
      test_case "boom 3" empty (boom 3);
      test_case "boom 4" empty (boom 4);
        (* boom 4 requires about 0.8 seconds *)
        (* boom 5 explodes, at over 25Gb and 60 seconds. *)
    ]
  )

(* -------------------------------------------------------------------------- *)

let testable_term =
  let pprint fmt t =
    PPrint.ToFormatter.pretty 0.9 80 fmt (MLPrinter.print_term t)
  in
  Alcotest.testable pprint Test.CheckML.equal_term

let test_ok ?(typedecl="") s expected =
  let (datatype_env, t) = Test.CheckML.from_string typedecl s in
  Alcotest.check' testable_term ~msg:"equal" ~expected ~actual:t;
  Alcotest.(check bool) "type inference" (Test.CheckML.test ~rectypes:false datatype_env t) true

let test_error_parsing ?(typedecl="") s =
  let ok =
    match Test.CheckML.from_string typedecl s with
    | exception Test.CheckML.ParsingError _ -> false
    | _ -> true in
  Alcotest.(check bool "parsing" ok false)

let test_id () =
  test_ok "fun x -> x" id

let test_delta_delta_error () =
  test_error_parsing "(fun x -> x x (fun x -> x x)"

let test_idid () =
  test_ok "(fun x -> x) (fun x -> x)" idid

let test_idid_error () =
  test_error_parsing "fun x -> x fun x -> x"

let test_unit () =
  test_ok "()" unit

let test_abs_match_with () =
  test_ok "fun x -> match () with () -> () end" abs_match_with

let test_let () =
  test_ok "let y = fun x -> x in ()"
    (ML.Let(None, ML.Non_recursive, "y", id, unit))

let test_let_prod_singleton () =
  test_ok "let (y,) = (fun x -> x,) in ()"
    (ML.LetProd (None, ["y"], ML.Tuple (None, [id]), unit))

let test_let_prod () =
  test_ok "let (y,z) = (fun x -> x, ()) in ()"
  (ML.LetProd (None, ["y";"z"], ML.Tuple (None, [id;unit]), unit))

let test_singleton () =
  test_ok
    "(fun x -> x,)"
    (ML.Tuple (None, [id]))

let test_pair_tuple () =
  test_ok
    "(fun x -> x, fun x -> x)"
    (ML.Tuple (None, [id; id]))

let option_env_str =
  "type option 'a = None | Some of 'a"

let test_none () =
  test_ok
    ~typedecl:option_env_str
    "None"
    none

let test_some () =
  test_ok
    ~typedecl:option_env_str
    "Some (fun x -> x)"
    some

let test_some_pair () =
  test_ok
    ~typedecl:option_env_str
    "Some (fun x -> x, fun x -> x)"
    (ML.Variant (None, Datatype.Label "Some",
                 Some (ML.Tuple (None, [id;id]))))

let list_env_str = "type list 'a = Nil | Cons of {'a * list 'a}"

let test_list_nil () =
  test_ok
    ~typedecl:list_env_str
    "Nil"
    nil

let test_list_cons () =
  test_ok
    ~typedecl:list_env_str
    "Cons (fun x -> x, Nil)"
    cons

let test_arrow () =
  test_ok
    ~typedecl:"type func 'a 'b = Func of 'a -> 'b"
    "Func (fun x -> x)"
    (ML.Variant (None, Datatype.Label "Func", Some id))

let test_match_tuple () =
  test_ok
    "match (fun x -> x, ()) with (f, ()) -> f end"
    (ML.Match
       (None,
        ML.Tuple (None, [id;unit]),
        [ (ML.PTuple (None, [ML.PVar (None, "f");
                                  ML.PTuple (None, [])]),
           ML.Var (None, "f")) ]
    ))

let test_match_none () =
  test_ok
    ~typedecl:option_env_str
    {|match None with
     | None -> None
     | Some x -> x
     end|}
  match_none

let test_match_some () =
  test_ok
    ~typedecl:option_env_str
    {|match Some (fun x -> x) with
     | None -> None
     | Some _ -> None
     end|}
  match_some

let test_match_some_annotated () =
  test_ok
    ~typedecl:option_env_str
    {|match Some (fun x -> x) with
     | None -> None
     | (Some _ : some 'a. option 'a) -> None
     end|}
  match_some_annotated

(** Regressions *)
let test_regression1 () =
  test_ok
    "let x1 = (...[], ...[]) in ...[] x1"
    regression1

let test_regression2 () =
  test_ok
    "let f = fun x -> let g = fun y -> (x, y) in g in fun x -> fun y -> f"
    regression2

let a = ML.TyVar (None, "'a")
let b = ML.TyVar (None, "'b")

let id_annot annot =
  ML.(Annot (None, Abs(None, "x", Var (None, "x")), annot))

let test_id_rigid () =
  test_ok
    "(fun x -> x : for 'a. 'a -> 'a)"
    (id_annot (ML.Rigid, ["'a"], ML.TyArrow (None, a, a)))

let test_id_flexible () =
  test_ok
    "(fun x -> x : some 'a 'b. 'a -> 'b)"
    (id_annot (ML.Flexible, ["'a"; "'b"], ML.TyArrow (None, a, b)))

let test_suite =
  let open Alcotest in
  test_suite ::
  [
    (
      "basics",
      [ test_case "id" `Quick test_id;
        test_case "id id" `Quick test_idid;
        test_case "id id error" `Quick test_idid_error;
        test_case "delta delta error" `Quick test_delta_delta_error;
        test_case "unit" `Quick test_unit;
        test_case "regression1" `Quick test_regression1;
        test_case "regression2" `Quick test_regression2;
        test_case "abs match with" `Quick test_abs_match_with;
        test_case "let" `Quick test_let;
        test_case "let prod singleton" `Quick test_let_prod_singleton;
        test_case "let prod" `Quick test_let_prod;
        test_case "singleton" `Quick test_singleton;
      ]
    ) ; (
      "data structures",
      [
        test_case "pair tuple" `Quick test_pair_tuple;
        test_case "none" `Quick test_none;
        test_case "some" `Quick test_some;
        test_case "some pair" `Quick test_some_pair;
        test_case "list nil" `Quick test_list_nil;
        test_case "list cons" `Quick test_list_cons;
        test_case "arrow" `Quick test_arrow;
      ]
    ) ; (
      "pattern matching",
      [
        test_case "match tuple" `Quick test_match_tuple;
        test_case "match none" `Quick test_match_none;
        test_case "match some" `Quick test_match_some;
        test_case "match some annotated" `Quick test_match_some_annotated;
      ]
    ) ; (
      "rigid",
      [
        test_case "id rigid" `Quick test_id_rigid;
        test_case "id flexible" `Quick test_id_flexible;
      ]
    )
  ]

let () =
  Alcotest.run ~verbose:false "ML test suite" test_suite
