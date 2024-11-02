module ML =
  Client.ML

(* [split n] produces two numbers [n1] and [n2] comprised between [0] and
   [n] (inclusive) whose sum is [n]. *)

let split n st =
  let n1 = Random.State.int st (n + 1) in
  let n2 = n - n1 in
  n1, n2

(* [k] is the number of variables that are currently in scope; [n] is
   the goal size, that is, the desired number of internal nodes). *)

open QCheck.Gen

let int2var k =
  "x" ^ string_of_int k

let var x =
  ML.Var (None, int2var x)

let bind k =
  int2var <$> pure k

let abs self k n =
  let+ x, t = pair (bind k) (self (k + 1, n - 1))
  in ML.Abs (None, x, t)

let app self k n =
  let* n1, n2 = split (n - 1) in
  let+ t1, t2 = pair (self (k, n1)) (self (k, n2))
  in ML.App (None, t1, t2)

let let_ self k n =
  let* n1, n2 = split (n - 1) in
  let* rec_ =
    frequency [
      3, pure ML.Non_recursive;
      1, pure ML.Recursive;
    ] in
  let+ x, t1, t2 =
    let inner_k = match rec_ with
      | ML.Non_recursive -> k
      | ML.Recursive -> k + 1 in
    triple (bind k) (self (inner_k, n1)) (self (k + 1, n2))
  in ML.Let (None, rec_, x, t1, t2)

let pair self k n =
  let* n1, n2 = split (n - 1) in
  let+ t1, t2 = pair (self (k, n1)) (self (k, n2))
  in ML.Tuple (None, [t1; t2])

let let_pair self k n =
  let* n1, n2 = split (n - 1) in
  let+ x1, x2, t1, t2 =
    quad
      (bind k)
      (bind (k + 1))
      (self (k, n1))
      (self (k + 2, n2))
  in ML.LetProd (None, [x1; x2], t1, t2)

let annot self k n =
  let+ t = self (k, n - 1) in
  ML.Annot (None, t, (ML.Flexible, ["'a"], ML.TyVar (None, "'a")))

let term = fix (fun self (k, n) ->
  if n = 0 then begin
    assert (k > 0);
    var <$> (int_bound (k - 1))
  end
  else if k = 0 then
    abs self k n
  else
    frequency [
      1, abs self k n ;
      1, app self k n ;
      1, let_ self k n ;
      1, pair self k n ;
      1, let_pair self k n ;
      1, annot self k n ;
    ]
)

let pure_lambda_term = fix (fun self (k, n) ->
  if n = 0 then begin
    assert (k > 0);
    var <$> (int_bound (k - 1))
  end
  else if k = 0 then
    abs self k n
  else
    frequency [
      8, abs self k n ;
      8, app self k n ;
      2, let_ self k n ;
      1, annot self k n ;
    ]
)
