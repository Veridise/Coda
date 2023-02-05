open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let tx = tf
let ty = re TF (eq nu (v "x"))
let c1 = Circuit {
  name = "c1";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  ctype = tfun "x" tf ty;
  body = []
}

let d = add_to_delta [] c1

let ty = re TF (eq nu (v "x"))

let c2 = Circuit {
  name = "c2";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  ctype = tfun "x" tf ty;
  body = [
    slet "y'" (Call ("c1", [v "x"]));
    assert_eq (v "y") (v "y'")
  ]
}

let cs2 = typecheck_circuit d c2


let (tloop, check_loop) = synthesize [] [] [] (Iter {
  s = z0; 
  e = zc 5; 
  body = lama "i" tint (lama "x" tf (add (v "x") f1));
  init = f0;
  inv = fun i -> fun x -> tfq (QExpr (eq (toUZ x) i))
})