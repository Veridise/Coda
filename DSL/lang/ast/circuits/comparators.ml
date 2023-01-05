open Lib__Ast
open Lib__Dsl
open Lib__Typecheck


let t_out = re TF (ite (eq (v "in") f0) (eq nu f1) (eq nu f0))
let is_zero = Circuit {
  name = "isZero";
  inputs = [("in", tf)];
  outputs = [("out", t_out)];
  exists = [("inv", tf)];
  ctype = tfun "in" tf t_out;
  body = [
    assert_eq (v "out") (add (opp (mul (v "in") (v "inv"))) f1);
    assert_eq (mul (v "in") (v "out")) f0
  ]
}

let check_is_zero = typecheck_circuit [] is_zero;;

let t_out = re TF (ite (eq (v "x") (v "y")) (eq nu f1) (eq nu f0))
let is_equal = Circuit {
  name = "isEqual";
inputs = [("x", tf);  ("y", tf)];
outputs = [("out", t_out)];
ctype = tfun "in" tf t_out;
exists = [];
  body = [
    slet "z0" (Call ("isZero", [sub (v "x") (v "y")]));
    (* slet "z1" (sub f1 (v "z0")); *)
    assert_eq (v "out") (v "z0")
  ]
}

let check_is_equal = typecheck_circuit (add_to_delta d_empty is_zero) is_equal;;