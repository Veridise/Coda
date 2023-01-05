open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let a = v "a"
let b = v "b"
let out = v "out"

let txor = tboole (eq nu (unint "xor" [v "a"; v "b"]))
let cxor = Circuit {
  name = "xor";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", txor)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary txor);
  body = [
    assert_eq out (sub (add a b) (muls [f2; a; b]))
  ]
}

let check_and = typecheck_circuit d_empty cand

let tand = tboole (eq nu (unint "and" [v "a"; v "b"]))
let cand = Circuit {
  name = "and";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", txor)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary txor);
  body = [
    assert_eq out (sub (add a b) (muls [f2; a; b]))
  ]
}

let check_and = typecheck_circuit d_empty cand