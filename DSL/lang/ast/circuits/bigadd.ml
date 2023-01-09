open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let a = v "a"
let b = v "b"
let c = v "c"
let out = v "out"

let t_mst = tboole (eq nu (unint "xor" [v "a"; v "b"]))
let cxor = Circuit {
  name = "xor";
  inputs = [("a", tf); ("b", tf_binary)];
  outputs = [("out", txor)];
  exists = [];
  (* TODO *)
  ctype = tfun "_" tf tf;
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