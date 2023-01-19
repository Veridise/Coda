open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let a = v "a"
let b = v "b"
let vin = v "in"
let out = v "out"


(* NOT *)
let tnot = tboole (eq nu (unint "not" [v "a"]))
let cnot = Circuit {
  name = "Not";
  inputs = [("in", tf_binary)];
  outputs = [("out", tnot)];
  exists = [];
  ctype = tfun "in" tf_binary tnot;
  body = [
    assert_eq out (sub (add1f vin) (mul f2 vin))
  ]
}
let check_not = typecheck_circuit d_empty cnot


(* XOR *)
let txor = tfq (ind_dec nu (unint "xor" [v "a"; v "b"]))
let cxor = Circuit {
  name = "Xor";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", txor)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary txor);
  body = [
    assert_eq out (sub (add a b) (muls [f2; a; b]))
  ]
}
let check_xor = typecheck_circuit d_empty cxor


(* AND *)
let tand = tfq (ind_dec nu (unint "and" [v "a"; v "b"]))
let cand = Circuit {
  name = "And";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", tand)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary tand);
  body = [
    assert_eq out (sub (add a b) (muls [f2; a; b]))
  ]
}
let check_and = typecheck_circuit d_empty cand


(* NAND *)
let tnand = tfq (ind_dec nu (unint "nand" [v "a"; v "b"]))
let cnand = Circuit {
  name = "Nand";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", tnand)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary tnand);
  body = [
    assert_eq out (sub f1 (mul a b))
  ]
}
let check_nand = typecheck_circuit d_empty cnand


(* OR *)
let tor = tfq (ind_dec nu (unint "or" [v "a"; v "b"]))
let cor =
  Circuit {
      name = "Or";
      inputs = [("a", tf_binary); ("b", tf_binary)];
      outputs = [("out", tor)];
      exists = [];
      (* \a => \b => TF{out | out = a + b - a * b} *)
      ctype = tfun "a" tf_binary (tfun "b" tf_binary tor);
      body = [
          assert_eq out (sub (add a b) (mul a b))
        ]
    }
let check_or = typecheck_circuit d_empty cor


(* NOR *)
let tnor = tboole (eq nu (unint "nor" [v "a"; v "b"]))
let cnor = Circuit {
  name = "Nor";
  inputs = [("a", tf_binary); ("b", tf_binary)];
  outputs = [("out", tnor)];
  exists = [];
  ctype = tfun "a" tf_binary (tfun "b" tf_binary tnor);
  body = [
    assert_eq out (sub (sub (add1f (mul a b)) a) b)
  ]
}
let check_nor = typecheck_circuit d_empty cnor