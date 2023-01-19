open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let vin = v "in"
let vout = v "out"
let x = v "x"
let y = v "y"
let z = v "z"
let n = v "n"

let t_is_zero = tfq (ind_dec nu (eq vin f0))
let c_is_zero = Circuit {
  name = "IsZero";
  inputs = [("in", tf)];
  outputs = [("out", t_is_zero)];
  exists = [("inv", tf)];
  ctype = tfun "in" tf t_is_zero;
  body = [
    assert_eq vout (add (opp (mul vin (v "inv"))) f1);
    assert_eq (mul vin vout) f0
  ]
}

let check_is_zero = typecheck_circuit [] c_is_zero

let t_is_equal = tfq (ind_dec nu (eq x y))
let c_is_equal = Circuit {
  name = "IsEqual";
  inputs = [("x", tf);  ("y", tf)];
  outputs = [("out", t_is_equal)];
  ctype = tfun "x" tf (tfun "y" tf t_is_equal);
  exists = [];
  body = [
    slet "z" (Call ("IsZero", [sub x y]));
    assert_eq vout z
  ]
}

let check_is_equal = typecheck_circuit (add_to_delta d_empty c_is_zero) c_is_equal

let t_lt = tfq (ind_dec nu (lt x y))
let c_less_than = Circuit {
  name = "LessThan";
  inputs = [("n", tnat); ("x", tf);  ("y", tf)];
  outputs = [("out", t_lt)];
  exists = [];
  ctype = tfun "x" tf (tfun "y" tf (t_lt));
  body = [
    slet "z" (call "Num2Bits" [add1z n; (add (sub x y) (pow f2 n))]);
    slet "b" (sub1f (get z n));
    assert_eq vout (v "b")
  ]
}