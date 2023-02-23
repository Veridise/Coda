open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let vin = v "in"
let vout = v "out"
let x = v "x"
let y = v "y"
let z = v "z"
let n = v "n"
let k = v "k"
let i = v "i"

let t_is_zero = tfq (ind_dec nu (eq vin f0))
let c_is_zero = Circuit {
  name = "IsZero";
  inputs = [("in", tf)];
  outputs = [("out", t_is_zero)];
  dep = None;
  body = [
    slet "inv" star;
    assert_eq vout (fadd1 (opp (fmul vin (v "inv"))));
    assert_eq (fmul vin vout) f0
  ]
}

let check_is_zero = typecheck_circuit [] c_is_zero

let t_is_equal = tfq (ind_dec nu (eq x y))
let c_is_equal = Circuit {
  name = "IsEqual";
  inputs = [("x", tf);  ("y", tf)];
  outputs = [("out", t_is_equal)];
  dep = None;
  body = [
    slet "z" (Call ("IsZero", [fsub x y]));
    assert_eq vout z
  ]
}

let check_is_equal = typecheck_circuit (add_to_delta d_empty c_is_zero) c_is_equal

let t_lt = tfq (ind_dec nu (lt (toUZ x) (toUZ y)))
let c_less_than = Circuit {
  name = "LessThan";
  inputs = [("n", tnat); ("x", tf);  ("y", tf)];
  outputs = [("out", t_lt)];
  dep = None;
  body = [
    slet "z" (call "Num2Bits" [nadd1 n; (fadd (fsub x y) (fpow f2 n))]);
    slet "b" (fsub1 (get z n));
    assert_eq vout (v "b")
  ]
}

let total = v "total"
let x0 = tget x 0
let x1 = tget x 1

let t_k = z_range 1 (zsub1 CPLen)
let t_arr_tf k = tarr tf QTrue k
let t_tf2 = ttuple [tf; tf]

let q_big_is_zero = qforall [i] (qimply (qand (qleq z0 i) (qlt i k)) (eq (get vin i) f0))
let t_big_is_zero = tfq (ind_dec nu q_big_is_zero)

(* TODO: Add real invariant *)
let inv_big_is_zero _ _ = tf

let lam_big_is_zero = lama "x" t_tf2 (fadd x0 (call "IsZero" [x1]))

let iter_big_is_zero = iter z0 k lam_big_is_zero f0 inv_big_is_zero

let c_big_is_zero =
  Circuit {
      name = "BigIsZero";
      inputs = [("k", t_k); ("in", t_arr_tf k)];
      outputs = [("out", t_big_is_zero)];
      dep = None;
      body = [
          (* total = (iter 0 k (\acc x => acc + #IsZero x) 0) in *)
          slet "total" (app iter_big_is_zero vin);
          (* out === #IsZero (k - total) *)
          assert_eq vout (call "IsZero" [fsub k total])
        ]
    }

let check_big_is_zero = typecheck_circuit (add_to_delta d_empty c_is_zero) c_big_is_zero
