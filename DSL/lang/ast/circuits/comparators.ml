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

let total = v "total"

let x0 = tget x 0
let x1 = tget x 1
let x2 = tget x 2
let x20 = tget x2 0
let x21 = tget x2 1

let t_k = z_range 1 (zsub1 CPLen)
let t_arr_tf k = tarr tf QTrue k

(* IsZero *)
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

(* IsEqual *)
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

(* LessThan *)
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

let q_biz = qforall [i] (qimply (qand (qleq z0 i) (qlt i k)) (eq (get vin i) f0))
let t_biz = tfq (ind_dec nu q_biz)
let t_biz_lam = ttuple [tnat; tf; tf]

(* TODO: Add real invariant *)
let inv_biz _ _ = tf

let lam_biz = lama "x" t_biz_lam (fadd x1 (call "IsZero" [x2]))

let iter_biz = iter z0 k lam_biz f0 inv_biz

(* BigIsZero *)
let c_big_is_zero =
  Circuit {
      name = "BigIsZero";
      inputs = [("k", t_k); ("in", t_arr_tf k)];
      outputs = [("out", t_biz)];
      dep = None;
      body = [
          (* total = (iter 0 k (\_i acc xi => acc + #IsZero xi) 0) in *)
          slet "total" (app iter_biz vin);
          (* out === #IsZero (k - total) *)
          assert_eq vout (call "IsZero" [fsub k total])
        ]
    }

let check_big_is_zero = typecheck_circuit (add_to_delta d_empty c_is_zero) c_big_is_zero

let q_bie = qforall [i] (qimply (qand (qleq z0 i) (qlt i k)) (eq (get a i) (get b i)))
let t_bie = tfq (ind_dec nu q_bie)
let t_bie_lam = ttuple [tnat; tf; ttuple [tf; tf]]

(* TODO: Add real invariant *)
let inv_bie _ _ = tf

let lam_bie = lama "x" t_bie_lam (fadd x1 (call "IsEqual" [x20; x21]))

let iter_bie = iter z0 k lam_bie f0 inv_bie

(* BigIsEqual *)
let c_big_is_equal =
  Circuit {
      name = "BigIsEqual";
      inputs = [("k", t_k); ("a", t_arr_tf k); ("b", t_arr_tf k)];
      outputs = [("out", t_bie)];
      dep = None;
      body = [
          (* ab = zip a b *)
          slet "ab" (zip a b);
          (* total = (iter 0 k (\_i acc (ai, bi) => acc + #IsEqual ai bi) 0) ab *)
          slet "total" (app iter_bie ab);
          (* out === #IsZero (k - total) *)
          assert_eq vout (call "IsZero" [fsub k total])
        ]
    }

let check_big_is_equal =
  typecheck_circuit (add_to_deltas d_empty [c_is_equal; c_is_zero]) c_big_is_equal
