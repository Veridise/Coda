open Ast
open Dsl
open Typecheck

let i = v "i"
let n = v "n"
let vin = v "in"
let vout = v "out"

let n2b_body = lama "i" tint (
  lama "lc1_e2" (ttuple [tf; tf]) (
    elet "lc1" (tget (v "lc1_e2") 0) (
    elet "e2" (tget (v "lc1_e2") 1) (
    tmake [
      fadd (v "lc1") (fmul (get vout i) (v "e2"));
      fadd (v "e2") (v "e2")]))))

let n2b_inv = fun i -> fun x -> ttuple [
  tfe (eq nu (to_big_int TF f1 i (take vout i)));
  tfe (eq nu (fpow f2 i))]

let (tn2bloop, check_n2bloop) = synthesize [] [("out", tarr tf QTrue (zc 5))] [] (
  (Iter { s = z0; e = zc 4; body = n2b_body; init = tmake [f0; f1];
    inv = n2b_inv}))

let n2b_tout = tarr tf_binary (QExpr (eq (to_big_int TF f1 n nu) vin)) (nadd1 n)

let num2bits = Circuit {
  name = "Num2Bits";
  inputs = [("n", tnat); ("in", tf)];
  outputs = [("out", n2b_tout)];
  dep = None;
  body = [
    (* slet "lc1_e2" (Iter {s = z0; e = n; body = n2b_body; init = tmake [f0; f1]; inv = n2b_inv});
    slet "lc1" (tget (v "lc1_e2") 0);
    assert_forall "i" (QExpr (binary_eq (get vout i))) *)
  ]
}

let check_n2b = typecheck_circuit d_empty num2bits

let b2n_tin = tarr tf_binary QTrue n
let b2n_tout = tfe (eq nu (to_big_int TF f1 n vin))

let bits2num = Circuit {
  name = "Bits2Num";
  inputs = [("n", tnat); ("in", b2n_tin)];
  outputs = [("out", b2n_tout)];
  dep = None;
  body = [
    (* slet "s" (
      sum z0 (sub1z n)
        (lam "i"
          (fmul (get vin i) (fpow f2 i))));
    assert_eq (v "s") vout *)
  ]
}

let check_b2n = typecheck_circuit d_empty bits2num;;