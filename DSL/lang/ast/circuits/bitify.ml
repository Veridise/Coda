open Lib__Ast
open Lib__Dsl
open Lib__Typecheck


let n2b_body = lama "i" tint (
  lama "lc1_e2" (ttuple [tf; tf]) (
    elet "lc1" (tget (v "lc1_e2") 0) (
    elet "e2" (tget (v "lc1_e2") 1) (
    tmake [
      add (v "lc1") (mul (get (v "out") (v "i")) (v "e2"));
      add (v "e2") (v "e2")]))))

let n2b_inv = fun i -> fun x -> ttuple [
  tfe (eq nu (to_big_int TF f1 i (take (v "out") i)));
  tfe (eq nu (pow f2 i))]

let (tn2bloop, check_n2bloop) = synthesize [] [("out", tarr tf QTrue (zc 5))] [] (
  (Iter { s = z0; e = zc 4; body = n2b_body; init = tmake [f0; f1];
    inv = n2b_inv}))

let n2b_tout = tarr tf_binary (QExpr (eq (to_big_int TF f1 (v "n") nu) (v "in"))) (v "n")

let num2bits = Circuit {
  name = "Num2Bits";
  inputs = [("n", tnat); ("in", tf)];
  outputs = [("out", n2b_tout)];
  ctype = tfun "n" tnat (tfun "in" tf (n2b_tout));
  exists = [];
  body = [
    slet "lc1_e2" (Iter {s = z0; e = v "n"; body = n2b_body; init = tmake [f0; f1]; inv = n2b_inv});
    assert_forall "i" (QExpr (binary_eq (get (v "out") (v "i"))))
  ]
}

let check_n2b = typecheck_circuit d_empty num2bits;;