open Lib__Ast
open Lib__Dsl
open Lib__Typecheck


let tx = tf
let ty = re TF (eq nu (v "x"))
let c1 = Circuit {
  name = "c1";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  exists = [];
  ctype = tfun "x" tf ty;
  body = []
}

let d = add_to_delta [] c1

let ty = re TF (eq nu (v "x"))

let c2 = Circuit {
  name = "c2";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  exists = [];
  ctype = tfun "x" tf ty;
  body = [
    slet "y'" (Call ("c1", [v "x"]));
    assert_eq (v "y") (v "y'")
  ]
}

let cs2 = typecheck_circuit d c2



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


let (tloop, check_loop) = synthesize [] [] [] (Iter {
  s = z0; 
  e = zc 5; 
  body = lama "i" tint (lama "x" tf (add (v "x") f1));
  init = f0;
  inv = fun i -> fun x -> tfq (QExpr (eq (toUZ x) i))
})

let (tn2bloop, check_n2bloop) = synthesize [] [("out", tarr tf QTrue (zc 5))] [] (
  (Iter {
  s=z0; 
  e=zc 4;
  body=
    lama "i" tint (
    lama "lc1_e2" (ttuple [tf;tf]) (
      elet "lc1" (tget (v "lc1_e2") 0) (
      elet "e2" (tget (v "lc1_e2") 1) (
      tmake [
        add (v "lc1") (mul (get (v "out") (v "i")) (v "e2"));
        add (v "e2") (v "e2")]))));
  init=tmake [f0; f1];
  inv = fun i -> fun x -> ttuple [
    tfe (eq nu (to_big_int f1 i (take (v "out") i) TF));
    tfe (eq nu (pow f2 i))]
}))
(* 

let num2bits = Circuit {
  name = "Num2Bits";
inputs = [("n", tint); ("in", tf)];
outputs = [("out", TArr (tf_binary, QExpr (eq (toBigInt "i" z1 (v "n") nu) (v "in")), v "n"))];
exists = [];
  body = [
    (* SSkip; *)
    SLetP (PProd [PStr "_"; PStr "lc1"; PStr "_"; PStr "cons"], None,
      (Foldl {
      f=LamP (
        PProd [PProd [PStr "i"; PStr "lc1"; PStr "e2"; PStr "cons"]; PStr "outi"],
        TTuple [tint; tf; tf; tbool]),
        
          (* i *)
          add (v "i") z1;
          (* lc1 *)
          add (v "lc1") (mul (v "outi") (v "e2"));
          (* e2 *)
          add (v "e2") (v "e2");
          (* cons *)
          band (v "cons") (eq f0 (mul (v "outi") (sub (v "outi") f1)))
        ], None));
      acc=PCons ([f0; f0; f1; btrue], None);
      xs=(v "out")})) ;
    SAssert (band (v "cons") (eq (v "lc1") (v "in")))
  ]
}

let check_num2bits = typecheck_circuit d_empty num2bits;;
*)