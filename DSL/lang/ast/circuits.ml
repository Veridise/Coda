open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

(* let c1 = Circuit {
  name = "c1";
  signals = [("x", Input, tf); ("y", Output, re TF (eq nu (v "x")))];
  (* property = Some (function [x] -> function [y] -> QExpr (eq x y)); *)
  property = None;
  body = []
}

let d = add_to_delta [] c1

let c2 = Circuit {
  name = "c2";
  signals = [("x", Input, tf); ("y", Output, re TF (eq nu (v "x")))];
  property = None;
  body = [
    slet "y'" (Call ("c1", [v "x"]));
    assert_eq (v "y") (v "y'")
  ]
}

let cs2 = typecheck_circuit d c2 *)



let is_zero_spec = re TF (ite (eq (v "in") f0) (eq nu f1) (eq nu f0))
let is_zero = Circuit {
  name = "isZero";
  signals = [("in", Input, tf); ("out", Output, is_zero_spec); ("inv", Exists, tf)];
  property = None;
  body = [
    assert_eq (v "out") (add (opp (mul (v "in") (v "inv"))) f1);
    assert_eq (mul (v "in") (v "out")) f0
  ]
}

let check_is_zero = typecheck_circuit [] is_zero;;

let is_equal_spec = re TF (ite (eq (v "x") (v "y")) (eq nu f1) (eq nu f0))
let is_equal = Circuit {
  name = "isEqual";
  signals = [("x", Input, tf); ("y", Input, tf); ("out", Output, is_equal_spec)];
  property = None;
  body = [
    slet "z0" (Call ("isZero", [sub (v "x") (v "y")]));
    (* slet "z1" (sub f1 (v "z0")); *)
    assert_eq (v "out") (v "z0")
  ]
}

let check_is_equal = typecheck_circuit (add_to_delta d_empty is_zero) is_equal;;

let (tloop, check_loop) = typecheck [] [] [] (Iter {
  s=z0; 
  e=zc 5; 
  body=Lam ("i", tint, Lam ("x", tf, add (v "x") f1));
  init=z0;
  inv= fun i -> fun x -> QExpr (eq i x)});; 
  (* 

let num2bits = Circuit {
  name = "Num2Bits";
  signals = [
    ("n", Input, tint); 
    ("in", Input, tf); 
    ("out", Output, TArr (tf_binary, QExpr (eq (toBigInt "i" z1 (v "n") nu) (v "in")), v "n"))
  ];
  property = None;
  body = [
    (* SSkip; *)
    SLetP (PProd [PStr "_"; PStr "lc1"; PStr "_"; PStr "cons"], None,
      (Foldl {
      f=LamP (
        PProd [PProd [PStr "i"; PStr "lc1"; PStr "e2"; PStr "cons"]; PStr "outi"],
        TProd ([tint; tf; tf; tbool], None),
        PCons ([
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