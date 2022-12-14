open Lib__Ast
open Lib__Dsl
open Lib__Typecheck


let _ = typecheck [] [] [] (Iter {
  s=z0; 
  e=zc 5; 
  body=Lam ("i", tint, Lam ("x", tf, add (v "x") f1));
  init=f0;
  inv=fun i -> fun x -> QExpr (eq i x)});;

let d = add_to_delta d_empty is_zero

let is_zero_spec = TRef (TF, QIte (QExpr (eq (v "in") f0), QExpr (eq nu f1), QExpr (eq nu f0)))
let is_zero = Circuit {
  name = "isZero";
  params = [("in", Input, tf); ("out", Output, is_zero_spec); ("inv", Exists, tf)];
  body = [
    assert_eq (v "out") (add (opp (mul (v "in") (v "inv"))) f1);
    assert_eq (mul (v "in") (v "out")) f0
  ]
}

let is_equal_spec = TRef (TF, QIte (QExpr (eq (v "x") (v "y")), QExpr (eq nu f1), QExpr (eq nu f0)))
let is_equal = Circuit {
  name = "isEqual";
  params = [("x", Input, tf); ("y", Input, tf); ("out", Output, is_equal_spec)];
  body = [
    slet "z0" (Call ("isZero", [sub (v "x") (v "y")]));
    (* slet "z1" (sub f1 (v "z0")); *)
    assert_eq (v "out") (v "z0")
  ]
}

let num2bits = Circuit {
  name = "Num2Bits";
  params = [
    ("n", Input, tint); 
    ("in", Input, tf); 
    ("out", Output, TArr (tf_binary, QExpr (eq (toBigInt "i" z1 (v "n") nu) (v "in")), v "n"))
  ];
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
