(** Circuits for codegen tests *)

open Lib__Ast
open Lib__Dsl

let is_zero =
  Circuit {
      name = "IsZero";
      signals = [
          ("in", Input, tf);
          ("out", Output, tf);
          ("inv", Exists, tf)
        ];
      property = None;
      body = [
          assert_eq (v "out") (sub (fc 1) (mul (v "in") (v "inv")));
          assert_eq (mul (v "in") (v "out")) (fc 0)
        ]
    }

let is_equal =
  Circuit {
      name = "IsEqual";
      signals = [
          (* Note: Unsure `QP` is correct for `qual` field *)
          ("in", Input, TArr (tf, QP, Const (CInt 2)));
          ("out", Output, tf)
        ];
      property = None;
      body = [
          slet
            "isz"
            (Call ("IsZero",
                   [sub (ArrayOp (Get, Var "in", Const (CInt 1))) (ArrayOp (Get, Var "in", Const (CInt 0)))]));
          assert_eq (v "isz") (v "out")
        ]
    }
