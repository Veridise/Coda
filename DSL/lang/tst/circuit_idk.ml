(** Circuits for codegen tests *)

open Langast.AST2

let is_zero =
  Circuit {
      name = "IsZero";
      params = [
          ("in", Input, tf);
          ("out", Output, tf);
          ("inv", Exists, tf)
        ];
      body = [
          assert_eq (v "out") (sub (fc 1) (mul (v "in") (v "inv")));
          assert_eq (mul (v "in") (v "out")) (fc 0)
        ]
    }

let is_equal =
  Circuit {
      name = "IsEqual";
      params = [
          (* Note: Unsure `QP` is correct for `qual` field *)
          ("in", Input, TArr (tf, QP, Const (CInt 2)));
          ("out", Output, tf)
        ];
      body = [
          slet
            "isz"
            (Call ("IsZero", [sub (Get (Var "in", Const (CInt 1))) (Get (Var "in", Const (CInt 0)))]));
          assert_eq (v "isz") (v "out")
        ]
    }
