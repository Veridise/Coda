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
          (* out === 1 - in * inv *)
          assert_eq (v "out") (sub f1 (mul (v "in") (v "inv")));
          (* in * out === 0 *)
          assert_eq (mul (v "in") (v "out")) f0
        ]
    }

let is_equal =
  Circuit {
      name = "IsEqual";
      signals = [
          (* Note: Unsure `QP` is correct for `qual` field *)
          ("in", Input, TArr (tf, QP, f2));
          ("out", Output, tf)
        ];
      property = None;
      body = [
          (* isz_in === in[1] - in[0] *)
          assert_eq (v "isz_in") (sub (ArrayOp (Get, v "in", f1)) (ArrayOp (Get, v "in", f0)));
          (* isz_out === IsZero isz_in *)
          assert_eq (v "isz_out") (Call ("IsZero", [v "isz_in"]));
          (* isz_out === out *)
          assert_eq (v "isz_out") (v "out")
        ]
    }

let num2bits =
  Circuit {
      name = "Num2Bits";
      signals = [
          ("n", Input, tint);
          ("in", Input, tf);
          (* Note: Copied this line from Junrui's version *)
          ("out", Output, TArr (tf_binary, QExpr (eq (toBigInt "i" z1 (v "n") nu) (v "in")), v "n"));
          ("lc1", Exists, tf)
        ];
      property = None;
      body = [
          (* cons = map (\x => x * (x - 1) === 0) out *)
          SLet ("cons",
                None,
                Map (Lam ("outi", tf, eq (mul (v "outi") (sub (v "outi") f1)) f0), v "out")
            );
          (* (foldl (\acc c => acc && c) true cons) && (lc1 === in) *)
          SAssert (band
                     (Foldl {
                          f = LamP (
                                  PProd [PStr "acc"; PStr "c"],
                                  TProd ([tbool; tbool], None),
                                  band (v "acc") (v "c")
                                );
                          acc = btrue;
                          xs = v "cons"
                     })
                     (eq (v "lc1") (v "in"))
            )
        ]
    }
