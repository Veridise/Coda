(** Circuits for codegen tests *)

open Lib__Ast
open Lib__Dsl

let is_zero =
  Circuit {
      name = "IsZero";
      inputs = [("in", tf)];
      exists = [("inv", tf)];
      outputs = [("out", tf_binary)];
      ctype = TFun ("in", tf, tf_binary);
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
      inputs = [("in", TArr (tf, QP, f2))];
      exists = [];
      outputs = [("out", tf_binary)];
      ctype = TFun ("in", TArr (tf, QP, f2), tf_binary);
      body = [
          (* isz_in === in[1] - in[0] *)
          assert_eq (v "isz_in") (sub (ArrayOp (Get, v "in", f1)) (ArrayOp (Get, v "in", f0)));
          (* isz_out === IsZero isz_in *)
          assert_eq (v "isz_out") (Call ("IsZero", [v "isz_in"]));
          (* isz_out === out *)
          assert_eq (v "isz_out") (v "out")
        ]
    }

(* Output type for Num2Bits *)
let n2b_tout = tarr tf_binary (QExpr (eq (to_big_int TF f1 (v "n") nu) (v "in"))) (v "n")

let num2bits =
  Circuit {
      name = "Num2Bits";
      inputs = [("n", tint); ("in", tf)];
      exists = [];
      outputs = [("out", n2b_tout)];
      ctype = TFun ("n", tnat, TFun ("in", tf, n2b_tout));
      body = [
          (* cons = map (\x => x * (x - 1) === 0) out *)
          SLet ("cons",
                Map (Lam ("outi", eq (mul (v "outi") (sub (v "outi") f1)) f0), v "out")
            );
          (* (lc1, _) = foldl (\(x, y) outi => (x + outi * y, y + y)) (0, 1) out *)
          SLetP (PProd [PStr "lc1"; PStr "_"],
                 Foldl {
                     f = LamP (
                             PProd [PProd [PStr "x"; PStr "y"]; PStr "outi"],
                             TMake [
                                 add (v "x") (mul (v "outi") (v "y"));
                                 add (v "y") (v "y")
                               ]
                           );
                     acc = TMake [f0; f1];
                     xs = v "out"
                   }
            );
          (* (foldl (\acc c => acc && c) true cons) && (lc1 === in) *)
          SAssert (QExpr (
                       band
                         (Foldl {
                              f = LamP (
                                      PProd [PStr "acc"; PStr "c"],
                                      band (v "acc") (v "c")
                                    );
                              acc = btrue;
                              xs = v "cons"
                         })
                         (eq (v "lc1") (v "in"))
                     )
            )
        ]
    }
