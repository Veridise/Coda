(** Circuits for testing *)

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
      inputs = [("n", tnat); ("in", tf)];
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


let big_is_zero =
  Circuit {
      name = "BigIsZero";
      inputs = [("k", tnat); ("in", tarr tf QTrue (v "k"))];
      exists = [];
      outputs = [("out", tf_binary)];
      ctype = TFun ("k", tnat, TFun ("in", tarr tf QTrue (v "k"), tf_binary));
      body = [
          (* is_zeros === map (\ini => #IsZero ini) in *)
          assert_eq (v "is_zeros") (Map (Lam ("ini", Call ("IsZero", [v "ini"])), v "in"));
          (* total === foldl (\acc iszi => acc - iszi) k is_zeros *)
          assert_eq
            (v "total")
            (Foldl {
                 f = LamP (PProd [PStr "acc"; PStr "iszi"], sub (v "acc") (v "iszi"));
                 acc = v "k";
                 xs = v "is_zeros"
            });
          (* out === #IsZero total *)
          assert_eq (v "out") (Call ("IsZero", [v "total"]))
        ]
    }

let mod_sub_three =
  Circuit {
      name = "ModSubThree";
      inputs = [("n", tint); ("a", tf); ("b", tf); ("c", tf)];
      exists = [];
      outputs = [("out", tf); ("borrow", tf)];
      ctype = TFun ("n", tint,
                    TFun ("a", tf, TFun ("b", tf, TFun ("c", tf, TTuple [tf; tf]))));
      body = [
          (* assert(n + 2) <= 253 *)
          SAssert (QExpr (Comp (Leq, add (v "n") z2, zc 253)));
          (* assert(a - b - c + (1 << n) >= 0 *)
          SAssert (QExpr (Comp (Leq, z0, add (sub (v "a") (sub (v "b") (v "c"))) (pow z2 (v "n")))));
          (* b_plus_c === b + c *)
          assert_eq (v "b_plus_c") (add (v "b") (v "c"));
          (* borrow === #LessThan (n + 1) a b_plus_c *)
          assert_eq (v "borrow") (Call ("LessThan", [add (v "n") f1; v "a"; v "b_plus_c"]));
          (* out === borrow * (1 << n) + a - b_plus_c *)
          assert_eq (v "out") (add (mul (v "borrow") (pow f2 (v "n"))) (sub (v "a") (v "b_plus_c")));
        ]
    }

let t_arr_tf k = TArr (tf, QP, k)

let big_add =
  Circuit {
      name = "BigAdd";
      inputs = [("n", tint); ("k", tnat);
                ("a", t_arr_tf (v "k")); ("b", t_arr_tf (v "k"))];
      exists = [];
      outputs = [("out", t_arr_tf (add (v "k") z1))];
      ctype = TFun ("n", tint, TFun ("k", tnat,
                                     TFun ("a", t_arr_tf (v "k"),
                                           TFun ("b", t_arr_tf (v "k"), t_arr_tf (add (v "k") z1)))));
      body = [
          (* abs = zip a b *)
          SLet ("abs", Zip (v "a", v "b"));
          (* (sums, carry) = foldl (\(ss, c) (a, b) =>
             let (si, ci) = ModSumThree n a b c in (ss ++ [si], ci)) ([], 0) abs *)
          SLetP (PProd [PStr "sums"; PStr "carry"],
                 Foldl {
                     f = LamP (
                             PProd [PProd [PStr "ss"; PStr "c"]; PProd [PStr "a"; PStr "b"]],
                             LetIn ("sci",
                                    Call ("ModSumThree", [v "n"; v "a"; v "b"; v "c"]),
                                    TMake [
                                        ArrayOp (Concat, v "ss", ArrayOp (Cons, tget (v "sci") 0, Const CNil));
                                        TGet (v "sci", 1)
                                      ]
                               )
                           );
                     acc = TMake [Const CNil; f0];
                     xs = v "abs"
                   }
            );
          (* out === sums ++ [carry] *)
          assert_eq (v "out") (ArrayOp (Concat, v "sums", ArrayOp (Cons, v "carry", Const CNil)))
        ]
    }
