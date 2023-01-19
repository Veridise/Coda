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
                                        ArrayOp (Concat, v "ss", ArrayOp (Cons, tget (v "sci") 0, cnil));
                                        TGet (v "sci", 1)
                                      ]
                               )
                           );
                     acc = TMake [cnil; f0];
                     xs = v "abs"
                   }
            );
          (* out === sums ++ [carry] *)
          assert_eq (v "out") (ArrayOp (Concat, v "sums", ArrayOp (Cons, v "carry", cnil)))
        ]
    }

let big_add_mod_p =
  Circuit {
      name = "BigAddModP";
      inputs = [("n", tint); ("k", tnat);
                ("a", t_arr_tf (v "k")); ("b", t_arr_tf (v "k")); ("p", t_arr_tf (v "k"))];
      exists = [];
      outputs = [("out", t_arr_tf (v "k"))];
      ctype = TFun ("n", tint, TFun ("k", tnat,
                                     TFun ("a", t_arr_tf (v "k"),
                                           TFun ("b", t_arr_tf (v "k"),
                                                 TFun ("c", t_arr_tf (v "k"), t_arr_tf (v "k"))))));
      body = [
          (* add = #BigAdd n k a b *)
          SLet ("add", Call ("BigAdd", [v "n"; v "k"; v "a"; v "b"]));
          (* lt = #BigLessThan n (k + 1) add (p ++ [0]) *)
          SLet (
              "lt",
              Call ("BigLessThan",
                    [v "n"; add (v "k") z1; v "add"; ArrayOp (Concat, v "p", ArrayOp (Cons, f0, cnil))])
            );
          (* p0 = map (\x => (1 - lt) * x) p *)
          SLet (
              "p0",
              Map (Lam ("x", mul (sub f1 (v "lt")) (v "x")), v "p")
            );
          (* sub = #BigSub n (k + 1) add (p0 ++ [0]) *)
          SLet (
              "sub",
              Call ("BigSub",
                    [v "n"; add (v "k") z1; v "add"; ArrayOp (Concat, v "p0", ArrayOp (Cons, f0, cnil))])
            );
          (* out ++ [0] = sub *)
          assert_eq (ArrayOp (Concat, v "out", ArrayOp (Cons, f0, cnil))) (v "sub")
        ]
    }

let big_mult_short_long =
  Circuit {
      name = "BigMultShortLong";
      inputs = [("n", tint); ("k", tnat); ("m_out", tnat);
                ("a", t_arr_tf (v "k")); ("b", t_arr_tf (v "k"))];
      exists = [];
      outputs = [("out", t_arr_tf (sub (mul z2 (v "k")) z1))];
      ctype = TFun ("n", tint,
                    TFun ("k", tnat,
                          TFun ("m_out", tnat,
                                TFun ("a", t_arr_tf (v "k"),
                                      TFun ("b", t_arr_tf (v "k"), t_arr_tf (sub (mul z2 (v "k")) z1))))));
      (* TODO: Add invariants *)
      body = [
          (* k2 = 2 * k - 1 *)
          slet "k2" (sub (mul f2 (v "k")) f1);
          (* pow = iter 0 k2
                        (\i acci =>
                            let powi = iter 0 k2 (\j accj => let powij = i ** j in accj ++ [powij]) []
                            in acci ++ [powi])
                        [] *)
          slet "pow" (
              Iter {
                  s = z0;
                  e = v "k2";
                  body = LamP (
                             PProd [PStr "i"; PStr "acci"],
                             elet
                               "powi"
                               (
                                 Iter {
                                     s = z0;
                                     e = v "k2";
                                     body = LamP (
                                                PProd [PStr "j"; PStr "accj"],
                                                elet
                                                  "powij"
                                                  (pow (v "i") (v "j"))
                                                  (concat (v "accj") (cons (v "powij") cnil))
                                              );
                                     init = cnil;
                                     inv = (fun _ -> fun _ -> tf)
                                   }
                               )
                               (concat (v "acci") (cons (v "powi") cnil))
                           );
                  init = cnil;
                  inv = (fun _ -> fun _ -> tf)
                }
            );
          (* arr_mul = \l0 l1 => let l = zip l0 l1 in map (\(x, y) => x * y) l *)
          slet "arr_mul" (
              LamP (PProd [PStr "l0"; PStr "l1"],
                    elet "l"
                      (Zip ((v "l0"), (v "l1")))
                      (Map (LamP (PProd [PStr "x"; PStr "y"], mul (v "x") (v "y")), v "l")))
            );
          (* sum = \l => foldl (\acc x => acc + x) 0 l *)
          slet "sum" (
              lam "l" (
                  Foldl {
                      f = LamP (PProd [PStr "acc"; PStr "x"], add (v "acc") (v "x"));
                      acc = f0;
                      xs = v "l"
                    }
                )
            );
          (* poly = \z => iter 0 k2 (\i acc => acc ++ [sum (arr_mul z pow[i])]) [] *)
          slet "poly" (
              lam "z" (
                  Iter {
                      s = z0;
                      e = v "k2";
                      body = LamP (
                                 PProd [PStr "i"; PStr "acc"],
                                 elet
                                   "powi"
                                   (get (v "pow") (v "i"))
                                   (concat
                                      (v "acc")
                                      (cons
                                         (app (v "sum") (app (v "arr_mul") (TMake [v "z"; v "powi"])))
                                         (cnil)))
                               );
                      init = cnil;
                      inv = (fun _ -> fun _ -> tf)
                    }
                )
            );
          (* poly out === arr_mul (poly a) (poly b) *)
          assert_eq
            (app (v "poly") (v "out"))
            (app (v "arr_mul") (TMake [app (v "poly") (v "a"); app (v "poly") (v "b")]))
        ]
    }



(* let pow := init(0, k2, lambda i. init(0, k2, lambda j. i**j) in
 * let poly := lambda x. init(0, k2, lambda i. sum(x * pow[i]) in 
 * poly out == poly a * poly b. *)
