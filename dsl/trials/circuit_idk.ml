(** Circuits for testing *)

(* open Ast
open Dsl

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
 * poly out == poly a * poly b. *) *)
