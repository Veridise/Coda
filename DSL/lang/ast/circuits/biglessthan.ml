open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let k = v "k"
let n = v "n"
let i = v "i"
let xs = v "xs"
let ys = v "ys"
let x = v "x"
let y = v "y"

(* circuit BigLessThan
   (n: nat) (k: nat)
   (xs: F^k) (ys: F^k) : { F | v = ([|a|] <= [|b|])? } {
   fold_left 
      \(lt, eq) -> 
      \(x,y) -> 
      (Or(lt, And(eq, LessThen(a,b))), And(eq, IsEqual(x,y)))
      zip(xs, ys)
} *)

(* let to_big k = to_big_int TInt n k *)
let to_big xs = Fn (ToBigUZ, [n; xs])
let big_op op xs ys = tfq (ind_dec nu (op (to_big xs) (to_big ys)))
let t_out = big_op lt xs ys
let tf_big_digit = tfe (leq (toUZ nu) (zsub1 (zpow z2 CPLen)))
let t_in = tarr tf_big_digit QTrue k

let c_big_lt = Circuit {
  name = "BigLessThan";
  inputs = [
    ("n", tnat_e (leq nu (zsub1 CPLen)));
    ("k", tnat_e (leq z2 nu));
    ("xs", t_in);
    ("ys", t_in)];
  outputs = [("out", t_out)];
  dep = None;
  body = [
    slet "lt" (tget (Iter {
      s = z0;
      e = k;
      init = make_pair f0 f1;
      body = lama "i" tint (lama "lt_eq" (tpair tf tf) (
        elet "lt" (fst_pair (v "lt_eq")) (
        elet "eq" (snd_pair (v "lt_eq")) (
        elet "x" (get xs i) (
        elet "y" (get ys i) (
        elet "x_lt_y" (call "LessThan" [n; x; y]) (
        elet "xs_lt_ys" (call "And" [v "eq"; v "x_lt_y"]) (
        elet "x_eq_y" (call "IsEqual" [x; y]) (
        tmake [
          call "Or" [
            v "lt";
            v "xs_lt_ys"
          ];
          call "And" [
            v "eq";
            v "x_eq_y"
          ]
        ])))))))));
      inv = fun i -> fun lt_eq -> 
        tpair
          (big_op lt (take xs i) (take ys i))
          (big_op eq (take xs i) (take ys i))
    }) 0);
    assert_eq (v "out") (v "lt")
  ];
}