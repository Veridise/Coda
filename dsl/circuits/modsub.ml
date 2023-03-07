(** Benchmark ModSubThree *)

open Ast
open Dsl
open Typecheck

let a = v "a"

let b = v "b"

let c = v "c"

let n = v "n"

let k = v "k"

let i = v "i"

let x = v "x"

let ab = v "ab"

let out = v "out"

let borrow = v "borrow"

let uf = v "underflow"

let b_plus_c = v "b_plus_c"

(* { v : Int | 1 <= v <= C.k - 2 } *)
let t_n = z_range z1 (zsub2 CPLen)

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let c_mod_sub_three =
  Circuit
    { name= "ModSubThree"
    ; inputs= [("n", t_n); ("a", tf_2n); ("b", tf_2n); ("c", tf_binary)]
    ; outputs= [("out", tf); ("borrow", tf_binary)]
    ; (* out = borrow * 2 ** n + a - (b + c) *)
      dep= Some (qeq out (fsub (fadd (fmul borrow (fpow f2 n)) a) (fadd b c)))
    ; body=
        [ (* b_plus_c = b + c *)
          slet "b_plus_c" (fadd b c)
        ; (* borrow === #LessThan (n + 1) a (b + c) *)
          assert_eq borrow (call "LessThan" [zadd n z1; a; b_plus_c])
        ; (* out === borrow * 2 ** n + a - (b + c) *)
          assert_eq out (fsub (fadd (fmul borrow (fpow f2 n)) a) b_plus_c) ] }

let deltas_ms3 = add_to_deltas d_empty [c_less_than; num2bits]

let check_mod_sub_three = typecheck_circuit deltas_ms3 c_mod_sub_three

(* Proper Big Int of length k *)
let t_big_int k = tarr tf_2n QTrue k

(* { F | binary(nu) /\ nu = 1 <-> [| a |] < [| b |] } *)
let t_uf = tfq (q_ind_dec nu (QExpr (lt (toUZ a) (toUZ b))))

(* \i (s, c) => let (si, ci) = #ModSubThree n (ab[i]).0 (ab[i]).1 c in (s ++ si, ci) *)
let lam_big_sub =
  lama "i" tint
    (lama "x"
       (ttuple [tarr tf QTrue i; tf])
       (elet "s" (tget x 0)
          (elet "c" (tget x 1)
             (elet "a"
                (tget (get ab i) 0)
                (elet "b"
                   (tget (get ab i) 1)
                   (elet "y"
                      (call "ModSubThree" [n; a; b; c])
                      (tmake [concat s (cons (tget y 0) cnil); tget y 1]) ) ) ) ) ) )

let inv_big_sub i _ = ttuple [t_big_int i; tf_binary]

let big_sub =
  Circuit {
      name = "BigSub";
      inputs = [("n", t_n); ("k", tpos); ("a", t_big_int k); ("b", t_big_int k)];
      outputs = [("out", t_big_int k); ("underflow", t_uf)];
      (* [| out |] = [| a |] - [| b |] + [| underflow |] * 2 ^ (n * k) *)
      dep = Some (qeq (toUZ out) (zadd (zsub (toUZ a) (toUZ b)) (zmul (toUZ uf) (zpow z2 (zmul n k)))));
      body = [
          (* ab = zip a b *)
          slet "ab" (zip a b);
          (* (sub, borrow) = iter 0 k lam_big_sub ([], 0) *)
          slet "x" (iter z0 k lam_big_sub (tmake [cnil; f0]) inv_big_sub);
          (* out === sub *)
          assert_eq out (tget x 0);
          (* underflow === borrow *)
          assert_eq uf (tget x 1)
        ]
    }

let deltas_bs = add_to_delta deltas_ms3 c_mod_sub_three

let check_big_sub = typecheck_circuit deltas_bs big_sub
