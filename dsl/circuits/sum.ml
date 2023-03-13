(** Benchmarks ModSumThree and BigAdd *)

open Ast
open Dsl

let n = v "n"

let k = v "k"

let p = v "p"

let p' = v "p'"

let a = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let s = v "s"

let x = v "x"

let y = v "y"

let n2b = v "n2b"

let sum = v "sum"

let sub = v "sub"

let carry = v "carry"

let add = v "add"

let lt = v "lt"

let ab = v "ab"

let out = v "out"

let t_n = z_range z1 (zsub1 CPLen)

let t_n' = z_range z1 (zsub2 CPLen)

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let mod_sum_three =
  Circuit
    { name= "ModSumThree"
    ; inputs= [("n", t_n); ("a", tf_2n); ("b", tf_2n); ("c", tf_binary)]
    ; outputs= [("sum", tf_2n); ("carry", tf_binary)]
    ; dep= Some (qeq (fadd sum (fmul carry (fpow f2 n))) (fadd (fadd a b) c))
    ; body=
        (* n2b = #Num2Bits (n + 2) (a + b + c) *)
        elet "n2b"
          (call "Num2Bits" [zadd n z2; fadd (fadd a b) c])
          (* carry === n2b[n] + 2 * n2b[n + 1] *)
          (elet "u0"
             (assert_eq carry
                (fadd (get n2b n) (fmul f2 (get n2b (zadd n z1)))) )
             (* sum === a + b + c - carry * 2^n *)
             (assert_eq sum
                (fsub (fadd (fadd a b) c) (fmul carry (fpow f2 n))) ) ) }

let t_x = ttuple [tnat; ttuple [tf; tf]; ttuple [tf; tf]]

(* Proper big Ints of length k *)
let t_big_int k = tarr_t_k tf_2n k

(* \i (s, c) => let (si, ci) = #ModSumThree n (ab[i]).0 (ab[i]).1 c in (s ++ si, ci) *)
let lam_big_add =
  lama "i" tint
    (lama "x"
       (ttuple [tf; tf])
       (elet "s" (tget x 0)
          (elet "c" (tget x 1)
             (elet "a"
                (tget (get ab i) 0)
                (elet "b"
                   (tget (get ab i) 1)
                   (elet "y"
                      (call "ModSumThree" [n; a; b; c])
                      (make [concat s (cons (tget y 0) cnil); tget y 1]) ) ) ) ) ) )

let inv_big_add i = ttuple [t_big_int i; tf_binary]

let big_add =
  Circuit
    { name= "BigAdd"
    ; inputs= [("n", t_n); ("k", tpos); ("a", t_big_int k); ("b", t_big_int k)]
    ; outputs= [("out", t_big_int (zadd1 k))]
    ; dep= None
    ; body=
        (* ab = zip a b *)
        elet "ab" (zip a b)
          (* (sum, carry) = iter 0 k lam_big_add ([], 0) *)
          (elet "x"
             (iter z0 k lam_big_add ~init:(make [cnil; f0]) ~inv:inv_big_add)
             (* out === sum ++ [carry] *)
             (assert_eq out (concat (tget x 0) (cons (tget x 1) cnil))) ) }

(* BigAddModP *)

let q_lt_p = QExpr (leq (toUZ nu) (zsub1 (toUZ p)))

let q_add_mod_p = qeq (toUZ nu) (zmod (zadd (toUZ a) (toUZ b)) (toUZ p))

let t_big_int_lt_p k = tarr_t_q_k tf_2n q_lt_p k

let t_big_int_add_mod_p k = tarr_t_q_k tf_2n q_add_mod_p k

let big_add_mod_p =
  Circuit
    { name= "BigAddModP"
    ; inputs=
        [ ("n", t_n')
        ; ("k", tpos)
        ; ("a", t_big_int_lt_p k)
        ; ("b", t_big_int_lt_p k)
        ; ("p", t_big_int k) ]
    ; outputs= [("out", t_big_int_add_mod_p k)]
    ; dep= None
    ; body=
        (* add = #BigAdd n k a b *)
        elet "add"
          (call "BigAdd" [n; k; a; b])
          (* lt = #BigLessThan n (k + 1) add (p ++ [0]) *)
          (elet "lt"
             (call "BigLessThan" [n; zadd1 k; add; concat p (cons f0 cnil)])
             (* p' = map (\p_i => (1 - lt) * p_i) (p ++ [0]) *)
             (elet "p'"
                (map
                   (lama "x" tf (fmul (fsub f1 lt) x))
                   (concat p (cons f0 cnil)) )
                (* sub = #BigSub n (k + 1) add p' *)
                (elet "sub"
                   (call "BigSub" [n; zadd1 k; add; p'])
                   (* sub[k] === 0 *)
                   (elet "u0"
                      (assert_eq (get sub k) f0)
                      (* out === take k sub *)
                      (assert_eq out (take k sub)) ) ) ) ) }
