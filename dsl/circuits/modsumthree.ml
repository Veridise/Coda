(** Benchmarks ModSumThree and BigAdd *)

open Ast
open Dsl
open Typecheck

let n = v "n"

let k = v "k"

let a = v "a"

let b = v "b"

let c = v "c"

let s = v "s"

let x = v "x"

let n2b = v "n2b"

let sum = v "sum"

let carry = v "carry"

let abs = v "abs"

let out = v "out"

let ms3_i = v "ms3_i"

let ts = tget (tget x 1) 0

let tc = tget (tget x 1) 1

let ta = tget (tget x 2) 0

let tb = tget (tget x 2) 1

let ms3_is = tget ms3_i 0

let ms3_ic = tget ms3_i 1

let tsum = tget x 0

let tcarry = tget x 1

let pstr x = PStr x

let pprod xs = PProd xs

let t_n = z_range z1 (zsub1 CPLen)

let t_arr_tf k = tarr tf QTrue k

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let mod_sum_three =
  Circuit
    { name= "ModSumThree"
    ; inputs= [("n", t_n); ("a", tf_2n); ("b", tf_2n); ("c", tf_binary)]
    ; outputs= [("sum", tf_2n); ("carry", tf_binary)]
    ; dep= Some (qeq (fadd sum (fmul carry (fpow f2 n))) (fadd (fadd a b) c))
    ; body=
        [ (* n2b = #Num2Bits (n + 2) (a + b + c) *)
          slet "n2b" (call "Num2Bits" [zadd n z2; fadd (fadd a b) c])
        ; (* carry === n2b[n] + 2 * n2b[n + 1] *)
          assert_eq carry (fadd (get n2b n) (fmul f2 (get n2b (zadd n z1))))
        ; (* sum === a + b + c - carry * 2^n *)
          assert_eq sum (fsub (fadd (fadd a b) c) (fmul carry (fpow f2 n))) ] }

let deltas_ms3 = add_to_delta d_empty num2bits

let check_mod_sum_three = typecheck_circuit deltas_ms3 mod_sum_three

let t_x = ttuple [tnat; ttuple [tf; tf]; ttuple [tf; tf]]

(* Proper big Ints of length k *)
let t_big_int k = tarr tf_2n QTrue k

(* \_ (s, c) (a, b) => let (si, ci) = #ModSumThree n a b c in (s ++ [si], ci) *)
let lam_big_add =
  lama "x" t_x
    (elet "ms3_i"
       (call "ModSumThree" [n; ta; tb; tc])
       (tmake [concat ts (cons ms3_is cnil); ms3_ic]) )

let inv_big_add _ _ = tf

let iter_big_add = iter z0 k lam_big_add (tmake [cnil; f0]) inv_big_add

let big_add =
  Circuit
    { name= "BigAdd"
    ; inputs= [("n", t_n); ("k", tpos); ("a", t_big_int k); ("b", t_big_int k)]
    ; outputs= [("out", t_big_int (zadd k z1))]
    ; dep= None
    ; body=
        [ (* abs = zip a b *)
          slet "abs" (zip a b)
        ; (* (sum, carry) = iter 0 k lam_big_add inv_big_add abs *)
          slet "x" (app iter_big_add abs)
        ; (* out === sum ++ [carry] *)
          assert_eq out (concat tsum (cons tcarry cnil)) ] }

let deltas_ba = add_to_delta deltas_ms3 mod_sum_three

let check_big_add = typecheck_circuit deltas_ba big_add
