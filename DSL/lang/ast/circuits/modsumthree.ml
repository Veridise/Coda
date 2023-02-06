(** Benchmarks ModSumThree and BigAdd *)

open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let n = v "n"
let k = v "k"
let a = v "a"
let b = v "b"
let c = v "c"
let s = v "s"

let n2b = v "n2b"
let sum = v "sum"
let carry = v "carry"
let abs = v "abs"
let out = v "out"
let ms3_i = v "ms3_i"

let pstr x = PStr x
let pprod xs = PProd xs

let t_n = z_range 1 (zsub1 CPLen)
let t_arr_tf k = tarr tf QTrue k

let mod_sum_three =
  Circuit {
      name = "ModSumThree";
      inputs = [("n", t_n); ("a", tf); ("b", tf); ("c", tf)];
      outputs = [("sum", tf), ("carry", tf)];
      dep = qeq (fadd sum (fmul carry (fpow f2 n))) (fadd (fadd a b) c);
      body = [
          (* n2b = #Num2Bits (n + 2) (a + b + c) *)
          slet "n2b" (call "Num2Bits" [zadd n z2; fadd (fadd a b) c]);
          (* carry === n2b[n] + 2 * n2b[n + 1] *)
          assert_eq carry (fadd (get n2b n) (fmul f2 (get n2b (zadd n z1))));
          (* sum === a + b + c - carry * 2^n *)
          assert_eq sum (fsub (fadd (fadd a b) c) (fmul carry (fpow f2 n)))
        ]
    }

let deltas_ms3 = add_to_delta d_empty num2bits

let check_mod_sum_three = typecheck_circuit deltas_ms3 mod_sum_three

(* \_ (s, c) (a, b) => let (si, ci) = #ModSumThree n a b c in (s ++ [si], ci) *)
let lam_big_add =
  lamp
    (pprod [pstr "_"; pprod [pstr s; pstr c]; pprod [pstr a; pstr b]])
    (elet ms3_i (call "ModSumThree" [n; a; b; c]) (tmake [concat s (cons (tget ms3_i 0) cnil); tget ms3_i 1]))

let inv_big_add _ _ = tf

let iter_big_add = iter z0 k lam_big_add (tmake [cnil; f0]) inv_big_add

let big_add =
  Circuit {
      name = "BigAdd";
      inputs = [("n", t_n); ("k", tpos);
                ("a", t_arr_tf k); ("b", t_arr_tf k)];
      outputs = [("out", t_arr_tf (zadd k z1))];
      dep = None;
      body = [
          (* abs = zip a b *)
          slet "abs" (zip a b);
          (* (sum, carry) = iter 0 k lam_big_add inv_big_add abs*)
          sletp (pprod [pstr sum; pstr carry]) (app iter_big_add abs);
          (* out === sum ++ [carry] *)
          assert_eq out (concat sum (cons carry cnil))
        ]
    }

let deltas_ba = add_to_delta deltas_ms3 mod_sum_three

let check_big_add = typecheck_circuit deltas_ba big_add
