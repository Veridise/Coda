(** Benchmark ModSumThree *)

open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let n = v "n"
let a = v "a"
let b = v "b"
let c = v "c"

let n2b = v "n2b"
let sum = v "sum"
let carry = v "carry"

let t_n = z_range 1 (zsub1 CPLen)

let mod_sum_three =
  Circuit {
      name = "ModSumThree";
      inputs = [("n", t_n); ("a", tf); ("b", tf); ("c", tf)];
      outputs = [("sum", tf), ("carry", tf)];
      dep = qeq (fadd sum (fmul carry (fpow f2 n))) (fadd (fadd a b) c);
      body = [
          (* n2b = #Num2Bits (n + 2) (a + b + c) *)
          slet "n2b" (call "Num2Bits" [zadd n z2; fadd (fadd a b) c]);
          (* carry = n2b[n] + 2 * n2b[n + 1] *)
          assert_eq carry (fadd (get n2b n) (fmul f2 (get n2b (fadd n f1))));
          (* sum = a + b + c - carry * 2^n *)
          assert_eq sum (fsub (fadd (fadd a b) c) (fmul carry (fpow f2 n)))
        ]
    }

let deltas = add_to_delta d_empty num2bits

let check_mod_sum_three = typecheck_circuit deltas mod_sum_three
