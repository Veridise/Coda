(** Benchmark ModSubThree *)

open Lib__Ast
open Lib__Dsl
open Lib__Typecheck

let a = v "a"
let b = v "b"
let c = v "c"
let n = v "n"

let out = v "out"
let borrow = v "borrow"
let b_plus_c = v "b_plus_c"

(* { v : Int | 1 <= v <= C.k - 2 } *)
let t_n = z_range z1 (zsub2 CPLen)

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let c_mod_sub_three =
  Circuit {
      name = "ModSubThree";
      inputs = [("n", t_n); ("a", tf_2n); ("b", tf_2n); ("c", tf_binary)];
      outputs = [("out", tf); ("borrow", tf_binary)];
      (* out = borrow * 2 ** n + a - (b + c) *)
      dep = Some (qeq out (fsub (fadd (fmul borrow (fpow f2 n)) a) (fadd b c)));
      body = [
          (* b_plus_c = b + c *)
          slet "b_plus_c" (fadd b c);
          (* borrow === #LessThan (n + 1) a (b + c) *)
          assert_eq borrow (call "LessThan" [zadd n z1; a; b_plus_c]);
          (* out === borrow * 2 ** n + a - (b + c) *)
          assert_eq out (fsub (fadd (fmul borrow (fpow f2 n)) a) b_plus_c)
        ]
    }

let check_mod_sub_three =
  typecheck_circuit (add_to_deltas d_empty [c_less_than; num2bits]) c_mod_sub_three
