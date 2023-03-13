open Codegen
open Circomlib.Gates
open Circomlib.Comparators

let _ = codegen [] cnot

let _ = codegen [] cxor

let _ = codegen [] cand

let _ = codegen [] cnand

let _ = codegen [] cor

let _ = codegen [] cxor

let _ = codegen [] c_is_zero

let _ = codegen (add_to_delta [] c_is_zero) c_is_equal

(* TODO: *)

(* #use "circuits/bitify.ml"
   let _ = (codegen [] num2bits);; *)

(* #use "circuits/trivial.ml"
   let _ = codegen_c_dep_caller;; *)

(* #use "circuits/biglessthan.ml"
   let _ = (codegen [] c_big_lt);; *)
