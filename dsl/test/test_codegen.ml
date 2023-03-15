open Codegen
open Circomlib.Gates
open Circomlib.Comparators
open Circomlib.Bitify

let _ = codegen [] [] cnot

let _ = codegen [] [] cxor

let _ = codegen [] [] cand

let _ = codegen [] [] cnand

let _ = codegen [] [] cor

let _ = codegen [] [] cxor

let _ = codegen [] [] c_is_zero

let _ = codegen (add_to_delta [] c_is_zero) [] c_is_equal

(* TODO: *)

let _ = codegen [] [] c_num2bits
