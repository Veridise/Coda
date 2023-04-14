open Core
open Typecheck
open Coqgen
open Circomlib
module U = Test_utils.Utils

let _ = U.test Gates.cnot []

let _ = U.test Gates.cxor []

let _ = U.test Gates.cand []

let _ = U.test Gates.cnand []

let _ = U.test Gates.cor []

let _ = U.test Gates.cnor []

let _ = U.test Comparators.is_zero []

let _ = U.test Comparators.is_equal [Comparators.is_zero]

let _ = U.test Comparators.less_than [Gates.cnot; Bitify.num2bits]

let _ =
  U.test Comparators.greater_than
    [Comparators.less_than; Bitify.num2bits; Gates.cnot]

let _ =
  U.test Comparators.leq [Comparators.less_than; Bitify.num2bits; Gates.cnot]

let _ =
  U.test Comparators.geq
    (Comparators.[leq; less_than] @ Bitify.[num2bits] @ Gates.[cnot])

let _ = U.test Bitify.num2bits []

let _ = U.test Bitify.bits2num []

let _ = U.test Mux1.multi_mux_1 []

(* let _ = U.test Multiplexer.escalar_product [] *)
