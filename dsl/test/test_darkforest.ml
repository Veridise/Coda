open Core
open Typecheck
open Coqgen
open Darkforest
module U = Test_utils.Utils

let _ = U.test calc_total []

let _ =
  U.test quin_selector
    (Circomlib.(Comparators.[is_equal; less_than]) @ [calc_total])

let _ = U.test is_neg Circomlib.(Bitify.[num2bits] @ Sign.[c_sign])

let _ = U.test random Circomlib.(Bitify.[num2bits] @ Mimcsponge.[mimc_sponge])

let _ =
  U.test range_proof Circomlib.(Bitify.[num2bits] @ Comparators.[less_than])

let _ =
  U.test multi_range_proof
    Circomlib.(Bitify.[num2bits] @ Comparators.[less_than] @ [range_proof])
