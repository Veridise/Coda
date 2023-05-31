open Core
open Typecheck
open Coqgen
open Zk_sql
module U = Test_utils.Utils

let _ = U.test calc_total []

let _ = U.test sum_equals Circomlib.(Comparators.[is_equal] @ [calc_total])

let _ = U.test is_not_zero Circomlib.(Comparators.[is_zero] @ Gates.[cnot])

let _ = U.test is_filtered Circomlib.(Comparators.[is_equal] @ [calc_total])

let _ = U.test is_equal_word Circomlib.(Comparators.[is_equal] @ [multisum])
