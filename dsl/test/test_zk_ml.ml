open Core
open Typecheck
open Coqgen
open Zk_ml

module U = Test_utils.Utils

let _ = U.test is_negative [sign; Circomlib.Comparators.is_zero]
let _ = U.test is_positive [sign; Circomlib.Comparators.is_zero]
let _ = U.test relu [is_positive]
let _ = U.test poly []