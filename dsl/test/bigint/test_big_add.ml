open Core
open Typecheck
open Coqgen
open Bigint
module U = Test_utils.Utils

let _ = U.test Big_add.mod_sum_three [Circomlib.Bitify.num2bits]
