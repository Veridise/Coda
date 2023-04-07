open Core
open Typecheck
open Coqgen
open Bigint
module U = Test_utils.Utils

let _ = U.test Big_sub.mod_sub_three [Circomlib.Comparators.less_than]
