open Core
open Typecheck
open Coqgen
open Zk_sbt

module U = Test_utils.Utils

let _ = U.test c_in Circomlib.Comparators.([greater_than; is_equal])