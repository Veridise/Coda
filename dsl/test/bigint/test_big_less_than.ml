open Core
open Typecheck
open Coqgen
open Bigint
open Big_less_than
module U = Test_utils.Utils

let _ =
  U.test big_lt Circomlib.(Comparators.[less_than; is_equal] @ Gates.[cand; cor])
