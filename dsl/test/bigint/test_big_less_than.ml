open Core
open Bigint
open Big_less_than
open Big_less_than_ex
module U = Test_utils.Utils

let _ =
  U.test big_lt Circomlib.(Comparators.[less_than; is_equal] @ Gates.[cand; cor])

let _ =
  U.test big_lt_ex
    Circomlib.(Comparators.[less_than; is_equal] @ Gates.[cand; cor])
