open Core
open Zk_ml
module U = Test_utils.Utils

let _ = U.test is_negative Circomlib.(Bitify.[num2bits] @ Sign.[c_sign])

let _ =
  U.test is_positive
    Circomlib.(Bitify.[num2bits] @ Sign.[c_sign] @ Comparators.[is_zero])

let _ = U.test relu [is_positive]

let _ = U.test poly []

let _ = U.test cmax Circomlib.[Comparators.greater_than; Switcher.switcher]

let _ = U.test flatten_2d []
