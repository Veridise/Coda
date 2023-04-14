open Core
open Typecheck
open Coqgen
open Ed25519
module U = Test_utils.Utils

let _ = U.test fulladder []

let _ = U.test onlycarry []

let _ = U.test bin_add [fulladder]

let _ =
  U.test less_than_power Circomlib.(Bitify.[num2bits] @ Comparators.[less_than])

let _ =
  U.test less_than_bounded
    Circomlib.(Bitify.[num2bits] @ Comparators.[less_than] @ [less_than_power])
