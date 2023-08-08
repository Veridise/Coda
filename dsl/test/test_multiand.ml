open Core
open Typecheck
open Coqgen

(* open Circomlib.Gates *)
open Circomlib.Multiand
module U = Test_utils.Utils

let _ =
  print_string
    "==== BEGIN test_multiand \
     ========================================================\n"

let _ = U.test circuit_MultiAND []

let _ =
  print_string
    "==== END test_multiand \
     ========================================================\n"
