open Core
open Typecheck
open Coqgen
open Bigint
open Split
open Circomlib.Bitify
module U = Test_utils.Utils

(* let _ = U.test split [num2bits] *)
let _ = U.test split_three [num2bits]
