open Core
open Typecheck
open Coqgen
open Ed25519_buggy
module U = Test_utils.Utils

(* let _ = U.test fulladder [] *)

(* let _ = U.test onlycarry [] *)

(* let _ = U.test bin_add [fulladder] *)

(* let _ = U.test less_than_power [] *)

let _ = U.test less_than_bounded [less_than_power]
