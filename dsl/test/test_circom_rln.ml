open Core
open Typecheck
open Coqgen
open Circomlib
open Circom_rln.Utils
open Circom_rln.Withdraw
module U = Test_utils.Utils

(* let _ =
     U.test mrkl_tree_incl_pf Circomlib.(Poseidon.[poseidon] @ Mux1.[multi_mux_1])

   let _ =
     U.test range_check Circomlib.(Comparators.[less_than] @ Bitify.[num2bits]) *)

(* let _ = U.test withdraw Circomlib.(Poseidon.[poseidon]) *)

(* let _ = U.test Circom_rln.Rln_diff.rln (Circomlib.(Poseidon.[poseidon])@ [mrkl_tree_incl_pf; range_check]) *)

let _ =
  U.test Circom_rln.Rln_same.rln
    (Circomlib.(Poseidon.[poseidon]) @ [mrkl_tree_incl_pf; range_check])
