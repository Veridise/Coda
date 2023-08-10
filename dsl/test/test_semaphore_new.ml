open Core
open Typecheck
open Coqgen
open Semaphore_new
module U = Test_utils.Utils

(* let _ = U.test calc_secret Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test calc_id_commit Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test calc_null_hash Circomlib.Poseidon.[poseidon] *)

(* let _ =
   U.test mrkl_tree_incl_pf Circomlib.(Poseidon.[poseidon] @ Mux1.[multi_mux_1]) *)

let _ =
  U.test circuit_Semaphore
    [ circuit_CalculateSecret
    ; circuit_CalculateIdentityCommitment
    ; circuit_CalculateNullifierHash
    ; circuit_MerkleTreeInclusionProof ]
