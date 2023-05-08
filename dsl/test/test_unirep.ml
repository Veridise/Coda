open Core
open Typecheck
open Coqgen
open Circomlib
open Unirep.LeafHasher
open Unirep.IncrementalMerkleTree
module U = Test_utils.Utils

(* let _ = U.test epoch_key_hasher Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test epoch_tree_leaf Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test state_tree_leaf Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test identity_secret Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test identity_commitment (Circomlib.Poseidon.[poseidon] @ Unirep.LeafHasher.[identity_secret]) *)

let _ = U.test signup (Circomlib.Poseidon.[poseidon] @ Unirep.LeafHasher.[identity_secret1; identity_commitment; state_tree_leaf])

(* let _ =
   U.test mrkl_tree_incl_pf Circomlib.(Poseidon.[poseidon] @ Mux1.[multi_mux_1] @ Comparators.[is_zero]) *)
