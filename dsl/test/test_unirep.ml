open Core
open Typecheck
open Coqgen
open Circomlib
open Unirep.LeafHasher
open Unirep.IncrementalMerkleTree
module U = Test_utils.Utils

let _ = U.test epoch_key_hasher Circomlib.Poseidon.[poseidon]

(* let _ = U.test epoch_tree_leaf Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test state_tree_leaf Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test identity_secret Circomlib.Poseidon.[poseidon] *)

(* let _ = U.test identity_commitment (Circomlib.Poseidon.[poseidon] @ Unirep.CoreCircuits.[identity_secret]) *)

(* let _ =
   U.test signup
     ( Circomlib.Poseidon.[poseidon]
     @ Unirep.CoreCircuits.[identity_secret1; identity_commitment; state_tree_leaf]
     ) *)

(* let _ = U.test epoch_key_lite (Circomlib.Poseidon.[poseidon] @ Unirep.CoreCircuits.[identity_secret1; identity_commitment; state_tree_leaf] @ Circomlib.Bitify.[num2bits]
   @ Circomlib.Comparators.[less_than] @ Unirep.CoreCircuits.[epoch_key_hasher]) *)

(* let _ =
   U.test epoch_key
     ( Circomlib.Poseidon.[poseidon]
     @ Unirep.CoreCircuits.
         [identity_secret1; identity_commitment; state_tree_leaf; epoch_key_lite; epoch_key_hasher]
     @ Circomlib.Bitify.[num2bits]
     @ Circomlib.Comparators.[less_than]
     @ Unirep.IncrementalMerkleTree.[mrkl_tree_incl_pf] ) *)

(* let _ =
   U.test prevent_double_action
     ( Circomlib.Poseidon.[poseidon]
     @ Unirep.CoreCircuits.
         [ identity_secret1
         ; identity_commitment
         ; state_tree_leaf
         ; epoch_key_lite
         ; epoch_key_hasher ]
     @ Circomlib.Bitify.[num2bits]
     @ Circomlib.Comparators.[less_than]
     @ Unirep.IncrementalMerkleTree.[mrkl_tree_incl_pf] ) *)

(* let _ =
   U.test prove_reputation
     ( Circomlib.Poseidon.[poseidon]
     @ Unirep.CoreCircuits.
         [ identity_secret1
         ; identity_commitment
         ; state_tree_leaf
         ; epoch_key_lite
         ; epoch_key_hasher
         ; epoch_key
         ; repl_field_equal ]
     @ Circomlib.Bitify.[num2bits]
     @ Circomlib.Comparators.[less_than; geq; is_zero; is_equal]
     @ Circomlib.Gates.[cor]
     @ Unirep.IncrementalMerkleTree.[mrkl_tree_incl_pf] ) *)

(* let _ =
   U.test user_state_transition
     ( Circomlib.Poseidon.[poseidon]
     @ Unirep.CoreCircuits.
         [ identity_secret1
         ; identity_commitment
         ; state_tree_leaf
         ; epoch_key_lite
         ; epoch_key_hasher
         ; epoch_key
         ; repl_field_equal ]
     @ Circomlib.Bitify.[num2bits]
     @ Circomlib.Comparators.[less_than; geq; greater_than; is_zero; is_equal]
     @ Circomlib.Gates.[cor]
     @ Unirep.IncrementalMerkleTree.[mrkl_tree_incl_pf] ) *)

(* let _ =
   U.test upper_less_than
     ( Circomlib.Bitify.[bits2num; num2bits]
     @ Circomlib.Comparators.[less_than]
     @ Unirep.CoreCircuits.[alias_check] ) *)

(* let _ =
   U.test repl_field_equal
     ( Circomlib.Bitify.[bits2num; num2bits]
     @ Circomlib.Comparators.[is_equal]
     @ Unirep.CoreCircuits.[alias_check] ) *)

(* let _ =
   U.test mrkl_tree_incl_pf Circomlib.(Poseidon.[poseidon] @ Mux1.[multi_mux_1] @ Comparators.[is_zero]) *)