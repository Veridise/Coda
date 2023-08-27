open Core
open Typecheck
open Coqgen
open Circomlib
open Unirep_auto.UserStateTransition_auto
module U = Test_utils.Utils

let _ =
  U.test circuit_UserStateTransition
    [ circuit_StateTreeLeaf
    ; circuit_EpochKeyHasher
    ; circuit_Num2Bits
    ; circuit_MerkleTreeInclusionProof
    ; circuit_GreaterThan
    ; circuit_LessThan
    ; circuit_IsZero
    ; circuit_IsEqual ]

(* @ Circomlib.Comparators.[less_than; geq; greater_than; is_zero; is_equal]
   @ Circomlib.Gates.[cor] ) *)

(* let _ =
   [ circuit_StateTreeLeaf (* state_tree_leaf *)
   ; circuit_EpochKeyHasher (* epoch_key_hasher *) ]
   (* [ circuit_IdentitySecret (* identity_secret1 *)
      ; circuit_IdentityCommitment (* identity_commitment *)
      ; circuit_StateTreeLeaf (* state_tree_leaf *)
      ; circuit_EpochKeyLite (* epoch_key_lite *)
      ; circuit_EpochKeyHasher (* epoch_key_hasher *)
      ; circuit_EpochKey (* epoch_key *)
      ; circuit_ReplFieldEqual (* repl_field_equal *) ] *)
   @ Circomlib.Bitify.[num2bits]
   @ Circomlib.Comparators.[less_than; geq; greater_than; is_zero; is_equal]
   @ Circomlib.Gates.[cor]
   @ [ circuit_MerkleTreeInclusionProof
       (* Unirep.IncrementalMerkleTree.mrkl_tree_incl_pf *) ] *)
