(** * DSL benchmark: Semaphore *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition Poseidon (nInputs : nat) (inputs : list F) : F := 0.

#[global]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[global]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[global]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[global]Hint Extern 10 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[global]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[global]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[global]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[global]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[global]Hint Extern 10 (_ < _) => lia: core.
#[global]Hint Extern 10 (_ < _)%nat => lia: core.
#[global]Hint Extern 10 (_ <= _) => lia: core.
#[global]Hint Extern 10 (_ <= _)%nat => lia: core.
#[global]Hint Extern 10 (_ > _) => lia: core.
#[global]Hint Extern 10 (_ > _)%nat => lia: core.
#[global]Hint Extern 10 (_ >= _) => lia: core.
#[global]Hint Extern 10 (_ >= _)%nat => lia: core.
#[global]Hint Extern 10 (S _ = S _) => f_equal: core.

(** ** CalculateSecret *)

(* print_endline (generate_lemmas calc_secret (typecheck_circuit (add_to_delta d_empty poseidon) calc_secret));; *)

Lemma CalculateSecret_obligation0: forall (identityNullifier : F) (identityTrapdoor : F) (v : Z), True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateSecret_obligation1: forall (identityNullifier : F) (identityTrapdoor : F) (v : (list F)), True -> True -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = identityNullifier)) /\ ((v!1%nat) = identityTrapdoor)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma CalculateSecret_obligation2_trivial: forall (identityNullifier : F) (identityTrapdoor : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil))))).
Proof. hammer. Qed.

(** ** CalculateIdentityCommitment *)

(* print_endline (generate_lemmas calc_id_commit (typecheck_circuit (add_to_delta d_empty poseidon) calc_id_commit));; *)

Lemma CalculateIdentityCommitment_obligation0: forall (secret : F) (v : Z), True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateIdentityCommitment_obligation1: forall (secret : F) (v : (list F)), True -> Forall (fun x1 => True) v -> True -> (((True /\ ((v!0%nat) = secret)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma CalculateIdentityCommitment_obligation2_trivial: forall (secret : F) (v : F), True -> True -> ((v = (Poseidon 1%nat (secret :: nil))) -> (v = (Poseidon 1%nat (secret :: nil)))).
Proof. hammer. Qed.

(** ** CalculateNullifierHash *)

(* print_endline (generate_lemmas calc_null_hash (typecheck_circuit (add_to_delta d_empty poseidon) calc_null_hash));; *)

Lemma CalculateNullifierHash_obligation0: forall (externalNullifier : F) (identityNullifier : F) (v : Z), True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateNullifierHash_obligation1: forall (externalNullifier : F) (identityNullifier : F) (v : (list F)), True -> True -> Forall (fun x2 => True) v -> True -> ((((True /\ ((v!0%nat) = externalNullifier)) /\ ((v!1%nat) = identityNullifier)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma CalculateNullifierHash_obligation2_trivial: forall (externalNullifier : F) (identityNullifier : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil)))) -> (v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil))))).
Proof. hammer. Qed.

(** ** MerkleTreeInclusionProof *)

(* print_endline (generate_lemmas mrkl_tree_incl_pf (typecheck_circuit (add_to_deltas d_empty [poseidon; multi_mux_1]) mrkl_tree_incl_pf));; *)

(* TODO *)

(** ** Semaphore *)

(* print_endline (generate_lemmas semaphore (typecheck_circuit (add_to_deltas d_empty [poseidon; calc_secret; calc_id_commit; calc_null_hash; mrkl_tree_incl_pf]) semaphore));; *)

(* TODO *)
