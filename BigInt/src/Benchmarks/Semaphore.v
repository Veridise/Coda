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

(* Note: This is a placeholder implementation that lets us prove many
trivial and even some nontrivial MerkleTreeInclusionProof obligations *)
Definition MrklTreeInclPfHash (xs : list (F * F)) (init : F) := init.

Definition zip {A B} (xs : list A) (ys : list B) := combine xs ys.

(** ** CalculateSecret *)

Lemma CalculateSecret_obligation0: forall (identityNullifier : F) (identityTrapdoor : F) (v : Z), True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateSecret_obligation1: forall (identityNullifier : F) (identityTrapdoor : F) (v : (list F)), True -> True -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = identityNullifier)) /\ ((v!1%nat) = identityTrapdoor)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma CalculateSecret_obligation2: forall (identityNullifier : F) (identityTrapdoor : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil))))).
Proof. hammer. Qed.

(** ** CalculateIdentityCommitment *)

Lemma CalculateIdentityCommitment_obligation0: forall (secret : F) (v : Z), True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateIdentityCommitment_obligation1: forall (secret : F) (v : (list F)), True -> Forall (fun x0 => True) v -> True -> (((True /\ ((v!0%nat) = secret)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma CalculateIdentityCommitment_obligation2: forall (secret : F) (v : F), True -> True -> ((v = (Poseidon 1%nat (secret :: nil))) -> (v = (Poseidon 1%nat (secret :: nil)))).
Proof. hammer. Qed.

(** ** CalculateNullifierHash *)

Lemma CalculateNullifierHash_obligation0: forall (externalNullifier : F) (identityNullifier : F) (v : Z), True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma CalculateNullifierHash_obligation1: forall (externalNullifier : F) (identityNullifier : F) (v : (list F)), True -> True -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = externalNullifier)) /\ ((v!1%nat) = identityNullifier)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma CalculateNullifierHash_obligation2: forall (externalNullifier : F) (identityNullifier : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil)))) -> (v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil))))).
Proof. hammer. Qed.

(** ** MerkleTreeInclusionProof *)

Lemma MerkleTreeInclusionProof_obligation0_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x0 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x1 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation1_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x5 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x6 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> (((0%nat <= v) /\ (v = nLevels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation2_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x10 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x11 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> (((0%nat <= v) /\ (v < nLevels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation3_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (v : F), True -> Forall (fun x15 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x16 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> True -> ((v = (MrklTreeInclPfHash (take i z) leaf)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation4_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (v : F), True -> Forall (fun x20 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x21 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> True -> ((v = j) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation5_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (v : F), True -> Forall (fun x25 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x26 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation6_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (v : F), True -> Forall (fun x30 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x31 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> True -> ((v = j) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation7_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (v : F), True -> Forall (fun x35 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x36 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x39 => match x39 with (x37,x38) => True end) z -> Forall (fun x39 => match x39 with (x37,x38) => True end) z -> Forall (fun x39 => match x39 with (x37,x38) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> True -> ((v = (1%F - j)%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation8: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (v : Z), True -> Forall (fun x40 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x41 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x46 => Forall (fun x45 => True) x46) c -> Forall (fun x46 => ((length x46) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation9: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (v : (list (list F))), True -> Forall (fun x47 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x48 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x51 => match x51 with (x49,x50) => True end) z -> Forall (fun x51 => match x51 with (x49,x50) => True end) z -> Forall (fun x51 => match x51 with (x49,x50) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x53 => Forall (fun x52 => True) x53) c -> Forall (fun x53 => ((length x53) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x55 => Forall (fun x54 => True) x55) v -> Forall (fun x55 => ((length x55) = 2%nat)) v -> True -> (((((True /\ ((v!0%nat) = (x :: (s :: nil)))) /\ ((v!1%nat) = (s :: (x :: nil)))) /\ ((length v) = 2%nat)) /\ (v = c)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation10: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (v : (list F)), True -> Forall (fun x56 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x57 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x60 => match x60 with (x58,x59) => True end) z -> Forall (fun x60 => match x60 with (x58,x59) => True end) z -> Forall (fun x60 => match x60 with (x58,x59) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x62 => Forall (fun x61 => True) x62) c -> Forall (fun x62 => ((length x62) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x63 => True) v -> True -> (((length v) = 2%nat) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation11_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (v : F), True -> Forall (fun x64 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x65 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x68 => match x68 with (x66,x67) => True end) z -> Forall (fun x68 => match x68 with (x66,x67) => True end) z -> Forall (fun x68 => match x68 with (x66,x67) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x70 => Forall (fun x69 => True) x70) c -> Forall (fun x70 => ((length x70) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> True -> ((v = j) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation12: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : Z), True -> Forall (fun x71 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x72 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x77 => Forall (fun x76 => True) x77) c -> Forall (fun x77 => ((length x77) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x78 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * j)%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation13: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : (list F)), True -> Forall (fun x79 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x80 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x85 => Forall (fun x84 => True) x85) c -> Forall (fun x85 => ((length x85) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x86 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * j)%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> Forall (fun x87 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < 2%nat -> ((v!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * j)%F + ((c!i)!0%nat))%F)) /\ ((length v) = 2%nat)) /\ (v = m)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation14: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (j : F) (s : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : F), True -> Forall (fun x88 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x89 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x92 => match x92 with (x90,x91) => True end) z -> Forall (fun x92 => match x92 with (x90,x91) => True end) z -> Forall (fun x92 => match x92 with (x90,x91) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> True -> ((j * (1%F - j)%F)%F = 0%F) -> Forall (fun x94 => Forall (fun x93 => True) x94) c -> Forall (fun x94 => ((length x94) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: (s :: nil)))) /\ ((c!1%nat) = (s :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x95 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * j)%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = (Poseidon 2%nat m)) -> (v = (MrklTreeInclPfHash (take (i + 1%nat)%nat z) leaf))).
Proof. Admitted.

Lemma MerkleTreeInclusionProof_obligation15: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x96 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x97 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x100 => match x100 with (x98,x99) => True end) z -> Forall (fun x100 => match x100 with (x98,x99) => True end) z -> Forall (fun x100 => match x100 with (x98,x99) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = leaf) -> (v = (MrklTreeInclPfHash (take 0%nat z) leaf))).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation16: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x101 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x102 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x105 => match x105 with (x103,x104) => True end) z -> Forall (fun x105 => match x105 with (x103,x104) => True end) z -> Forall (fun x105 => match x105 with (x103,x104) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = (MrklTreeInclPfHash (take nLevels z) leaf)) -> (v = (MrklTreeInclPfHash (zip pathIndices siblings) leaf))).
Proof. hammer. Qed.

(** ** Semaphore *)

Lemma Semaphore_obligation0_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x0 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x1 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation1_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x2 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x3 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityTrapdoor) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation2_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (v : F), True -> True -> Forall (fun x4 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x5 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> True -> (((v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) /\ (v = secret)) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation3_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x6 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x7 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation4_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x8 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x9 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation5_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x10 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x11 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation6_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x12 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x13 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation7: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : Z), True -> True -> Forall (fun x14 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x15 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((0%nat <= v) /\ (v = nLevels)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Semaphore_obligation8_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x16 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x17 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((v = (Poseidon 1%nat (secret :: nil))) /\ (v = id_commit)) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation9: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x18 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x19 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x20 => True) v -> True -> ((((length v) = nLevels) /\ (v = treePathIndices)) -> ((length v) = nLevels)).
Proof. hammer. Qed.

Lemma Semaphore_obligation10: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x21 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x22 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x23 => True) v -> True -> ((((length v) = nLevels) /\ (v = treeSiblings)) -> ((length v) = nLevels)).
Proof. hammer. Qed.

Lemma Semaphore_obligation11: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x24 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x25 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (MrklTreeInclPfHash (zip treePathIndices treeSiblings) id_commit)) -> (v = (MerkleTreeInclusionProof nLevels (CalculateIdentityCommitment (CalculateSecret identityNullifier identityTrapdoor)) treePathIndices treeSiblings))).
Proof. Admitted.

Lemma Semaphore_obligation12_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x26 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x27 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = externalNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation13_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x28 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x29 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation14: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x30 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x31 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil)))) -> (v = (CalculateNullifierHash externalNullifier identityNullifier))).
Proof. Admitted.

Lemma Semaphore_obligation15_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit), True -> True -> Forall (fun x32 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x33 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> (True -> True).
Proof. hammer. Qed.
