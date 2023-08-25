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

Local Coercion N.of_nat : nat >->
  N.
Local Coercion Z.of_nat : nat >->
  Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition Poseidon (nInputs : nat)
  (inputs : list F) : F. Admitted.

Axiom Poseidon_2 : forall inputs : list F,
  length inputs = 2%nat ->
  Poseidon 2%nat inputs = Poseidon 2%nat ((inputs!0%nat)::(inputs!1%nat)::nil).

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

Definition zip {A B} (xs : list A)
  (ys : list B) := combine xs ys.

(* Note: This is a placeholder implementation that lets us prove many
trivial and even some nontrivial MerkleTreeInclusionProof obligations *)
Definition MrklTreeInclPfHash (xs : list (F * F))
  (init : F) := 
  fold_left (fun (y:F)
  (x:(F*F)) => if dec (fst x = 0%F) then (Poseidon 2%nat (y :: (snd x) :: nil)) else (Poseidon 2%nat ((snd x):: y :: nil))) 
                        xs init.

Definition CalculateIdentityCommitment a := Poseidon 1%nat (a :: nil).

Definition CalculateSecret a b := Poseidon 2%nat (a :: (b :: nil)).

Definition CalculateNullifierHash a b := Poseidon 2%nat (a :: (b :: nil)).

Definition MerkleTreeInclusionProof i a b := MrklTreeInclPfHash (zip a b) i.

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

Print F.

(* Source: https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/tree.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom *)

Module Semaphore_new.


Lemma Semaphore_obligation48: forall (signalHash : F) (externalNullifier : F) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices_i0 : F) (treePathIndices_i1 : F) (treePathIndices_i2 : F) (treePathIndices_i3 : F) (treePathIndices_i4 : F) (treePathIndices_i5 : F) (treePathIndices_i6 : F) (treePathIndices_i7 : F) (treePathIndices_i8 : F) (treePathIndices_i9 : F) (treePathIndices_i10 : F) (treePathIndices_i11 : F) (treePathIndices_i12 : F) (treePathIndices_i13 : F) (treePathIndices_i14 : F) (treePathIndices_i15 : F) (treePathIndices_i16 : F) (treePathIndices_i17 : F) (treePathIndices_i18 : F) (treePathIndices_i19 : F) (treeSiblings_i0 : F) (treeSiblings_i1 : F) (treeSiblings_i2 : F) (treeSiblings_i3 : F) (treeSiblings_i4 : F) (treeSiblings_i5 : F) (treeSiblings_i6 : F) (treeSiblings_i7 : F) (treeSiblings_i8 : F) (treeSiblings_i9 : F) (treeSiblings_i10 : F) (treeSiblings_i11 : F) (treeSiblings_i12 : F) (treeSiblings_i13 : F) (treeSiblings_i14 : F) (treeSiblings_i15 : F) (treeSiblings_i16 : F) (treeSiblings_i17 : F) (treeSiblings_i18 : F) (treeSiblings_i19 : F) (var0_v1 : Z) (calculateSecret_dot_identityNullifier : F) (calculateSecret_dot_identityTrapdoor : F) (calculateSecret_result : F) (calculateSecret_dot_out : F) (secret : F) (calculateIdentityCommitment_dot_secret : F) (calculateIdentityCommitment_result : F) (calculateIdentityCommitment_dot_out : F) (calculateNullifierHash_dot_externalNullifier : F) (calculateNullifierHash_dot_identityNullifier : F) (calculateNullifierHash_result : F) (calculateNullifierHash_dot_out : F) (inclusionProof_dot_leaf : F) (var1_v1 : F) (inclusionProof_dot_siblings_i0 : F) (inclusionProof_dot_pathIndices_i0 : F) (var1_v2 : F) (inclusionProof_dot_siblings_i1 : F) (inclusionProof_dot_pathIndices_i1 : F) (var1_v3 : F) (inclusionProof_dot_siblings_i2 : F) (inclusionProof_dot_pathIndices_i2 : F) (var1_v4 : F) (inclusionProof_dot_siblings_i3 : F) (inclusionProof_dot_pathIndices_i3 : F) (var1_v5 : F) (inclusionProof_dot_siblings_i4 : F) (inclusionProof_dot_pathIndices_i4 : F) (var1_v6 : F) (inclusionProof_dot_siblings_i5 : F) (inclusionProof_dot_pathIndices_i5 : F) (var1_v7 : F) (inclusionProof_dot_siblings_i6 : F) (inclusionProof_dot_pathIndices_i6 : F) (var1_v8 : F) (inclusionProof_dot_siblings_i7 : F) (inclusionProof_dot_pathIndices_i7 : F) (var1_v9 : F) (inclusionProof_dot_siblings_i8 : F) (inclusionProof_dot_pathIndices_i8 : F) (var1_v10 : F) (inclusionProof_dot_siblings_i9 : F) (inclusionProof_dot_pathIndices_i9 : F) (var1_v11 : F) (inclusionProof_dot_siblings_i10 : F) (inclusionProof_dot_pathIndices_i10 : F) (var1_v12 : F) (inclusionProof_dot_siblings_i11 : F) (inclusionProof_dot_pathIndices_i11 : F) (var1_v13 : F) (inclusionProof_dot_siblings_i12 : F) (inclusionProof_dot_pathIndices_i12 : F) (var1_v14 : F) (inclusionProof_dot_siblings_i13 : F) (inclusionProof_dot_pathIndices_i13 : F) (var1_v15 : F) (inclusionProof_dot_siblings_i14 : F) (inclusionProof_dot_pathIndices_i14 : F) (var1_v16 : F) (inclusionProof_dot_siblings_i15 : F) (inclusionProof_dot_pathIndices_i15 : F) (var1_v17 : F) (inclusionProof_dot_siblings_i16 : F) (inclusionProof_dot_pathIndices_i16 : F) (var1_v18 : F) (inclusionProof_dot_siblings_i17 : F) (inclusionProof_dot_pathIndices_i17 : F) (var1_v19 : F) (inclusionProof_dot_siblings_i18 : F) (inclusionProof_dot_pathIndices_i18 : F) (var1_v20 : F) (inclusionProof_dot_siblings_i19 : F) (inclusionProof_dot_pathIndices_i19 : F) (inclusionProof_result : F) (inclusionProof_dot_root : F) (var1_v21 : F) (root : F) (signalHashSquared : F) (nullifierHash : F) (v : F), 
  (calculateSecret_dot_identityNullifier = identityNullifier) ->
  (calculateSecret_dot_identityTrapdoor = identityTrapdoor) ->
  (calculateSecret_result = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) ->
  ((calculateSecret_dot_out = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (calculateSecret_dot_out = calculateSecret_result)) ->
  (((secret = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (secret = calculateSecret_result)) /\ (secret = calculateSecret_dot_out)) ->
  ((((calculateIdentityCommitment_dot_secret = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (calculateIdentityCommitment_dot_secret = calculateSecret_result)) /\ (calculateIdentityCommitment_dot_secret = calculateSecret_dot_out)) /\ (calculateIdentityCommitment_dot_secret = secret)) ->
  (calculateIdentityCommitment_result = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) ->
  ((calculateIdentityCommitment_dot_out = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) /\ (calculateIdentityCommitment_dot_out = calculateIdentityCommitment_result)) ->
  (calculateNullifierHash_dot_externalNullifier = externalNullifier) ->
  (calculateNullifierHash_dot_identityNullifier = identityNullifier) ->
  (calculateNullifierHash_result = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) ->
  ((calculateNullifierHash_dot_out = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) /\ (calculateNullifierHash_dot_out = calculateNullifierHash_result)) ->
  (((inclusionProof_dot_leaf = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) /\ (inclusionProof_dot_leaf = calculateIdentityCommitment_result)) /\ (inclusionProof_dot_leaf = calculateIdentityCommitment_dot_out)) ->
  (inclusionProof_dot_siblings_i0 = treeSiblings_i0) ->
  (inclusionProof_dot_pathIndices_i0 = treePathIndices_i0) ->
  (inclusionProof_dot_siblings_i1 = treeSiblings_i1) ->
  (inclusionProof_dot_pathIndices_i1 = treePathIndices_i1) ->
  (inclusionProof_dot_siblings_i2 = treeSiblings_i2) ->
  (inclusionProof_dot_pathIndices_i2 = treePathIndices_i2) ->
  (inclusionProof_dot_siblings_i3 = treeSiblings_i3) ->
  (inclusionProof_dot_pathIndices_i3 = treePathIndices_i3) ->
  (inclusionProof_dot_siblings_i4 = treeSiblings_i4) ->
  (inclusionProof_dot_pathIndices_i4 = treePathIndices_i4) ->
  (inclusionProof_dot_siblings_i5 = treeSiblings_i5) ->
  (inclusionProof_dot_pathIndices_i5 = treePathIndices_i5) ->
  (inclusionProof_dot_siblings_i6 = treeSiblings_i6) ->
  (inclusionProof_dot_pathIndices_i6 = treePathIndices_i6) ->
  (inclusionProof_dot_siblings_i7 = treeSiblings_i7) ->
  (inclusionProof_dot_pathIndices_i7 = treePathIndices_i7) ->
  (inclusionProof_dot_siblings_i8 = treeSiblings_i8) ->
  (inclusionProof_dot_pathIndices_i8 = treePathIndices_i8) ->
  (inclusionProof_dot_siblings_i9 = treeSiblings_i9) ->
  (inclusionProof_dot_pathIndices_i9 = treePathIndices_i9) ->
  (inclusionProof_dot_siblings_i10 = treeSiblings_i10) ->
  (inclusionProof_dot_pathIndices_i10 = treePathIndices_i10) ->
  (inclusionProof_dot_siblings_i11 = treeSiblings_i11) ->
  (inclusionProof_dot_pathIndices_i11 = treePathIndices_i11) ->
  (inclusionProof_dot_siblings_i12 = treeSiblings_i12) ->
  (inclusionProof_dot_pathIndices_i12 = treePathIndices_i12) ->
  (inclusionProof_dot_siblings_i13 = treeSiblings_i13) ->
  (inclusionProof_dot_pathIndices_i13 = treePathIndices_i13) ->
  (inclusionProof_dot_siblings_i14 = treeSiblings_i14) ->
  (inclusionProof_dot_pathIndices_i14 = treePathIndices_i14) ->
  (inclusionProof_dot_siblings_i15 = treeSiblings_i15) ->
  (inclusionProof_dot_pathIndices_i15 = treePathIndices_i15) ->
  (inclusionProof_dot_siblings_i16 = treeSiblings_i16) ->
  (inclusionProof_dot_pathIndices_i16 = treePathIndices_i16) ->
  (inclusionProof_dot_siblings_i17 = treeSiblings_i17) ->
  (inclusionProof_dot_pathIndices_i17 = treePathIndices_i17) ->
  (inclusionProof_dot_siblings_i18 = treeSiblings_i18) ->
  (inclusionProof_dot_pathIndices_i18 = treePathIndices_i18) ->
  (inclusionProof_dot_siblings_i19 = treeSiblings_i19) ->
  (inclusionProof_dot_pathIndices_i19 = treePathIndices_i19) ->
  (inclusionProof_result = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) ->
  ((inclusionProof_dot_root = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) /\ (inclusionProof_dot_root = inclusionProof_result)) ->
  (((root = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) /\ (root = inclusionProof_result)) /\ (root = inclusionProof_dot_root)) ->
  (signalHashSquared = (signalHash * signalHash)%F) ->
  (((nullifierHash = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) /\ (nullifierHash = calculateNullifierHash_result)) /\ (nullifierHash = calculateNullifierHash_dot_out)) ->
  (((((v = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) /\ (v = inclusionProof_result)) /\ (v = inclusionProof_dot_root)) /\ (v = root)) ->
  (v = (MerkleTreeInclusionProof (CalculateIdentityCommitment (CalculateSecret identityNullifier identityTrapdoor)) (treePathIndices_i0 :: (treePathIndices_i1 :: (treePathIndices_i2 :: (treePathIndices_i3 :: (treePathIndices_i4 :: (treePathIndices_i5 :: (treePathIndices_i6 :: (treePathIndices_i7 :: (treePathIndices_i8 :: (treePathIndices_i9 :: (treePathIndices_i10 :: (treePathIndices_i11 :: (treePathIndices_i12 :: (treePathIndices_i13 :: (treePathIndices_i14 :: (treePathIndices_i15 :: (treePathIndices_i16 :: (treePathIndices_i17 :: (treePathIndices_i18 :: (treePathIndices_i19 :: nil)))))))))))))))))))) (treeSiblings_i0 :: (treeSiblings_i1 :: (treeSiblings_i2 :: (treeSiblings_i3 :: (treeSiblings_i4 :: (treeSiblings_i5 :: (treeSiblings_i6 :: (treeSiblings_i7 :: (treeSiblings_i8 :: (treeSiblings_i9 :: (treeSiblings_i10 :: (treeSiblings_i11 :: (treeSiblings_i12 :: (treeSiblings_i13 :: (treeSiblings_i14 :: (treeSiblings_i15 :: (treeSiblings_i16 :: (treeSiblings_i17 :: (treeSiblings_i18 :: (treeSiblings_i19 :: nil))))))))))))))))))))))).
Proof. hammer. Admitted.

Lemma Semaphore_obligation49: forall (signalHash : F) (externalNullifier : F) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices_i0 : F) (treePathIndices_i1 : F) (treePathIndices_i2 : F) (treePathIndices_i3 : F) (treePathIndices_i4 : F) (treePathIndices_i5 : F) (treePathIndices_i6 : F) (treePathIndices_i7 : F) (treePathIndices_i8 : F) (treePathIndices_i9 : F) (treePathIndices_i10 : F) (treePathIndices_i11 : F) (treePathIndices_i12 : F) (treePathIndices_i13 : F) (treePathIndices_i14 : F) (treePathIndices_i15 : F) (treePathIndices_i16 : F) (treePathIndices_i17 : F) (treePathIndices_i18 : F) (treePathIndices_i19 : F) (treeSiblings_i0 : F) (treeSiblings_i1 : F) (treeSiblings_i2 : F) (treeSiblings_i3 : F) (treeSiblings_i4 : F) (treeSiblings_i5 : F) (treeSiblings_i6 : F) (treeSiblings_i7 : F) (treeSiblings_i8 : F) (treeSiblings_i9 : F) (treeSiblings_i10 : F) (treeSiblings_i11 : F) (treeSiblings_i12 : F) (treeSiblings_i13 : F) (treeSiblings_i14 : F) (treeSiblings_i15 : F) (treeSiblings_i16 : F) (treeSiblings_i17 : F) (treeSiblings_i18 : F) (treeSiblings_i19 : F) (var0_v1 : F) (calculateSecret_dot_identityNullifier : F) (calculateSecret_dot_identityTrapdoor : F) (calculateSecret_result : F) (calculateSecret_dot_out : F) (secret : F) (calculateIdentityCommitment_dot_secret : F) (calculateIdentityCommitment_result : F) (calculateIdentityCommitment_dot_out : F) (calculateNullifierHash_dot_externalNullifier : F) (calculateNullifierHash_dot_identityNullifier : F) (calculateNullifierHash_result : F) (calculateNullifierHash_dot_out : F) (inclusionProof_dot_leaf : F) (var1_v1 : F) (inclusionProof_dot_siblings_i0 : F) (inclusionProof_dot_pathIndices_i0 : F) (var1_v2 : F) (inclusionProof_dot_siblings_i1 : F) (inclusionProof_dot_pathIndices_i1 : F) (var1_v3 : F) (inclusionProof_dot_siblings_i2 : F) (inclusionProof_dot_pathIndices_i2 : F) (var1_v4 : F) (inclusionProof_dot_siblings_i3 : F) (inclusionProof_dot_pathIndices_i3 : F) (var1_v5 : F) (inclusionProof_dot_siblings_i4 : F) (inclusionProof_dot_pathIndices_i4 : F) (var1_v6 : F) (inclusionProof_dot_siblings_i5 : F) (inclusionProof_dot_pathIndices_i5 : F) (var1_v7 : F) (inclusionProof_dot_siblings_i6 : F) (inclusionProof_dot_pathIndices_i6 : F) (var1_v8 : F) (inclusionProof_dot_siblings_i7 : F) (inclusionProof_dot_pathIndices_i7 : F) (var1_v9 : F) (inclusionProof_dot_siblings_i8 : F) (inclusionProof_dot_pathIndices_i8 : F) (var1_v10 : F) (inclusionProof_dot_siblings_i9 : F) (inclusionProof_dot_pathIndices_i9 : F) (var1_v11 : F) (inclusionProof_dot_siblings_i10 : F) (inclusionProof_dot_pathIndices_i10 : F) (var1_v12 : F) (inclusionProof_dot_siblings_i11 : F) (inclusionProof_dot_pathIndices_i11 : F) (var1_v13 : F) (inclusionProof_dot_siblings_i12 : F) (inclusionProof_dot_pathIndices_i12 : F) (var1_v14 : F) (inclusionProof_dot_siblings_i13 : F) (inclusionProof_dot_pathIndices_i13 : F) (var1_v15 : F) (inclusionProof_dot_siblings_i14 : F) (inclusionProof_dot_pathIndices_i14 : F) (var1_v16 : F) (inclusionProof_dot_siblings_i15 : F) (inclusionProof_dot_pathIndices_i15 : F) (var1_v17 : F) (inclusionProof_dot_siblings_i16 : F) (inclusionProof_dot_pathIndices_i16 : F) (var1_v18 : F) (inclusionProof_dot_siblings_i17 : F) (inclusionProof_dot_pathIndices_i17 : F) (var1_v19 : F) (inclusionProof_dot_siblings_i18 : F) (inclusionProof_dot_pathIndices_i18 : F) (var1_v20 : F) (inclusionProof_dot_siblings_i19 : F) (inclusionProof_dot_pathIndices_i19 : F) (inclusionProof_result : F) (inclusionProof_dot_root : F) (var1_v21 : F) (root : F) (signalHashSquared : F) (nullifierHash : F) (v : F), (calculateSecret_dot_identityNullifier = identityNullifier) ->
  (calculateSecret_dot_identityTrapdoor = identityTrapdoor) ->
  (calculateSecret_result = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) ->
  ((calculateSecret_dot_out = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (calculateSecret_dot_out = calculateSecret_result)) ->
  (((secret = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (secret = calculateSecret_result)) /\ (secret = calculateSecret_dot_out)) ->
  ((((calculateIdentityCommitment_dot_secret = (Poseidon 2%nat (calculateSecret_dot_identityNullifier :: (calculateSecret_dot_identityTrapdoor :: nil)))) /\ (calculateIdentityCommitment_dot_secret = calculateSecret_result)) /\ (calculateIdentityCommitment_dot_secret = calculateSecret_dot_out)) /\ (calculateIdentityCommitment_dot_secret = secret)) ->
  (calculateIdentityCommitment_result = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) ->
  ((calculateIdentityCommitment_dot_out = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) /\ (calculateIdentityCommitment_dot_out = calculateIdentityCommitment_result)) ->
  (calculateNullifierHash_dot_externalNullifier = externalNullifier) ->
  (calculateNullifierHash_dot_identityNullifier = identityNullifier) ->
  (calculateNullifierHash_result = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) ->
  ((calculateNullifierHash_dot_out = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) /\ (calculateNullifierHash_dot_out = calculateNullifierHash_result)) ->
  (((inclusionProof_dot_leaf = (Poseidon 1%nat (calculateIdentityCommitment_dot_secret :: nil))) /\ (inclusionProof_dot_leaf = calculateIdentityCommitment_result)) /\ (inclusionProof_dot_leaf = calculateIdentityCommitment_dot_out)) ->
  (inclusionProof_dot_siblings_i0 = treeSiblings_i0) ->
  (inclusionProof_dot_pathIndices_i0 = treePathIndices_i0) ->
  (inclusionProof_dot_siblings_i1 = treeSiblings_i1) ->
  (inclusionProof_dot_pathIndices_i1 = treePathIndices_i1) ->
  (inclusionProof_dot_siblings_i2 = treeSiblings_i2) ->
  (inclusionProof_dot_pathIndices_i2 = treePathIndices_i2) ->
  (inclusionProof_dot_siblings_i3 = treeSiblings_i3) ->
  (inclusionProof_dot_pathIndices_i3 = treePathIndices_i3) ->
  (inclusionProof_dot_siblings_i4 = treeSiblings_i4) ->
  (inclusionProof_dot_pathIndices_i4 = treePathIndices_i4) ->
  (inclusionProof_dot_siblings_i5 = treeSiblings_i5) ->
  (inclusionProof_dot_pathIndices_i5 = treePathIndices_i5) ->
  (inclusionProof_dot_siblings_i6 = treeSiblings_i6) ->
  (inclusionProof_dot_pathIndices_i6 = treePathIndices_i6) ->
  (inclusionProof_dot_siblings_i7 = treeSiblings_i7) ->
  (inclusionProof_dot_pathIndices_i7 = treePathIndices_i7) ->
  (inclusionProof_dot_siblings_i8 = treeSiblings_i8) ->
  (inclusionProof_dot_pathIndices_i8 = treePathIndices_i8) ->
  (inclusionProof_dot_siblings_i9 = treeSiblings_i9) ->
  (inclusionProof_dot_pathIndices_i9 = treePathIndices_i9) ->
  (inclusionProof_dot_siblings_i10 = treeSiblings_i10) ->
  (inclusionProof_dot_pathIndices_i10 = treePathIndices_i10) ->
  (inclusionProof_dot_siblings_i11 = treeSiblings_i11) ->
  (inclusionProof_dot_pathIndices_i11 = treePathIndices_i11) ->
  (inclusionProof_dot_siblings_i12 = treeSiblings_i12) ->
  (inclusionProof_dot_pathIndices_i12 = treePathIndices_i12) ->
  (inclusionProof_dot_siblings_i13 = treeSiblings_i13) ->
  (inclusionProof_dot_pathIndices_i13 = treePathIndices_i13) ->
  (inclusionProof_dot_siblings_i14 = treeSiblings_i14) ->
  (inclusionProof_dot_pathIndices_i14 = treePathIndices_i14) ->
  (inclusionProof_dot_siblings_i15 = treeSiblings_i15) ->
  (inclusionProof_dot_pathIndices_i15 = treePathIndices_i15) ->
  (inclusionProof_dot_siblings_i16 = treeSiblings_i16) ->
  (inclusionProof_dot_pathIndices_i16 = treePathIndices_i16) ->
  (inclusionProof_dot_siblings_i17 = treeSiblings_i17) ->
  (inclusionProof_dot_pathIndices_i17 = treePathIndices_i17) ->
  (inclusionProof_dot_siblings_i18 = treeSiblings_i18) ->
  (inclusionProof_dot_pathIndices_i18 = treePathIndices_i18) ->
  (inclusionProof_dot_siblings_i19 = treeSiblings_i19) ->
  (inclusionProof_dot_pathIndices_i19 = treePathIndices_i19) ->
  (inclusionProof_result = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) ->
  ((inclusionProof_dot_root = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) /\ (inclusionProof_dot_root = inclusionProof_result)) ->
  (((root = (MrklTreeInclPfHash (zip (inclusionProof_dot_pathIndices_i0 :: (inclusionProof_dot_pathIndices_i1 :: (inclusionProof_dot_pathIndices_i2 :: (inclusionProof_dot_pathIndices_i3 :: (inclusionProof_dot_pathIndices_i4 :: (inclusionProof_dot_pathIndices_i5 :: (inclusionProof_dot_pathIndices_i6 :: (inclusionProof_dot_pathIndices_i7 :: (inclusionProof_dot_pathIndices_i8 :: (inclusionProof_dot_pathIndices_i9 :: (inclusionProof_dot_pathIndices_i10 :: (inclusionProof_dot_pathIndices_i11 :: (inclusionProof_dot_pathIndices_i12 :: (inclusionProof_dot_pathIndices_i13 :: (inclusionProof_dot_pathIndices_i14 :: (inclusionProof_dot_pathIndices_i15 :: (inclusionProof_dot_pathIndices_i16 :: (inclusionProof_dot_pathIndices_i17 :: (inclusionProof_dot_pathIndices_i18 :: (inclusionProof_dot_pathIndices_i19 :: nil)))))))))))))))))))) (inclusionProof_dot_siblings_i0 :: (inclusionProof_dot_siblings_i1 :: (inclusionProof_dot_siblings_i2 :: (inclusionProof_dot_siblings_i3 :: (inclusionProof_dot_siblings_i4 :: (inclusionProof_dot_siblings_i5 :: (inclusionProof_dot_siblings_i6 :: (inclusionProof_dot_siblings_i7 :: (inclusionProof_dot_siblings_i8 :: (inclusionProof_dot_siblings_i9 :: (inclusionProof_dot_siblings_i10 :: (inclusionProof_dot_siblings_i11 :: (inclusionProof_dot_siblings_i12 :: (inclusionProof_dot_siblings_i13 :: (inclusionProof_dot_siblings_i14 :: (inclusionProof_dot_siblings_i15 :: (inclusionProof_dot_siblings_i16 :: (inclusionProof_dot_siblings_i17 :: (inclusionProof_dot_siblings_i18 :: (inclusionProof_dot_siblings_i19 :: nil))))))))))))))))))))) inclusionProof_dot_leaf)) /\ (root = inclusionProof_result)) /\ (root = inclusionProof_dot_root)) ->
  (signalHashSquared = (signalHash * signalHash)%F) ->
  (((nullifierHash = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) /\ (nullifierHash = calculateNullifierHash_result)) /\ (nullifierHash = calculateNullifierHash_dot_out)) ->
  (((((v = (Poseidon 2%nat (calculateNullifierHash_dot_externalNullifier :: (calculateNullifierHash_dot_identityNullifier :: nil)))) /\ (v = calculateNullifierHash_result)) /\ (v = calculateNullifierHash_dot_out)) /\ (v = nullifierHash)) ->
  (v = (CalculateNullifierHash externalNullifier identityNullifier))).
Proof. hammer. Admitted.

End Semaphore_new.