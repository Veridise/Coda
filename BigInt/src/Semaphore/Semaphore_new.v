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

From Circom Require Import Circom Util Default Tuple LibTactics Simplify Repr ListUtil.
From Circom.CircomLib Require Import Bitify.

Local Open Scope list_scope.
Local Open Scope F_scope.

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
                       
Definition Poseidon (nInputs : nat) (inputs : list F) : F. Admitted.

Axiom Poseidon_2 : forall inputs : list F,
  length inputs = 2%nat ->
  Poseidon 2%nat inputs = Poseidon 2%nat ((inputs!0%nat)::(inputs!1%nat)::nil).

Definition zip {A B} (xs : list A) (ys : list B) := combine xs ys.

(* Note: This is a placeholder implementation that lets us prove many
trivial and even some nontrivial MerkleTreeInclusionProof obligations *)
Definition MrklTreeInclPfHash (xs : list (F * F)) (init : F) := 
  fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0%F) then (Poseidon 2%nat (y :: (snd x) :: nil)) else (Poseidon 2%nat ((snd x):: y :: nil))) 
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

(* Source: https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/tree.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom *)

Module Semaphore_new.

(* non-trivial lemmas *)

Lemma Semaphore_obligation7: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : Z), True -> True -> Forall (fun x106 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x107 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((0%nat <= v) /\ (v = nLevels)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Semaphore_obligation9: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x110 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x111 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x112 => True) v -> True -> ((((length v) = nLevels) /\ (v = treePathIndices)) -> ((length v) = nLevels)).
Proof. hammer. Qed.

Lemma Semaphore_obligation10: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x113 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x114 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x115 => True) v -> True -> ((((length v) = nLevels) /\ (v = treeSiblings)) -> ((length v) = nLevels)).
Proof. hammer. Qed.

Lemma Semaphore_obligation11: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x116 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x117 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (MrklTreeInclPfHash (zip treePathIndices treeSiblings) id_commit)) -> (v = (MerkleTreeInclusionProof (CalculateIdentityCommitment (CalculateSecret identityNullifier identityTrapdoor)) treePathIndices treeSiblings))).
Proof. hammer. Qed.

Lemma Semaphore_obligation14: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x122 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x123 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil)))) -> (v = (CalculateNullifierHash externalNullifier identityNullifier))).
Proof. hammer. Qed.

(* trivial lemmas *)

Lemma Semaphore_obligation0_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x92 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x93 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation1_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x94 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x95 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityTrapdoor) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation2_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (v : F), True -> True -> Forall (fun x96 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x97 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> True -> (((v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) /\ (v = secret)) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation3_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x98 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x99 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation4_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x100 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x101 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation5_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x102 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x103 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation6_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x104 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x105 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.


Lemma Semaphore_obligation8_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x108 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x109 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((v = (Poseidon 1%nat (secret :: nil))) /\ (v = id_commit)) -> True).
Proof. hammer. Qed.


Lemma Semaphore_obligation12_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x118 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x119 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = externalNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation13_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x120 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x121 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation15_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit), True -> True -> Forall (fun x124 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x125 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> (True -> True).
Proof. hammer. Qed.

End Semaphore_new.