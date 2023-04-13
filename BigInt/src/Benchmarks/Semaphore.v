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

Definition Poseidon (nInputs : nat) (inputs : list F) : F. Admitted.

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

Definition zip {A B} (xs : list A) (ys : list B) := combine xs ys.

(* Lemma list_eq_forall:
  forall (l1 l2:list F),
    (forall (i:nat), 0 <= i < length l1 -> l1!i = l2!i) ->
    (length l1 = length l2) ->
    l1 = l2.
Proof.
  induction l1; intros; destruct l2; simpl in *; try easy.
  inversion H0. 
  assert (a = f). 
  { assert ( (a :: l1) ! 0 = (f :: l2) ! 0). specialize (H 0%nat). destruct H;try lia;auto.
    auto. }
  subst;f_equal. apply IHl1;intuition. specialize (H (S i)). 
  assert ( (f :: l1) ! (S i) = (f :: l2) ! (S i)). destruct H;try lia;auto.
  assert ( l1 = (f::l1)[1:]). { auto. }
  assert ( l2 = (f::l2)[1:]). { auto. } rewrite H5, H6. unfold_default.
  do 2 rewrite skipn_nth. fold_default;simpl;try lia.
  destruct H;try lia;auto.
Qed. *)

Lemma list_combine_eq_forall:
  forall (l1 l2:list F) z,
    (forall (i:nat), 0 <= i < length l1 -> fst (z!i) = l1!i /\ snd (z!i) = l2!i) ->
    (length l1 = length l2) ->
    (length z = length l1) ->
    z = combine l1 l2.
Proof.
  induction l1; intros; destruct l2; simpl in *; try easy.
  destruct z;try easy.
  inversion H0. destruct z;try easy.
  assert (p = (a, f)). 
  { assert ( fst ((p :: z) ! 0) = (a :: l1) ! 0). specialize (H 0%nat). destruct H;try lia;auto.
    assert ( snd ((p :: z) ! 0) = (f :: l2) ! 0). specialize (H 0%nat). destruct H;try lia;auto.
    destruct p;simpl in *. f_equal;auto. }
  subst;f_equal. apply IHl1;auto. 
  intros. specialize (H (S i)). 
  assert ( fst (((a, f) :: z) ! S i) = (a :: l1) ! S i /\ snd (((a, f) :: z) ! S i) = (f :: l2) ! S i). destruct H;try lia;auto.
  assert ( l1 = (a::l1)[1:]). { auto. }
  assert ( l2 = (f::l2)[1:]). { auto. }
  assert ( z = ((a, f) :: z)[1:]). { auto. } rewrite H5, H6, H7. unfold_default.
  do 3 rewrite skipn_nth. fold_default;simpl;try lia.
  destruct H;try lia;auto.
Qed.

(* Note: This is a placeholder implementation that lets us prove many
trivial and even some nontrivial MerkleTreeInclusionProof obligations *)
Definition MrklTreeInclPfHash (xs : list (F * F)) (init : F) := 
  fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0%F) then (Poseidon 2%nat (y :: (snd x) :: nil)) else (Poseidon 2%nat ((snd x):: y :: nil))) 
                       xs init.

Definition CalculateIdentityCommitment a := Poseidon 1%nat (a :: nil).

Definition CalculateSecret a b := Poseidon 2%nat (a :: (b :: nil)).

Definition CalculateNullifierHash a b := Poseidon 2%nat (a :: (b :: nil)).

Definition MerkleTreeInclusionProof i a b := MrklTreeInclPfHash (zip a b) i.

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

Lemma fold_left_firstn_S:
  forall (l: list (F*F))(i: nat)(b: F)f,
  i < length l ->
  fold_left f  (l [:S i]) b = 
  f (fold_left f (l [:i]) b) (l ! i).
Proof.
  intros. 
  assert(l [:S i] = l [:i] ++ ((l ! i)::nil)).
  { erewrite firstn_S;try lia. unfold_default. auto. }
  rewrite H0.
  apply fold_left_app.
Qed.

Lemma combine_fst_n: forall n (j:nat) (l1 l2: list F),
  length l1 = length l2 ->
  j < n ->
  fst ((combine (l1) (l2)) ! j) = l1 ! j.
Proof.
  intros. 
  unfold_default. simpl. rewrite combine_nth;simpl;auto.
Qed.

Lemma combine_snd_n: forall n (j:nat) (l1 l2: list F),
  length l1 = length l2 ->
  j < n ->
  fst ((combine (l1) (l2)) ! j) = l1 ! j.
Proof.
  intros. 
  unfold_default. simpl. rewrite combine_nth;simpl;auto.
Qed.

Lemma MerkleTreeInclusionProof_obligation0_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x3 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x4 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x7 => match x7 with (x5,x6) => True end) z -> Forall (fun x7 => match x7 with (x5,x6) => True end) z -> Forall (fun x7 => match x7 with (x5,x6) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation1_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x8 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x9 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x12 => match x12 with (x10,x11) => True end) z -> Forall (fun x12 => match x12 with (x10,x11) => True end) z -> Forall (fun x12 => match x12 with (x10,x11) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> (((0%nat <= v) /\ (v = nLevels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation2_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x13 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x14 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x17 => match x17 with (x15,x16) => True end) z -> Forall (fun x17 => match x17 with (x15,x16) => True end) z -> Forall (fun x17 => match x17 with (x15,x16) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> (((0%nat <= v) /\ (v < nLevels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation3_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (v : F), True -> Forall (fun x18 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x19 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x22 => match x22 with (x20,x21) => True end) z -> Forall (fun x22 => match x22 with (x20,x21) => True end) z -> Forall (fun x22 => match x22 with (x20,x21) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> True -> ((v = (MrklTreeInclPfHash (take i z) leaf)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation4_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (v : F), True -> Forall (fun x23 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x24 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x27 => match x27 with (x25,x26) => True end) z -> Forall (fun x27 => match x27 with (x25,x26) => True end) z -> Forall (fun x27 => match x27 with (x25,x26) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation5_trivial: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (v : F), True -> Forall (fun x28 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x29 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x32 => match x32 with (x30,x31) => True end) z -> Forall (fun x32 => match x32 with (x30,x31) => True end) z -> Forall (fun x32 => match x32 with (x30,x31) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> True -> ((v = (1%F - (fst (z!i)))%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation6: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : Z), True -> Forall (fun x33 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x34 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x37 => match x37 with (x35,x36) => True end) z -> Forall (fun x37 => match x37 with (x35,x36) => True end) z -> Forall (fun x37 => match x37 with (x35,x36) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> (((fst (z!i)) * (1%F - (fst (z!i)))%F)%F = 0%F) -> Forall (fun x39 => Forall (fun x38 => True) x39) c -> Forall (fun x39 => ((length x39) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation7: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list (list F))), True -> Forall (fun x40 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x41 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> Forall (fun x44 => match x44 with (x42,x43) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> (((fst (z!i)) * (1%F - (fst (z!i)))%F)%F = 0%F) -> Forall (fun x46 => Forall (fun x45 => True) x46) c -> Forall (fun x46 => ((length x46) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x48 => Forall (fun x47 => True) x48) v -> Forall (fun x48 => ((length x48) = 2%nat)) v -> True -> (((((True /\ ((v!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((v!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length v) = 2%nat)) /\ (v = c)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation8: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list F)), True -> Forall (fun x49 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x50 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x53 => match x53 with (x51,x52) => True end) z -> Forall (fun x53 => match x53 with (x51,x52) => True end) z -> Forall (fun x53 => match x53 with (x51,x52) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> (((fst (z!i)) * (1%F - (fst (z!i)))%F)%F = 0%F) -> Forall (fun x55 => Forall (fun x54 => True) x55) c -> Forall (fun x55 => ((length x55) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x56 => True) v -> True -> (((length v) = 2%nat) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation9: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : Z), True -> Forall (fun x57 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x58 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x61 => match x61 with (x59,x60) => True end) z -> Forall (fun x61 => match x61 with (x59,x60) => True end) z -> Forall (fun x61 => match x61 with (x59,x60) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> (((fst (z!i)) * (1%F - (fst (z!i)))%F)%F = 0%F) -> Forall (fun x63 => Forall (fun x62 => True) x63) c -> Forall (fun x63 => ((length x63) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x64 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation10: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : (list F)), True -> Forall (fun x65 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x66 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x69 => match x69 with (x67,x68) => True end) z -> Forall (fun x69 => match x69 with (x67,x68) => True end) z -> Forall (fun x69 => match x69 with (x67,x68) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (i < nLevels) -> (x = (MrklTreeInclPfHash (take i z) leaf)) -> (((fst (z!i)) * (1%F - (fst (z!i)))%F)%F = 0%F) -> Forall (fun x71 => Forall (fun x70 => True) x71) c -> Forall (fun x71 => ((length x71) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x72 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> Forall (fun x73 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < 2%nat -> ((v!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!i)))%F + ((c!i)!0%nat))%F)) /\ ((length v) = 2%nat)) /\ (v = m)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation11: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : F), True -> Forall (fun x74 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x75 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x78 => match x78 with (x76,x77) => True end) z -> Forall (fun x78 => match x78 with (x76,x77) => True end) z -> Forall (fun x78 => match x78 with (x76,x77) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> (_i < nLevels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x80 => Forall (fun x79 => True) x80) c -> Forall (fun x80 => ((length x80) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x81 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = (Poseidon 2%nat m)) -> (v = (MrklTreeInclPfHash (take (_i + 1%nat)%nat z) leaf))).
Proof. 
intuition; subst; unfold MrklTreeInclPfHash, take in *; simpl in *;unwrap_C.
specialize (H13 0%nat) as Hm1; specialize (H13 1%nat) as Hm2; simpl in *.
assert ((c!1)!0%nat = snd (z ! _i)). { rewrite H22. auto. } 
assert ((c!0)!1%nat = snd (z ! _i)). { rewrite H23. auto. }
assert ((c!1)!1%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H22. auto. }
assert ((c!0)!0%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H23. auto. }
rewrite H1, H9, H15, H17 in *. rewrite Poseidon_2;auto. 
replace (_i + 1)%nat with (S _i) by lia. rewrite fold_left_firstn_S; auto.
destruct dec.
- rewrite e in *. 
  assert (m ! 1 = snd (z ! _i)). 
  { rewrite Hm2;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  assert (m ! 0 = (c ! 1) ! 1).
  { rewrite Hm1;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  rewrite H24, H25. rewrite H15. auto.
- assert (fst (z ! _i) = 1%F). { fqsatz. }
  rewrite H24 in *.
  assert (m ! 1 = (c ! 1) ! 1) by (rewrite Hm2;auto;try fqsatz).
  assert (m ! 0 = snd (z ! _i)) by (rewrite Hm1;auto;try fqsatz).
  rewrite H25, H26. rewrite H15. auto.
Qed.

Lemma MerkleTreeInclusionProof_obligation12: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x82 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x83 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x86 => match x86 with (x84,x85) => True end) z -> Forall (fun x86 => match x86 with (x84,x85) => True end) z -> Forall (fun x86 => match x86 with (x84,x85) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = leaf) -> (v = (MrklTreeInclPfHash (take 0%nat z) leaf))).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation13: forall (nLevels : nat) (leaf : F) (pathIndices : (list F)) (siblings : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x87 => True) pathIndices -> ((length pathIndices) = nLevels) -> Forall (fun x88 => True) siblings -> ((length siblings) = nLevels) -> Forall (fun x91 => match x91 with (x89,x90) => True end) z -> Forall (fun x91 => match x91 with (x89,x90) => True end) z -> Forall (fun x91 => match x91 with (x89,x90) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndices) -> (((fst (z!iz)) = (pathIndices!iz)) /\ ((snd (z!iz)) = (siblings!iz)))) /\ ((length z) = (length pathIndices))) -> True -> ((v = (MrklTreeInclPfHash (take nLevels z) leaf)) -> (v = (MrklTreeInclPfHash (zip pathIndices siblings) leaf))).
Proof. 
  intuition; unwrap_C.
  unfold zip, take in *; simpl in *.
  assert (z = combine pathIndices siblings).
  { apply list_combine_eq_forall;auto. }
  rewrite <- H7. rewrite H1 in H11. rewrite <- H11 in H9.
  erewrite ListUtil.List.firstn_all in H9;auto.
Qed.

(** ** Semaphore *)

Lemma Semaphore_obligation0_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x109 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x110 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation1_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (v : F), True -> True -> Forall (fun x111 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x112 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> True -> ((v = identityTrapdoor) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation2_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (v : F), True -> True -> Forall (fun x113 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x114 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> True -> (((v = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) /\ (v = secret)) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation3_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x115 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x116 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation4_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (v : F), True -> True -> Forall (fun x117 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x118 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation5_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x119 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x120 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation6_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (v : F), True -> True -> Forall (fun x121 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x122 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = signalHash) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation7: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : Z), True -> True -> Forall (fun x123 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x124 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((0%nat <= v) /\ (v = nLevels)) -> (0%nat <= v)).
Proof. Admitted.

Lemma Semaphore_obligation8_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x125 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x126 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> (((v = (Poseidon 1%nat (secret :: nil))) /\ (v = id_commit)) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation9: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x127 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x128 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x129 => True) v -> True -> ((((length v) = nLevels) /\ (v = treePathIndices)) -> ((length v) = nLevels)).
Proof. Admitted.

Lemma Semaphore_obligation10: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : (list F)), True -> True -> Forall (fun x130 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x131 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> Forall (fun x132 => True) v -> True -> ((((length v) = nLevels) /\ (v = treeSiblings)) -> ((length v) = nLevels)).
Proof. Admitted.

Lemma Semaphore_obligation11: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x133 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x134 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (MrklTreeInclPfHash (zip treePathIndices treeSiblings) id_commit)) -> (v = (MerkleTreeInclusionProof (CalculateIdentityCommitment (CalculateSecret identityNullifier identityTrapdoor)) treePathIndices treeSiblings))).
Proof. Admitted.

Lemma Semaphore_obligation12_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x135 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x136 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = externalNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation13_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x137 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x138 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = identityNullifier) -> True).
Proof. hammer. Qed.

Lemma Semaphore_obligation14: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit) (v : F), True -> True -> Forall (fun x139 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x140 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> True -> ((v = (Poseidon 2%nat (externalNullifier :: (identityNullifier :: nil)))) -> (v = (CalculateNullifierHash externalNullifier identityNullifier))).
Proof. Admitted.

Lemma Semaphore_obligation15_trivial: forall (nLevels : nat) (identityNullifier : F) (identityTrapdoor : F) (treePathIndices : (list F)) (treeSiblings : (list F)) (signalHash : F) (externalNullifier : F) (secret : F) (id_commit : F) (signalHashSquared : F) (u : unit), True -> True -> Forall (fun x141 => True) treePathIndices -> ((length treePathIndices) = nLevels) -> Forall (fun x142 => True) treeSiblings -> ((length treeSiblings) = nLevels) -> True -> True -> (secret = (Poseidon 2%nat (identityNullifier :: (identityTrapdoor :: nil)))) -> (id_commit = (Poseidon 1%nat (secret :: nil))) -> (signalHashSquared = (signalHash * signalHash)%F) -> (signalHashSquared = (signalHash * signalHash)%F) -> (True -> True).
Proof. hammer. Qed.
