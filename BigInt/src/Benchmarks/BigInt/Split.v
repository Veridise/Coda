Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ Coda.

Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.

Global Open Scope list_scope.
Global Open Scope F_scope.
Global Open Scope Z_scope.
Global Open Scope circom_scope.
Global Open Scope tuple_scope.

Global Coercion Z.of_nat: nat >-> Z.
Global Coercion N.of_nat: nat >-> N.

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Global Notation "[| xs | n ]" := (RZ.as_le n xs).
Global Notation "[\ xs \ n ]" := (RZ.as_be n xs).


#[local]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[local]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[local]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[local]Hint Extern 10 => match goal with 
  [ |- context[length _] ] => rewrite_length end: core.
#[local]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[local]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[local]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[local]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[local]Hint Extern 10 (_ < _) => lia: core.
#[local]Hint Extern 10 (_ < _)%nat => lia: core.
#[local]Hint Extern 10 (_ <= _) => lia: core.
#[local]Hint Extern 10 (_ <= _)%nat => lia: core.
#[local]Hint Extern 10 (_ > _) => lia: core.
#[local]Hint Extern 10 (_ > _)%nat => lia: core.
#[local]Hint Extern 10 (_ >= _) => lia: core. 
#[local]Hint Extern 10 (_ >= _)%nat => lia: core. 
#[local]Hint Extern 10 (S _ = S _) => f_equal: core. 
#[local]Hint Extern 1 (@eq (F.F q) _ _) => fqsatz: core.
#[local]Hint Extern 1 False => fqsatz || lia : core.

Lemma Split_obligation0: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (v : Z), True -> True -> True -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Split_obligation1_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (v : F), True -> True -> True -> True -> ((v = small) -> True).
Proof. hammer. Qed.

Lemma Split_obligation2: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (v : Z), True -> True -> True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> True -> (((0%nat <= v) /\ (v = m)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Split_obligation3_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (v : F), True -> True -> True -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> True -> ((v = big) -> True).
Proof. hammer. Qed.

Lemma Split_obligation4_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : F), True -> True -> True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> ((v = small) -> True).
Proof. hammer. Qed.

Lemma Split_obligation5_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : F), True -> True -> True -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> ((v = big) -> True).
Proof. hammer. Qed.

Lemma Split_obligation6_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : F), True -> True -> True -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma Split_obligation7: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : Z), True -> True -> True -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Split_obligation8_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : F), True -> True -> True -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. hammer. Qed.

Lemma Split_obligation9_trivial: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (u0 : (list F)) (u1 : (list F)) (v : F), True -> True -> True -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) u0 -> (((as_le_f u0) = small) /\ ((length u0) = n)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) u1 -> (((as_le_f u1) = big) /\ ((length u1) = m)) -> True -> ((v = (big * (2%F ^ n)%F)%F) -> True).
Proof. hammer. Qed.

Lemma Split_obligation10: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (bits_small : (list F)) (bits_big : (list F)) (u0 : unit) (v : F), (n < C.k) -> (m < C.k) -> True -> True -> True -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) bits_small -> (((as_le_f bits_small) = small) /\ ((length bits_small) = n)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) bits_big -> (((as_le_f bits_big) = big) /\ ((length bits_big) = m)) -> (_in = (small + (big * (2%F ^ n)%F)%F)%F) -> True -> ((v = small) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. 
    unwrap_C. unfold as_le_f. intuit.
    assert (Repr.as_le 1 bits_small | (length bits_small)). apply Repr.as_le_ub; try lia. eapply Forall_weaken. apply Repr.in_range_binary. auto.
    assert (2^n < 2^C.k). apply Zpow_facts.Zpower_lt_monotone; lia.
    subst v small. rewrite H12 in *. lia.
Qed.

Lemma Split_obligation11: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (bits_small : (list F)) (bits_big : (list F)) (u0 : unit) (v : F), (n < C.k) -> (m < C.k) -> True -> True -> True -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) bits_small -> (((as_le_f bits_small) = small) /\ ((length bits_small) = n)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) bits_big -> (((as_le_f bits_big) = big) /\ ((length bits_big) = m)) -> (_in = (small + (big * (2%F ^ n)%F)%F)%F) -> True -> ((v = big) -> ((^ v) <= ((2%nat ^ m)%Z - 1%nat)%Z)).
Proof.
    unwrap_C. unfold as_le_f. intuit.
    assert (Repr.as_le 1 bits_big | (length bits_big)). apply Repr.as_le_ub; try lia. eapply Forall_weaken. apply Repr.in_range_binary. auto.
    assert (2^n < 2^C.k). apply Zpow_facts.Zpower_lt_monotone; lia.
    subst v big. rewrite H13 in *. lia.
Qed.

Lemma Split_obligation12: forall (n : nat) (m : nat) (_in : F) (small : F) (big : F) (bits_small : (list F)) (bits_big : (list F)) (u0 : unit), (n < C.k) -> (m < C.k) -> True -> True -> True -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) bits_small -> (((as_le_f bits_small) = small) /\ ((length bits_small) = n)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) bits_big -> (((as_le_f bits_big) = big) /\ ((length bits_big) = m)) -> (_in = (small + (big * (2%F ^ n)%F)%F)%F) -> (True -> (_in = (small + (big * (2%F ^ n)%F)%F)%F)).
Proof. unwrap_C. hammer. Qed.


Lemma SplitThree_obligation0: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = n)) -> (0%nat <= v)).
Proof. Admitted.

Lemma SplitThree_obligation1_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> True -> ((v = small) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation2: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = m)) -> (0%nat <= v)).
Proof. Admitted.

Lemma SplitThree_obligation3_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> True -> ((v = medium) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation4: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = k)) -> (0%nat <= v)).
Proof. Admitted.

Lemma SplitThree_obligation5_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> True -> ((v = big) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation6_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = small) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation7_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = medium) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation8_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation9: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma SplitThree_obligation10_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation11_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (medium * (2%F ^ n)%F)%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation12_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x25 => ((x25 = 0%F) \/ (x25 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x26 => ((x26 = 0%F) \/ (x26 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (small + (medium * (2%F ^ n)%F)%F)%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation13_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x29 => ((x29 = 0%F) \/ (x29 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = big) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation14_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x32 => ((x32 = 0%F) \/ (x32 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation15_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation16_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x37 => ((x37 = 0%F) \/ (x37 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x38 => ((x38 = 0%F) \/ (x38 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((((0%nat <= v) /\ (v < C.k)) /\ (v = m)) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation17: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : Z), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x40 => ((x40 = 0%F) \/ (x40 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x41 => ((x41 = 0%F) \/ (x41 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (n + m)%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma SplitThree_obligation18_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x43 => ((x43 = 0%F) \/ (x43 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x44 => ((x44 = 0%F) \/ (x44 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (2%F ^ (n + m)%nat)%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation19_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x45 => ((x45 = 0%F) \/ (x45 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x46 => ((x46 = 0%F) \/ (x46 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x47 => ((x47 = 0%F) \/ (x47 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> True -> ((v = (big * (2%F ^ (n + m)%nat)%F)%F) -> True).
Proof. hammer. Qed.

Lemma SplitThree_obligation20: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (u0 : unit) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x49 => ((x49 = 0%F) \/ (x49 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x50 => ((x50 = 0%F) \/ (x50 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> (_in = ((small + (medium * (2%F ^ n)%F)%F)%F + (big * (2%F ^ (n + m)%nat)%F)%F)%F) -> True -> ((v = small) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
    unwrap_C. unfold as_le_f. intuit.
    assert (Repr.as_le 1 bs | (length bs)). apply Repr.as_le_ub; try lia. eapply Forall_weaken. apply Repr.in_range_binary. auto.
    assert (2^n < 2^C.k). apply Zpow_facts.Zpower_lt_monotone; lia.
    subst v small. rewrite H16 in *. lia.
Qed.

Lemma SplitThree_obligation21: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (u0 : unit) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x51 => ((x51 = 0%F) \/ (x51 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x52 => ((x52 = 0%F) \/ (x52 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x53 => ((x53 = 0%F) \/ (x53 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> (_in = ((small + (medium * (2%F ^ n)%F)%F)%F + (big * (2%F ^ (n + m)%nat)%F)%F)%F) -> True -> ((v = medium) -> ((^ v) <= ((2%nat ^ m)%Z - 1%nat)%Z)).
Proof.
    unwrap_C. unfold as_le_f. intuit.
    assert (Repr.as_le 1 bm | (length bm)). apply Repr.as_le_ub; try lia. eapply Forall_weaken. apply Repr.in_range_binary. auto.
    assert (2^n < 2^C.k). apply Zpow_facts.Zpower_lt_monotone; lia.
    subst v medium. rewrite H17 in *. lia.
Qed.

Lemma SplitThree_obligation22: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (u0 : unit) (v : F), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x54 => ((x54 = 0%F) \/ (x54 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x55 => ((x55 = 0%F) \/ (x55 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x56 => ((x56 = 0%F) \/ (x56 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> (_in = ((small + (medium * (2%F ^ n)%F)%F)%F + (big * (2%F ^ (n + m)%nat)%F)%F)%F) -> True -> ((v = big) -> ((^ v) <= ((2%nat ^ k)%Z - 1%nat)%Z)).
Proof.
    unwrap_C. unfold as_le_f. intuit.
    assert (Repr.as_le 1 bb | (length bb)). apply Repr.as_le_ub; try lia. eapply Forall_weaken. apply Repr.in_range_binary. auto.
    assert (2^n < 2^C.k). apply Zpow_facts.Zpower_lt_monotone; lia.
    subst v big. rewrite H18 in *. lia.
Qed.

Lemma SplitThree_obligation23_trivial: forall (n : nat) (m : nat) (k : nat) (_in : F) (small : F) (medium : F) (big : F) (bs : (list F)) (bm : (list F)) (bb : (list F)) (u0 : unit), (n < C.k) -> (m < C.k) -> (k < C.k) -> True -> True -> True -> True -> Forall (fun x57 => ((x57 = 0%F) \/ (x57 = 1%F))) bs -> (((as_le_f bs) = small) /\ ((length bs) = n)) -> Forall (fun x58 => ((x58 = 0%F) \/ (x58 = 1%F))) bm -> (((as_le_f bm) = medium) /\ ((length bm) = m)) -> Forall (fun x59 => ((x59 = 0%F) \/ (x59 = 1%F))) bb -> (((as_le_f bb) = big) /\ ((length bb) = k)) -> (_in = ((small + (medium * (2%F ^ n)%F)%F)%F + (big * (2%F ^ (n + m)%nat)%F)%F)%F) -> (True -> True).
Proof. unwrap_C. hammer. Qed.