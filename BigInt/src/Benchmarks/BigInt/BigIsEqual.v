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

Lemma BigIsEqual_obligation0_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((k <= C.k) /\ True) -> Forall (fun x0 => True) a -> ((length a) = k) -> Forall (fun x1 => True) b -> ((length b) = k) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation1_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((k <= C.k) /\ True) -> Forall (fun x2 => True) a -> ((length a) = k) -> Forall (fun x3 => True) b -> ((length b) = k) -> True -> ((((0%nat <= v) /\ ((k <= C.k) /\ True)) /\ (v = k)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation2_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((k <= C.k) /\ True) -> Forall (fun x4 => True) a -> ((length a) = k) -> Forall (fun x5 => True) b -> ((length b) = k) -> True -> (((0%nat <= v) /\ (v < k)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation3_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), ((k <= C.k) /\ True) -> Forall (fun x6 => True) a -> ((length a) = k) -> Forall (fun x7 => True) b -> ((length b) = k) -> (i < k) -> True -> ((((^ v) <= i) /\ ((((^ v) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ v) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation4_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (x : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x8 => True) a -> ((length a) = k) -> Forall (fun x9 => True) b -> ((length b) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> ((v = (a!i)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation5_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (x : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x10 => True) a -> ((length a) = k) -> Forall (fun x11 => True) b -> ((length b) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> ((v = (b!i)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation6_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (x : F) (ise : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x12 => True) a -> ((length a) = k) -> Forall (fun x13 => True) b -> ((length b) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> ((a!i) = (b!i))) /\ ((ise = 0%F) -> ~((a!i) = (b!i))))) -> True -> (((((^ v) <= i) /\ ((((^ v) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ v) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation7_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (x : F) (ise : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x14 => True) a -> ((length a) = k) -> Forall (fun x15 => True) b -> ((length b) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> ((a!i) = (b!i))) /\ ((ise = 0%F) -> ~((a!i) = (b!i))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((a!i) = (b!i))) /\ ((v = 0%F) -> ~((a!i) = (b!i))))) /\ (v = ise)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation8: forall (k : nat) (a : (list F)) (b : (list F)) (i : nat) (x : F) (ise : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x16 => True) a -> ((length a) = k) -> Forall (fun x17 => True) b -> ((length b) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((a!bie_j) = (b!bie_j))))))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> ((a!i) = (b!i))) /\ ((ise = 0%F) -> ~((a!i) = (b!i))))) -> True -> ((v = (x + ise)%F) -> (((^ v) <= (i + 1%nat)%nat) /\ ((((^ v) = (i + 1%nat)%nat) -> (forall (bie_j:nat), 0%nat <= bie_j < (i + 1%nat)%nat -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ v) = (i + 1%nat)%nat)) -> (exists (bie_j:nat), 0%nat <= bie_j < (i + 1%nat)%nat /\ ~(((a!bie_j) = (b!bie_j)))))))).
Proof. 
  unwrap_C. intros.
  assert (2^k0 <= 2^k). apply Zpow_facts.Zpower_le_monotone; lia.
  assert ((k0 <= 2^k0)). apply Zpow_facts.Zpower2_le_lin; lia.
  
  destruct H6. apply Repr.in_range_binary in H6.
  split; intros; destruct (dec (^x = i)); subst v.
  - autorewrite with F_to_Z; try (pose_nonneg; lia).
  - autorewrite with F_to_Z; try (pose_nonneg; lia).
  - split; intros; autorewrite with F_to_Z in H8; try (pose_nonneg; lia);
    replace ((Z.of_nat (Init.Nat.add i (S O)))) with (i+1) in H8 by lia.
    assert (^ise = 1) by lia.
    assert (ise=1%F). apply ReprZUnsigned.F_to_Z_inj. autorewrite with F_to_Z; try lia.
    intuit.
    destruct (dec (bie_j < i)). auto.
    assert (bie_j = i) by lia. subst bie_j. auto.
    assert (^ise = 0) by (pose_nonneg; lia).
    assert (ise = 0%F). apply ReprZUnsigned.F_to_Z_inj. autorewrite with F_to_Z; try lia.
    intuit.
    exists i. split; auto.
  - split; intros.
    (* x < i, x+ise = i+1 *)
    (autorewrite with F_to_Z in H8; try (pose_nonneg; lia)).
    (* x < i, x+ise < i+1 *)
    intuit.
    (autorewrite with F_to_Z in H8; try (pose_nonneg; lia)).

    intuit. destruct H14 as [i' H14]. exists i'.
    split; hammer.
Qed.

Lemma BigIsEqual_obligation9: forall (k : nat) (a : (list F)) (b : (list F)) (v : F), ((k <= C.k) /\ True) -> Forall (fun x18 => True) a -> ((length a) = k) -> Forall (fun x19 => True) b -> ((length b) = k) -> True -> ((v = 0%F) -> (((^ v) <= 0%nat) /\ ((((^ v) = 0%nat) -> (forall (bie_j:nat), 0%nat <= bie_j < 0%nat -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ v) = 0%nat)) -> (exists (bie_j:nat), 0%nat <= bie_j < 0%nat /\ ~(((a!bie_j) = (b!bie_j)))))))).
Proof. 
  intros. subst v. intuit. autorewrite with F_to_Z. lia.
  lia.
Qed.

Lemma BigIsEqual_obligation10: forall (k : nat) (a : (list F)) (b : (list F)) (total : F) (v : Z), ((k <= C.k) /\ True) -> Forall (fun x20 => True) a -> ((length a) = k) -> Forall (fun x21 => True) b -> ((length b) = k) -> (((^ total) <= k) /\ ((((^ total) = k) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ total) = k)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> ((((0%nat <= v) /\ ((k <= C.k) /\ True)) /\ (v = k)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation11_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (total : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x22 => True) a -> ((length a) = k) -> Forall (fun x23 => True) b -> ((length b) = k) -> (((^ total) <= k) /\ ((((^ total) = k) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ total) = k)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> ((v = (F.of_nat q k)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation12_trivial: forall (k : nat) (a : (list F)) (b : (list F)) (total : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x24 => True) a -> ((length a) = k) -> Forall (fun x25 => True) b -> ((length b) = k) -> (((^ total) <= k) /\ ((((^ total) = k) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ total) = k)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> (((((^ v) <= k) /\ ((((^ v) = k) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ v) = k)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j))))))) /\ (v = total)) -> True).
Proof. hammer. Qed.

Lemma BigIsEqual_obligation13: forall (k : nat) (a : (list F)) (b : (list F)) (total : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x26 => True) a -> ((length a) = k) -> Forall (fun x27 => True) b -> ((length b) = k) -> (((^ total) <= k) /\ ((((^ total) = k) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~(((^ total) = k)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j))))))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((F.of_nat q k) = total)) /\ ((v = 0%F) -> ~((F.of_nat q k) = total)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (forall (bie_j:nat), 0%nat <= bie_j < k -> ((a!bie_j) = (b!bie_j)))) /\ (~((v = 1%F)) -> (exists (bie_j:nat), 0%nat <= bie_j < k /\ ~(((a!bie_j) = (b!bie_j)))))))).
Proof. 
  unwrap_C.
  unfold F.of_nat.
  intros.
  assert (Hk0k: 2^k0 <= 2^k). apply Zpow_facts.Zpower_le_monotone; lia.
  assert (Hpowk0k: (k0 <= 2^k0)). apply Zpow_facts.Zpower2_le_lin; lia.
  intuit.
  assert (F.to_Z total <> Z.of_nat k0).
  intros ?. apply f_equal with (f:=F.of_Z q) in H13.
  rewrite F.of_Z_to_Z in H13. apply H4. auto.
  auto.
  apply f_equal with (f:=F.to_Z) in H4.
  rewrite F.to_Z_of_Z, Zmod_small in H4 by lia.
  symmetry in H4. auto.
Qed.

