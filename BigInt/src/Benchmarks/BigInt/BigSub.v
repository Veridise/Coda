(** * DSL benchmark: ModSumThree, BigAdd, BigAddModP *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition as_le_f := Repr.as_le 1%nat.
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

Lemma F_to_Z_nonneg: forall (x:F), 0 <= ^x.
Proof.
  intros. apply F.to_Z_range. lia.
Qed.

Ltac pose_nonneg := repeat match goal with
| [ |- context[F.to_Z ?x ] ] =>
  let t := type of (F_to_Z_nonneg x) in
  lazymatch goal with
  (* already posed *)
  | [ _: t |- _] => fail
  | _ => 
    let Hnonneg := fresh "_Hnonneg" in
    pose proof (F_to_Z_nonneg x) as Hnonneg
    ; move Hnonneg at top
  end
| _ => fail
end.

Lemma ModSubThree_obligation0_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 2%nat)%Z)) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation1_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation2: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (n + 1%nat)%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed.

Lemma ModSubThree_obligation3: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = a)) -> ((^ v) < (2%nat ^ (n + 1%nat)%nat)%Z)).
Proof. 
  intros. apply Repr.in_range_binary in H2. intuit. subst.
  replace (Z.of_N (N.of_nat (Init.Nat.add n (S O)))) with (n+1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.

Lemma ModSubThree_obligation4_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation5_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation6: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (b + c)%F) -> ((^ v) < (2%nat ^ (n + 1%nat)%nat)%Z)).
Proof.
  unwrap_C. intros. subst. 
  assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
    replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  replace (Z.of_N (N.of_nat (Init.Nat.add n (S O)))) with (n+1)%Z by lia. rewrite Zpower_exp by lia. simplify.
  pose proof (F_to_Z_nonneg b). pose proof (F_to_Z_nonneg c).
  apply Repr.in_range_binary in H2.
  autorewrite with F_to_Z; try lia.
Qed.

Lemma ModSubThree_obligation7_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((v = 0%F) -> ~((^ a) < (^ (b + c)%F))))) /\ (v = borrow)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation8_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation9_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (borrow * 2%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation10: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : Z), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 2%nat)%Z)) /\ (v = n)) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSubThree_obligation11_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = ((borrow * 2%F)%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation12_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation13_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (((borrow * 2%F)%F ^ n)%F + a)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation14_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation15_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation16_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (b + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation17: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F * F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> match v with (x0,x1) => (x0 = ((((borrow * 2%F)%F ^ n)%F + a)%F - (b + c)%F)%F) end -> match v with (x0,x1) => ((((x1 = 0%F) \/ (x1 = 1%F)) /\ (((x1 = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((x1 = 0%F) -> ~((^ a) < (^ (b + c)%F))))) /\ (x1 = borrow)) end -> match v with (x0,x1) => True end -> (True -> (fst (v) = ((((snd (v) * 2%F)%F ^ n)%F + a)%F - (b + c)%F)%F)).
Proof.
  unwrap_C. intros. apply Repr.in_range_binary in H2.
  destruct v as [sum borrow']. destruct H5. destruct H5.  apply Repr.in_range_binary in H5.
  simpl. subst.
  fqsatz.
Qed.

Lemma ModSubThree_obligation18_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = ((((borrow * 2%F)%F ^ n)%F + a)%F - (b + c)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation19: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), (n <= (C.k - 2%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((v = 0%F) -> ~((^ a) < (^ (b + c)%F))))) /\ (v = borrow)) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((v = 0%F) -> ~((^ a) < (^ (b + c)%F)))))).
Proof. 
  intros. intuit.
Qed.