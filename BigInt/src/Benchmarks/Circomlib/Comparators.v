(** * DSL benchmark: Comparators *)

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

(** ** IsZero *)

Lemma IsZero_obligation0_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = 1%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation1_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = 0%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation2_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = _in) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation3_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = inv) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation4_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = (_in * inv)%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation5_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = (0%F - (_in * inv)%F)%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation6_trivial: forall (_in : F) (inv : F) (out : F) (u1 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> True -> ((v = _in) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation7_trivial: forall (_in : F) (inv : F) (out : F) (u1 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> True -> ((v = out) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation8: forall (_in : F) (inv : F) (out : F) (u1 : unit) (u2 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> ((_in * out)%F = 0%F) -> True -> ((v = out) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F))))).
Proof.
  unwrap_C. intros.
  destruct (dec (_in = 0%F)).
  - subst. simplify; intuit. fqsatz.
  - subst v. simplify; intuit. left. 
  assert (_in <> 0)%F by intuit. fqsatz.
  fqsatz.
Qed.


(** ** IsEqual *)


Lemma IsEqual_obligation0: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = x) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation1: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = y) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation2: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = (x - y)%F) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation3: forall (x : F) (y : F) (v : F), True -> True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((x - y)%F = 0%F)) /\ ((v = 0%F) -> ~((x - y)%F = 0%F)))) -> (True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (x = y)) /\ ((v = 0%F) -> ~(x = y))))).
Proof.
  unwrap_C. intros. subst.
  destruct H1 as [H1 [H1' H1'']].
  intuit.
  - subst. apply H1. fqsatz.
  - fqsatz.
Qed.

Lemma IsEqual_obligation4: forall (x : F) (y : F) (v : F), True -> True -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((x - y)%F = 0%F)) /\ ((v = 0%F) -> ~((x - y)%F = 0%F)))) -> True).
Proof. intuition. Qed.

(** ** LessThan *)

Lemma LessThan_obligation0_trivial: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((((0%nat <= v)%Z /\ (v < (C.k - 1%nat)%Z)%Z) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation1_trivial: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation2: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = (n + 1%nat)%nat) -> (0%nat <= v)%Z).
Proof. intuit. Qed.

Lemma LessThan_obligation3_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> (((F.to_Z v < (2%nat ^ n)%Z)%Z /\ (v = x)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation4_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> (((F.to_Z v < (2%nat ^ n)%Z)%Z /\ (v = y)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation5_trivial: 
  forall (n : nat) (x : F) (y : F) (v : F), 
  (n < (C.k - 1%nat)%Z)%Z -> 
  (F.to_Z x < (2%nat ^ n)%Z)%Z -> 
  (F.to_Z y < (2%nat ^ n)%Z)%Z -> 
  True -> 
  ((v = (x - y)%F) -> True).
  Proof. intuit. Qed.


Lemma LessThan_obligation6_trivial: 
  forall (n : nat) (x : F) (y : F) (v : F), 
  (n < (C.k - 1%nat)%Z)%Z -> 
  (F.to_Z x < (2%nat ^ n)%Z)%Z -> 
  (F.to_Z y < (2%nat ^ n)%Z)%Z -> 
  True -> 
  ((v = 2%F) -> True).
  Proof. intuit. Qed.

Lemma LessThan_obligation7: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((((0%nat <= v)%Z /\ (v < (C.k - 1%nat)%Z)%Z) /\ (v = n)) -> (0%nat <= v)%Z).
Proof. 
  intros.
  lia.
Qed.

Lemma LessThan_obligation8_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation9_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = ((x - y)%F + (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Definition as_le_f := Repr.as_le 1%nat.


Lemma LessThan_obligation10: forall (n : nat) (x : F) (y : F) (z : (list F)) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) z -> (((as_le_f z) = ((x - y)%F + (2%F ^ n)%F)%F) /\ ((length z) = (n + 1%nat)%nat)) -> True -> ((v = (z!n)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. 
  intros.
  subst.
  unfold_default. apply Forall_nth; auto. lia.
Qed.
  
Definition f_not (x:F) := (x = 0)%F.

Lemma binary_not0: forall (x:F), ((x = 0 \/ x = 1) -> x <> 0 -> x = 1)%F.
Proof. intuit. Qed.

Lemma binary_not1: forall (x:F), ((x = 0 \/ x = 1) -> x <> 1 -> x = 0)%F.
Proof. intuit. Qed.
Ltac ind x :=
  match goal with
  | [H: (x = 0%F \/ x = 1 %F) /\ (x = 1%F -> ?P) /\ (x = 0%F -> ?Q) |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    destruct H as [H1 [H2 H3]];
    try match goal with
    | [ Hx: x <> 1%F |- _ ] =>
      apply binary_not1 in Hx; try apply H1
    | [ Hx: x <> 0%F |- _ ] =>
      apply binary_not0 in Hx; try apply H1
    end;
    match goal with
    | [ Hx: x = 1%F |- _] =>
      apply H2 in Hx
    | [ Hx: x = 0%F |- _] =>
      apply H3 in Hx
    end;
    clear H1; clear H2; clear H3
  end.

Ltac assert_consequence H :=
  match type of H with
  | ?P -> ?Q -> ?R => assert R
  end.

Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

Ltac switch dst l :=
  let H := fresh "H" in
  match goal with
  | [ |- ?G ] =>
    assert (H: G <-> dst) by l;
    apply H;
    clear H
  end.


Lemma LessThan_obligation11: forall (n : nat) (x : F) (y : F) (z : (list F)) (v : F), (n <= (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) z -> (((as_le_f z) = ((x - y)%F + (2%F ^ n)%F)%F) /\ ((length z) = (n + 1%nat)%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not (z!n))) /\ ((v = 0%F) -> ~(f_not (z!n))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z x < F.to_Z y)%Z) /\ ((v = 0%F) -> ~(F.to_Z x < F.to_Z y)%Z)))).
Proof.
  unwrap_C.
  intros. unfold f_not, as_le_f in *.
  assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
  assert (H_x_nonneg: (0 <= F.to_Z x)%Z). apply F.to_Z_range. lia.
  assert (H_y_nonneg: (0 <= F.to_Z y)%Z). apply F.to_Z_range. lia.
  assert (H_to_Z: ^ (x - y + (1 + 1) ^ n) = ^x - ^y + 2 ^ n). {
    replace (x - y + 2^n)%F with (x + 2^ n - y)%F by fqsatz.
    autorewrite with F_to_Z; try lia; repeat autorewrite with F_to_Z; simpl; try lia.
  }
  split; intuit; subst v.
  (* MSB = 1 -> out = 0 -> x >= y *)
  - assert (z!n = 1)%F. {
      unfold_default. apply binary_not0. apply Forall_nth; eauto. lia. 
      fold_default. intuit.
    }
    generalize H10. switch (^x >= ^y) lia.
    assert (^[|z|] >= 2^n). {
      applys_eq Repr.as_le_lb'; eauto; try lia.
      rewrite nat_N_Z. reflexivity.
      lia.
      fold_default. auto.
    }
    apply f_equal with (f:=F.to_Z) in H6. 
    rewrite H6, H_to_Z in *.
    lia.
  - (* MSB = 0 -> out = 1 -> x < y *)
  assert ([|z|] | (n)). {
    assert (Hzn: [| z[:n] |] = [| z |]). {
      symmetry. erewrite Repr.as_le_split_last' with (i:=n).
      rewrite H3. simplify. reflexivity.
      lia.
    }
    rewrite <- Hzn.
    applys_eq Repr.as_le_ub'.
    repeat f_equal. rewrite firstn_length_le; lia.
    apply Forall_firstn. auto.
    rewrite firstn_length_le; lia.
  }
  apply f_equal with (f:=F.to_Z) in H6. lia.
Qed.


(** ** GreaterThan *)

Lemma GreaterThan_obligation0: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z) -> (F.to_Z x < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> ((((0%nat <= v) /\ (v < (C.k - 1%nat)%Z)) /\ (v = n)) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. intuit. Qed.

Lemma GreaterThan_obligation1: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z x < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> (((F.to_Z v < (2%nat ^ n)%Z) /\ (v = y)) -> (F.to_Z v < (2%nat ^ n)%Z)).
Proof. intuit. Qed.

Lemma GreaterThan_obligation2: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z x < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> (((F.to_Z v < (2%nat ^ n)%Z) /\ (v = x)) -> (F.to_Z v < (2%nat ^ n)%Z)).
Proof. intuit. Qed.

Lemma GreaterThan_obligation3_trivial: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> (F.to_Z b < (2%nat ^ n)%Z) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z b < F.to_Z a)) /\ ((v = 0%F) -> ~(F.to_Z b < F.to_Z a)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z b < F.to_Z a)) /\ ((v = 0%F) -> ~(F.to_Z b < F.to_Z a))))).
Proof. intuit. Qed.

(** ** LessEqThan *)

Lemma LessEqThan_obligation0: forall (n : nat) (a : F) (b : F) (v : Z), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> (F.to_Z b < (2%nat ^ n)%Z) -> True -> ((((0%nat <= v) /\ (v < (C.k - 1%nat)%Z)) /\ (v = n)) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. intuit. Qed.

Lemma LessEqThan_obligation1: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> (F.to_Z b < (2%nat ^ n)%Z) -> True -> (((F.to_Z v < (2%nat ^ n)%Z) /\ (v = a)) -> (F.to_Z v < (2%nat ^ n)%Z)).
Proof. intuit. Qed.

Lemma LessEqThan_obligation2_trivial: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> (F.to_Z b < (2%nat ^ n)%Z) -> True -> (((F.to_Z v < (2%nat ^ n)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma LessEqThan_obligation3_trivial: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> (F.to_Z b < (2%nat ^ n)%Z) -> True -> ((v = 1%F) -> True).
Proof. intuit. Qed.

Lemma LessEqThan_obligation4: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> ((F.to_Z b + 1%nat)%Z < (2%nat ^ n)%Z) -> True -> ((v = (b + 1%F)%F) -> (F.to_Z v < (2%nat ^ n)%Z)).
Proof.
  unwrap_C. intuit. subst v.
  assert (^(b+1) = ^b + 1). {
    assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
    repeat autorewrite with F_to_Z; try lia.
    assert (H_y_nonneg: (0 <= F.to_Z b)%Z). apply F.to_Z_range. lia.
    lia.
  }
  lia.
Qed.

Lemma LessEqThan_obligation5: forall (n : nat) (a : F) (b : F) (v : F), (n < (C.k - 1%nat)%Z) -> (F.to_Z a < (2%nat ^ n)%Z) -> ((F.to_Z b + 1%nat)%Z < (2%nat ^ n)%Z) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z a < F.to_Z (b + 1%F)%F)) /\ ((v = 0%F) -> ~(F.to_Z a < F.to_Z (b + 1%F)%F)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z a <= F.to_Z b)) /\ ((v = 0%F) -> ~(F.to_Z a <= F.to_Z b))))).
Proof.
  unwrap_C. intros.
  assert (^(b+1) = ^b + 1). {
    assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
    repeat autorewrite with F_to_Z; try lia.
    assert (H_y_nonneg: (0 <= F.to_Z b)%Z). apply F.to_Z_range. lia.
    lia.
  }
  intuit. subst v.
  lia.
  lia.
Qed.


Lemma GreaterEqThan_obligation0: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z) -> ((F.to_Z x + 1%nat)%Z < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> ((((0%nat <= v) /\ (v < (C.k - 1%nat)%Z)) /\ (v = n)) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. intuit. Qed.

Lemma GreaterEqThan_obligation1: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z) -> ((F.to_Z x + 1%nat)%Z < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> (((F.to_Z v < (2%nat ^ n)%Z) /\ (v = y)) -> (F.to_Z v < (2%nat ^ n)%Z)).
Proof. intuit. Qed.

Lemma GreaterEqThan_obligation2: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z) -> ((F.to_Z x + 1%nat)%Z < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> ((((F.to_Z v + 1%nat)%Z < (2%nat ^ n)%Z) /\ (v = x)) -> ((F.to_Z v + 1%nat)%Z < (2%nat ^ n)%Z)).
Proof. intuit. Qed.

Lemma GreaterEqThan_obligation3_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z) -> ((F.to_Z x + 1%nat)%Z < (2%nat ^ n)%Z) -> (F.to_Z y < (2%nat ^ n)%Z) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z y <= F.to_Z x)) /\ ((v = 0%F) -> ~(F.to_Z y <= F.to_Z x)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z y <= F.to_Z x)) /\ ((v = 0%F) -> ~(F.to_Z y <= F.to_Z x))))).
Proof. intuit. Qed.
