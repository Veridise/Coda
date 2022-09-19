Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.ZArith.Znat.
Require Import Coq.Classes.Equivalence.
Require Import Setoid Morphisms.


Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.


From Circom Require Import Circom Util LibTactics Simplify.


Module Signed.
Local Open Scope circom_scope.
Local Open Scope Z_scope.


Definition cong := eqm q.
Infix "~" := cong (at level 70).

#[local]Instance cong_setoid : Equivalence cong.
Proof. unfold cong, eqm. constructor; eauto with *. Qed.


#[local]Instance Zplus_cong : Proper (cong ==> cong ==> cong) Zplus.
Proof.
  unfold cong, eqm; repeat red; intros. rewrite Zplus_mod, H, H0, <- Zplus_mod; auto.
Qed.

#[local]Instance Zminus_cong : Proper (cong ==> cong ==> cong) Zminus.
Proof.
  unfold cong, eqm; repeat red; intros. rewrite Zminus_mod, H, H0, <- Zminus_mod; auto.
Qed.

#[local]Instance Zmult_cong : Proper (cong ==> cong ==> cong) Zmult.
Proof.
  unfold cong, eqm; repeat red; intros. rewrite Zmult_mod, H, H0, <- Zmult_mod; auto.
Qed.


Lemma cong_add_eqmruence (a a' b b': Z):
  a ~ a' ->
  b ~ b' ->
  a + b ~ a' + b'.
Proof.
  intros.
  rewrite H, H0. eauto with *.
Qed.

Lemma cong_mul_eqmruence (a a' b b': Z):
  a ~ a' ->
  b ~ b' ->
  a * b ~ a' * b'.
Proof.
  intros. rewrite H, H0. eauto with *.
Qed.

Lemma pow_r: 2 * 2^r <= 2^k.
Proof.
  unwrap_C. pose proof r_k.
  replace (2*2^r) with (2^(r+1)).
  apply Zpow_facts.Zpower_le_monotone; try lia.
  rewrite Zpower_exp; simplify.
Qed.

Definition to_Z (x: F) : Z := if dec (|^x| <= half) then |^x| else |^x| - q.

Notation "$ x" := (to_Z x) (at level 30).
Notation "| x |" := (Z.abs x) (at level 60).
Notation "x <=$ y" := (-y <= x <= y) (at level 50).
Notation "x <$ y" := (-y < x < y) (at level 65).

Notation "q//2" := half.

Lemma to_Z_congruent: forall x, |^x| ~ $x.
Proof.
  intros. unfold to_Z. split_dec.
  - reflexivity.
  - unfold cong, eqm. rewrite Zminus_mod.
    rewrite Z_mod_same_full. simplify. rewrite Zmod_mod. auto.
Qed.

Lemma Zabs_spec: forall a,
  |a| = if (a >= 0)? then a else -a.
Proof.
  intros.
  pose proof (Zabs.Zabs_spec a).
  split_dec; intuit; lia.
Qed.

Lemma triangle_add (a b: Z):
  |a + b| <= |a| + |b|.
Proof.
  repeat rewrite Zabs_spec.
  split_dec; lia.
Qed.

Lemma triangle_mul (a b: Z):
  |a * b| <= |a| * |b|.
Proof.
  repeat rewrite Zabs_spec.
  split_dec; lia.
Qed.

Axiom half_spec:
  q//2 + q//2 < q /\
  q//2 + q//2 + 1 >= q.

Lemma abs_lt (a b: Z):
  |a| < b ->
  a <$ b.
Proof.
  pose proof (Zabs_spec a).
  intuit; split_dec; lia.
Qed.

Lemma Zmod_mod': forall a,
  a mod q ~ a.
Proof. intros. repeat red. rewrite Zmod_mod. auto. Qed.

Lemma leq_lt_sub: forall x y a b,
  a - y <= x < b - y ->
  a <= x + y < b.
Proof. intros. lia. Qed.


Lemma to_Z_add: forall x y,
  (|$x| + |$y|) < q//2 ->
  $(x + y) = $x + $y.
Proof.
  intros.
  assert ($ (x + y) ~ $x + $y).
  etransitivity.
  symmetry.
  apply to_Z_congruent.
  rewrite F.to_Z_add.
  rewrite Zmod_mod'.
  erewrite cong_add_eqmruence with (a:=$x) (b:=$y).
  reflexivity.
  symmetry. apply to_Z_congruent.
  symmetry. apply to_Z_congruent.
  
  assert (H1: $ (x + y) + q//2 ~ ($x + $ y) + q//2). {
    eapply cong_add_eqmruence; auto. reflexivity.
  }
  assert (H2: |$x + $y| < q//2). {
    eapply Z.le_lt_trans.
    apply triangle_add.
    auto.
  }
  unfold eqm in *.
  pose proof half_spec. intuit.
  apply abs_lt in H2.
  repeat red in H1.
  rewrite ?Zmod_small in H1;
  try lia.
  assert (0 <= |^ x + y | < q) by (apply F.to_Z_range; lia).
  unfold to_Z in *. split_dec; try lia.
Qed.

Lemma to_Z_mul: forall x y,
  (|$x| * |$y|) < q//2 ->
  $(x * y) = $x * $y.
Proof.
  intros.
  assert ($ (x * y) ~ $x * $y). {
    etransitivity.
    symmetry. apply to_Z_congruent.
    rewrite F.to_Z_mul.
    rewrite Zmod_mod'.
    erewrite cong_mul_eqmruence with (a:=$x) (b:=$y).
    reflexivity.
    symmetry. apply to_Z_congruent.
    symmetry. apply to_Z_congruent.
  }
  assert (H1: $ (x * y) + q//2 ~ ($x * $ y) + q//2). {
    eapply cong_add_eqmruence; auto. reflexivity.
  }
  assert (H2: |$x * $y| < q//2). {
    eapply Z.le_lt_trans.
    apply triangle_mul.
    auto.
  }
  unfold eqm in *.
  pose proof half_spec. intuit.
  apply abs_lt in H2.
  repeat red in H1.
  rewrite ?Zmod_small in H1;
  try lia.
  assert (0 <= |^ x * y | < q) by (apply F.to_Z_range; lia).
  unfold to_Z in *. split_dec; try lia.
Qed.

End Signed.