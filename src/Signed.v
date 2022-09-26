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

Definition to_Z (x: F) : Z := if dec (^x <= half) then ^x else ^x - q.

Notation "$ x" := (to_Z x) (at level 30).
Notation "| x |" := (Z.abs x) (at level 60).

Lemma to_Z_congruent: forall x, ^x ~ $x.
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

Lemma abs_lt (a b: Z):
  |a| < b ->
  -b < a < b.
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
  assert (0 <= ^(x + y) < q) by (apply F.to_Z_range; lia).
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
  assert (0 <= ^(x * y) < q) by (apply F.to_Z_range; lia).
  unfold to_Z in *. split_dec; try lia.
Qed.

Local Open Scope circom_scope.

Lemma le_sub1_r_pow: forall x a b,
  0 < x ->
  0 <= a ->
  a <= b - 1 ->
  x * x^a <= x^b.
Proof.
  intros.
  assert (a + 1 <= b) by lia.
  replace (x*x^a) with (x^(1+a)). apply Zpow_facts.Zpower_le_monotone. lia.
  lia.
  rewrite Zpower_exp; try lia.
Qed.

Lemma le_sub1_l_pow: forall x a b,
  0 < x ->
  0 <= a ->
  0 <= b ->
  a - 1 <= b  ->
  x^a <= x * x^b.
Proof.
  intros.
  assert (a <= b+1) by lia.
  replace (x*x^b) with (x^(1+b)). apply Zpow_facts.Zpower_le_monotone. lia.
  lia.
  rewrite Zpower_exp; try lia.
Qed.

Lemma pow_sub_l_le: forall x a b c,
  0 < x ->
  0 <= b <= a ->
  x^(a-b) <= c <->
  x^a <= x^b * c.
Proof.
  intros. assert (0 <= x ^ b) by lia.
  replace (x^a) with (x^(b + (a-b))) by (f_equal; lia).
  rewrite Zpower_exp in * by lia.
  nia.
Qed.

Lemma pow_sub_r_le: forall x a b c,
  0 < x ->
  0 <= b <= a ->
  c <= x^(a-b) <->
  x^b * c <= x^a.
Proof.
  intros. assert (0 <= x ^ b) by lia.
  replace (x^a) with (x^(b + (a-b))) by (f_equal; lia).
  rewrite Zpower_exp in * by lia.
  nia.
Qed.

Lemma half_lb: 2^(k-1) <= q//2.
Proof.
  unwrap_C.
  destruct half_spec.
  apply pow_sub_l_le; try lia.
Qed.

Lemma lt_pow: forall a b x,
  1 < x ->
  0 <= a < b -> 
  x^a < x^b.
Proof.
  intros. apply Zpow_facts.Zpower_lt_monotone; lia.
Qed.

Lemma le_pow: forall a b x,
  1 < x ->
  0 <= a < b -> 
  x^a <= x^b.
Proof.
  intros. apply Zpow_facts.Zpower_le_monotone; lia.
Qed.

Lemma pow_2_k_sub_1: 2 <= 2^(k-1).
Proof.
  unwrap_C.
  (* assert (2^1 < 2^k). apply lt_pow; lia. *)
  replace (2 <= 2^(k-1)) with (2^1 <= 2^(k-1)).
  apply Zpow_facts.Zpower_le_monotone; try lia.
  f_equal.
Qed.

Lemma half_ge_2: 2 <= q//2.
Proof.
  etransitivity. apply pow_2_k_sub_1. apply half_lb.
Qed.

Lemma to_Z_2_pow: forall (n:N),
  n <= k - 1 ->
  $((2:F) ^ n) = $(2:F) ^ n.
Proof.
  unwrap_C.
  intros n Hnk. unfold to_Z.
  pose proof Hnk as Hnk'.
  apply (le_sub1_r_pow 2) in Hnk; try lia.
  pose proof half_ge_2.
  destruct half_spec as [half_spec half_spec'].
  repeat (autorewrite with F_to_Z; try lia);
  try (simpl; lia).
  split_dec; try lia.
  exfalso. apply n0.
  etransitivity.
  2: { apply half_lb. }
  simpl.
  apply Zpow_facts.Zpower_le_monotone; try lia.
Qed.


Lemma to_Z_0: $0 = 0.
Proof.
  unwrap_C.
  unfold to_Z.
  autorewrite with F_to_Z; try lia.
  split_dec.
  auto.
  pose proof half_spec.
  lia.
Qed.

Lemma to_Z_1: $1 = 1.
Proof.
  unwrap_C.
  unfold to_Z. 
  autorewrite with F_to_Z; try lia.
  split_dec.
  auto.
  pose proof half_spec.
  lia.
Qed.

Lemma to_Z_2: $2 = 2%Z.
Proof.
  unwrap_C.
  unfold to_Z. 
  autorewrite with F_to_Z; try lia.
  split_dec.
  auto.
  pose proof half_spec.
  pose proof half_geq_2. lia.
Qed.



End Signed.

Notation "$ x" := (Signed.to_Z x) (at level 30) : circom_scope.