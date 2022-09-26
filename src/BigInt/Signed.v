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

(* Local Coercion Zpos: positive >-> Z. *)

Definition cong (a: Z) (b: Z) := a mod q = b mod q.
Local Infix "~" := cong (at level 70).

Lemma cong_reflexive: forall x, x ~ x.
Admitted.

#[local]Instance Equivalence_cong: Equivalence cong.
Admitted.

Lemma cong_add: forall x, x ~ x + q.
Admitted.

Lemma cong_sub: forall x, x ~ x - q.
Admitted.

Lemma pow_r: 2 * 2^r <= 2^k.
Proof.
  unwrap_C. pose proof r_k.
  replace (2*2^r) with (2^(r+1)).
  apply Zpow_facts.Zpower_le_monotone; try lia.
  rewrite Zpower_exp; simplify.
Qed.

Lemma add_mod: forall a b,
  (a + b) mod b = a mod b.
Admitted.

Lemma sub_mod: forall a b,
  (a - b) mod b = a mod b.
Admitted.

Definition to_Z (x: F) : Z := if dec (|^x| <= half) then |^x| else |^x| - q.

Notation "$ x" := (to_Z x) (at level 10).
Notation "| x |" := (Z.abs x) (at level 70).
Notation "x <=$ y" := (-y <= x <= y) (at level 50).
Notation "x <$ y" := (-y < x < y) (at level 50).
Notation "q//2" := half.

Lemma to_Z_congruent: forall x, |^x| ~ $x.
Proof.
  intros. unfold to_Z. split_dec.
  - reflexivity.
  - apply cong_sub.
Qed.

Lemma to_Z_add: forall x y,
  |$x + $y| < q//2 ->
  $(x + y) = $x + $y.
Admitted.

Lemma to_Z_mult: forall x y,
  |$x * $y| < q//2 ->
  $(x * y) = $x * $y.