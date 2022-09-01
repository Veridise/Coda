Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.ZUtil Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

From Circom Require Import Circom Simplify.

Ltac invert H := inversion H; subst; clear H.

(* When proving Q in P /\ Q, we're allowed to assume P *)
Lemma conj_use: forall (P Q: Prop), P /\ (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

Ltac split_dec := 
  repeat match goal with
  | [ |- context[dec ?P] ] => destruct (dec P)
  | [ H: context[dec ?P] |- _ ] => destruct (dec P)
  end.

Ltac lrewrite :=
  repeat match goal with
  | [ H: ?x = _ |- context[?x] ] => rewrite H
  end.

Ltac intuit := intuition idtac.

Local Open Scope circom_scope.
Local Coercion Z.of_nat: nat >-> Z.

Lemma binary_in_range: forall (n:nat) x,
  n > 0 ->
  binary x -> 
  x | (n).
Proof.
  unwrap_C. intros n x Hn Hbin.
  destruct (dec (n>1)).
  destruct Hbin; subst; autorewrite with F_to_Z; try lia.
  assert (2^1 < 2^n)%Z. apply Zpow_facts.Zpower_lt_monotone; lia.
  transitivity (2^1)%Z; simpl; lia.
  assert (n=1)%nat by lia. subst. simpl. destruct Hbin; subst; autorewrite with F_to_Z; lia.
Qed.


Lemma one_minus_binary: forall (x y: F),
  (x = 1 - y)%F ->
  binary y ->
  binary x.
Proof.
  unwrap_C.
  intros.
  destruct H0; ((right; fqsatz) || (left; fqsatz)).
Qed.

Ltac split_and := match goal with
  | [ |- _ /\ _] => split
  end.