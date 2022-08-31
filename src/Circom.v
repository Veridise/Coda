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
Require Import Crypto.Util.Decidable.

Require Import Circom.BabyJubjub.
(* Require Import Circom.Tuple. *)
(* Require Import Crypto.Util.Decidable Crypto.Util.Notations. *)
(* Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac. *)

Module Type CIRCOM.
  Parameter q: positive.
  Parameter r: Z.
  Parameter k: Z.
  Axiom prime_q: prime q.
  Axiom two_lt_q: 2 < q.
  Axiom r_k: r = k - 1.
  Axiom k_positive: 1 < k.
  Axiom q_lb: 2^k < q.
  Axiom q_gtb_1: (1 <? q)%positive = true.
  Axiom pow_nonzero: forall (a: N), a <= k -> @F.pow q (F.add F.one F.one) a <> F.zero.
  Axiom to_Z_2pow: forall (a: N), a <= k -> F.to_Z (@F.pow q (F.add F.one F.one) a) = 2^a.
End CIRCOM.


Module C : CIRCOM.
Definition q := BabyJubjub.p.
Definition k := 253.
Definition r := 252.

Fact r_k: r = k - 1.
Proof. unfold r, k. lia. Qed.

Fact prime_q: prime q.
Proof. exact BabyJubjub.is_prime. Qed.

Fact two_lt_q: 2 < q.
Proof. unfold q, BabyJubjub.p. lia. Qed.

Fact k_positive: 1 < k.
Proof. unfold k. lia. Qed.

Fact q_lb: 2^k < q.
Proof. unfold k, q, BabyJubjub.p. lia. Qed.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  pose proof two_lt_q.
  apply Pos.ltb_lt. lia.
Qed.

Lemma pow_nonzero: forall (a: N), 
  a <= k -> 
  @F.pow q (F.add F.one F.one) a <> F.zero.
Admitted.

Lemma to_Z_2pow: forall (a: N), 
  a <= k -> 
  F.to_Z (@F.pow q (F.add F.one F.one) a) = 2^a.
Admitted.

End C.


Export C.

Global Hint Rewrite q_gtb_1 : circom.
Global Hint Rewrite two_lt_q : circom.
Global Ltac fqsatz := fsatz_safe; autorewrite with circom; auto.
Global Ltac unwrap_C :=
  pose proof prime_q as prime_q;
  pose proof two_lt_q as two_lt_q;
  pose proof k_positive as k_positive;
  pose proof q_lb as q_lb;
  pose proof pow_nonzero as pow_nonzero;
  pose proof to_Z_2pow as to_Z_2pow.

Declare Scope circom_scope.
Delimit Scope circom_scope with circom.
  
Global Notation "x <z y" := (F.to_Z x < y) (at level 50) : circom_scope.
Global Notation "x <=z y" := (F.to_Z x <= y) (at level 50) : circom_scope.
Global Notation "x >z y" := (F.to_Z x > y) (at level 50) : circom_scope.
Global Notation "x >=z y" := (F.to_Z x >= y) (at level 50) : circom_scope.

Global Notation "x <q y" := (F.to_Z x < F.to_Z y) (at level 50) : circom_scope.
Global Notation "x <=q y" := (F.to_Z x <= F.to_Z y) (at level 50) : circom_scope.
Global Notation "x >q y" := (F.to_Z x > F.to_Z y) (at level 50) : circom_scope.
Global Notation "x >=q y" := (F.to_Z x >= F.to_Z y) (at level 50) : circom_scope.

Global Notation F := (ModularArithmetic.F q).

Global Notation "2" := (F.add F.one F.one : F) : circom_scope.

Definition binary (x: F) := x = F.zero \/ x = F.one.

Global Notation "P '?'" :=
(match (@dec P _) with
  | left _ => true
  | right _ => false
  end)
(at level 100).

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion N.of_nat : nat >-> N.
Local Open Scope circom_scope.

Global Notation "x | ( n )" := (x <=z (2^n-1)%Z) (at level 40) : circom_scope.
Global Notation "xs |: ( n )" := (List.Forall (fun x => x | (n)) xs) (at level 40) : circom_scope.
Global Notation "|^ x |" := (@F.to_Z q x) : circom_scope.

Local Close Scope circom_scope.
