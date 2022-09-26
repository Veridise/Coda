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
  Parameter k: Z.
  Axiom prime_q: prime q.
  Axiom two_lt_q: 2 < q.
  Axiom k_lb: 2 <= k.
  Axiom q_lb: 2^k < q.
  Axiom q_gtb_1: (1 <? q)%positive = true.
End CIRCOM.


Module C : CIRCOM.
Definition q := BabyJubjub.p.
Definition k := 253.

Fact prime_q: prime q.
Proof. exact BabyJubjub.is_prime. Qed.

Fact two_lt_q: 2 < q.
Proof. unfold q, BabyJubjub.p. lia. Qed.

Fact k_lb: 2 <= k.
Proof. unfold k. lia. Qed.

Fact q_lb: 2^k < q.
Proof. unfold k, q, BabyJubjub.p. lia. Qed.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  pose proof two_lt_q.
  apply Pos.ltb_lt. lia.
Qed.

End C.


Export C.

Global Hint Rewrite q_gtb_1 : circom.
Global Hint Rewrite two_lt_q : circom.
Global Ltac fqsatz := fsatz_safe; autorewrite with circom; auto.
Global Ltac unwrap_C :=
  pose proof prime_q as prime_q;
  pose proof two_lt_q as two_lt_q;
  pose proof k_lb as k_lb;
  pose proof q_lb as q_lb.

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
Global Notation "^ x" := (@F.to_Z q x) (at level 30): circom_scope.


(* Facts about q/2 *)
Definition half := q / 2.
Notation "q//2" := half.

Lemma prime_odd: forall p,
  prime p ->
  p > 2 ->
  p mod 2 = 1.
Proof.
  intros.
  assert (rel_prime p 2). apply rel_prime_sym, H. lia.
  apply Zrel_prime_neq_mod_0 in H1; try lia.
  assert (0 <= p mod 2 < 2). apply Z_mod_lt. lia.
  lia.
Qed.

Lemma half_spec:
  q//2 + q//2 < q /\
  q <= q//2 + q//2 + 1.
Proof.
  unwrap_C.
  unfold half.
  replace (q / 2 + q / 2) with (q / 2 * 2) by lia.
  rewrite Modulo.Z.mul_div_eq' by lia.
  assert (0 <= q mod 2 < 2). apply Z_mod_lt. lia.
  rewrite prime_odd; auto; lia.
Qed.

Lemma half_lt_q: q//2 + q//2 < q.
Proof. pose proof half_spec. easy. Qed.

Lemma half_gt_q: q <= q//2 + q//2 + 1.
Proof. pose proof half_spec. easy. Qed.

Lemma half_geq_2: 2 <= q//2.
Proof.
  unwrap_C.
  assert (2*2 <= 2* q//2). {
    unfold half.
    replace (2*(q/2)) with ((q / 2) * 2) by nia.
    rewrite Modulo.Z.mul_div_eq' by lia.
    assert (0 <= q mod 2 < 2). apply Z_mod_lt. lia.
    rewrite prime_odd; auto; try lia.
    assert (2^2 <= q - 1).
    transitivity (2^k).
    apply Zpow_facts.Zpower_le_monotone; try lia.
    lia.
    lia.
  }
  lia.
Qed.


Lemma pow_nonzero: forall (a: N),
  a <= k -> 
  @F.pow q (F.add F.one F.one) a <> F.zero.
Admitted.

Lemma to_Z_2pow: forall (a: N), a <= k -> 
  ^(@F.pow q (F.add F.one F.one) a) = 2^a.
Admitted.

Local Close Scope circom_scope.
