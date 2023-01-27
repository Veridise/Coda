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

From Circom Require Import Circom Util Default Tuple LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope F_scope.

(** ** Proof obligations for IsZero *)

Lemma iszero_obligation1: forall (inv : F) (_in : F) (out : F),
    True -> True -> True ->
    (out = (1%F - (_in * inv))) ->
    ((_in * out) = 0%F) ->
    (((out = 0%F) \/ (out = 1%F)) /\ (((out = 1%F) -> (_in = 0%F)) /\ ((out = 0%F) -> ~(_in = 0%F)))).
Proof.
  unwrap_C. intros. intuition.
  destruct (dec (_in = 0)).
  - right. fqsatz.
  - left. fqsatz.
  - fqsatz.
  - fqsatz.
Qed.

(** ** Proof obligations for IsEqual *)

Lemma isequal_obligation1: forall (nu : F) (x : F) (y : F) (out : F),
    True -> True -> True -> (nu = (x - y)) -> True.
Proof.
  auto.
Qed.

Lemma isequal_obligation2: forall (x : F) (y : F) (out : F) (z : F),
    True -> True -> True ->
    (((z = 0%F) \/ (z = 1%F)) /\
       (((z = 1%F) -> ((x - y) = 0%F)) /\
          ((z = 0%F) -> ~((x - y) = 0%F)))) ->
    (out = z) ->
    (((out = 0%F) \/ (out = 1%F)) /\ (((out = 1%F) -> (x = y)) /\ ((out = 0%F) -> ~(x = y)))).
Proof.
  unwrap_C. intros. subst.
  destruct H2 as [H2 [H2' H2'']].
  intuit.
  - subst. apply H2. fqsatz.
  - fqsatz.
Qed.
