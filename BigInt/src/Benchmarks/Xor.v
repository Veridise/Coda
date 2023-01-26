(** * DSL benchmark XOR *)

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

(** ** Proof obligations from typechecking *)

Definition f_xor (x: F) (y: F) := x <> y.

Lemma _obligation1: forall (a : F) (b : F) (out : F),
    ((a = 0%F) \/ (a = 1%F)) ->
    ((b = 0%F) \/ (b = 1%F)) -> True ->
    (out = ((a + b) - ((1 + 1)%F * (a * b)))) ->
    (((out = 0%F) \/ (out = 1%F)) /\ (((out = 1%F) -> (f_xor a b)) /\ ((out = 0%F) -> ~(f_xor a b)))).
Proof.
  unwrap_C. unfold f_xor. intros.
  intuit; try fqsatz; subst; auto.
  - left. fqsatz.
  - right. fqsatz.
  - right. fqsatz.
  - left. fqsatz.
Qed.
