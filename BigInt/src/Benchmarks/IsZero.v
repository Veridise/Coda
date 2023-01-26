(** * DSL benchmark IsZero *)

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

Lemma _obligation1: forall (inv : F) (_in : F) (out : F),
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
