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
From Circom Require Import Circom DSL.

Ltac invert H := inversion H; subst; clear H.

(* When proving Q in P /\ Q, we're allowed to assume P *)
Lemma conj_use: forall (P Q: Prop), P /\ (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

(* Remember the iterating function *)
Ltac rem_iter :=   
  repeat match goal with
  | [ _: context[DSL.iter ?f _ _] |- _] =>
    match f with
    | fun _ => _ => let fn := fresh "f" in remember f as fn
    | _ => fail
    end
  end.