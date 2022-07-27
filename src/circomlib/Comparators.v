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

Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Circom.circomlib.Bitify.
Require Import Circom.Circom.

Local Open Scope list_scope.
Local Open Scope F_scope.

(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Comparators (C: CIRCOM).
Import C.
Module B := (Bitify C).
Import B.

(***********************
 *       IsZero
 ***********************)

Module IsZero.

(* IsZero constraints *)
Definition cons (_in _out _inv: F) :=
  _out = 1 - _in * _inv /\
  _in * _out = 0.

(* IsZero *)
Class t : Type := mk { _in: F; _out: F; _cons: exists _inv, cons _in _out _inv }.

(* IsZero spec *)
Definition spec (w: t) : Prop :=
  (w.(_in) = 0 -> w.(_out) = 1) /\
  (~(w.(_in) = 0) -> w.(_out) = 0).

(* IsZero is sound *)
Theorem soundness:
  forall (w: t), spec w.
Proof.
  unwrap_C.
  intros.
  destruct w as [_in _out].
  unfold spec, cons in *.
  simpl.
  split_eqns;
  intros;
  split_eqns; fqsatz.
Qed.

(* Theorem IsZero_complete: forall (w: t),
  IsZero_spec w -> cons w.
Proof.
  unwrap_C. intros. destruct w as [_in _out];
  unfold cons, IsZero_template, IsZero_spec, IsZero_cons in *;
  intros.
  - destruct (dec (_in = 0)).
    + exists 1; split_eqns; intuition idtac; fqsatz.
    + exists (1/_in). destruct H as [_ H]. specialize (H n).
      split_eqns; fqsatz.
Qed. *)

End IsZero.

(***********************
 *       IsEqual
 ***********************)

Module IsEqual.

(* Hint Extern 10 (_ = _) => fqsatz : core. *)
(* Hint Extern 10 (_ <> _) => fqsatz : core. *)

(* Ltac extract :=
  match goal with
  | [ H: forall _ : ?a = _?b, _ |- _] => assert (a=b) by fqsatz; intuition idtac
  | [ H: forall _ : ?a <> _?b, _ |- _] => assert (a<>b) by fqsatz; intuition idtac
  end. *)

(* TODO: how to encode anonymous circuit instantiation? *)
Definition cons x y _out := exists (isz: IsZero.t),
    isz.(IsZero._in) = (x - y) /\
    _out = isz.(IsZero._out).

Class t : Type := mk { x: F; y: F; _out: F; _cons: cons x y _out }.

Definition spec t :=
  (t.(x) = t.(y) -> t.(_out) = 1) /\ (~ t.(x) = t.(y) -> t.(_out) = 0).

Theorem soundness: forall t, spec t.
Proof.
  unwrap_C.
  intros t. destruct t as [x y _out].
  unfold spec, cons in *.
  destruct _cons0.
  pose proof (IsZero.soundness x0).
  unfold IsZero.spec in H.
  simpl in *.
  split_eqns.
  (* FIXME: automate this *)
  - assert (IsZero._in = 0) by fqsatz.
    intuition idtac. fqsatz.
  - assert (IsZero._in <> 0) by fqsatz. intuition idtac. fqsatz.
(* FIXME: type error *)
Admitted.

End IsEqual.


(* (***********************
 *      IsNotEqual
 ***********************)
Definition IsNotEqual_cons x y _out _tmp :=
  IsEqualTemplate x y _tmp /\ _out = 1 - _tmp.

Definition IsNotEqualTemplate x y _out :=
  exists _tmp, IsNotEqual_cons x y _out _tmp.

(* IsNotEqual *)
Class IsNotEqual : Type := mkIsNotEqual { 
  x: F; 
  y: F; 
  out: F; 
  cons: IsNotEqualTemplate x y out
}.

Definition IsNotEqual_spec (x y _out: F) :=
  (x = y -> _out = 0) /\ (~ x = y -> _out = 1).

Theorem IsNotEqual_correct: forall x y _out,
  IsNotEqualTemplate x y _out -> IsNotEqual_spec x y _out.
Proof.
  unfold IsNotEqualTemplate, IsNotEqual_spec, IsNotEqual_cons.
  intros.
  destruct H as [inv [Heq Hout] ].
  apply IsEqual_correct in Heq. unfold IsEqual_spec in Heq.
  split_eqns; intuition; fqsatz. 
Qed.

(* use Record to repr template *)
Theorem IsNotEqualSoundness: 
  forall (t : IsNotEqual), IsNotEqual_spec t.(x) t.(y) t.(out).
Proof.
  intros. apply IsNotEqual_correct. exact t.(cons).
Qed.
 *)

(***********************
 *       LessThan
 ***********************)

Module LessThan.

Local Notation "2" := (1 + 1 : F).

Local Open Scope B_scope.

Definition LessThan_cons (n: nat) (_in: tuple F 2) (_out: F) :=
  exists (n2b: Num2Bits.t),
    n2b.(Num2Bits.n) = S n /\
    n2b.(Num2Bits._in) = (_in [0] + 2^(N.of_nat n) - _in[1]) /\
    _out = 1 - n2b.(Num2Bits._out)[n].

Class t: Type := mk {
  n: nat;
  _in: tuple F 2;
  _out: F
}.

End LessThan.

End Comparators.