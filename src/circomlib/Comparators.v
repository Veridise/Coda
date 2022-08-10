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
Module B := Bitify C.
Import B C.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Notation "w [ i ]" := (Tuple.nth_default 0 i w).

(***********************
 *       IsZero
 ***********************)

Module IsZero.

Definition cons (_in _out _inv: F) :=
  _out = 1 - _in * _inv /\
  _in * _out = 0.

(* IsZero *)
Class t : Type := mk { _in: F; _out: F; _cons: exists _inv, cons _in _out _inv }.

(* IsZero spec *)
Definition spec (c: t) : Prop :=
  (c.(_in) = 0 -> c.(_out) = 1) /\
  (~(c.(_in) = 0) -> c.(_out) = 0).

(* IsZero is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros. destruct c as [_in _out].
  unfold spec, cons in *. simpl. destruct _cons0.
  simpl.
  split_eqns;
  intros;
  split_eqns. fqsatz. fqsatz.
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
  destruct _cons0 as [iszero H].
  pose proof (IsZero.soundness iszero).
  unfold IsZero.spec in *.
  simpl in *.
  split_eqns.
  (* FIXME: automate this *)
  - assert (IsZero._in = 0) by fqsatz.
    intuition idtac. fqsatz.
  - assert (IsZero._in <> 0) by fqsatz. intuition idtac. fqsatz.
(* FIXME: type error *)
Admitted.

End IsEqual.

(***********************
 *       LessThan
 ***********************)

Module LessThan.

Definition cons (n: nat) (_in: tuple F 2) (_out: F) :=
  exists (n2b: Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = (_in [0] + 2^n - _in[1]) /\
    _out = 1 - n2b.(Num2Bits._out)[n].

Class t (n: nat): Type := mk {
  _in: tuple F 2;
  _out: F;
  _cons: cons n _in _out;
}.

Definition spec (n: nat) (w: t n) :=
  (binary _out) /\
  (_out = 1 -> w.(_in)[0] <q w.(_in)[1]) /\
  (_out = 0 -> w.(_in)[0] >=q w.(_in)[1]).

Lemma one_minus_binary: forall (x y: F),
  x = 1 - y ->
  binary y ->
  binary x.
Proof.
  unwrap_C.
  intros.
  destruct H0; ((right; fqsatz) || (left; fqsatz)).
Qed.

Lemma to_Z_sub: forall x y, F.to_Z y < q ->
@F.to_Z q (x - y) = (F.to_Z x - F.to_Z y mod q) mod q.
Proof.
  unwrap_C.
  intros ? ? Hy. unfold F.sub. rewrite F.to_Z_add. rewrite F.to_Z_opp.
  destruct (dec (F.to_Z y = 0)%Z).
  - rewrite e. rewrite Z_mod_zero_opp_full. replace (F.to_Z x + 0)%Z with (F.to_Z x - 0)%Z by lia. reflexivity.
    apply Zmod_0_l.
  - rewrite Z_mod_nz_opp_full.
    replace (F.to_Z x + (q - F.to_Z y mod q))%Z with ((F.to_Z x - F.to_Z y mod q) + 1 * q)%Z by lia.
    rewrite Z_mod_plus by lia.
    reflexivity.
    rewrite Z.mod_small. auto.
    apply F.to_Z_range. lia.
Qed.


Create HintDb F_to_Z discriminated.
Hint Rewrite (@F.to_Z_add q) : F_to_Z.
Hint Rewrite (@F.to_Z_mul q) : F_to_Z.
Hint Rewrite (@F.to_Z_pow q) : F_to_Z.
Hint Rewrite (@F.to_Z_1 q) : F_to_Z.
Hint Rewrite (to_Z_2) : F_to_Z.
Hint Rewrite (@F.pow_1_r q) : F_to_Z.
Hint Rewrite to_Z_sub : F_to_Z.
Hint Rewrite Z.mod_small : F_to_Z.


Lemma soundness: forall (n: nat) (w : t n)
  (H_nk: n <= k - 1)
  (H_x: 0 <= F.to_Z (w.(_in)[0]) <= 2 ^ n )
  (H_y: 0 <= F.to_Z (w.(_in)[1]) <= 2 ^ n ),
  spec n w.
Proof.
  unwrap_C. intros. unfold spec.
  remember (_in[0]) as x. eremember (_in[1]) as y.
  destruct w as [_in _out _cons].
  unfold binary. unfold cons in *.
  destruct _cons as [n2b H].
  cbn [LessThan._in LessThan._out] in *.
  assert (H_pow_nk: 2 * 2^n <= 2^k). {
    replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  rewrite <- Heqx, <- Heqy in *.
  pose proof (Num2Bits.soundness _ n2b) as H_n2b.
  pose proof H_n2b as H_n2b'.
  unfold Num2Bits.spec in *. unfold repr_le2, repr_le in H_n2b.
  destruct H as [H_n H_out ].
  intuition.
  - eapply one_minus_binary; eauto.
    rewrite <- nth_default_to_list, nth_default_eq. apply Forall_nth. apply Forall_in_range. auto.
    lia.
  - assert (Hn: Num2Bits._out [n] = 0) by fqsatz.
    rewrite <- nth_default_to_list, nth_default_eq in Hn.
    remember (to_list (S n) Num2Bits._out) as n2b_out.
      unfold repr_le2 in *.
      eapply repr_le_last0' in Hn. 2: { rewrite H_n in H_n2b'. apply H_n2b'. }
      fold repr_le2 in Hn.
      apply repr_le_ub in Hn; try lia.
    assert (F.to_Z x + 2^n - F.to_Z y <= 2^n - 1 ). {
      autorewrite with F_to_Z in Hn; try lia;
      repeat autorewrite with F_to_Z; simpl; try lia.
      simpl in Hn. lia.
    }
    lia.
  - assert (Hn: Num2Bits._out [n] = 1) by fqsatz.
    rewrite H_n in *.
    rewrite <- nth_default_to_list, nth_default_eq in Hn.
    eapply repr_le_lb with (i:=n) in Hn; eauto; try lia.
    assert (F.to_Z x + 2^n - F.to_Z y >= 2^n). {
      autorewrite with F_to_Z in Hn; try lia;
      repeat autorewrite with F_to_Z; simpl; try lia.
      simpl in Hn. lia.
    }
    lia.
Qed.

End LessThan.

End Comparators.