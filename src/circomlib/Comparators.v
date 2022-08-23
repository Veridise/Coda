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

Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Circom.circomlib.Bitify.
Require Import Circom.Circom Circom.Util Circom.Default Circom.Repr.

Local Open Scope list_scope.
Local Open Scope F_scope.

(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Comparators (C: CIRCOM).
Import C.
Module B := Bitify C.
Module R := Repr C.
Import B C R.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Open Scope tuple_scope.


(***********************
 *       IsZero
 ***********************)

Module IsZero.

Definition cons (_in out _inv: F) :=
  out = 1 - _in * _inv /\
  _in * out = 0.

(* IsZero *)
Record t : Type := { _in: F; out: F; _cons: exists _inv, cons _in out _inv }.

(* IsZero spec *)
Definition spec (c: t) : Prop :=
  if (c.(_in) = 0)? then
    c.(out) = 1
  else
    c.(out) = 0.

(* IsZero is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros. destruct c as [x y [x_inv H]].
  unfold spec, cons in *. simpl.
  intuition.
  destruct (dec (x = 0)); fqsatz.
Qed.

(* Theorem IsZero_complete: forall (w: t),
  IsZero_spec w -> cons w.
Proof.
  unwrap_C. intros. destruct w as [_in out];
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

Definition cons (_in: F^2) (out: F) := 
  let x := _in[0] in
  let y := _in[1] in
  exists (isz: IsZero.t),
    isz.(IsZero._in) = (x - y) /\
    isz.(IsZero.out) = out.

Record t : Type := { _in: F^2; out: F; _cons: cons _in out }.

Theorem soundness: forall t,
  if ( t.(_in)[0] = t.(_in)[1] )? then
    t.(out) = 1
  else
    t.(out) = 0.
Proof.
  unwrap_C.
  intros t. destruct t as [_in out [isz [H1 H2]]].
  simpl.
  pose proof (IsZero.soundness isz) as H_isz. unfold IsZero.spec in H_isz.
  intuition.
  rewrite H1, H2 in *.
  destruct (dec (_in[0] = _in[1])); destruct (dec (_in[0] - _in[1] = 0)); try fqsatz.
Qed.

Lemma is_binary: forall c, binary c.(out).
Proof.
  intro. specialize (soundness c). intuition.
  destruct (dec (_in c [0] = _in c [1])). right. auto. left. auto.
Qed.

Lemma is_complete: forall t,
  t.(out) = 1 <-> t.(_in)[0] = t.(_in)[1].
Proof.
  unwrap_C. 
  intro c. specialize (soundness c).
   intuition; destruct (dec (_in c [0] = _in c [1])); (auto || fqsatz).
Qed.

Definition wgen : IsEqual.t. Admitted.
#[global] Instance IsEqual_Default: Default IsEqual.t. constructor. exact wgen. Defined.

End IsEqual.

(***********************
 *       LessThan
 ***********************)

Module LessThan.

Section LessThan.
Context {n: nat}.

Definition cons (_in: tuple F 2) (out: F) :=
  exists (n2b: Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = (_in [0] + 2^n - _in[1]) /\
    out = 1 - n2b.(Num2Bits.out)[n].

Record t: Type := {
  _in: F^2;
  out: F;
  _cons: cons _in out;
}.

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

Lemma soundness: forall (w : t),
  (* pre-conditions: both inputs are at most (k-1) bits *)
  n <= C.k - 1 ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  (* post-condition *)
  binary w.(out) /\
  let '(x, y) := (w.(_in)[0], w.(_in)[1]) in
  if (w.(out) = 1)? then
    x <q y
  else
    x >=q y.
Proof.
  unwrap_C. intros w H_nk Hx Hy. unfold in_range in Hx, Hy.
  remember (w.(_in)[0]) as x. remember (w.(_in)[1]) as y.
  destruct w as [_in out [n2b H]]. simpl in *.
  rewrite <- Heqx, <- Heqy in *.
  pose proof (Num2Bits.soundness _ n2b) as H_n2b.
  pose proof H_n2b as H_n2b'.
  unfold Num2Bits.spec in *. unfold repr_le2, repr_le in H_n2b.
  destruct H as [H_n Hout ].
  apply conj_use.
  intuition.
  - eapply one_minus_binary; eauto.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq. 
    apply Forall_nth. apply Forall_in_range. auto.
    lia.
  - assert (H_pow_nk: 2 * 2^n <= 2^k). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
    assert (H_x_nonneg: 0 <= F.to_Z x). apply F.to_Z_range. lia.
    assert (H_y_nonneg: 0 <= F.to_Z y). apply F.to_Z_range. lia.
    destruct (dec (out = 1)).
    + assert (Hn: Num2Bits.out [n] = 0) by fqsatz.
      rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
      remember (to_list (S n) Num2Bits.out) as n2bout.
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
    + destruct H0; try fqsatz. assert (Hn: Num2Bits.out [n] = 1) by fqsatz.
    rewrite H_n in *.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
    eapply repr_le_lb with (i:=n) in Hn; eauto; try lia.
    assert (F.to_Z x + 2^n - F.to_Z y >= 2^n). {
      autorewrite with F_to_Z in Hn; try lia;
      repeat autorewrite with F_to_Z; simpl; try lia.
      simpl in Hn. lia.
    }
    lia.
Qed.

Lemma is_binary: forall (w:t), 
  n <= C.k - 1 ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  binary w.(out).
Proof.
  intros. specialize (soundness w). intuition.
Qed.

Lemma is_sound: forall (w:t),
  n <= C.k - 1 ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  let '(x, y) := (w.(_in)[0], w.(_in)[1]) in
  if (w.(out) = 1)? then
    x <q y
  else
    x >=q y.
Proof.
  intros. specialize (soundness w). intuition.
Qed.

Lemma is_complete: forall (w:t),
  n <= C.k - 1 ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  w.(out) = 1 <-> w.(_in)[0] <q w.(_in)[1].
Proof.
  unwrap_C.
  intros. specialize (soundness w).
  intuition; destruct (dec (out w = 1)); (auto || fqsatz || lia).
Qed.

Definition wgen: LessThan.t. Admitted.

#[global] Instance LessThan_Default: Default LessThan.t. constructor. exact wgen. Defined.

End LessThan.
End LessThan.

End Comparators.