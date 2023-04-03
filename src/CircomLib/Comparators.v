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

Local Open Scope list_scope.
Local Open Scope F_scope.

(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Comparators.
Module B := Bitify.
Module R := Repr.
Import B R.


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

Definition wgen: t. skip. Defined.

#[global] Instance IsZero_Default: Default t. constructor. exact wgen. Defined.

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

Definition wgen : IsEqual.t. skip. Defined.
#[global] Instance IsEqual_Default: Default IsEqual.t. constructor. exact wgen. Defined.

End IsEqual.

(***********************
 *       LessThan
 ***********************)

Module LessThan.

Section LessThan.
Context {n: nat}.

Definition cons (_in: tuple F 2) (out: F) :=
  exists (n2b: @Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = (_in [0] + 2^n - _in[1]) /\
    out = 1 - n2b.(Num2Bits.out)[n].

Record t: Type := {
  _in: F^2;
  out: F;
  _cons: cons _in out;
}.


Lemma soundness: forall (w : t),
  (* pre-conditions: both inputs are at most (k-1) bits *)
  (n <= C.k - 1)%Z ->
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
  unwrap_C. intros w H_nk Hx Hy.
  remember (w.(_in)[0]) as x. remember (w.(_in)[1]) as y.
  destruct w as [_in out [n2b H]]. simpl in *.
  rewrite <- Heqx, <- Heqy in *.
  pose proof (Num2Bits.soundness n2b) as H_n2b.
  pose proof H_n2b as H_n2b'.
  unfold repr_le2, repr_le in H_n2b.
  destruct H as [H_n Hout ].
  apply conj_use.
  intuition.
  - eapply one_minus_binary; eauto.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq. 
    apply Forall_nth. apply Forall_in_range. auto.
    lia.
  - assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
    assert (H_x_nonneg: (0 <= F.to_Z x)%Z). apply F.to_Z_range. lia.
    assert (H_y_nonneg: (0 <= F.to_Z y)%Z). apply F.to_Z_range. lia.
    destruct (dec (out = 1)).
    + assert (Hn: Num2Bits.out n2b [n] = 0) by fqsatz.
      rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
      remember (to_list (S n) (Num2Bits.out n2b)) as n2bout.
        unfold repr_le2 in *.
        eapply repr_le_last0' in Hn. 2: { rewrite H_n in H_n2b'. apply H_n2b'. }
        fold repr_le2 in Hn.
        apply repr_le_ub in Hn; try lia.
      assert (F.to_Z x + 2^n - F.to_Z y <= 2^n - 1 )%Z. {
        autorewrite with F_to_Z in Hn; try lia;
        repeat autorewrite with F_to_Z; simpl; try lia.
        simpl in Hn. lia.
      }
      lia.
    + destruct H0; try fqsatz. assert (Hn: Num2Bits.out n2b [n] = 1) by fqsatz.
    rewrite H_n in *.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
    eapply repr_le_lb with (i:=n) in Hn; eauto; try lia.
    assert (F.to_Z x + 2^n - F.to_Z y >= 2^n)%Z. {
      autorewrite with F_to_Z in Hn; try lia;
      repeat autorewrite with F_to_Z; simpl; try lia.
      simpl in Hn. lia.
    }
    lia.
Qed.

Lemma soundness': forall (w : t),
  (* pre-conditions: both inputs are at most (k-1) bits *)
  (n <= C.k - 1)%Z ->
  (^ w.(_in)[0] <= 2^n)%Z ->
  (^ w.(_in)[1] <= 2^n)%Z  ->
  (* post-condition *)
  binary w.(out) /\
  let '(x, y) := (w.(_in)[0], w.(_in)[1]) in
  if (w.(out) = 1)? then
    x <q y
  else
    x >=q y.
Proof.
  unwrap_C. intros w H_nk Hx Hy.
  remember (w.(_in)[0]) as x. remember (w.(_in)[1]) as y.
  destruct w as [_in out [n2b H]]. simpl in *.
  rewrite <- Heqx, <- Heqy in *.
  pose proof (Num2Bits.soundness n2b) as H_n2b.
  pose proof H_n2b as H_n2b'.
  unfold repr_le2, repr_le in H_n2b.
  destruct H as [H_n Hout ].
  apply conj_use.
  intuition.
  - eapply one_minus_binary; eauto.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq. 
    apply Forall_nth. apply Forall_in_range. auto.
    lia.
  - assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
      replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
      apply Zpow_facts.Zpower_le_monotone; lia.
    }
    assert (H_x_nonneg: (0 <= F.to_Z x)%Z). apply F.to_Z_range. lia.
    assert (H_y_nonneg: (0 <= F.to_Z y)%Z). apply F.to_Z_range. lia.
    destruct (dec (out = 1)).
    + assert (Hn: Num2Bits.out n2b [n] = 0) by fqsatz.
      rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
      remember (to_list (S n) (Num2Bits.out n2b)) as n2bout.
        unfold repr_le2 in *.
        eapply repr_le_last0' in Hn. 2: { rewrite H_n in H_n2b'. apply H_n2b'. }
        fold repr_le2 in Hn.
        apply repr_le_ub in Hn; try lia.
      assert (F.to_Z x + 2^n - F.to_Z y <= 2^n - 1 )%Z. {
        autorewrite with F_to_Z in Hn; try lia;
        repeat autorewrite with F_to_Z; simpl; try lia.
        simpl in Hn. lia.
      }
      lia.
    + destruct H0; try fqsatz. assert (Hn: Num2Bits.out n2b [n] = 1) by fqsatz.
    rewrite H_n in *.
    rewrite nth_Default_nth_default, <- nth_default_to_list, nth_default_eq in Hn.
    eapply repr_le_lb with (i:=n) in Hn; eauto; try lia.
    assert (F.to_Z x + 2^n - F.to_Z y >= 2^n)%Z. {
      autorewrite with F_to_Z in Hn; try lia;
      repeat autorewrite with F_to_Z; simpl; try lia.
      simpl in Hn. lia.
    }
    lia.
Qed.

Lemma is_binary: forall (w:t), 
  (n <= C.k - 1)%Z ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  binary w.(out).
Proof.
  intros. specialize (soundness w). intuition.
Qed.

Lemma is_sound: forall (w:t),
  (n <= C.k - 1)%Z ->
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
  (n <= C.k - 1)%Z ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  w.(out) = 1 <-> w.(_in)[0] <q w.(_in)[1].
Proof.
  unwrap_C.
  intros. specialize (soundness w).
  intuition; destruct (dec (out w = 1)); (auto || fqsatz || lia).
Qed.

Definition wgen: LessThan.t. skip. Defined.

#[global] Instance LessThan_Default: Default LessThan.t. constructor. exact wgen. Defined.

End LessThan.
End LessThan.

(***********************
 *       LessThanEq
 ***********************)
Module LessEqThan.

Section LessEqThan.
Context {n: nat}.

(* template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;
    lt.out ==> out;
} *)

Definition cons (in_: F^2) (out: F) :=
  exists (lt: @LessThan.t n),
    lt.(LessThan._in)[0] = in_[0] /\
    lt.(LessThan._in)[1] = in_[1] + 1 /\
    lt.(LessThan.out) = out.

Record t: Type := {
  _in: F^2;
  out: F;
  _cons: cons _in out;
}.

Lemma soundness : forall (w: t),
  (n <= C.k - 1)%Z ->
  w.(_in)[0] | (n) ->
  w.(_in)[1] | (n) ->
  binary w.(out) /\
  let '(x, y) := (w.(_in)[0], w.(_in)[1]) in
  if (w.(out) = 1)? then
    x <=q y
  else
    x >q y.
Proof.
  intros. 
  destruct w as [w_in w_out [lt [H_lt_in0 [H_lt_in1 H_lt_out]]]].
  pose proof (@F.to_Z_range q (w_in [0])) as hhh1. 
  pose proof (@F.to_Z_range q (w_in [1])) as hhh2. 
  simpl in *. pose proof two_lt_q. pose proof q_lb as q_lb.
  pose proof (LessThan.soundness' lt) as H_lt.
  unfold LessThan.cons in H_lt.
  subst. rewrite H_lt_in0, H_lt_in1 in *.
  assert (Hndm: (2 ^ n <= 2^k)%Z). apply Zpow_facts.Zpower_le_monotone; lia.
  destruct H_lt;auto;try lia. 
  { unfold F.to_Z. simpl. do 2 rewrite Zmod_small;try lia. }
  split; auto.
  destruct (dec (LessThan.out lt = 1)).
  - apply Ztac.Zlt_le_add_1 in H4. simpl in *.
    rewrite Zmod_small in H4 at 1. 
    2:{ rewrite Zmod_small;try lia. } 
    rewrite Zmod_small in H4 at 1;lia.
  - simpl in *. rewrite Zmod_small in H4 at 1. 
    2:{ rewrite Zmod_small;try lia. }
    rewrite Zmod_small in H4 at 1;lia. 
Qed.

End LessEqThan.
End LessEqThan.

End Comparators.