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

Definition cons (n: nat) (_in: tuple F 2) (_out: F) :=
  exists (n2b: Num2Bits.t),
    n2b.(Num2Bits.n) = S n /\
    n2b.(Num2Bits._in) = (_in [0] + 2^(N.of_nat n) - _in[1]) /\
    _out = 1 - n2b.(Num2Bits._out)[n].

Class t: Type := mk {
  n: nat;
  _in: tuple F 2;
  _out: F;
  _cons: cons n _in _out;
}.

Local Notation "a q< b" := (Num2Bits.lt a b) (at level 50).
(* FIXME: define q<= q>= q> *)
(* Local Notation "a q<= b" := (Num2Bits.leq a b) (at level 50). *)
Local Notation "a z<= z" := (Num2Bits.leq_z a z) (at level 50).
Local Notation "a z>= z" := (Num2Bits.geq_z a z) (at level 50).

Definition spec (w: t) :=
  (Num2Bits.binary _out) /\
  (_out = 1 -> w.(_in)[0] q< w.(_in)[1]) /\
  (_out = 0 -> ~(w.(_in)[0] q< w.(_in)[1])).

Lemma one_minus_binary: forall x y,
  x = 1 - y ->
  Num2Bits.binary y ->
  Num2Bits.binary x.
Proof.
Admitted.

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


Lemma eq_forall {A: Type}: forall l1 l2 (d: A),
  length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth i l1 d = nth i l2 d)
  -> l1 = l2.
Proof.
  induction l1; simpl; intros; destruct l2; simpl in H; try lia.
  - reflexivity.
  - assert (a = a0). specialize (H0 0%nat). apply H0. lia.
    rewrite H1. f_equal.
    eapply IHl1. lia.
    intros. specialize (H0 (S i)). apply H0. lia.
Qed.

(* Lemma Fto_Z_sub: forall x y,  *)

Local Notation "2" := (1 + 1).

Local Coercion N.of_nat: nat >-> N.

Lemma soundness: forall (w : t)
  (H_nk: w.(n) <= k - 1)
  (H_x: 0 <= F.to_Z (w.(_in)[0]) <= 2 ^ n )
  (H_y: 0 <= F.to_Z (w.(_in)[1]) <= 2 ^ n ),
  spec w.
Proof.
  unwrap_C. intros. unfold spec.
  remember (_in[0]) as x. eremember (_in[1]) as y.
  destruct w as [n _in _out _cons].
  unfold Num2Bits.binary. unfold cons in *.
  destruct _cons as [n2b H].
  cbn [LessThan._in LessThan._out LessThan.n] in *.
  assert (H_pow_nk: 2 * 2^(Z.of_nat n) <= 2^k). {
    replace (2 * 2 ^ Z.of_nat n)%Z with (2 ^ (Z.of_nat n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  rewrite <- Heqx, <- Heqy in *.
  pose proof (Num2Bits.soundness n2b) as H_n2b. unfold Num2Bits.spec in H_n2b.
  intuition idtac.
  - destruct H_n2b as [_ [H_bin _] ]. specialize (H_bin n).
    eapply one_minus_binary; eauto. 
    rewrite <- nth_default_eq, nth_default_to_list in H_bin.
    apply H_bin. lia.
  - assert (H_n2b_out: Num2Bits._out [n] = 0) by fqsatz.
    assert (H_last: exists ws, ws ++ 0 :: nil = to_list Num2Bits.n Num2Bits._out). {
      exists (firstn n (to_list Num2Bits.n Num2Bits._out)).
      erewrite <- firstn_skipn with (n:=n).
      apply app_inv_head_iff.
      eapply eq_forall. simpl. rewrite skipn_length, length_to_list. lia.
      intros.
      simpl in H7.
      destruct i; try lia.
      simpl. 
      rewrite Num2Bits.nth_skipn.
      simpl. rewrite <- nth_default_eq, nth_default_to_list. symmetry. exact H_n2b_out.
      rewrite length_to_list. lia.
    }
    destruct H_last as [ws H_ws].
    rewrite <- H_ws in H_n2b.
    rewrite H0 in H_n2b.
    apply Num2Bits.repr_binary_last0 in H_n2b.
    apply Num2Bits.repr_binary_ub in H_n2b; try lia.
    rewrite H5 in H_n2b.
    assert (F.to_Z x + 2 ^ Z.of_nat n - F.to_Z y <= 2^Z.of_nat n - 1 ). {
      unfold Num2Bits.leq_z in H_n2b.
      replace (x + 2 ^ N.of_nat n - y) with (x + (2 ^ N.of_nat n - y)) in * by fqsatz.
        rewrite F.to_Z_add, to_Z_sub, F.to_Z_pow, Num2Bits.to_Z_2 in H_n2b by lia.
        (* rewrite nat_N_Z in *. *)
        do 4 rewrite Z.mod_small in H_n2b;
        try lia;
        repeat rewrite Z.mod_small; lia.
    }
    unfold Num2Bits.lt. lia.
  - 
    assert (H_n2b_out: Num2Bits._out [n] = 1) by fqsatz.
    eapply Num2Bits.repr_binary_lb with (i:=n) in H_n2b; try lia.
    + rewrite H5 in *. clear H5.
      unfold Num2Bits.geq_z in H_n2b.
      assert (F.to_Z x + 2 ^ Z.of_nat n - F.to_Z y >= 2^Z.of_nat n). {
        replace (x + 2 ^ N.of_nat n - y) with (x + (2 ^ N.of_nat n - y)) in * by fqsatz.
        rewrite F.to_Z_add, to_Z_sub, F.to_Z_pow, Num2Bits.to_Z_2 in H_n2b by lia.
        (* rewrite nat_N_Z in *. *)
        do 4 rewrite Z.mod_small in H_n2b;
        try lia;
        repeat rewrite Z.mod_small; try lia.
      }
      unfold Num2Bits.lt in *. lia.
    + rewrite <- nth_default_eq, nth_default_to_list. auto.
Qed.
End LessThan.

End Comparators.