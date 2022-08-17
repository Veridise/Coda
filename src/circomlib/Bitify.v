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
Require Crypto.Algebra.Nsatz.

Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable.
(* Require Import Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Circom.Circom Circom.DSL Circom.Util Circom.ListUtil.
Require Import Circom.Default.
Require Import Circom.Repr.
(* Require Import VST.zlist.Zlist. *)


(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Bitify (C: CIRCOM).

Import C.

Module D := DSL C.

Module R := Repr C.

Import R.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion N.of_nat : nat >-> N.


(* Base 2^n representations *)
Lemma to_Z_2: @F.to_Z q 2 = 2%Z.
Proof. unwrap_C. simpl. repeat rewrite Z.mod_small; lia. Qed.

(* peel off 1 from x^(i+1) in field exp *)
Lemma pow_S_N: forall (x: F) (i: nat),
  x ^ (S i) = x * x ^ i.
Proof.
  unwrap_C. intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) (i: nat),
  (x ^ (S i) = x * x ^ i)%Z.
Proof.
  unwrap_C. intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.


Module Num2Bits.

Local Open Scope tuple_scope.
Definition cons (n: nat) (_in: F) (out: F^n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (D.iter (fun (i: nat) '(lc1, e2, _C) =>
    let out_i := (out [i] ) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    n
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C.

Theorem cons_imply_binary n _in out:
  cons n _in out -> (forall i, (i < n)%nat -> binary (out[i])).
Proof.
  unwrap_C. unfold cons.
  (* provide loop invariant *)
  pose (Inv := fun i '((lc1, e2, _C): (F * F * Prop)) =>
    (_C -> (forall j, (j < i)%nat -> binary (out[j])))).
  (* iter initialization *)
  remember (0, 1, True) as a0.
  intros prog i H_i_lt_n.
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?f ?n ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* invariant holds *)
  assert (Hinv: forall i, Inv i (D.iter f i a0)). {
  intros. apply D.iter_inv; unfold Inv.
  - (* base case *) 
    subst. intros _ j impossible. lia.
  - (* inductive case *)
    intros j res Hprev.
    destruct res. destruct p.
    rewrite Heqf.
    intros _ Hstep j0 H_j0_lt.
    destruct Hstep as [Hstep HP].
    specialize  (Hprev HP).
    destruct (dec (j0 < j)%nat).
    + auto.
    + unfold binary. intros.
      replace j0 with j by lia.
      destruct (dec (out[j] = 0)).
      * auto.
      * right. fqsatz.
   }
  unfold Inv in Hinv.
  specialize (Hinv n).
  destruct (D.iter f n a0).
  destruct p.
  intuition.
Qed.

Class t (n: nat): Type := mk {
  _in: F; 
  out: F^n; 
  _cons: cons n _in out
}.

Definition spec (n: nat) (w: t n) := 
  repr_le2 w.(_in) n (to_list n w.(out)).

Theorem soundness: forall (n: nat) (w: t n), spec n w.
Proof.
  unwrap_C. intros.
  destruct w as [_in _out _cons]. unfold spec, cons in *. simpl.
  remember (to_list _ _out) as out.
  pose (Inv := fun (i: nat) '((lc1, e2, _C)) => 
    (_C: Prop) ->
      (e2 = (2^i) /\
      let firsti := firstn i (to_list n _out) in
      repr_le2 lc1 i firsti)).
  remember (fun (i : nat) '(y, _C) =>
  let
  '(lc1, e2) := y in
    (lc1 + _out[i] * e2, 
    e2 + e2,
    _out[i] * (_out[i] - 1) = 0 /\
    _C)) as f.
  assert (Hinv: Inv n (D.iter f n (0,1,True))). {
    apply D.iter_inv; unfold Inv.
    - intuition. simpl. rewrite F.pow_0_r. fqsatz.
      simpl. apply repr_le_base.
    - intros j acc. destruct acc as [acc _C]. destruct acc as [lc1 e2].
      intros Hprev Hjn. subst. intuition.
      + rewrite pow_S_N. subst. fqsatz.
      + unfold repr_le2, repr_le in *.
        pose proof (length_to_list _out).
        intuition.
        * rewrite firstn_length_le; lia.
        * apply Forall_in_range in H3. apply Forall_in_range.
          apply Forall_nth. intros. subst.
          destruct (dec (i < j)%nat).
          -- rewrite fistn_prev by lia. pose proof Forall_nth.
            apply Forall_nth. apply H3. lia.
          -- rewrite firstn_length_le in H5. assert (i = j) by lia. subst.
            rewrite firstn_nth by lia.
            rewrite nth_oblivious with (d2:=0) by lia.
            rewrite <- nth_default_eq, nth_default_to_list.
            unfold binary.
            destruct (dec (_out[j] = 0)); (left; fqsatz) || (right; fqsatz).
            rewrite length_to_list. lia.
        * subst. erewrite firstn_S with (d:=0) by lia.
          rewrite as_le_app.
          rewrite <- nth_default_eq, nth_default_to_list.
          cbn [as_le].
          rewrite firstn_length_le.
          rewrite N.mul_1_l.
            fqsatz.
          rewrite length_to_list. lia.
  }
  destruct (D.iter f n (0,1,True)) as [ [lc1 e2] _C].
  unfold Inv in Hinv. intuition.
  subst. rewrite <- firstn_to_list. auto.
Qed.
End Num2Bits.

End Bitify.