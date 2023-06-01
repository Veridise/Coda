(* Basic workflow:
  1. Represent your data using Coq data types
  2. Express computation as Coq programs that operate on the data type
  3. State and prove theorems about computation
*)

(* Note: you can follow along the first module using the JsCoq
  online IDE: https://coq.vercel.app/ *)

Module MyNat.

Inductive nat :=
  | O: nat
  | S: nat -> nat.

Fixpoint add (n m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Notation "1" := (S O).
Notation "2" := (S 1).
Notation "3" := (S 2).

Fact add_2_1: add 2 1 = 3.
Proof.
  simpl. reflexivity.
Qed.

Lemma add_0_r: forall (n: nat), add n O = n.
Proof.
Admitted.

Lemma add_m_Sn: forall (m n: nat), add m (S n) = S (add m n).
Proof.
Admitted.

Theorem add_comm: forall n m, add n m = add m n.
Proof.
  induction n.
  - intros. simpl. rewrite add_0_r. reflexivity.
  - intros. simpl. rewrite IHn. rewrite add_m_Sn. reflexivity.
Qed.

End MyNat.




(* Let's now nstantiate the recipe to prove circom circuits! *)
(* Note that the following must be run as part of the circom-coq project:
 * https://github.com/Veridise/circom-coq *)

Section circom.

(* 1. Represent your data using Coq data types *)

(* Relies on existing formalizations in Coq and the Fiat-Crypto project *)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Util.

(* Some prep work... *)

Local Open Scope list_scope.
Local Open Scope F_scope.

Ltac fqsatz := fsatz_safe; autorewrite with core; auto.
Context (q:positive) (k:Z) {prime_q: prime q} {two_lt_q: 2 < q} {k_positive: 1 < k} {q_lb: 2^k < q}.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  apply Pos.ltb_lt. lia.
Qed.

Lemma q_gt_2: 2 < q.
Proof.
  replace 2%Z with (2^1)%Z by lia.
  apply Z.le_lt_trans with (m := (2 ^ k)%Z); try lia.
  eapply Zpow_facts.Zpower_le_monotone; try lia.
Qed.

Hint Rewrite q_gtb_1 : core.

(* test whether a field element is binary *)
Definition binary (x: F q) := x = 0 \/ x = 1.
Definition two : F q := 1 + 1.
Notation "2" := two.
Notation "x [ i ]" := (Tuple.nth_default 0 i x).



(* 2. Express computation as Coq programs that operate on the data type *)

(***********************
 *      Num2Bits
 ***********************)

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/bitify.circom
*)

Definition Num2Bits (n: nat) (_in: F q) (_out: tuple (F q) n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (iter n (fun (i: nat) '(lc1, e2, _C) =>
      (* circom: lc += out[i] * e2 *)
      (lc1 + _out[i] * e2,
      (* circom: e2 = e2 + e2 *)
      e2 + e2,
      (* circom: out[i] * (out[i] -1 ) === 0 *)
      (_out[i] * (_out[i] - 1) = 0) /\ _C))
    (lc1, e2, True)) in
  _C /\ (lc1 = _in).
Print Num2Bits.



(* 3. State and prove theorems about computation *)

(* All output signals are binary *)
Theorem Num2Bits_is_binary n _in _out:
  Num2Bits n _in _out ->
  (forall i, (i < n)%nat -> binary (_out[i])).
Proof.
  unfold Num2Bits.
  (* provide the loop invariant *)
  pose (Inv := fun i '((lc1, e2, _C): (F.F q * F.F q * Prop)) =>
    (_C -> (forall j, Nat.lt j i -> binary (_out[j])))).
  (* iter initialization *)
  remember (0, 1, True) as a0.
  intros prog i H_i_lt_n.
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?n ?f ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* Prove that the invariant holds *)
  assert (Hinv: forall i, Inv i (iter i f a0)). {
  intros. apply iter_inv; unfold Inv.
  - (* base case *) 
    subst. intros _ j impossible. lia.
  - (* inductive case *)
    intros j res Hprev.
    destruct res. destruct p.
    rewrite Heqf.
    intros Hstep j0 H_j0_lt.
    destruct Hstep as [Hstep HP].
    specialize  (Hprev HP).
    assert (H_j0_leq: (j0 <= j)%nat) by lia.
    destruct (dec (j0 < j)%nat).
    + auto.
    + unfold binary.
      replace j0 with j by lia.
      destruct (dec (Tuple.nth_default 0 j _out = 0)).
      * auto.
      * right. fqsatz.
   }
  unfold Inv in Hinv.
  specialize (Hinv n).
  destruct (iter n f a0).
  destruct p.
  (* This is a big hammer for proving things that are _obviously_ true *)
  intuition.
Qed.