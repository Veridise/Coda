Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.


Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.


Require Import Util.
(* From Coq Require Import Lia. *)

(* Require Import Crypto.Spec.ModularArithmetic. *)
(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/bitify.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope.

Context (q:positive) {prime_q:prime q}.


(***********************
 *      Num2Bits
 ***********************)

Definition F_q := F q.

Definition binary (x: F_q) := x = 0 \/ x = 1.

(* WIP: decode a binary signal vector to its value
Definition decode0b (xs: tuple F n) := fold_right add zero xs.

Definition w (i: F) := F.pow 2 i.

Definition decode_0b_list (xs: list F) :=  
  *)


Definition Num2Bits n (_in: F_q) (_out: tuple F_q n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (iter n (fun i '(lc1, e2, _C) =>
    let out_i := (Tuple.nth_default 0 i _out) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C.


Theorem Num2Bits_correct n _in _out:
  Num2Bits n _in _out -> (forall i, Nat.lt i n -> binary (Tuple.nth_default 0 i _out)).
Proof using Type*.
  pose proof prime_q.
  pose (Inv := fun i '((lc1, e2, _C): (F.F q * F.F q * Prop)) =>
    (* match acc with *)
    (* |  => *)
      (_C -> (forall j, Nat.lt j i -> binary (Tuple.nth_default 0 j _out)))).
  pose proof (iter_inv Inv) as Hinv.
  unfold Num2Bits.
  intros prog i H_i_lt_n.
  (* iter initialization *)
  remember (0, 1, True) as a0.
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?n ?f ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* Prove Inv hold for initialization *)
  assert (Hinit: Inv Nat.zero a0).
  {
    unfold Inv.
    rewrite Heqa0. intros _ j impossible.
    inversion impossible.
  }
  (* Prove Inv is inductive *)
  assert (Hind: forall (j : nat) (b : F.F q * F.F q * Prop),
    Inv j b -> Inv (S j) (f j b)).
  {
    unfold Inv.
    intros j res Hprev.
    destruct res. destruct p.
    rewrite Heqf.
    intros Hstep j0 H_j0_lt.
    destruct Hstep as [Hstep HP].
    specialize  (Hprev HP).
    assert (H_j0_leq: Nat.le j0 j) by lia.
    destruct (lt_dec j0 j).
    - auto.
    - unfold binary.
      replace j0 with j by lia.
      destruct (dec (Tuple.nth_default 0 j _out = 0)).
      + auto.
      + right.
      rewrite <- Ring.sub_zero_iff.
      apply Hierarchy.zero_product_zero_factor in Hstep.
      destruct (dec (nth_default 0 j _out = 0)); intuition.
  }
  specialize (Hinv f a0 Hinit Hind n). clear Hind Hinit.
  unfold Inv in Hinv.
  destruct (iter n f a0).
  destruct p.
  intuition.
Qed.