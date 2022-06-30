Require Import BabyJubjub.
Require Import Crypto.Util.Tuple.
Require Import BabyJubjub.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.PArith.BinPosDef.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

(* Require Import Crypto.Spec.ModularArithmetic. *)
(* Circuit:
 * https://github.com/iden3/circomlib/blob/master/circuits/bitify.circom
 *)

 Context {F eq zero one opp add sub mul inv div}
 {fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
 {eq_dec:DecidableRel eq}.
Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
Local Notation "0" := zero.  Local Notation "1" := one.
Local Infix "+" := add. Local Infix "*" := mul.
Local Infix "-" := sub. Local Infix "/" := div.

(***********************
 *      Num2Bits
 ***********************)

(* Definition fold_i {A B n} (f: nat -> A -> B) (x: list A) -> list B :=  *)
  
  (* fun xx => snd (@mapi_with unit A B n (fun n _ x => (tt, f n x)) tt xx). *)
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Require Import Coq.PArith.BinPosDef.
Require Import Util.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Crypto.Util.Decidable.
(* Require Import Crypto.Arithmetic.PrimeFieldTheorems. *)

(* Context (m:positive) {prime_m:prime m}. *)

Definition binary (x: F) := x = zero \/ x = one.

Definition sum (xs: list F) := fold_right add zero xs.

Definition Num2Bits n (_in: F) (_out: tuple (F) n) : Prop :=
  let lc1 := zero in
  let e2 := one in
  match (iter n
    (fun i acc =>
      match acc with
      | (lc1, e2, _C) =>
        let out_i := (Tuple.nth_default zero i _out) in
          (lc1 + out_i * e2,
          e2 + e2,
          (out_i * (out_i - 1) = 0) /\ _C)
      end)
      (lc1, e2, True)) with
  | (lc1, e2, _C) => (lc1 = _in) /\ _C
  end.

Definition Num2Bits_spec n (_in: F) (_out: tuple F n) :=
  (forall i, Nat.lt i n -> binary (Tuple.nth_default zero i _out)).

Definition Num2Bits_inv n (_out: tuple F n) i (acc: (F * F * Prop)) :=
  match acc with
  | (lc1, e2, _C) =>
    _C -> forall j, Nat.lt j i -> binary (Tuple.nth_default zero j _out)
  end.

Theorem Num2Bits_correct n _in _out:
  Num2Bits n _in _out -> Num2Bits_spec n _in _out.
Proof using Type*.
  unfold Num2Bits, Num2Bits_spec.
  intros prog i H_i_lt_n.
  pose proof (iter_inv (Num2Bits_inv n _out)) as Hinv.
  (* iter initialization *)
  remember (0, 1, True) as a0.
  (* iter function *)
  remember (fun (i : nat) (acc : bitify.F * bitify.F * Prop) =>
    let (y, _C) := acc in
    let (lc1, e2) := y in
    (lc1 + Tuple.nth_default 0 i _out * e2, e2 + e2,
    Tuple.nth_default 0 i _out * (Tuple.nth_default 0 i _out - 1) = 0 /\
    _C)) as f.
  (* Prove Inv hold for initialization *)
  assert (Hinit: Num2Bits_inv n _out 0 a0).
  {
    unfold Num2Bits_inv.
    rewrite Heqa0. intros _ j H_j_lt_0.
    unfold binary. left. lia.
  }
  (* Prove Inv is inductive *)
  assert (Hind: forall (j : nat) (b : bitify.F * bitify.F * Prop),
    Num2Bits_inv n _out j b -> Num2Bits_inv n _out (S j) (f j b)).
  {
    unfold Num2Bits_inv.
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
      + right. Field.fsatz.
  }
  specialize (Hinv f a0 Hinit Hind n).
  unfold Num2Bits_inv in Hinv.
  destruct (iter n f a0).
  destruct p.
  intuition.
Qed.