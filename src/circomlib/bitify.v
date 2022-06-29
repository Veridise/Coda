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

Theorem fold_right_invariant
  (A B: Type)
  (l: list B)
  (f: B -> A -> A)
  (a0: A) 
  (P: list B -> A -> Prop)
  (Hinit: P nil a0)
  (Hinv: forall a b bs, P bs a -> P (b::bs) (f b a)):
  P l (fold_right f a0 l).
Proof.
  induction l; eauto.
Qed.

Definition uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z.
Proof. destruct p; apply f; eauto. Defined.

Local Open Scope nat_scope.
Definition fold_i {A B: Type} (f: nat -> B -> A -> A) (a0: A) :=
  fold_right (fun b (ia: (nat * A)) => let (i,a):= ia in (i+1, f i b a)) (0,a0).
Local Close Scope nat_scope.
Require Import Coq.PArith.BinPosDef.


(* Context (m:positive) {prime_m:prime m}. *)

Require Import Util.

Definition Num2Bits n (_in: F) (_out: tuple (F) n) : Prop :=
  let lc1 := zero in
  let e2 := one in
  match (iter n (fun i acc =>
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

Definition binary (x: F) := x = zero \/ x = one.

Definition sum (xs: list F) := fold_right add zero xs.

Require Import Coq.Arith.PeanoNat.

(* Definition bits2num (_out: list (F)) := fold_right (fun (F.pow 2) *)

Definition Num2Bits_spec n (_in: F) (_out: tuple F n) :=
  (forall i, Nat.lt i n -> binary (Tuple.nth_default zero i _out)).

Definition Num2Bits_inv n (_out: tuple F n) i (acc: (F * F * Prop)) :=
  match acc with
  | (lc1, e2, _C) =>
    _C -> forall j, Nat.lt j i -> binary (Tuple.nth_default zero j _out)
  end.
  
(* Compute (Num2Bits_inv 5 0). *)

From Coq Require Import Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Crypto.Util.Decidable.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Theorem Num2Bits_correct n _in _out:
  Num2Bits n _in _out -> Num2Bits_spec n _in _out.
Proof using Type*.
  unfold Num2Bits, Num2Bits_spec.
  intros.
  pose proof (@iter_inv _ (Num2Bits_inv n _out)).
  remember (fun (i : nat) (acc : bitify.F * bitify.F * Prop) =>
  let (y, _C) := acc in
  let (lc1, e2) := y in
  (lc1 + Tuple.nth_default 0 i _out * e2, e2 + e2,
  Tuple.nth_default 0 i _out * (Tuple.nth_default 0 i _out - 1) = 0 /\
  _C)) as f.
  remember (0, 1, True) as a0.
  assert (Num2Bits_inv n _out 0 a0).
  {
    unfold Num2Bits_inv.
    rewrite Heqa0. intuition.
    unfold binary. left. lia.
  }
  specialize (H1 f a0).
  specialize (H1 H2).
  assert (forall (j : nat) (b : bitify.F * bitify.F * Prop),
  Num2Bits_inv n _out j b -> Num2Bits_inv n _out (S j) (f j b)).
  {
    unfold Num2Bits_inv.
    intros.
    destruct b. destruct p.
    rewrite Heqf.
    intros.
    destruct H4.
    specialize (H3 H6).
    assert (Nat.le j0 j). lia.
    destruct (lt_dec j0 j).
    - apply H3. trivial.
    - assert (Nat.eq j0 j) by lia. unfold binary. {
      destruct (dec (Tuple.nth_default 0 j0 _out = 0)).
      + left. trivial.
      + right. rewrite H8 in *. Field.fsatz.
    }
  }
  specialize (H1 H3).
  unfold Num2Bits_inv in H1.
  specialize (H1 n).
  destruct (iter n f a0).
  destruct p.
  destruct H.
  specialize (H1 H4).
  apply H1.
  lia.
Qed.