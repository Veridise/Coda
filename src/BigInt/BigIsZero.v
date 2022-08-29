Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators Gates.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigIsZero.

Module D := DSL.
Module R := Repr.
Module C := Comparators.
Import R.
Import C.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigIsZero.
Context {k: nat}.

(* // check if k-register variable a is equal to zero
template BigIsZero(k) {
    signal input in[k];
    signal output out;

    component isZeros[k];
    var total = k;
    for (var i = 0; i < k; i ++) {
        isZeros[i] = IsZero();
        isZeros[i].in <== in[i];
        total -= isZeros[i].out;
    }
    component checkZero = IsZero();
    checkZero.in <== total;
    out <== checkZero.out;
} *)

Definition cons (_in: F^k) (out: F) :=
  exists (isZeros: @IsZero.t ^ k) (checkZero: @IsZero.t),
  let total := F.of_nat q k in 
  let '(total, _C) := 
    (D.iter (fun i '(total, _cons) =>
      (total - isZeros[i].(IsZero.out),
      _cons /\
      isZeros[i].(IsZero._in) = _in[i]
      )) k (total, True)) in
  checkZero.(IsZero._in) = total /\
  out = checkZero.(IsZero.out) /\
  _C.

Local Close Scope F_scope.

Record t := {
  _in: F^k;
  out: F;
  _cons: cons _in out
}.

Local Open Scope F_scope. 

Lemma fold_left_firstn_S:
  forall (i: nat)(l: list F)(b: F)(f: (F -> F -> F)),
  fold_left f (l [:S i]) b = f (fold_left f (l [:i]) b) (l ! i).
Proof.
  induction i;simpl;intros.
Admitted.

Lemma soundness_helper_lemma1:
  forall l,
  fold_left (fun x y : F => if if dec (y = 0) then true else false then x - 1 else x) 
  l (F.of_nat q k) = 0 ->
  forallb (fun x : F => if dec (x = 0) then true else false) l = true.
Proof.
Admitted.

Lemma soundness_helper_lemma2:
  forall l,
  fold_left (fun x y : F => if if dec (y = 0) then true else false then x - 1 else x) 
  l (F.of_nat q k) <> 0 ->
  forallb (fun x : F => if dec (x = 0) then true else false) l = false.
Proof.
Admitted.

Theorem soundness: forall (c: t), 
  if (forallb (fun x => (x = 0)? ) (' c.(_in))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c. 
  destruct c as [_in out _cons]. 
  destruct _cons as [isZeros [checkZero]]. subst. simpl in *.
  rem_iter.
  pose proof (length_to_list _in) as Hlen_k. 
  pose (Inv := fun (i:nat) '((total, _cons): (F * Prop)) => _cons ->
      total = (fold_left 
                  (fun x y => if (y = 0)? then x - 1 else x) 
                  (' _in[:i])
                  (F.of_nat q k))).
  assert (H_inv: Inv k (D.iter f k ((F.of_nat q k), True))). {
    apply D.iter_inv; unfold Inv.
    - intros;simpl;auto.
    - intros i b H H0. destruct b as [? ?];subst. intros.
      destruct D.iter eqn: ditr;subst.
      destruct y as [? [?]]. destruct H1. subst.
      specialize (H H1). lift_to_list. subst.
      pose proof (IsZero.soundness (' isZeros ! i)). unfold IsZero.spec in H.
      rewrite H5 in *.
      destruct dec.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1. destruct dec; fqsatz.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1. destruct dec; fqsatz.
  } 
  destruct (D.iter f k (F.of_nat q k, True)) as [total _cons] eqn:iter.
  destruct y as [? [?]]. apply H_inv in H1. subst.
  pose proof (IsZero.soundness checkZero). unfold IsZero.spec in H.
  destruct dec.
  - rewrite H1 in e. apply soundness_helper_lemma1 in e.
    replace (' _in) with (' _in [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_k;auto. }
    destruct forallb;easy.
  - rewrite H1 in n. apply soundness_helper_lemma2 in n.
    replace (' _in) with (' _in [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_k;auto. }
    destruct forallb;easy.
Qed.

End _BigIsZero.
End BigIsZero.
