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

From Circom.Spec Import Circom DSL Repr ReprZ.
From Circom Require Import Default Util Tuple ListUtil LibTactics Simplify.
From Circom.CircomLib Require Import Bitify Comparators Gates.
From Circom.BigInt.Definition Require Import BigIsZero.
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

Lemma F_0_1_ff: 1%F <> @F.zero q.
Proof.
unwrap_C.
intro. pose proof @F.to_Z_0 q. rewrite <- H in H0. simpl in *. rewrite Zmod_1_l in H0;try lia.
Qed.

Lemma fold_left_firstn_S:
  forall (l: list F)(i: nat)(b: F)f,
  i < length l ->
  fold_left f  (l [:S i]) b = 
  f (fold_left f (l [:i]) b) (l ! i).
Proof.
  intros. 
  assert(l [:S i] = l [:i] ++ ((l ! i)::nil)).
  { erewrite firstn_S;try lia. unfold_default. auto. }
  rewrite H0.
  apply fold_left_app.
Qed.

Lemma soundness_helper_lemma:
  forall l (k:Z) (RNG: 1 <= k <= C.k ),
  (k > length l)%Z ->
  (fold_left
      (fun x y : Z =>
       if if dec (y = 0)%Z then true else false then (x - 1)%Z else x) l
      k <> 0%Z)%F.
Proof.
  unwrap_C.
  induction l;simpl;intros.
  - intro. subst. simpl in *. rewrite Z.mod_small in *;try lia.
  - assert (RNG1: 0 <= length l < q).
    { destruct RNG. assert (C.k < 2 ^ C.k). apply Zpow_facts.Zpower2_lt_lin;lia. lia. }
    destruct dec;subst;simpl in *.
    + apply IHl;simpl;lia.
    + apply IHl;simpl;lia.
Qed.

Lemma soundness_helper:
  forall l (k:nat) (RNG: 1 <= k <= C.k ),
  (k > length l) ->
  (fold_left
      (fun x y : F =>
       if if dec (y = 0) then true else false then (x - 1) else x) l
       (F.of_nat q k) <> 0).
Proof.
  unwrap_C. 
  induction l;simpl;intros.
  - intro. subst. simpl in *. rewrite Z.mod_small in *;try lia.
    assert (RNG1: (C.k < 2 ^ C.k)).
    { apply Zpow_facts.Zpower2_lt_lin;lia. }
    assert(F.of_nat q k0 <> 0).
    { unfold F.of_nat. apply F.of_Z_small_nonzero;try lia. }
    easy.
    rewrite Z.mod_small;try lia.
  - assert (RNG1: 0 <= length l < q).
    { destruct RNG. assert (C.k < 2 ^ C.k). apply Zpow_facts.Zpower2_lt_lin;lia. lia. }
    destruct dec;subst;simpl in *.
    + unfold F.of_nat in *. 
      assert ((F.of_Z q k0 - 1) = (F.of_Z q (k0 - 1)%nat)).
      { assert ((Z.of_nat (k0 - 1)) = (Z.of_nat k0) - 1)%Z. lia.
        rewrite H0. rewrite F.of_Z_sub. fqsatz. }
      rewrite H0.
      eapply IHl;simpl;try lia.
    + unfold F.of_nat in *.
      eapply IHl;simpl;try lia.
Qed.

Lemma add_sub: forall (x y: F), x + y - y = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Lemma soundness_helper_lemma1:
  forall l (k:nat) (RNG: (k <= C.k)%Z),
  k = length l ->
  fold_left (fun x y : F => if if dec (y = 0) then true else false then x - 1 else x) 
  l (F.of_nat q k) = 0 ->
  forallb (fun x : F => if dec (x = 0) then true else false) l = true.
Proof.
  unwrap_C.
  induction l;intros;simpl in *;trivial.
  destruct dec;simpl.
  - subst. eapply (IHl (length l));eauto;try lia.
    replace (F.of_nat q (length l)) with ((F.of_nat q (S (length l)) - 1));auto.
    replace (S (length l)) with (length l + 1)%nat by lia.
    rewrite F.of_nat_add.
    replace (F.of_nat q 1) with (@F.one q);auto.
    rewrite add_sub. fqsatz. 
  - apply soundness_helper in H0;try lia;try easy. 
Qed.

Lemma soundness_helper_lemma2:
  forall l k,
  k = length l ->
  fold_left (fun x y : F => if if dec (y = 0) then true else false then x - 1 else x) 
  l (F.of_nat q k) <> 0 ->
  forallb (fun x : F => if dec (x = 0) then true else false) l = false.
Proof.
  unwrap_C.
  induction l;intros;simpl in *;subst;try easy.
  destruct dec;simpl;auto.
  subst. eapply IHl;eauto.
  replace (F.of_nat q (length l)) with ((F.of_nat q (S (length l)) - 1));auto.
  replace (S (length l)) with (length l + 1)%nat by lia.
  rewrite F.of_nat_add.
  replace (F.of_nat q 1) with (@F.one q);auto.
  rewrite add_sub. fqsatz.
Qed.

Theorem soundness: forall (c: t),
  1 <= k <= C.k ->
  if (forallb (fun x => (x = 0)? ) (' c.(_in))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c RNG. 
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
        rewrite fold_left_firstn_S at 1;try lia. destruct dec; fqsatz.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1;try lia. destruct dec; fqsatz.
  } 
  destruct (D.iter f k (F.of_nat q k, True)) as [total _cons] eqn:iter.
  destruct y as [? [?]]. apply H_inv in H1. subst.
  pose proof (IsZero.soundness checkZero). unfold IsZero.spec in H.
  assert (k = length (' _in [:k])).
  { rewrite firstn_length. lia. }
  assert (RNG1: k < q).
  { destruct RNG. assert (C.k < 2 ^ C.k). apply Zpow_facts.Zpower2_lt_lin;lia. lia. }
  destruct dec.
  - rewrite H1 in e. apply soundness_helper_lemma1 in e;auto;try lia.
    replace (' _in) with (' _in [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_k;auto. }
    destruct forallb;easy.
  - rewrite H1 in n. apply soundness_helper_lemma2 in n;auto;try lia.
    replace (' _in) with (' _in [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_k;auto. }
    destruct forallb;easy.
Qed.

End _BigIsZero.
End BigIsZero.
