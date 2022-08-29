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

Module BigIsEqual.
Context {n: nat}.

Module C := Comparators.
Module D := DSL.
Module R := Repr.
Import R.
Import C.
Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigIsEqual.
Context {k: nat}.

(* // check if k-register variables a, b are equal everywhere
template BigIsEqual(k) {
    signal input a[k];
    signal input b[k];
    signal output out;

    component isEquals[k];
    var total = k;
    for (var i = 0; i < k; i ++) {
        isEquals[i] = IsEqual();
        isEquals[i].in[0] <== a[i];
        isEquals[i].in[1] <== b[i];
        total -= isEquals[i].out;
    }
    component checkZero = IsZero();
    checkZero.in <== total;
    out <== checkZero.out;
} *)

Definition cons (a: F^k) (b: F^k) (out: F) :=
  exists (isEquals: IsEqual.t ^ k) (checkZero: @IsZero.t),
  let total := F.of_nat q k in 
  let '(total, _C) := 
    (D.iter (fun i '(total, _cons) =>
      (total - isEquals[i].(IsEqual.out),
      _cons /\
      isEquals[i].(IsEqual._in)[0] = a[i] /\
      isEquals[i].(IsEqual._in)[1] = b[i]
      )) k (total, True)) in
  checkZero.(IsZero._in) = total /\
  out = checkZero.(IsZero.out) /\
  _C.

Local Close Scope F_scope.

Record t := {
  a: F^k;
  b: F^k;
  out: F;
  _cons: cons a b out
}.

Local Open Scope F_scope. 

Instance Default : Default (F * F) := { default := (0, 0) }.

Lemma fold_left_firstn_S:
  forall (i: nat)(l1 l2: list F)(b: F)(f: (F -> F * F -> F)),
  fold_left f (ListUtil.map2 pair (l1 [:S i]) (l2 [:S i])) b = 
  f (fold_left f (ListUtil.map2 pair (l1 [:i]) (l2 [:i])) b) ((ListUtil.map2 pair (l1 [:i]) (l2 [:i])) ! i).
Proof.
  induction i;simpl;intros.
Admitted.

Lemma soundness_helper_lemma1:
  forall l1 l2,
  fold_left (fun x y => if (fst y = snd y)? then x - 1 else x)  (ListUtil.map2 pair l1 l2) (F.of_nat q k) = 0 ->
  forallb (fun x : F * F => if dec (fst x = snd x) then true else false) (ListUtil.map2 pair l1 l2) = true.
Proof.
Admitted.

Lemma soundness_helper_lemma2:
  forall l1 l2,
  fold_left (fun x y => if (fst y = snd y)? then x - 1 else x)  (ListUtil.map2 pair l1 l2) (F.of_nat q k) <> 0 ->
  forallb (fun x : F * F => if dec (fst x = snd x) then true else false) (ListUtil.map2 pair l1 l2) = false.
Proof.
Admitted.

Lemma list_map_pair_nth_fst:
  forall i a b,
  fst (ListUtil.map2 pair (a [:i]) (b [:i]) ! i) = (a [:i]) ! i.
Admitted.

Lemma list_map_pair_nth_snd:
  forall i a b,
  snd (ListUtil.map2 pair (a [:i]) (b [:i]) ! i) = (b [:i]) ! i.
Admitted.

Theorem soundness: forall (c: t), 
  if (forallb (fun x => (fst x = snd x)? ) (ListUtil.map2 pair (' c.(a)) (' c.(b)))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c. 
  destruct c as [a b out _cons]. 
  destruct _cons as [isEquals [checkZero]]. subst. simpl in *.
  rem_iter.
  pose proof (length_to_list a) as Hlen_ka.
  pose proof (length_to_list b) as Hlen_kb.
  pose (Inv := fun (i:nat) '((total, _cons): (F * Prop)) => _cons ->
      total = (fold_left 
                  (fun x y => if (fst y = snd y)? then x - 1 else x) 
                  (ListUtil.map2 pair (' a [:i]) (' b [:i]))
                  (F.of_nat q k))).
  assert (H_inv: Inv k (D.iter f k ((F.of_nat q k), True))). {
    apply D.iter_inv; unfold Inv.
    - intros;simpl;auto.
    - intros i b0 H H0. destruct b0 as [? ?];subst. intros.
      destruct D.iter eqn: ditr;subst.
      destruct y as [? [?]]. destruct H1 as [? [?]]. subst.
      specialize (H H1). lift_to_list. subst.
      pose proof (IsEqual.soundness (' isEquals ! i)). lift_to_list. rewrite H5, H6 in *.
      destruct dec.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1.
        destruct dec; try easy. rewrite list_map_pair_nth_fst, list_map_pair_nth_snd in n0.
        replace ((' a [:i]) ! i) with  (' a ! i) in n0 by admit.
        replace ((' b [:i]) ! i) with  (' b ! i) in n0 by admit. easy.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1.
        destruct dec; try fqsatz. rewrite list_map_pair_nth_fst, list_map_pair_nth_snd in e.
        replace ((' a [:i]) ! i) with  (' a ! i) in e by admit.
        replace ((' b [:i]) ! i) with  (' b ! i) in e by admit. easy.
  } 
  destruct (D.iter f k (F.of_nat q k, True)) as [total _cons] eqn:iter.
  destruct y as [? [?]]. apply H_inv in H1. subst.
  pose proof (IsZero.soundness checkZero). unfold IsZero.spec in H.
  destruct dec.
  - rewrite H1 in e. apply soundness_helper_lemma1 in e.
    replace (' a) with (' a [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_ka;auto. }
    replace (' b) with (' b [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_kb;auto. }
    destruct forallb;easy.
  - rewrite H1 in n0. apply soundness_helper_lemma2 in n0.
    replace (' a) with (' a [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_ka;auto. }
    replace (' b) with (' b [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_kb;auto. }
    destruct forallb;easy.
Admitted.

End _BigIsEqual.
End BigIsEqual.
