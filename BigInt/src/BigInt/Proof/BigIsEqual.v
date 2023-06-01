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

From Circom Require Import Circom DSL Repr ReprZ.
From Circom Require Import Default Util Tuple ListUtil LibTactics Simplify.
From Circom.CircomLib Require Import Bitify Comparators Gates.
From Circom.BigInt.Definition Require Import BigIsEqual.
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

Lemma list_map_pair_nth:
  forall i a b,
  (i < length a)%nat ->
  i < length b ->
  (ListUtil.map2 pair (a [:S i]) (b [:S i]) ! i) = ((a [:S i]) ! i, (b [:S i]) ! i).
Proof.
  intros. unfold "!". erewrite ListUtil.nth_default_map2.
  destruct lt_dec.
  2:{ exfalso. apply n0. do 2 rewrite firstn_length. lia. }
  auto.
Qed.

Lemma list_map_pair_append:
  forall l1 l2 a b (f: (F -> F -> F * F)),
  length l1 = length l2 ->
  (ListUtil.map2 f (l1 ++ (a :: nil)) (l2 ++ (b :: nil))) =
  ListUtil.map2 f l1 l2 ++ (f a b) :: nil.
Proof.
  intros.
  rewrite ListUtil.map2_app;auto.
Qed.

Lemma fold_left_firstn_S_default:
  forall (l: list (F*F))(i: nat)(b: F)f,
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

Lemma firstn_map2 {A B:Type}: forall n (f: A -> A -> B) (l1 l2: list A),
    firstn n (ListUtil.map2 f l1 l2) = ListUtil.map2 f (firstn n l1) (firstn n l2).
Proof using Type.
  intro n; induction n; intros.
  - simpl; f_equal; trivial.
  - destruct l1, l2;try easy. simpl.
    rewrite IHn;auto.
Qed.

Lemma fold_left_firstn_S:
  forall (i: nat)(l1 l2: list F)(b: F) f,
  i < length l1 ->
  i < length l2 ->
  fold_left f (ListUtil.map2 pair (l1 [:S i]) (l2 [:S i])) b = 
  f (fold_left f (ListUtil.map2 pair (l1 [:i]) (l2 [:i])) b) ((ListUtil.map2 pair (l1 [:S i]) (l2 [:S i])) ! i).
Proof.
  intros.
  assert(exists l, forall i, l [:i] = (ListUtil.map2 pair (l1 [:i]) (l2 [:i])) /\ length l = length (ListUtil.map2 pair (l1) (l2))).
  { exists (ListUtil.map2 pair l1 l2);intros;split.
    + apply firstn_map2.
    + auto. 
  }
  destruct H1 as [?]. pose proof (H1 i) as []. pose proof  (H1 (S i)) as [].
  rewrite <- H4. rewrite <- H2.
  replace ((x [:S i]) ! i) with (x ! i). 2:{ unfold_default. erewrite firstn_nth;try lia;auto. }
  apply fold_left_firstn_S_default. rewrite H5. 
  rewrite ListUtil.map2_length.
  lia. 
Qed.

Lemma soundness_helper:
  forall (l:list (F * F)) (k:nat) (RNG: 1 <= k <= C.k ),
  (k > length l) ->
  (fold_left
    (fun x y => if (fst y = snd y)? then x - 1 else x) l
    (F.of_nat q k) <> 0).
Proof.
  unwrap_C. 
  induction l;simpl;intros.
  - intros;destruct k0;try easy;try lia.
    replace (S k0) with (k0 + 1)%nat by lia.
    unfold F.of_nat. replace 0%F with (F.of_Z q 0). intro.
    rewrite <- F.eq_of_Z_iff in H0. 
    apply Modulo.Z.small_mod_eq in H0;try split;try lia.
    rewrite Z.mod_small in H0;try lia. 
    assert (C.k < 2 ^ C.k). apply Zpow_facts.Zpower2_lt_lin;lia. lia.
    rewrite <- F.inv_0. pose proof F.inv_spec as [? ?]. rewrite H0.
    auto.
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
  k = (length l) ->
  fold_left (fun x y => if (fst y = snd y)? then x - 1 else x)  l (F.of_nat q k) = 0 ->
  forallb (fun x : F * F => if dec (fst x = snd x) then true else false) l = true.
Proof.
  unwrap_C.
  induction l;intros;simpl in *;trivial.
  destruct dec;simpl.
  - subst. eapply (IHl (length l));eauto;try lia.
    replace (F.of_nat q (length l)) with ((F.of_nat q (S (length l)) - 1));auto;try lia.
    replace (S (length l)) with (length l + 1)%nat by lia.
    rewrite F.of_nat_add.
    replace (F.of_nat q 1) with (@F.one q);auto.
    rewrite add_sub. fqsatz. 
  - apply soundness_helper in H0;try lia;try easy. 
Qed.

Lemma soundness_helper_lemma2:
forall l k,
k = (length l) ->
fold_left (fun x y => if (fst y = snd y)? then x - 1 else x)  l (F.of_nat q k) <> 0 ->
forallb (fun x : F * F => if dec (fst x = snd x) then true else false) l = false.
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

Lemma list_map_pair_nth_fst:
  forall i a b,
  (i < length a) %nat ->
  i < length b ->
  fst (ListUtil.map2 pair (a [:S i]) (b [:S i]) ! i) = (a [:S i]) ! i.
Proof.
  intros.
  eapply list_map_pair_nth in H0;eauto. rewrite H0;auto.
Qed.

Lemma list_map_pair_nth_snd:
  forall i a b,
  (i < length a) %nat ->
  i < length b ->
  snd (ListUtil.map2 pair (a [:S i]) (b [:S i]) ! i) = (b [:S i]) ! i.
Proof.
  intros.
  eapply list_map_pair_nth in H0;eauto. rewrite H0;auto.
Qed.

Theorem soundness: forall (c: t), 
  1 <= k <= C.k ->
  if (forallb (fun x => (fst x = snd x)? ) (ListUtil.map2 pair (' c.(a)) (' c.(b)))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c RNG. 
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
        rewrite fold_left_firstn_S at 1;try lia.
        destruct dec; try easy. rewrite list_map_pair_nth_fst, list_map_pair_nth_snd in n0; try lia.
        replace ((' a [:S i]) ! i) with  (' a ! i) in n0.
        2:{ unfold_default. erewrite firstn_nth;try lia;auto. }
        replace ((' b [:S i]) ! i) with  (' b ! i) in n0.
        2:{ unfold_default. erewrite firstn_nth;try lia;auto. } easy.
      + rewrite H; symmetry. 
        rewrite fold_left_firstn_S at 1;try lia.
        destruct dec; try fqsatz. rewrite list_map_pair_nth_fst, list_map_pair_nth_snd in e; try lia.
        replace ((' a [:S i]) ! i) with  (' a ! i) in e.
        2:{ unfold_default. erewrite firstn_nth;try lia;auto. }
        replace ((' b [:S i]) ! i) with  (' b ! i) in e.
        2:{ unfold_default. erewrite firstn_nth;try lia;auto. } easy.
  } 
  destruct (D.iter f k (F.of_nat q k, True)) as [total _cons] eqn:iter.
  destruct y as [? [?]]. apply H_inv in H1. subst.
  pose proof (IsZero.soundness checkZero). unfold IsZero.spec in H.
  assert (length (ListUtil.map2 pair (' a [:k]) (' b [:k])) = k).
  { rewrite ListUtil.map2_length. do 2 rewrite firstn_length. lia. }
  assert (RNG1: k < q).
  { destruct RNG. assert (C.k < 2 ^ C.k). apply Zpow_facts.Zpower2_lt_lin;lia. lia. }
  destruct dec.
  - rewrite H1 in e. apply soundness_helper_lemma1 in e;auto;try lia.
    replace (' a) with (' a [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_ka;auto. }
    replace (' b) with (' b [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_kb;auto. }
    destruct forallb;easy.
  - rewrite H1 in n0. apply soundness_helper_lemma2 in n0;auto.
    replace (' a) with (' a [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_ka;auto. }
    replace (' b) with (' b [:k]). 2:{ rewrite <- firstn_all. rewrite Hlen_kb;auto. }
    destruct forallb;easy.
Qed.

End _BigIsEqual.
End BigIsEqual.
