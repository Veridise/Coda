(* 
Circuit:
// Checks that that for every i there is only one index == 1 for all assets
template CheckIndices(n, nInAssets, nAssets) {
  signal input indices[n][nInAssets][nAssets];
  signal input amounts[n][nInAssets];

  for (var i = 0; i < n; i++) {
      for (var j = 0; j < nInAssets; j++) {
          var varSumIndices = 0;
          for (var z = 0; z < nAssets; z++) {
              varSumIndices += indices[i][j][z];
              // all indices are 0 or 1
              indices[i][j][z] * (1 - indices[i][j][z]) === 0;
          }
          // only one index for one asset is 1
          varSumIndices * (1 - varSumIndices)=== 0;
          // if amount != 0 there should be one an asset assigned to it
          varSumIndices * amounts[i][j] === amounts[i][j];
      }
  }
}
*)

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
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

From Circom Require Import Circom Util Default Tuple LibTactics Simplify Repr ListUtil.
From Circom.CircomLib Require Import Bitify.

Local Open Scope list_scope.
Local Open Scope F_scope.

Module Lightprotocol.
Module D := DSL.
Import D.
Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Open Scope tuple_scope.

Local Notation "x [ i ]" := (Tuple.nth_default 0 i x) (at level 20).
Definition nth2 {m n} (i: nat) (x: (F^n)^m) := Tuple.nth_default (repeat 0 n) i x.
Local Notation "x [ i ][ j ]" := (Tuple.nth_default 0 j (nth2 i x)) (at level 20).
Definition nth3 {m n p} (i: nat) (x: ((F^n)^m)^p) := Tuple.nth_default (repeat (repeat 0 n) m) i x.
Local Notation "x [ i ][ j ][ k ]" := (Tuple.nth_default 0 k (nth2 j (nth3 i x))) (at level 20).


Section CheckIndices.
Context {n nInAssets nAssets: nat}.

Definition cons (indices: ((F^nAssets)^nInAssets)^n)(amounts: (F^nInAssets)^n) :=
  let _C := 
    (D.iter (fun i _cons =>
    _cons /\
    (D.iter (fun j _cons =>
    _cons /\
        let varSumIndices := 0%F in
        let '(varSumIndices, _C) := 
            (D.iter (fun z  '(varSumIndices, _C) =>
                (varSumIndices + indices[i][j][z], 
                _C /\ 
                indices[i][j][z] * (1 - indices[i][j][z]) = 0
                )
                ) nAssets (varSumIndices, True)) in
        (varSumIndices * (1 - varSumIndices) = 0 /\
        varSumIndices * amounts[i][j] = amounts[i][j] /\
        _C)
      ) nInAssets True) 
      ) n True) in _C.

(* CheckIndices *)
Record t : Type := 
{ indices: ((F^nAssets)^nInAssets)^n; 
  amounts: (F^nInAssets)^n; 
  _cons: cons indices amounts }.

(* CheckIndices spec *)
Definition spec (c: t) : Prop :=
  (nAssets < q)%Z ->
  forall i j, i < n /\ j < nInAssets ->
  (forall k k', 
        k < nAssets /\ k' < nAssets ->
        c.(indices)[i][j][k'] = 1 /\ c.(indices)[i][j][k] = 1 -> k' = k) /\
  ( c.(amounts)[i][j] >z 0 -> exists k, c.(indices)[i][j][k] = 1).

Lemma fold_left_all_positive:
  forall (l:list F) (B: Forall binary l) (a:F),
  ( ^a + length l < q)%Z ->
  a <> 0 ->
  fold_left (fun x y : F => x + y) l a <> 0.
Proof.
unwrap_C.
  induction l;simpl;try easy;intros;intro;subst. 
  assert((a0 + a) <> 0).
  { pose proof (F.to_Z_range a0).
    rewrite F.eq_to_Z_iff in *. simpl in *. 
    rewrite Forall_forall in B. specialize (B a). destruct B;simpl;auto;subst.
    + rewrite F.to_Z_0 in *. do 2 rewrite Z.mod_small in *;try lia. 
    + erewrite F.to_Z_1 in *. do 2 rewrite Z.mod_small in *;try lia. 
  }
  assert(Forall binary l). rewrite Forall_forall. rewrite Forall_forall in B. intros. apply B;simpl;auto.
  rewrite Forall_forall in B. specialize (B a). destruct B;simpl;auto;subst.
  + apply IHl in H2;auto. rewrite Fadd_0_r. lia.
  + apply IHl in H2;auto. rewrite F.to_Z_add. simpl. do 2 rewrite Z.mod_small in *;try lia. 
    split;try lia. pose proof (F.to_Z_range a0). lia.
Unshelve. auto.
Qed.

Lemma fold_left_sum_0 {n1:nat}:
  forall (l:list F) (B: Forall binary l) (RNG: (length l < q)%Z),
  fold_left (fun x y : F => x + y) l 0 = 0 ->
  forall k, 
    k < length l ->
    List.nth k l 0 = 0.
Proof.
  induction l;try easy;intros.
  simpl in H.
  assert(Forall binary l). rewrite Forall_forall. rewrite Forall_forall in B. intros. apply B;simpl;auto.
  assert(a = 0).
  { destruct (dec (a=0));try easy. rewrite Forall_forall in B. specialize (B a). destruct B;simpl;auto.
    rewrite Fadd_0_l in H.
    apply fold_left_all_positive in H;try lia;auto.
    subst. simpl in *. rewrite Z.mod_small in *;try lia. 
  }
  subst. simpl. destruct k0;simpl in *;auto.
  apply IHl;auto;try lia. 
Qed.

Lemma fold_left_equal_init {n1:nat}:
  forall (l:list F) a b,
  fold_left (fun x y : F => x + y) l (1+a) = (b+1) ->
  fold_left (fun x y : F => x + y) l a = b.
Proof.
unwrap_C.
  induction l;try easy;intros;simpl in *;try lia.
  { pose proof (F.to_Z_range b). pose proof (F.to_Z_range a). destruct H0;try lia. destruct H1;try lia.
    rewrite F.eq_to_Z_iff. inversion H. 
    assert(1 mod q = 1)%Z. rewrite Z.mod_small;try lia. rewrite H4 in *.
    destruct (dec (^a < q-1)%Z);destruct (dec (^b < q-1)%Z);try lia.
    + do 2 rewrite Z.mod_small in *;intuit;try lia.
    + rewrite Z.mod_small in *;intuit;try lia. assert (^b=q-1)%Z. lia. rewrite H6 in *.
      assert ((0)%Z = ((q - 1 + 1) mod q)%Z).
      assert ((q - 1 + 1) = q)%Z. lia. rewrite H7.
      rewrite Z_mod_same_full;auto. rewrite <- H7 in H5. lia.
    + symmetry in H5. rewrite Z.mod_small in *;intuit;try lia. assert (^a=q-1)%Z. lia. rewrite H6 in *.
      assert ((0)%Z = ((1 + (q - 1)) mod q)%Z).
      assert ((1 + (q - 1)) = q)%Z. lia. rewrite H7.
      rewrite Z_mod_same_full;auto. rewrite <- H7 in H5. lia. }
  apply IHl;auto;try lia. 
  pose proof F.ring_theory q. destruct H0.
  replace (1 + (a0 + a)) with (1 + a0 + a);auto.
Qed.

Lemma fold_left_sum_1_0 {n1:nat}:
  forall (l:list F) (B: Forall binary l) (RNG: (length l < q)%Z),
  fold_left (fun x y : F => x + y) l 1 = 1 ->
  forall k, 
    k < length l ->
    List.nth k l 0 = 0.
Proof.
  intros.
  replace 1 with (@F.zero q +1)%F in H at 2. 2: apply Fadd_0_l.
  replace 1 with (1+ @F.zero q)%F in H at 1. 2: apply Fadd_0_r.
  eapply fold_left_equal_init in H;try lia.
  eapply fold_left_sum_0;eauto.
Unshelve. all:auto.
Qed.

Lemma fold_left_sum_1 {n1:nat}:
  forall (l:list F)(B: Forall binary l) (RNG: (length l < q)%Z),
  fold_left (fun x y : F => x + y) l 0 = 1 ->
  forall k1 k2, 
  k1 < length l ->
  k2 < length l ->
  List.nth k1 l 0 = 1 /\ List.nth k2 l 0 = 1 -> k1 = k2.
Proof.
  induction l;try easy;intros.
  simpl in H.
  assert(B1:Forall binary l). rewrite Forall_forall. rewrite Forall_forall in B. intros. apply B;simpl;auto.
  destruct (dec (a=0));simpl in *;subst;intuition;try easy.
  - destruct k1;try easy; destruct k2;try easy;inversion H3. 
    do 2 rewrite Z.mod_small in H6;try lia. inversion H4. do 2 rewrite Z.mod_small in H7;try lia.
    f_equal. apply H2;try lia;auto.
  - assert(a=1).
    { rewrite Forall_forall in B. specialize (B a). destruct B;simpl;auto. apply n0 in H5;easy. } subst.
    rewrite Fadd_0_l in *.
    destruct k1;try easy; destruct k2;try easy. 
    + eapply fold_left_sum_1_0 with (k:=k2) in H;eauto;try lia. rewrite H in H4.
      symmetry in H4. apply n0 in H4;easy.
    + eapply fold_left_sum_1_0 with (k:=k1) in H;eauto;try lia. rewrite H in H3.
      symmetry in H3. apply n0 in H3;easy.
    + eapply fold_left_sum_1_0 with (k:=k1) in H;eauto;try lia. rewrite H in H3.
      symmetry in H3. apply n0 in H3;easy.
Unshelve. all:auto.
Qed.

Lemma fold_left_sum_1' {n1:nat}:
  forall (l:list F)(B: Forall binary l) (RNG: (length l < q)%Z),
  fold_left (fun x y : F => x + y) l 0 = 1 ->
  exists k1, 
  k1 < length l /\
  List.nth k1 l 0 = 1.
Proof.
unwrap_C.
  induction l;simpl in *;try easy;intros.
  inversion H. do 2 rewrite Z.mod_small in H1;try lia.
  assert(B1:Forall binary l). rewrite Forall_forall. rewrite Forall_forall in B. intros. apply B;simpl;auto.
  destruct (dec (a=0));simpl in *;subst;intuition;try easy.
  - rewrite Fadd_0_l in *. apply H0 in H;try lia. destruct H. exists (S x). split;auto. lia.
    intuit.
  - rewrite Fadd_0_l in *.
    assert(a=1).
    { rewrite Forall_forall in B. specialize (B a). destruct B;simpl;auto. apply n0 in H1;easy. } subst.
    exists 0%nat. split;auto. lia.
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

Lemma forall_Forall_firstn:
  forall (P: F -> Prop) m (l: F^m),
  (forall j : nat, j < m -> P (l [j])) ->
  Forall P (firstn m (' l)).
Proof.
  intros. pose_lengths.
  assert(Forall P (' l [:length('l)])).
  { rewrite Forall_forall;intros. rewrite firstn_all in H0.
    pose proof (@In_nth F (' l) x 0).
    apply H1 in H0. destruct H0. intuit. 
    subst. fold_default. rewrite nth_Default_List_tuple;auto. apply H. lia. }
  rewrite _Hlen in *. auto.
Qed.

Lemma soundness_lemma: 
forall (indices_ij: (F^nAssets)) amounts_ij,
    (let '(varSumIndices, _C) :=
        D.iter
            (fun (z : nat) '(varSumIndices, _C) =>
            (varSumIndices + indices_ij[z],
            _C /\
            indices_ij[ z] *
            (1 - indices_ij[ z]) = 0)) nAssets
            (0, True) in
        varSumIndices * (1 - varSumIndices) = 0 /\
        varSumIndices * amounts_ij =
        amounts_ij /\ _C )->
    (nAssets < q)%Z ->
    (forall k k', 
        k < nAssets /\ k' < nAssets ->
        indices_ij[k'] = 1 /\ indices_ij[k] = 1 -> k' = k) /\
    (amounts_ij >z 0 -> exists k, indices_ij[k] = 1).
Proof.
  unwrap_C.
  intros indices_ij amounts_ij. destruct D.iter eqn: iter;intros. rename H0 into RNG.
  rem_iter. pose_lengths.
  pose (Inv := fun (z:nat) '((total, _cons): (F * Prop)) => _cons ->
        total = (fold_left 
                    (fun x y => x + y) 
                    (firstn z (' indices_ij))
                    0) /\
        (forall j, j < z -> binary (indices_ij[j]))
        ).
  assert(HInv: Inv nAssets (D.iter f0 nAssets (0, True))).
  { apply D.iter_inv.
    unfold Inv;intros. 
    - intuition;try easy.
    - intuition;try easy. unfold Inv. destruct (f0 j b) eqn: iter';intros. subst.
      destruct b. inversion iter'. subst. unfold Inv in H1. intuition.
      + rewrite H1. rewrite fold_left_firstn_S;try lia.
        rewrite nth_Default_List_tuple;auto. 
      + destruct (dec (j0 < j));auto.
        assert(j0=j) by lia;subst. unfold binary.
        destruct (dec (indices_ij[j] = 0)).
        * auto.
        * right. fqsatz. 
  }
  assert(BF: binary f). { intuition. destruct (dec (f = 0)). * unfold binary. auto. * right. fqsatz. }
  unfold Inv in HInv. rewrite iter in HInv. intuition.
  - assert(ForallB: Forall binary (' indices_ij [:nAssets])).
    { apply forall_Forall_firstn;auto. }
    destruct BF;subst;symmetry in H3.
    + eapply fold_left_sum_0 with (k:=k0) in H3;eauto;
      try rewrite firstn_length;try rewrite _Hlen;try lia.
      assert (indices_ij [k0] = 0).
      replace (' indices_ij [:nAssets]) with (' indices_ij [:length (' indices_ij)])in H3.
      rewrite firstn_all in H3.
      fold_default' H3.
      rewrite nth_Default_List_tuple in H3;auto. 
      rewrite _Hlen;auto. fqsatz. 
    + eapply fold_left_sum_1 in H3;eauto;
      try rewrite firstn_length;try rewrite _Hlen;try lia. 
      replace (' indices_ij [:nAssets]) with (' indices_ij [:length (' indices_ij)]) by (rewrite _Hlen;auto).
      rewrite firstn_all.
      fold_default. intuition;
      rewrite nth_Default_List_tuple;auto.
  - assert(ForallB: Forall binary (' indices_ij [:nAssets])).
    { apply forall_Forall_firstn;auto. }
    destruct BF;subst;symmetry in H3.
    + destruct (dec (amounts_ij = 0));try fqsatz. subst. simpl in *. rewrite Zmod_0_l in H1;lia.
    + replace (' indices_ij [:nAssets]) with (' indices_ij [:length (' indices_ij)]) in *.
      eapply fold_left_sum_1' in H3;eauto;
      try rewrite firstn_length;try rewrite _Hlen;try lia.
      destruct H3;intuition. exists x.
      rewrite firstn_all in H6, H5.
      rewrite fold_nth in H6; subst; try lia.
      rewrite nth_Default_List_tuple in H6;auto. 
      rewrite _Hlen;auto.
Unshelve. all: auto.
Qed.

Lemma iter_f_Prop:
  forall f n,
  D.iter (fun i cons => cons /\ f i) n True ->
  forall i, i < n -> f i.
Proof.
  induction n0;unfold D.iter in *;auto;intros.
  lia.
  destruct (dec (i<n0));auto.
  - apply IHn0;try lia. rewrite D.iter'_S in H. easy.
  - assert(i=n0) by lia. subst. rewrite D.iter'_S in H. easy.
Qed.

(* CheckIndices is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c. 
  destruct c as [indices amounts _cons]. 
  unfold spec, cons in *. simpl.
  rem_iter. intros. subst. 
  eapply iter_f_Prop with (i:=i) in _cons;try easy.  
  eapply iter_f_Prop with (i:=j) in _cons;try easy. 
  eapply (soundness_lemma (nth2 j (nth3 i indices)));eauto.
Qed.

End CheckIndices.

End Lightprotocol.