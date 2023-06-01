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

(* Source: https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/tree.circom *)
(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom *)

Module Semaphore.
Module D := DSL.
Import D.
Local Coercion N.of_nat : nat >-> N.

Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Open Scope tuple_scope.

Local Notation "x [[ i ]]" := (Tuple.nth_default 0 i x) (at level 20).
Definition nth2 {m n} (i: nat) (x: (F^n)^m) := Tuple.nth_default (repeat 0 n) i x.
Local Notation "x [ i ][ j ]" := (Tuple.nth_default 0 j (nth2 i x)) (at level 20).
Definition nth3 {m n p} (i: nat) (x: ((F^n)^m)^p) := Tuple.nth_default (repeat (repeat 0 n) m) i x.
Local Notation "x [ i ][ j ][ k ]" := (Tuple.nth_default 0 k (nth2 j (nth3 i x))) (at level 20).



Module Poseidon.
Section Poseidon.
Context {nInputs: nat}.

Definition cons (inputs: F^nInputs) (out: F) := True.

Record t : Type := 
{ inputs: F^nInputs;
  out: F;
  _cons: cons inputs out; }.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End Poseidon.

Module PoseidonHypo.
Definition poseidon_1 : F -> F. skip. Defined.
Definition poseidon_2 : F -> F -> F. skip. Defined.
Lemma poseidon_1_spec : 
  forall (p: @Poseidon.t 1) x, p.(inputs)[0] = x -> p.(Poseidon.out) = poseidon_1 x. skip. Defined.
Lemma poseidon_2_spec :
  forall (p: @Poseidon.t 2) x y, p.(inputs)[0] = x -> p.(inputs)[1] = y -> p.(Poseidon.out) = poseidon_2 x y. skip. Defined.
End PoseidonHypo.

End Poseidon.



(* Source: https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/mux1.circom#L21 *)
Module MultiMux.
Section MultiMux.
Context {n: nat}.

Definition cons (c: (F^2)^n) (s: F) (out: F^n) :=
let _C := 
    (D.iter (fun i _C =>
    _C /\
    out[i] = (c[i][1] - c[i][0])*s + c[i][0]
    ) n True) in _C.

Record t : Type := 
{ c: (F^2)^n;
  s: F;
  out: F^n;
  _cons: cons c s out; }.

Definition spec (m: t) : Prop :=
  (m.(s) = 0 -> forall i, 0 <= i < n -> m.(out)[i] = m.(c)[i][0]) /\
  (m.(s) = 1 -> forall i, 0 <= i < n -> m.(out)[i] = m.(c)[i][1]).

(* MultiMux is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c. 
  destruct c as [c s out _cons1].
  unfold spec, cons in *. simpl.
  rem_iter.
  pose (Inv1 := fun (i: nat) (_cons: Prop) => _cons -> 
                (forall j, j < i -> out [j] = (c [j ][ 1] - c [j ][ 0]) * s + c [j ][ 0])).
  assert (HInv1: Inv1 n (D.iter f n True)).
  { apply D.iter_inv; unfold Inv1;intros;try lia.
    subst. destruct H1. destruct (dec (j0 = j));intuit.
    + subst. auto.
    + apply H4;auto. lia. }
  apply HInv1 in _cons1 as inv.
  split;intros;intuit.
  - apply inv in H2. subst. fqsatz.
  - apply inv in H2. subst. fqsatz.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End MultiMux.
End MultiMux.



(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L6 *)
Module CalculateSecret.
Module Poseidon:= Poseidon.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.
Section CalculateSecret.

Definition cons (identityNullifier identityTrapdoor: F) (out: F) :=
  exists poseidon: @Poseidon.t 2, 
    poseidon.(Poseidon.inputs)[0] = identityNullifier /\
    poseidon.(Poseidon.inputs)[1] = identityTrapdoor /\
    out = poseidon.(Poseidon.out).

Record t : Type := 
{ identityNullifier: F;
  identityTrapdoor: F;
  out: F;
  _cons: cons identityNullifier identityTrapdoor out; }.

Definition spec (c: t) : Prop :=
  forall x y, 
  c.(identityNullifier) = x ->
  c.(identityTrapdoor) = y ->
  c.(out) = poseidon_2 x y.

(* CalculateSecret is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C. unfold spec. intros. destruct c. subst. simpl in *.
  destruct _cons0 as [x _cons]. destruct _cons. destruct H0.
  subst. pose proof Poseidon.PoseidonHypo.poseidon_2_spec. erewrite H;eauto.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End CalculateSecret.
End CalculateSecret.



(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L20 *)
Module CalculateIdentityCommitment.
Module Poseidon:= Poseidon.
Definition poseidon_1 := Poseidon.PoseidonHypo.poseidon_1.
Section CalculateIdentityCommitment.

Definition cons (secret: F) (out: F) :=
  exists poseidon: @Poseidon.t 1, 
    poseidon.(Poseidon.inputs)[0] = secret /\
    out = poseidon.(Poseidon.out).

Record t : Type := 
{ secret: F;
  out: F;
  _cons: cons secret out; }.

Definition spec (c: t) : Prop :=
  forall x, 
  c.(secret) = x ->
  c.(out) = poseidon_1 x.

(* CalculateIdentityCommitment is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C. unfold spec. intros. destruct c. subst. simpl in *.
  destruct _cons0 as [x _cons]. destruct _cons. 
  subst. pose proof Poseidon.PoseidonHypo.poseidon_1_spec. erewrite H;eauto.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End CalculateIdentityCommitment.
End CalculateIdentityCommitment.



(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L32 *)
Module CalculateNullifierHash.
Module Poseidon:= Poseidon.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.
Section CalculateNullifierHash.

Definition cons (externalNullifier identityNullifier: F) (out: F) :=
  exists poseidon: @Poseidon.t 2, 
    poseidon.(Poseidon.inputs)[0] = externalNullifier /\
    poseidon.(Poseidon.inputs)[1] = identityNullifier /\
    out = poseidon.(Poseidon.out).

Record t : Type := 
{ externalNullifier: F;
  identityNullifier: F;
  out: F;
  _cons: cons externalNullifier identityNullifier out; }.

Definition spec (c: t) : Prop :=
  forall x y, 
  c.(externalNullifier) = x ->
  c.(identityNullifier) = y ->
  c.(out) = poseidon_2 x y.

(* CalculateNullifierHash is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C. unfold spec. intros. destruct c. subst. simpl in *.
  destruct _cons0 as [x _cons]. destruct _cons. destruct H0.
  subst. pose proof Poseidon.PoseidonHypo.poseidon_2_spec. erewrite H;eauto.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End CalculateNullifierHash.
End CalculateNullifierHash.



(* Source: https://github.com/semaphore-protocol/semaphore/blob/ec5c69a795c95d87dcc2e69ad21b50acbb479e35/packages/circuits/tree.circom#L6 *)
Module MerkleTreeInclusionProof.
Module Poseidon:= Poseidon.
Module MultiMux:= MultiMux.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.

Section MerkleTreeInclusionProof.
Context {nLevels: nat}.

Definition cons (leaf: F) (pathIndices: F^nLevels) (siblings: F^nLevels) (root: F) :=
  exists (poseidons: (@Poseidon.t 2)^nLevels) (mux: (@MultiMux.t 2)^nLevels)
         (hashes: F^(nLevels + 1)),
  hashes[0] = leaf /\
  let _C := 
    (D.iter (fun i _C =>
    _C /\
    pathIndices[i] * (1 - pathIndices[i]) = 0 /\
    (mux[i].(MultiMux.c))[0][0] = hashes[i] /\
    mux[i].(MultiMux.c)[0][1] = siblings[i] /\
    mux[i].(MultiMux.c)[1][0] = siblings[i] /\
    mux[i].(MultiMux.c)[1][1] = hashes[i] /\
    mux[i].(MultiMux.s) = pathIndices[i] /\
    poseidons[i].(Poseidon.inputs)[0] = mux[i].(MultiMux.out)[0] /\
    poseidons[i].(Poseidon.inputs)[1] = mux[i].(MultiMux.out)[1] /\
    hashes[i + 1] = poseidons[i].(Poseidon.out)
    ) nLevels True) in _C /\
  root = hashes[nLevels].

(* MerkleTreeInclusionProof *)
Record t : Type := 
{ leaf: F;
  pathIndices: F^nLevels; 
  siblings: F^nLevels; 
  root: F;
  _cons: cons leaf pathIndices siblings root; }.

(* MerkleTreeInclusionProof specification *)
Definition spec (c: t) : Prop :=
  (forall i, 0 <= i < nLevels -> binary (c.(pathIndices)[i])) /\
  c.(root) = fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0) then (poseidon_2 y (snd x)) else (poseidon_2 (snd x) y)) 
                       (combine ('(c.(pathIndices))) ('(c.(siblings)))) c.(leaf).

Instance DefaultFF: Default (F*F). constructor. exact (0,0). Defined.
Lemma fold_left_firstn_S:
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

Lemma combine_fst_n: forall n j (l1 l2: F^n),
  j < n ->
  j < n ->
  fst (combine (' l1) (' l2) ! j) = l1 [j].
Proof.
  intros. pose proof (length_to_list l1). pose proof (length_to_list l2). 
  unfold_default. simpl. rewrite combine_nth;simpl;auto.
  rewrite nth_Default_nth_default. rewrite <- nth_default_to_list. unfold_default. auto.
  rewrite H1, H2;auto.
Qed.

Lemma combine_snd_n: forall n j (l1 l2: F^n),
  j < n ->
  j < n ->
  snd (combine (' l1) (' l2) ! j) = l2 [j].
Proof.
  intros. pose proof (length_to_list l1). pose proof (length_to_list l2). 
  unfold_default. simpl. rewrite combine_nth;simpl;auto.
  rewrite nth_Default_nth_default. rewrite <- nth_default_to_list. unfold_default. auto.
  rewrite H1, H2;auto.
Qed.

(* MerkleTreeInclusionProof is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c. 
  destruct c as [leaf pathIndices siblings root _cons]. 
  unfold spec, cons in *. simpl. 
  destruct _cons as [poseidons _cons]. destruct _cons as [mux _cons]. destruct _cons as [hashes _cons].
  destruct _cons as [_cons1 _cons2]. destruct _cons2 as [_cons2 _cons3].
  rem_iter. subst. rem_iter.
  pose (Inv1 := fun (i: nat) (_cons: Prop) => _cons -> 
                (forall j, j < i -> binary ((pathIndices)[j]))).
  assert (HInv1: Inv1 nLevels (D.iter f nLevels True)).
  { apply D.iter_inv; unfold Inv1;intros;try lia.
    subst. destruct H1. destruct (dec (j0 = j));intuit.
    + subst. unfold binary. 
      destruct (dec (pathIndices [j] = 0));auto.
      destruct (dec (pathIndices [j] = 1));auto. fqsatz.
    + apply H11;auto. lia. }
  apply HInv1 in _cons2 as inv1.
  split;intros. apply inv1;lia.
  pose (Inv2 := fun (i: nat) (_cons: Prop) => _cons -> 
                (hashes [i] = (fold_left 
                (fun (y : F) (x : F * F) => if dec (fst x = 0) then poseidon_2 y (snd x) else poseidon_2 (snd x) y)
                (firstn i (combine (' pathIndices) (' siblings)))
                (hashes [0])))).
  assert (HInv2: Inv2 nLevels (D.iter f nLevels True)).
  { apply D.iter_inv; unfold Inv2;intros;try lia. 
    + simpl. auto.
    + subst. destruct H1.
      do 8 destruct H2 as [? H2]. pose proof (MultiMux.soundness (mux [j])). unfold MultiMux.spec in H11.
      erewrite (fold_left_firstn_S (combine (' pathIndices) (' siblings)));simpl.
      2:{ pose_lengths. rewrite combine_length. rewrite _Hlen4, _Hlen2. lia. }
      assert(FST: (fst (combine (' pathIndices) (' siblings) ! j) = pathIndices [j])). 
      { rewrite combine_fst_n;auto. }
      assert(SND: (snd (combine (' pathIndices) (' siblings) ! j) = siblings [j])). 
      { rewrite combine_snd_n;auto. }
      rewrite FST, SND in *. destruct H11. pose proof (H H1) as HASHJ.
      destruct (dec (pathIndices [j] = 0)).
      ++ rewrite e in *. pose proof (H11 H8). 
         rewrite H13 in H9;try lia. rewrite H13 in H10;try lia.
         rewrite HASHJ in H4. rewrite H4, H6 in *. replace (S j) with (j+1)%nat by lia.
         rewrite H2. apply Poseidon.PoseidonHypo.poseidon_2_spec;auto. 
      ++ pose proof (inv1 j). destruct H13;try lia;try easy. rewrite H13 in *. pose proof (H12 H8). 
         rewrite H14 in H9;try lia. rewrite H14 in H10;try lia.
         rewrite HASHJ in H7. rewrite H5, H7 in *. replace (S j) with (j+1)%nat by lia.
         rewrite H2. apply Poseidon.PoseidonHypo.poseidon_2_spec;auto.  }
  apply HInv2 in _cons2 as inv2.
  rewrite inv2. rewrite combine_firstn. pose_lengths.
  assert((' siblings [:nLevels]) = (' siblings)).
  { rewrite <- _Hlen1 at 1. apply ListUtil.List.firstn_all. }
  rewrite <- _Hlen0 at 1. rewrite ListUtil.List.firstn_all. rewrite H. auto.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End MerkleTreeInclusionProof.
End MerkleTreeInclusionProof.



(* Source: https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L47 *)
Module Semaphore.
Module Poseidon:= Poseidon.
Module MerkleTreeInclusionProof:= MerkleTreeInclusionProof.
Import Poseidon MerkleTreeInclusionProof CalculateSecret CalculateIdentityCommitment CalculateNullifierHash.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.

Section Semaphore.
Context {nLevels: nat}.

Definition cons (identityNullifier: F) (identityTrapdoor: F) (treePathIndices: F^nLevels) 
                (treeSiblings: F^nLevels) (signalHash: F) (externalNullifier: F) 
                (root: F) (nullifierHash: F) :=
  exists (calculateSecret: CalculateSecret.t) (calculateIdentityCommitment: CalculateIdentityCommitment.t) (calculateNullifierHash: CalculateNullifierHash.t) (inclusionProof: @MerkleTreeInclusionProof.t nLevels),
  calculateSecret.(CalculateSecret.identityNullifier) = identityNullifier /\
  calculateSecret.(CalculateSecret.identityTrapdoor) = identityTrapdoor /\
  calculateIdentityCommitment.(CalculateIdentityCommitment.secret) = calculateSecret.(CalculateSecret.out) /\
  calculateNullifierHash.(CalculateNullifierHash.externalNullifier) = externalNullifier /\
  calculateNullifierHash.(CalculateNullifierHash.identityNullifier) = identityNullifier /\
  inclusionProof.(MerkleTreeInclusionProof.leaf) = calculateIdentityCommitment.(CalculateIdentityCommitment.out) /\
  inclusionProof.(MerkleTreeInclusionProof.pathIndices) = treePathIndices /\
  inclusionProof.(MerkleTreeInclusionProof.siblings) = treeSiblings /\
  root = inclusionProof.(MerkleTreeInclusionProof.root) /\
  nullifierHash = calculateNullifierHash.(CalculateNullifierHash.out) /\
  signalHash * signalHash = signalHash.

(* Semaphore *)
Record t : Type := 
{ identityNullifier: F;
  identityTrapdoor: F;
  treePathIndices: F^nLevels; 
  treeSiblings: F^nLevels; 
  signalHash: F;
  externalNullifier: F;
  root: F;
  nullifierHash: F;
  _cons: cons identityNullifier identityTrapdoor treePathIndices treeSiblings signalHash externalNullifier root nullifierHash; }.

(* Semaphore specification *)
Definition spec (c: t) : Prop :=
  c.(nullifierHash) = poseidon_2 c.(externalNullifier) c.(identityNullifier) /\
  let identityCommitment := poseidon_1 (poseidon_2 c.(identityNullifier) c.(identityTrapdoor)) in
  c.(root) = fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0) then (poseidon_2 y (snd x)) else (poseidon_2 (snd x) y)) 
                       (combine ('(c.(treePathIndices))) ('(c.(treeSiblings)))) identityCommitment.

(* Semaphore is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c.
  destruct c as [identityNullifier identityTrapdoor treePathIndices treeSiblings signalHash externalNullifier root nullifierHash _cons].
  unfold spec, cons in *. simpl.
  destruct _cons as [calculateSecret _cons]. destruct _cons as [calculateIdentityCommitment _cons]. destruct _cons as [calculateNullifierHash _cons].
  destruct _cons as [inclusionProof _cons]. destruct _cons as [_cons1 _cons2]. destruct _cons2 as [_cons2 _cons3].
  destruct _cons3 as [_cons3 _cons4]. destruct _cons4 as [_cons4 _cons5]. destruct _cons5 as [_cons5 _cons6].
  destruct _cons6 as [_cons6 _cons7]. destruct _cons7 as [_cons7 _cons8]. destruct _cons8 as [_cons8 _cons9].
  destruct _cons9 as [_cons9 _cons10]. destruct _cons10 as [_cons10 _cons11]. subst.
  pose proof (CalculateSecret.soundness calculateSecret). pose proof (CalculateIdentityCommitment.soundness calculateIdentityCommitment). 
  pose proof (CalculateNullifierHash.soundness calculateNullifierHash). pose proof (MerkleTreeInclusionProof.soundness inclusionProof).
  unfold CalculateSecret.spec, CalculateIdentityCommitment.spec, CalculateNullifierHash.spec, MerkleTreeInclusionProof.spec in *.
  split;auto.
  destruct H2. rewrite H3.
  rewrite _cons6. erewrite H0;eauto. erewrite <- H;auto.
Qed.

End Semaphore.
End Semaphore.

End Semaphore.