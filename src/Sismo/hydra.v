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
Require Import Ring.

From Circom Require Import Circom Util Default Tuple LibTactics Simplify Repr ListUtil.
From Circom.CircomLib Require Import Bitify Comparators EdDSA.

Local Open Scope list_scope.
Local Open Scope F_scope.

(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/hydra-s2.circom *)
(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/common/verify-hydra-commitment.circom *)
(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/common/verify-merkle-path.circom *)

Module Hydra.
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


(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/common/verify-merkle-path.circom#L10 *)
Module PositionSwitcher.
Section PositionSwitcherProof.

Definition cons (_in: (F^2)) (s: F) (out: F^2) :=
  s * (1 - s) = 0 /\
  out[0] = (_in[1] - _in[0])*s + _in[0] /\
  out[1] = (_in[0] - _in[1])*s + _in[1].

Record t : Type := 
{ _in: F^2;
  s: F;
  out: F^2;
  _cons: cons _in s out; }.

Definition spec (m: t) : Prop :=
  binary m.(s) /\
  (m.(s) = 0 -> m.(out)[0] = m.(_in)[0] /\ m.(out)[1] = m.(_in)[1]) /\
  (m.(s) = 1 -> m.(out)[0] = m.(_in)[1] /\ m.(out)[1] = m.(_in)[0]).
(*   - (1) s is binary
     - (2) out[0] = s ? in[1] : in[0]
     - (3) out[1] = s ? in[0] : in[1] *)


(* PositionSwitcher is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c. 
  destruct c as [_in s out _cons1].
  unfold spec, cons in *. simpl.
  split;intros;intuit.
  - unfold binary. destruct (dec (s = 0));try fqsatz;auto.
    destruct (dec (s = 1));try fqsatz;auto.
  - subst. fqsatz.
  - subst. fqsatz.
  - subst. fqsatz.
  - subst. fqsatz.
Qed.


Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End PositionSwitcherProof.
End PositionSwitcher.





(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/common/verify-merkle-path.circom#L24 *)
Module VerifyMerklePath.
Module Poseidon:= Poseidon.
Module PositionSwitcher:= PositionSwitcher.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.

Section VerifyMerklePathProof.
Context {levels: nat}.

Definition cons (leaf: F) (root: F) (enabled: F) (pathElements: F^levels) (pathIndices: F^levels) :=
  exists (selectors: PositionSwitcher.t^levels) (hashers: (@Poseidon.t 2)^levels) (computedPath: F^levels),
  let _C :=
    (D.iter (fun i _C =>
    _C /\
    selectors[i].(PositionSwitcher._in)[0] = (if i =? 0 then leaf else computedPath[i - 1]) /\
    selectors[i].(PositionSwitcher._in)[1] = pathElements[i] /\
    selectors[i].(PositionSwitcher.s) = pathIndices[i] /\
    hashers[i].(Poseidon.inputs)[0] = selectors[i].(PositionSwitcher.out)[0] /\
    hashers[i].(Poseidon.inputs)[1] = selectors[i].(PositionSwitcher.out)[1] /\
    computedPath[i] = hashers[i].(Poseidon.out))levels True)
  in _C /\
  (root - computedPath[levels - 1])*enabled = 0.

(* VerifyMerklePath *)
Record t : Type := 
{ leaf: F;
  root: F;
  enabled: F;
  pathElements: F^levels;
  pathIndices: F^levels;
  _cons: cons leaf root enabled pathElements pathIndices; }.

(* VerifyMerklePathProof specification *)
Definition spec (c: t) : Prop :=
  (forall i, 0 <= i < levels -> binary (c.(pathIndices)[i])) /\
  (c.(enabled) <> 0 -> c.(root) = fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0) then (poseidon_2 y (snd x)) else (poseidon_2 (snd x) y)) 
                       (combine ('(c.(pathIndices))) ('(c.(pathElements)))) c.(leaf)).

(*   - (1) forall i, 0 <= i < levels -> pathIndices[i] is binary
     - (2) enabled != 0 -> 
        root = foldl (fun x y => if (fst x = 0) then (poseidons_2 y (snd x)) else (poseidons_2 (snd x) y)) 
            (combine pathIndices pathElements) leaf *)

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

(* VerifyMerklePathProof is sound *)
Theorem soundness:
  forall (c: t), spec c.
Proof.
  unwrap_C.
  intros c. 
  destruct c as [leaf root enabled pathElements pathIndices _cons]. 
  unfold spec, cons in *. simpl. 
  destruct _cons as [switchs _cons]. destruct _cons as [poseidons _cons]. destruct _cons as [hashes _cons].
  destruct _cons as [_cons1 _cons2].
  rem_iter. subst. rem_iter.
  pose (Inv1 := fun (i: nat) (_cons: Prop) => _cons -> 
                (forall j, j < i -> binary ((pathIndices)[j]))).
  assert (HInv1: Inv1 levels (D.iter f levels True)).
  { apply D.iter_inv; unfold Inv1;intros;try lia.
    subst. destruct H1. destruct (dec (j0 = j));intuit.
    + subst.
      pose proof (PositionSwitcher.soundness (switchs [j])). unfold PositionSwitcher.spec in H.
      intuit. unfold binary in *. rewrite H5 in *. auto.
    + apply H8;auto. lia. }
  apply HInv1 in _cons1 as inv1.
  split;intros. apply inv1;lia.
  pose (Inv2 := fun (i: nat) (_cons: Prop) => _cons -> 
                (hashes [i - 1] = (fold_left 
                (fun (y : F) (x : F * F) => if dec (fst x = 0) then poseidon_2 y (snd x) else poseidon_2 (snd x) y)
                (firstn i (combine (' pathIndices) (' pathElements)))
                (leaf)))).
  assert (HInv2: Inv2 levels (D.iter f levels True)).
  { apply D.iter_inv; unfold Inv2;intros;try lia. 
    + simpl. auto. skip. 
    + subst. destruct H2.
      do 5 destruct H3 as [? H3]. 
      pose proof (PositionSwitcher.soundness (switchs [j])). unfold PositionSwitcher.spec in H9.
      erewrite (fold_left_firstn_S (combine (' pathIndices) (' pathElements)));simpl.
      2:{ pose_lengths. rewrite combine_length. rewrite _Hlen4, _Hlen3. lia. }
      assert(FST: (fst (combine (' pathIndices) (' pathElements) ! j) = pathIndices [j])). 
      { rewrite combine_fst_n;auto. }
      assert(SND: (snd (combine (' pathIndices) (' pathElements) ! j) = pathElements [j])). 
      { rewrite combine_snd_n;auto. }
      rewrite FST, SND in *. destruct H9, H10. pose proof (H0 H2) as HASHJ.
      replace (j - 0)%nat with j by lia.
      destruct (dec (pathIndices [j] = 0)).
      ++ rewrite e in *. pose proof (H10 H6). inversion H12. 
         rewrite H13 in H7;try lia. rewrite H14 in H8;try lia.
         rewrite HASHJ in H4. rewrite H4, H5 in *.
         rewrite H3. apply Poseidon.PoseidonHypo.poseidon_2_spec;auto.
         rewrite H7. destruct j;try easy. 
      ++ pose proof (inv1 j). destruct H12;try lia;try easy. rewrite H12 in *. 
         pose proof (H11 H6). destruct H13. 
         rewrite H13 in *;try lia. rewrite H14 in *;try lia.
         rewrite H4, H5 in *.
         rewrite HASHJ in H8. rewrite H3. apply Poseidon.PoseidonHypo.poseidon_2_spec;auto.
          rewrite H8. destruct j;try easy. 
  }
  apply HInv2 in _cons1 as inv2.
  assert (root = hashes [levels - 1]). fqsatz. subst.
  rewrite inv2. rewrite combine_firstn. pose_lengths.
  assert((' pathElements [:levels]) = (' pathElements)).
  { rewrite <- _Hlen1 at 1. apply ListUtil.List.firstn_all. }
  rewrite <- _Hlen0 at 1. rewrite ListUtil.List.firstn_all. rewrite H0. auto.
Qed.

Theorem circuit_disabled (leaf: F) (enabled: F) (pathElements: F^levels) (pathIndices: F^levels)
(selectors: PositionSwitcher.t^levels) (hashers: (@Poseidon.t 2)^levels) (computedPath: F^levels):
let _C :=
  (D.iter (fun i _C =>
  _C /\
  selectors[i].(PositionSwitcher._in)[0] = (if i =? 0 then leaf else computedPath[i - 1]) /\
  selectors[i].(PositionSwitcher._in)[1] = pathElements[i] /\
  selectors[i].(PositionSwitcher.s) = pathIndices[i] /\
  hashers[i].(Poseidon.inputs)[0] = selectors[i].(PositionSwitcher.out)[0] /\
  hashers[i].(Poseidon.inputs)[1] = selectors[i].(PositionSwitcher.out)[1] /\
  computedPath[i] = hashers[i].(Poseidon.out))levels True)
in _C ->
forall root,
enabled = 0 ->
(root - computedPath[levels - 1])*enabled = 0.
Proof.
  intros.
  subst. rewrite Fmul_0_r. auto.
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End VerifyMerklePathProof.
End VerifyMerklePath.





(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/common/verify-hydra-commitment.circom#L10 *)
Module VerifyHydraCommitment.
Module Poseidon := Poseidon.
Module EdDSA := EdDSA.
Module EdDSAPoseidonVerifier := EdDSAPoseidonVerifier.

Section VerifyHydraCommitmentProof.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.

Definition eddsa_poseidon := EdDSA.EdDSAPoseidonVerifier.eddsa_poseidon.

Definition cons (address: F)(accountSecret: F)(vaultSecret: F)(enabled: F)
                (commitmentMapperPubKey: F^2)(commitmentReceipt: F^3): Prop :=
  exists (commitment: (@Poseidon.t 2)) (message: (@Poseidon.t 2)) (eddsa: EdDSAPoseidonVerifier.t),
    commitment.(Poseidon.inputs)[0] = vaultSecret /\
    commitment.(Poseidon.inputs)[1] = accountSecret /\
    message.(Poseidon.inputs)[0] = address /\
    message.(Poseidon.inputs)[1] = commitment.(Poseidon.out) /\
    eddsa.(EdDSAPoseidonVerifier.enabled) = enabled /\
    eddsa.(EdDSAPoseidonVerifier.Ax) = commitmentMapperPubKey[0] /\
    eddsa.(EdDSAPoseidonVerifier.Ay) = commitmentMapperPubKey[1] /\
    eddsa.(EdDSAPoseidonVerifier.R8x) = commitmentReceipt[0] /\
    eddsa.(EdDSAPoseidonVerifier.R8y) = commitmentReceipt[1] /\
    eddsa.(EdDSAPoseidonVerifier.S) = commitmentReceipt[2] /\
    eddsa.(EdDSAPoseidonVerifier.M) = message.(Poseidon.out).

(* VerifyHydraCommitment *)
Record t: Type := mk {
  address: F;
  accountSecret: F;
  vaultSecret: F;
  enabled: F;
  commitmentMapperPubKey: F^2;
  commitmentReceipt: F^3;
  _cons: cons address accountSecret vaultSecret enabled commitmentMapperPubKey commitmentReceipt
}.

Definition spec (c: t): Prop :=
  c.(enabled) <> 0 ->
  let message := poseidon_2 c.(address) (poseidon_2 c.(vaultSecret) c.(accountSecret)) in
  eddsa_poseidon (c.(commitmentMapperPubKey)[0]) (c.(commitmentMapperPubKey)[1]) (c.(commitmentReceipt)[2]) (c.(commitmentReceipt)[0]) (c.(commitmentReceipt)[1]) message.

(* - (1) enabled != 0 ->
        let message = poseidons_2 address (poseidons_2 vaultSecret accountSecret) in 
        eddsa_poseidon commitmentMapperPubKey[0] commitmentMapperPubKey[1] commitmentReceipt[2] commitmentReceipt[0] commitmentReceipt[1] message *)

Theorem soundness: forall (c: t), spec c.
Proof.
  intros. unfold spec. intuition.
  destruct c. simpl in *. intuition.
  destruct _cons0 as [commitment _cons].
  destruct _cons as [message _cons].
  destruct _cons as [eddsa _cons].
  intuition.
  pose proof (Poseidon.PoseidonHypo.poseidon_2_spec commitment) as commitment_spec.
  pose proof (Poseidon.PoseidonHypo.poseidon_2_spec message) as message_spec. 
  pose proof (CircomLib.EdDSA.EdDSAPoseidonVerifier.EdDSAPoseidonVerifierProof.EdDSAPoseidonVerifier_spec eddsa) as eddsa_spec.
  intuit. subst.
  apply eddsa_spec in H.
  rewrite H5, H6, H7, H8, H9, H11 in H. unfold eddsa_poseidon. unfold poseidon_2.
  rewrite <- message_spec;auto.
  rewrite <- commitment_spec;auto.
Qed.

Definition tt: Prop := True.

Theorem circuit_disabled: forall (c:t), c.(enabled) = 0 -> tt.
Proof.
  intros.
  destruct c. simpl in *. intuition.
  destruct _cons0 as [commitment _cons].
  destruct _cons as [message _cons].
  destruct _cons as [eddsa _cons].
  intuit.
  destruct eddsa as [enabled Ax Ay R8x R8y S M cons]. simpl in *.
  pose proof (CircomLib.EdDSA.EdDSAPoseidonVerifier.EdDSAPoseidonVerifierProof.EdDSAPoseidonVerifier_spec_disabled
  Ax Ay R8x R8y S M) as eddsa_spec_disabled.
  destruct cons. do 2 destruct H10. intuit. subst.
  specialize (eddsa_spec_disabled x x0 x1).
  intuit.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.BabyDbl.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.BabyDbl.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.BabyDbl.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.edwards_mult.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.edwards_add.
  destruct CircomLib.EdDSA.EdDSAPoseidonVerifier.edwards_mult.
  intuit.
  (* signals are unconstrained *)
  assert(CircomLib.EdDSA.EdDSAPoseidonVerifier.EdDSAPoseidonVerifierProof.unconstrained
  f9 f7). auto.
  assert(CircomLib.EdDSA.EdDSAPoseidonVerifier.EdDSAPoseidonVerifierProof.unconstrained
  f10 f8). auto.
  unfold tt. auto.
Qed.

Definition wgen: t. skip. Defined.
#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End VerifyHydraCommitmentProof.
End VerifyHydraCommitment.





(* Source: https://github.com/sismo-core/hydra-s2-zkps/blob/main/circuits/hydra-s2.circom#L16 *)
Module HydraS2.
Module VerifyMerklePath := VerifyMerklePath.
Module VerifyHydraCommitment := VerifyHydraCommitment.
Module Poseidon := Poseidon.
Module B := Bitify.
Module Cmp := Comparators.
Module R := Repr.

Section HydraS2Proof.
Context (registryTreeHeight: nat).
Context (accountsTreeHeight: nat).

Import B R VerifyHydraCommitment VerifyMerklePath Poseidon Cmp.
Definition poseidon_2 := Poseidon.PoseidonHypo.poseidon_2.

Definition cons (sourceIdentifier: F) (sourceSecret: F) (sourceValue: F) (vaultSecret: F) (sourceCommitmentReceipt: F^3)
                (destinationIdentifier: F) (destinationSecret: F) (destinationCommitmentReceipt: F^3)
                (accountMerklePathElements: F^accountsTreeHeight) (accountMerklePathIndices: F^accountsTreeHeight) (accountsTreeRoot: F)
                (registryMerklePathElements: F^registryTreeHeight) (registryMerklePathIndices: F^registryTreeHeight) (registryTreeRoot: F)
                (extraData: F) (commitmentMapperPubKey: F^2)
                (requestIdentifier: F) (proofIdentifier: F)
                (statementValue: F) (statementComparator: F) (accountsTreeValue: F)
                (vaultIdentifier: F) (vaultNamespace: F)
                (sourceVerificationEnabled: F) (destinationVerificationEnabled: F) : Prop :=
exists (sourceCommitmentVerification: VerifyHydraCommitment.t) (destinationCommitmentVerification: VerifyHydraCommitment.t)
       (accountsTreeValueIsZero: IsZero.t) (accountLeafConstructor: @Poseidon.t 2) (accountsTreesPathVerifier: @VerifyMerklePath.t accountsTreeHeight)
       (registryLeafConstructor: @Poseidon.t 2) (registryTreePathVerifier: @VerifyMerklePath.t registryTreeHeight)
       (sourceInRange: @Num2Bits.t 252) (statementInRange: @Num2Bits.t 252) (leq: @LessEqThan.t 252)
       (sourceSecretHash: F) (sourceSecretHasher: @Poseidon.t 2) (requestIdentifierIsZero: IsZero.t) (proofIdentifierHasher: @Poseidon.t 2)
       (vaultNamespaceIsZero: IsZero.t) (vaultIdentifierHasher: @Poseidon.t 2),
  (* Verify the source account went through the Hydra Delegated Proof of Ownership
     That means the user own the source address *)
  sourceCommitmentVerification.(VerifyHydraCommitment.address) = sourceIdentifier /\
  sourceCommitmentVerification.(VerifyHydraCommitment.vaultSecret) = vaultSecret /\
  sourceCommitmentVerification.(VerifyHydraCommitment.accountSecret) = sourceSecret /\
  sourceCommitmentVerification.(VerifyHydraCommitment.enabled) = sourceVerificationEnabled /\
  sourceCommitmentVerification.(VerifyHydraCommitment.commitmentMapperPubKey) = commitmentMapperPubKey /\
  sourceCommitmentVerification.(VerifyHydraCommitment.commitmentReceipt) = sourceCommitmentReceipt /\
  (* Verify the destination account went through the Hydra Delegated Proof of Ownership
     That means the user own the destination address *)
  destinationCommitmentVerification.(VerifyHydraCommitment.address) = destinationIdentifier /\
  destinationCommitmentVerification.(VerifyHydraCommitment.vaultSecret) = vaultSecret /\
  destinationCommitmentVerification.(VerifyHydraCommitment.accountSecret) = destinationSecret /\
  destinationCommitmentVerification.(VerifyHydraCommitment.enabled) = destinationVerificationEnabled /\
  destinationCommitmentVerification.(VerifyHydraCommitment.commitmentMapperPubKey) = commitmentMapperPubKey /\
  destinationCommitmentVerification.(VerifyHydraCommitment.commitmentReceipt) = destinationCommitmentReceipt /\
  accountsTreeValueIsZero.(IsZero._in) = accountsTreeValue /\
  (* Recreating the leaf *)
  accountLeafConstructor.(Poseidon.inputs)[0] = sourceIdentifier /\
  accountLeafConstructor.(Poseidon.inputs)[1] = sourceValue /\
  accountsTreesPathVerifier.(VerifyMerklePath.leaf) = accountLeafConstructor.(Poseidon.out) /\
  accountsTreesPathVerifier.(VerifyMerklePath.root) = accountsTreeRoot /\
  accountsTreesPathVerifier.(VerifyMerklePath.enabled) = (1 - accountsTreeValueIsZero.(IsZero.out)) /\
  accountsTreesPathVerifier.(VerifyMerklePath.pathElements) = accountMerklePathElements /\
  accountsTreesPathVerifier.(VerifyMerklePath.pathIndices) = accountMerklePathIndices /\
  (* Recreating the leaf *)
  registryLeafConstructor.(Poseidon.inputs)[0] = accountsTreeRoot /\
  registryLeafConstructor.(Poseidon.inputs)[1] = accountsTreeValue /\
  registryTreePathVerifier.(VerifyMerklePath.leaf) = registryLeafConstructor.(Poseidon.out) /\
  registryTreePathVerifier.(VerifyMerklePath.root) = registryTreeRoot /\
  registryTreePathVerifier.(VerifyMerklePath.enabled) = (1 - accountsTreeValueIsZero.(IsZero.out)) /\
  registryTreePathVerifier.(VerifyMerklePath.pathElements) = registryMerklePathElements /\
  registryTreePathVerifier.(VerifyMerklePath.pathIndices) = registryMerklePathIndices /\
  (* Verify statement value validity *)
  sourceInRange.(Num2Bits._in) = sourceValue /\
  statementInRange.(Num2Bits._in) = statementValue /\
  leq.(LessEqThan._in)[0] = statementValue /\
  leq.(LessEqThan._in)[1] = sourceValue /\
  leq.(LessEqThan.out) = 1 /\
  0 = (statementComparator - 1) * statementComparator /\
  sourceValue = sourceValue+((statementValue-sourceValue)*statementComparator) /\
  (* Verify the proofIdentifier is valid
     compute the sourceSecretHash using the hash of the sourceSecret *)
  sourceSecretHasher.(Poseidon.inputs)[0] = sourceSecret /\
  sourceSecretHasher.(Poseidon.inputs)[1] = 1 /\
  sourceSecretHash = sourceSecretHasher.(Poseidon.out) /\
  (* Check the proofIdentifier is valid only if requestIdentifier is not 0 *)
  requestIdentifierIsZero.(IsZero._in) = requestIdentifier /\
  proofIdentifierHasher.(Poseidon.inputs)[0] = sourceSecretHash /\
  proofIdentifierHasher.(Poseidon.inputs)[1] = requestIdentifier /\
  (proofIdentifierHasher.(Poseidon.out) - proofIdentifier) * (1 - requestIdentifierIsZero.(IsZero.out)) = 0 /\
  (* Compute the vaultIdentifier *)
  vaultNamespaceIsZero.(IsZero._in) = vaultNamespace /\
  vaultIdentifierHasher.(Poseidon.inputs)[0] = vaultSecret /\
  vaultIdentifierHasher.(Poseidon.inputs)[1] = vaultNamespace /\
  (vaultIdentifierHasher.(Poseidon.out) - vaultIdentifier) * (1 - vaultNamespaceIsZero.(IsZero.out)) = 0.

(* HydraS2 *)
Record t := mk {
  sourceIdentifier: F;
  sourceSecret: F;
  sourceValue: F;
  vaultSecret: F;
  sourceCommitmentReceipt: F^3;
  destinationIdentifier: F;
  destinationSecret: F;
  destinationCommitmentReceipt: F^3;
  accountMerklePathElements: F^accountsTreeHeight;
  accountMerklePathIndices: F^accountsTreeHeight;
  accountsTreeRoot: F;
  registryMerklePathElements: F^registryTreeHeight;
  registryMerklePathIndices: F^registryTreeHeight;
  registryTreeRoot: F;
  extraData: F;
  commitmentMapperPubKey: F^2;
  requestIdentifier: F;
  proofIdentifier: F;
  statementValue: F;
  statementComparator: F;
  accountsTreeValue: F;
  vaultIdentifier: F;
  vaultNamespace: F;
  sourceVerificationEnabled: F;
  destinationVerificationEnabled: F;
  _cons: cons sourceIdentifier sourceSecret sourceValue vaultSecret sourceCommitmentReceipt destinationIdentifier destinationSecret destinationCommitmentReceipt accountMerklePathElements accountMerklePathIndices accountsTreeRoot registryMerklePathElements registryMerklePathIndices registryTreeRoot extraData commitmentMapperPubKey requestIdentifier proofIdentifier statementValue statementComparator accountsTreeValue vaultIdentifier vaultNamespace sourceVerificationEnabled destinationVerificationEnabled;
  }.

(* HydraS2 Specifications *)
Definition spec (c: t): Prop :=
  (* (1) *)
  ( c.(sourceVerificationEnabled) <> 0 ->
    let sourceSecretHash := poseidon_2 c.(sourceIdentifier) (poseidon_2 c.(vaultSecret) c.(sourceSecret)) in
    eddsa_poseidon (c.(commitmentMapperPubKey)[0]) (c.(commitmentMapperPubKey)[1]) (c.(sourceCommitmentReceipt)[2]) (c.(sourceCommitmentReceipt)[0]) (c.(sourceCommitmentReceipt)[1]) sourceSecretHash) /\
  (* (2) *)
  ( c.(destinationVerificationEnabled) <> 0 ->
    let destinationSecretHash := poseidon_2 c.(destinationIdentifier) (poseidon_2 c.(vaultSecret) c.(destinationSecret)) in
    eddsa_poseidon (c.(commitmentMapperPubKey)[0]) (c.(commitmentMapperPubKey)[1]) (c.(destinationCommitmentReceipt)[2]) (c.(destinationCommitmentReceipt)[0]) (c.(destinationCommitmentReceipt)[1]) destinationSecretHash) /\
  (* (3) *)
  ( c.(accountsTreeValue) <> 0 ->
    let leaf := poseidon_2 c.(sourceIdentifier) c.(sourceValue) in
    c.(accountsTreeRoot) = fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0) then (poseidon_2 y (snd x)) else (poseidon_2 (snd x) y)) (combine ('(c.(accountMerklePathIndices))) ('(c.(accountMerklePathElements)))) leaf) /\
  (* (4) *)
  ( c.(accountsTreeValue) <> 0 ->
    let leaf := poseidon_2 c.(accountsTreeRoot) c.(accountsTreeValue) in
    c.(registryTreeRoot) = fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0) then (poseidon_2 y (snd x)) else (poseidon_2 (snd x) y)) (combine ('(c.(registryMerklePathIndices))) ('(c.(registryMerklePathElements)))) leaf) /\
  (* (5) *)
  ( c.(sourceValue) | (252) /\ c.(statementValue) | (252) /\ c.(statementValue) <=q c.(sourceValue)) /\
  (* (6) *)
  ( c.(statementComparator) = 1 -> c.(statementValue) = c.(sourceValue)) /\
  (* (7) *)
  ( c.(requestIdentifier) <> 0 -> c.(proofIdentifier) = poseidon_2 (poseidon_2 c.(sourceSecret) 1%F) c.(requestIdentifier)) /\
  (* (8) *)
  ( c.(vaultNamespace) <> 0 -> c.(vaultIdentifier) = poseidon_2 c.(vaultSecret) c.(vaultNamespace))
  .

Ltac destruct_cons _cons0 :=
  destruct _cons0 as [sourceCommitmentVerification _cons];
  destruct _cons as [destinationCommitmentVerification _cons];
  destruct _cons as [accountsTreeValueIsZero _cons];
  destruct _cons as [accountLeafConstructor _cons];
  destruct _cons as [accountsTreesPathVerifier _cons];
  destruct _cons as [registryLeafConstructor _cons];
  destruct _cons as [registryTreesPathVerifier _cons];
  destruct _cons as [sourceInRange _cons];
  destruct _cons as [statementInRange _cons];
  destruct _cons as [leq _cons];
  destruct _cons as [sourceSecretHash _cons];
  destruct _cons as [sourceSecretHasher _cons];
  destruct _cons as [requestIdentifierIsZero _cons];
  destruct _cons as [proofIdentifierHasher _cons];
  destruct _cons as [vaultNamespaceIsZero _cons];
  destruct _cons as [vaultIdentifierHasher _cons];
  simpl in *;intuit.

Lemma F_0_1_ff: 1%F <> @F.zero q.
Proof.
unwrap_C.
intro. pose proof @F.to_Z_0 q. rewrite <- H in H0. simpl in *. rewrite Zmod_1_l in H0;try lia.
Qed.

Lemma F_sub_eq: forall (a b: F), a - b = 0 -> a = b.
Proof.
  intros.
  pose proof (F.ring_theory q). destruct H0.
  apply Crypto.Algebra.Ring.sub_zero_iff;auto.
Qed.

Hypothesis CPLen: (C.k > 252)%Z.

(* HydraS2 is sound *)
Theorem soundness: forall (c: t), spec c.
Proof.
  intros.
  destruct c. simpl in *.
  unfold spec. intuition;simpl.
  - destruct_cons _cons0. subst.
    pose proof (VerifyHydraCommitment.soundness sourceCommitmentVerification) as sourceCommitmentVerification_spec.
    unfold VerifyHydraCommitment.spec in sourceCommitmentVerification_spec.
    apply sourceCommitmentVerification_spec. auto.
  - destruct_cons _cons0. subst.
    pose proof (VerifyHydraCommitment.soundness destinationCommitmentVerification) as destinationCommitmentVerification_spec.
    unfold VerifyHydraCommitment.spec in destinationCommitmentVerification_spec.
    rewrite <- H10, <- H7.   
    apply destinationCommitmentVerification_spec. auto. 
  - destruct_cons _cons0. subst.
    pose proof (VerifyMerklePath.soundness accountsTreesPathVerifier) as accountsTreesPathVerifier_spec.
    unfold VerifyMerklePath.spec in accountsTreesPathVerifier_spec. intuit.
    erewrite <- (Poseidon.PoseidonHypo.poseidon_2_spec);eauto.
    rewrite H1;auto. rewrite H15;auto.
    pose proof (IsZero.soundness accountsTreeValueIsZero) as accountsTreeValueIsZero_spec.
    unfold IsZero.spec in accountsTreeValueIsZero_spec.
    destruct (dec (IsZero._in accountsTreeValueIsZero = 0));try easy.
    rewrite accountsTreeValueIsZero_spec in H17. rewrite H17. intro.
    replace (1-0)%F with (@F.one q) in H2. 
    apply F_0_1_ff in H2;easy.
    rewrite Fsub_0_r;auto.
  - destruct_cons _cons0. subst.
    pose proof (VerifyMerklePath.soundness registryTreesPathVerifier) as registryTreesPathVerifier_spec.
    unfold VerifyMerklePath.spec in registryTreesPathVerifier_spec. intuit.
    erewrite <- (Poseidon.PoseidonHypo.poseidon_2_spec);eauto.
    rewrite H1;auto. rewrite H22;auto.
    pose proof (IsZero.soundness accountsTreeValueIsZero) as accountsTreeValueIsZero_spec.
    unfold IsZero.spec in accountsTreeValueIsZero_spec.
    destruct (dec (IsZero._in accountsTreeValueIsZero = 0));try easy.
    rewrite accountsTreeValueIsZero_spec in H24. rewrite H24. intro.
    replace (1-0)%F with (@F.one q) in H2. 
    apply F_0_1_ff in H2;easy.
    rewrite Fsub_0_r;auto.
  - destruct_cons _cons0. subst.
    pose proof (Num2Bits.range_check sourceInRange). 
    rewrite H26 in *. rewrite H;try lia.
  - destruct_cons _cons0. subst.
    pose proof (Num2Bits.range_check statementInRange). 
    rewrite H;try lia.
  - destruct_cons _cons0. subst.
    pose proof (LessEqThan.soundness leq). intuition.
    destruct H;try lia;auto.
    pose proof (Num2Bits.range_check statementInRange). 
    rewrite H28 in *. rewrite H;try lia.
    pose proof (Num2Bits.range_check sourceInRange). 
    rewrite H26,H29 in *. rewrite H;try lia.
    destruct (dec (LessEqThan.out leq = 1));try easy.
    rewrite <- H28. rewrite H29 in H0. auto.
  - destruct_cons _cons0. subst.
    rewrite Fmul_1_r in H33. 
    assert (inputs accountLeafConstructor [1] +
    (Num2Bits._in statementInRange - inputs accountLeafConstructor [1]) = Num2Bits._in statementInRange).
    { pose proof F.ring_theory q. destruct H. rewrite Rsub_def. rewrite Radd_assoc.
      rewrite Radd_comm. rewrite Radd_assoc.
      specialize (Ropp_def (inputs accountLeafConstructor [1])).
      erewrite Radd_comm in Ropp_def. rewrite Ropp_def. 
      rewrite Fadd_0_l. auto. }
    rewrite H in *. auto.
  - destruct_cons _cons0. subst.
    pose proof (Poseidon.PoseidonHypo.poseidon_2_spec proofIdentifierHasher).
    pose proof (IsZero.soundness requestIdentifierIsZero) as requestIdentifierIsZero_spec.
    unfold IsZero.spec in requestIdentifierIsZero_spec.
    destruct (dec (IsZero._in requestIdentifierIsZero = 0));try easy.
    rewrite requestIdentifierIsZero_spec in *. rewrite Fsub_0_r,Fmul_1_r in *.
    assert (out proofIdentifierHasher = proofIdentifier0). apply F_sub_eq;auto.
    erewrite <- H1, H0;eauto.
    rewrite H38.
    pose proof (Poseidon.PoseidonHypo.poseidon_2_spec sourceSecretHasher).
    erewrite <- H2;eauto.
  - destruct_cons _cons0. subst.
    pose proof (Poseidon.PoseidonHypo.poseidon_2_spec vaultIdentifierHasher).
    pose proof (IsZero.soundness vaultNamespaceIsZero) as vaultNamespaceIsZero_spec.
    unfold IsZero.spec in vaultNamespaceIsZero_spec.
    destruct (dec (IsZero._in vaultNamespaceIsZero = 0));try easy.
    rewrite vaultNamespaceIsZero_spec in *. rewrite Fsub_0_r,Fmul_1_r in *.
    assert (out vaultIdentifierHasher = vaultIdentifier0). apply F_sub_eq;auto.
    erewrite <- H1, H0;eauto.
Qed.

End HydraS2Proof.
End HydraS2.


End Hydra.