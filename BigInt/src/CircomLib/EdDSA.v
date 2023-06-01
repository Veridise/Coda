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
From Circom.CircomLib Require Import Bitify Comparators.

Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Open Scope tuple_scope.

Local Notation "x [[ i ]]" := (Tuple.nth_default 0 i x) (at level 20).
Definition nth2 {m n} (i: nat) (x: (F^n)^m) := Tuple.nth_default (repeat 0 n) i x.
Local Notation "x [ i ][ j ]" := (Tuple.nth_default 0 j (nth2 i x)) (at level 20).
Definition nth3 {m n p} (i: nat) (x: ((F^n)^m)^p) := Tuple.nth_default (repeat (repeat 0 n) m) i x.
Local Notation "x [ i ][ j ][ k ]" := (Tuple.nth_default 0 k (nth2 j (nth3 i x))) (at level 20).

(* Poseidon *)
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
Axiom poseidon_1 : F -> F.
Axiom poseidon_2 : F -> F -> F.
Axiom poseidons_5: F -> F -> F -> F -> F -> F.

Lemma poseidon_1_spec : 
  forall (p: @Poseidon.t 1) x, p.(inputs)[0] = x -> p.(Poseidon.out) = poseidon_1 x. skip. Defined.
Lemma poseidon_2_spec :
  forall (p: @Poseidon.t 2) x y, p.(inputs)[0] = x -> p.(inputs)[1] = y -> p.(Poseidon.out) = poseidon_2 x y. skip. Defined.
Lemma poseidon_5_spec :
  forall (p: @Poseidon.t 5) x y z w v, p.(inputs)[0] = x -> p.(inputs)[1] = y -> p.(inputs)[2] = z -> p.(inputs)[3] = w -> p.(inputs)[4] = v -> p.(Poseidon.out) = poseidons_5 x y z w v. skip. Defined.

End PoseidonHypo.

End Poseidon.



(* Source: https://github.com/iden3/circomlib/blob/master/circuits/eddsaposeidon.circom *)
Module EdDSAPoseidonVerifier.
Module Poseidon:= Poseidon.
Module Cmp := Comparators.
Import Cmp.
Section EdDSAPoseidonVerifier.

Definition poseidons_5 := Poseidon.PoseidonHypo.poseidons_5.

Axiom BabyDbl: F -> F -> F*F.

Axiom edwards_mult: F -> F -> F -> F*F.

Axiom edwards_add: F -> F -> F -> F -> F*F.

Definition q1 := (F.of_nat q 5299619240641551281634865583518297030282874472190772894086521144482721001553).
Definition q2 := (F.of_nat q 16950150798460657717958625567821834550301663161624707787222815936182638968203).

Definition eddsa_poseidon Ax Ay S R8x R8y M := 
  let hash := poseidons_5 R8x R8y Ax Ay M in
  let '(dbl1_xout, dbl1_yout)  := BabyDbl Ax Ay in
  let '(dbl2_xout, dbl2_yout)  := BabyDbl dbl1_xout dbl1_yout in
  let '(dbl3_xout, dbl3_yout)  := BabyDbl dbl2_xout dbl2_yout in
  let '(right2_x, right2_y)  := edwards_mult hash dbl3_xout dbl3_yout in
  let '(right_x, right_y) := edwards_add R8x R8y right2_x right2_y in
  let '(left_x, left_y) := edwards_mult S q1 q2 in
  left_x = right_x /\ left_y = right_y.

Definition cons (enabled: F) (Ax: F) (Ay: F) (S: F) (R8x: F) (R8y: F) (M: F) :=
  exists (hash: @Poseidon.t 5) (eqCheckX eqCheckY: ForceEqualIfEnabled.t), 
    (hash.(Poseidon.inputs)[0] = R8x) /\
    (hash.(Poseidon.inputs)[1] = R8y) /\
    (hash.(Poseidon.inputs)[2] = Ax) /\
    (hash.(Poseidon.inputs)[3] = Ay) /\
    (hash.(Poseidon.inputs)[4] = M) /\
    let '(dbl1_xout, dbl1_yout)  := BabyDbl Ax Ay in
    let '(dbl2_xout, dbl2_yout)  := BabyDbl dbl1_xout dbl1_yout in
    let '(dbl3_xout, dbl3_yout)  := BabyDbl dbl2_xout dbl2_yout in
    let '(right2_x, right2_y)  := edwards_mult hash.(Poseidon.out) dbl3_xout dbl3_yout in
    let '(right_x, right_y) := edwards_add R8x R8y right2_x right2_y in
    let '(left_x, left_y) := edwards_mult S q1 q2 in
    eqCheckX.(ForceEqualIfEnabled.enabled) = enabled /\
    eqCheckX.(ForceEqualIfEnabled._in)[0] = left_x /\
    eqCheckX.(ForceEqualIfEnabled._in)[1] = right_x /\
    eqCheckY.(ForceEqualIfEnabled.enabled) = enabled /\
    eqCheckY.(ForceEqualIfEnabled._in)[0] = left_y /\
    eqCheckY.(ForceEqualIfEnabled._in)[1] = right_y.

Record t : Type := 
{ enabled: F;
  Ax: F;
  Ay: F;
  S: F;
  R8x: F;
  R8y: F;
  M: F;
  _cons: cons enabled Ax Ay S R8x R8y M; }.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End EdDSAPoseidonVerifier.

Module EdDSAPoseidonVerifierProof.

Lemma EdDSAPoseidonVerifier_spec :
  forall (p: @EdDSAPoseidonVerifier.t),
    p.(enabled) <> 0 ->
    eddsa_poseidon p.(Ax) p.(Ay) p.(S) p.(R8x) p.(R8y) p.(M).
Proof.
  intros. unwrap_C. destruct p eqn:hh;simpl in *.
  unfold cons in *.
  destruct _cons0. simpl in *. destruct p;simpl in *.
  destruct e.
  destruct e. pose proof a.
  intuition. 
  destruct BabyDbl eqn: db1 in H6.
  destruct BabyDbl eqn: db2 in H6.
  destruct BabyDbl eqn: db3 in H6.
  destruct edwards_mult eqn: em in H6.
  destruct edwards_add eqn: ea in H6.
  destruct edwards_mult eqn: em2 in H6.
  intuition.
  subst.
  unfold eddsa_poseidon.
  rewrite db1, db2, db3.
  erewrite <- (Poseidon.PoseidonHypo.poseidon_5_spec x);eauto.
  rewrite em, ea, em2.
  pose proof (Cmp.ForceEqualIfEnabled.soundness x0). 
  pose proof (Cmp.ForceEqualIfEnabled.soundness x1).
  simpl in *. subst. intuit.
  apply H1;auto. rewrite H8. auto.
Qed.

Definition unconstrained:= ForceEqualIfEnabled.unconstrained.

(* forall Ax Ay S R8x R8y M, EdDSAPoseidonVerifier 0 Ax Ay S R8x R8y M *)
Lemma EdDSAPoseidonVerifier_spec_disabled :
  forall Ax Ay S R8x R8y M (hash: @Poseidon.t 5) (eqCheckX eqCheckY: ForceEqualIfEnabled.t),
    (hash.(Poseidon.inputs)[0] = R8x) ->
    (hash.(Poseidon.inputs)[1] = R8y) ->
    (hash.(Poseidon.inputs)[2] = Ax) ->
    (hash.(Poseidon.inputs)[3] = Ay) ->
    (hash.(Poseidon.inputs)[4] = M) ->
    let
    '(dbl1_xout, dbl1_yout) := BabyDbl Ax Ay in
     let
     '(dbl2_xout, dbl2_yout) := BabyDbl dbl1_xout dbl1_yout
      in
      let
      '(dbl3_xout, dbl3_yout) := BabyDbl dbl2_xout dbl2_yout
       in
       let
       '(right2_x, right2_y) :=
        edwards_mult (Poseidon.out hash) dbl3_xout dbl3_yout
        in
        let
        '(right_x, right_y) :=
         edwards_add R8x R8y right2_x right2_y in
         let
         '(left_x, left_y) := edwards_mult S q1 q2 in
    eqCheckX.(ForceEqualIfEnabled.enabled) = 0 /\
    eqCheckX.(ForceEqualIfEnabled._in)[0] = left_x /\
    eqCheckX.(ForceEqualIfEnabled._in)[1] = right_x /\
    eqCheckY.(ForceEqualIfEnabled.enabled) = 0 /\
    eqCheckY.(ForceEqualIfEnabled._in)[0] = left_y /\
    eqCheckY.(ForceEqualIfEnabled._in)[1] = right_y ->
    unconstrained left_x right_x /\ unconstrained left_y right_y.
Proof.
  intros.
  destruct BabyDbl eqn: db1.
  destruct (BabyDbl f _) eqn: db2.
  destruct (BabyDbl f1 _) eqn: db3.
  destruct edwards_mult eqn: em.
  destruct edwards_add eqn: ea.
  destruct (edwards_mult S0 _ _) eqn: em2. subst. 
  intuit.
  pose proof (Cmp.ForceEqualIfEnabled.circuit_disabled eqCheckX);intuit.
  rewrite <-H1,<-H. unfold unconstrained. auto.
  pose proof (Cmp.ForceEqualIfEnabled.circuit_disabled eqCheckY);intuit.
  rewrite <-H3,<-H5. unfold unconstrained. auto. 
Qed.

End EdDSAPoseidonVerifierProof.

End EdDSAPoseidonVerifier.