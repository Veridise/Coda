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
From Circom.circomlib Require Import Bitify Comparators Gates.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module CheckCarryToZero.
Context {n: nat}.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.

Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Lemma Nat_of_nat_add_1: forall (n: nat),
  (N.of_nat n + 1%N)%N = N.of_nat (n+1)%nat.
Proof. lia. Qed.


Local Open Scope F_scope.

Local Notation "[| xs |]" := (R.as_le n xs).

Section _CheckCarryToZero.
Context {m k: nat}.

Definition cons (_in: F^k) :=
  let EPSILON := 1%nat in
  exists (carry: F^k) (carryRangeChecks: (@Num2Bits.t (m + EPSILON - n)) ^ k),
    D.iter (fun (i: nat) _cons => _cons /\
      if (dec (i=0))%nat then
        _in[i] = carry[i] * 2^n
      else
        _in[i] + carry[i-1%nat] = carry[i] * 2^n)
      (k-1)%nat True /\
    _in[k-1] + carry[k-2] = 0.

Local Close Scope F_scope.

Record t := {
  _in: F^k;
  _cons: cons _in
}.

Local Open Scope F_scope.


Theorem soundness: forall (c: t), 
  1 <= n <= C.k ->
  2 <= k ->
  'c.(_in) |: (n) ->
  [| 'c.(_in) |] = 0.
Proof.
  unwrap_C.
  intros c H_n H_k H_in. destruct c as [_in _cons]. destruct _cons as [carry [check [iter last] ] ]. simpl.
  simpl in *.
  remember (fun (i : nat) (_cons : Prop) =>
  _cons /\
  (if dec (i = 0)%nat
   then _in [i] = carry [i] * (1 + 1) ^ n
   else _in [i] + carry [i - 1] = carry [i] * (1 + 1) ^ n))%F as f.
  pose proof (length_to_list _in).
  pose proof (length_to_list carry).

  pose (Inv := fun (i: nat) _cons => _cons -> 
    forall (j: nat), j < i -> 
    (2^(n*(j+1)) * ('carry ! j)) = [| ' _in [:j+1] |]).
  assert (Hinv: Inv (k-1)%nat (D.iter f (k-1)%nat (True))). {
    apply D.iter_inv; unfold Inv.
    - intuition idtac. lia.
    - intros i b IH Hi Hstep j Hj.
      destruct (dec (j = i)%nat). subst. intuition.
      (* interesting case: j = i *)
      + destruct (dec (i=0)%nat).
        * subst. simplify.
          erewrite firstn_1 by lia. cbn [RZ.as_le].
          lift_to_list.
          fold_default.
          rewrite H4.
          simpl. simplify. fqsatz.
        * specialize (H5 (i-1)%nat).
          lift_to_list.
          assert (2^n <> 0)%F. { unfold not. apply pow_nonzero. lia. }
          replace ((' carry) ! i) with (((' _in) ! i + (' carry) ! (i - 1)) / (2^n))%F by fqsatz.
          simplify.
          erewrite R.as_le_split_last with (i:=i).
          rewrite firstn_firstn. rewrite Nat.min_l by lia. simplify.
          erewrite <- fold_nth with (l:=((' _in) [:i + 1])) by (rewrite firstn_length_le; lia).
          rewrite firstn_nth by lia.
          fold_default.
          replace (i-1+1)%nat with i in H5 by lia.
          rewrite <- H5 by lia.
          replace ((i - 1)%nat + 1)%N with (N.of_nat i) by lia.
          simplify.
          fqsatz.
          eapply R.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
          apply R.repr_trivial.
          lift_to_list. auto.
      + assert (j < i)%nat by lia. apply IH. subst. intuition. lia.
  }
  unfold Inv in Hinv.
  intuition.
  specialize (H3 (k-2)%nat).
  erewrite R.as_le_split_last with (i:= (k-1)%nat).
  lift_to_list.
  rewrite Nat_of_nat_add_1 in H3.
  replace (k-2+1)%nat with (k-1)%nat in H3 by lia.
  rewrite <- H3 by lia.
  simplify.
  fqsatz.
  applys_eq R.repr_trivial.
  lia.
  lift_to_list; auto.
Unshelve. exact F.zero. exact F.zero.
Qed.

End _CheckCarryToZero.
End CheckCarryToZero.