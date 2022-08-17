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


Require Import Util DSL.
Require Import Circom.Circom Circom.Default.
Require Import Circom.LibTactics.
Require Import Circom.Tuple.
Require Import Circom.circomlib.Bitify Circom.circomlib.Comparators.
Require Import Circom.ListUtil.
Require Import Circom.Repr.
(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)


Module CheckCarryToZero (C: CIRCOM).
Context {n: nat}.

Module B := Bitify C.
Module Cmp := Comparators C.
Module R := Repr C.
Module D := DSL C.
Import B C R.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Lemma Fmul_0_r: forall (x: F), x * 0 = 0.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_0_l: forall (x: F), 0 * x = 0.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_1_r: forall (x: F), x * 1 = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_1_l: forall (x: F), 1 * x = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fadd_0_r: forall (x: F), x + 0 = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fadd_0_l: forall (x: F), 0 + x = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Create HintDb simplify_F discriminated.
Hint Rewrite (Fmul_0_r) : simplify_F.
Hint Rewrite (Fmul_0_l) : simplify_F.
Hint Rewrite (Fmul_1_r) : simplify_F.
Hint Rewrite (Fmul_1_l) : simplify_F.
Hint Rewrite (Fadd_0_r) : simplify_F.
Hint Rewrite (Fadd_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_r) : simplify_F.
Hint Rewrite (@F.pow_1_l) : simplify_F.
Hint Rewrite (@F.pow_1_r) : simplify_F.
Hint Rewrite (@F.pow_add_r) : simplify_F.
Hint Rewrite <- (Nat2N.inj_mul) : natsimplify.
Hint Rewrite (Nat.mul_1_l) : natsimplify.
Hint Rewrite (Nat.mul_1_r): natsimplify.
Hint Rewrite (Nat.mul_0_l): natsimplify.
Hint Rewrite (Nat.mul_0_r): natsimplify.
Hint Rewrite (Nat.add_0_r): natsimplify.
Hint Rewrite (Nat.add_0_l): natsimplify.
Hint Rewrite (Nat.mul_succ_r): natsimplify.

Local Notation "[| xs |]" := (as_le n xs).

Section _CheckCarryToZero.
Context {m k: nat}.

Definition cons (_in: F^k) :=
  let EPSILON := 1%nat in
  exists (carry: F^k) (carryRangeChecks: (Num2Bits.t (m + EPSILON - n)) ^ k),
    D.iter (fun (i: nat) _cons => _cons /\
      if (dec (i=0))%nat then
        _in[i] = carry[i] * 2^n
      else
        _in[i] + carry[i-1%nat] = carry[i] * 2^n)
      (k-1)%nat True /\
    _in[k-1] + carry[k-2] = 0.

Record t := {
  _in: F^k;
  _cons: cons _in
}.

Lemma fold_nth {T} `{Default T}: forall (i:nat) d l,
  i < length l ->
  List.nth i l d = List_nth_Default i l.
Proof. intros. unfold List_nth_Default. rewrite nth_default_eq. erewrite nth_oblivious; eauto.  Qed.


Lemma nth_Default_List_tuple {T l} `{Default T} (xs: tuple T l) i:
  (to_list _ xs) ! i = xs [i].
Proof.
  unfold List_nth_Default. unfold nth_Default, nth. rewrite nth_default_to_list. reflexivity.
Qed.

Ltac lift_to_list := repeat match goal with
| [H: context[nth_Default _ _] |- _] => rewrite <-nth_Default_List_tuple in H; try lia
| [ |- context[nth_Default _ _] ] => rewrite <-nth_Default_List_tuple; try lia
| [H: tforall _ _ |- _] => apply tforall_Forall in H
| [ |- tforall _ _] => apply tforall_Forall
end.


Theorem soundness: forall (c: t), 
  (1 <= n)%Z ->
  (n <= C.k)%Z ->
  k >= 2 ->
  c.(_in) |: (n) ->
  [| 'c.(_in) |] = 0.
Proof.
  unwrap_C.
  intros c H_n Hn_ub H_k H_in. destruct c as [_in _cons]. destruct _cons as [carry [check [iter last] ] ]. simpl.
  simpl in *.
  remember (fun (i : nat) (_cons : Prop) =>
  _cons /\
  (if dec (i = 0)%nat
   then _in [i] = carry [i] * (1 + 1) ^ n
   else _in [i] + carry [i - 1] = carry [i] * (1 + 1) ^ n)) as f.
  pose proof (length_to_list _in).
  pose proof (length_to_list carry).

  pose (Inv := fun (i: nat) _cons => _cons -> 
    forall j, j < i -> 
      2^(n*(j+1))%nat * 'carry ! j = as_le n (' _in [:j+1])).
  assert (Hinv: Inv (k-1)%nat (D.iter f (k-1)%nat (True))). {
    apply D.iter_inv; unfold Inv.
    - intuition idtac. lia.
    - intros i b IH Hi Hstep j Hj.
      destruct (dec (j = i)%nat). subst. intuition.
      (* interesting case: j = i *)
      + destruct (dec (i=0)%nat).
        * subst.
          autorewrite with natsimplify simplify_F.
          erewrite firstn_1 by lia. simpl.
          lift_to_list.
          erewrite fold_nth by lia. fqsatz.
        * specialize (H3 (i-1)%nat).
          lift_to_list.
          assert (2^n <> 0). { unfold not. apply pow_nonzero. lia. }
          replace ((' carry) ! i) with (((' _in) ! i + (' carry) ! (i - 1)) / (2^n)).
          replace ((1 + 1) ^ (n * (i + 1))%nat) with (2^ (n * i)%nat * 2^n).
          erewrite as_le_split_last with (i:=i).
          rewrite firstn_firstn. replace (Init.Nat.min i (i + 1)) with i by lia.
          erewrite <- fold_nth with (l:=((' _in) [:i + 1])) by (rewrite firstn_length_le; lia).
          rewrite firstn_nth by lia.
          rewrite fold_nth by lia.
          replace (i-1+1)%nat with i in H3 by lia.
          rewrite <- H3 by lia.
          fqsatz.
          eapply repr_le_firstn; eauto. rewrite firstn_length_le; lia.
          apply repr_trivial.
          lift_to_list. auto.
          rewrite Nat.mul_add_distr_l. rewrite Nat2N.inj_add. rewrite F.pow_add_r. autorewrite with natsimplify simplify_F. fqsatz.
          fqsatz.
      + assert (j < i)%nat by lia. apply IH. subst. intuition. lia.
  }
  unfold Inv in Hinv.
  intuition.
  specialize (H1 (k-2)%nat).
  erewrite as_le_split_last with (i:= (k-1)%nat).
  replace (k - 2 + 1)%nat with (k-1)%nat in H1.
  rewrite <- H1.
  lift_to_list.
  fqsatz.
  lia. lia.
  applys_eq repr_trivial.
  lia.
  lift_to_list; auto.
Unshelve. exact F.zero. exact F.zero.
Qed.

End _CheckCarryToZero.
End CheckCarryToZero.