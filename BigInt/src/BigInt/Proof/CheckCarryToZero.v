Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.ZArith.Znat.


Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.


From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ Signed.
From Circom.CircomLib Require Import Bitify Comparators Gates.
From Circom.BigInt.Definition Require Import CheckCarryToZero.
(* Circuit:Z
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module CheckCarryToZero.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZS := ReprZSigned.
Module RZ := RZS.RZ.

Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Lemma Nat_of_nat_add_1: forall (n: nat),
  (N.of_nat n + 1%N)%N = N.of_nat (n+1)%nat.
Proof. lia. Qed.

Section _CheckCarryToZero.
Context {n m k: nat}.

Local Notation "[| xs |]" := (RZ.as_le n xs).

Definition cons (_in: F^k) :=
  let EPSILON := 1%nat in
  exists
  (carry: F^k)
  (carryRangeChecks: (@Num2Bits.t (m + EPSILON - n)) ^ k),
    D.iter (fun (i: nat) _cons => _cons /\
      (if (dec (i=0))%nat then
        _in[i] = carry[i] * 2^n
      else
        _in[i] + carry[i-1] = carry[i] * 2^n) /\
      carryRangeChecks[i].(Num2Bits._in) = carry[i] + 2^(m+EPSILON-n-1)
      )
      (k-1) True /\
    _in[k-1] + carry[k-2] = 0.

Local Close Scope F_scope.

Record t := {
  _in: F^k;
  _cons: cons _in
}.

Local Open Scope F_scope.

Lemma pow_S: forall (i:nat),
  (2 * 2^i = 2^(i+1))%Z.
Proof.
  intros.
  rewrite Zpower_exp; lia.
Qed.

Lemma pow_sub_le: forall x (j i: Z),
  0 <= j ->
  0 <= i <= j ->
  (x <= 2^(j-i))%Z ->
  (2^i * x <= 2^j)%Z.
Proof.
  intros.
  apply Z.mul_le_mono_nonneg_l with (p:=(2^i)%Z) in H1; try nia.
  rewrite <- Zpower_exp in H1 by lia.
  replace (i + (j - i))%Z with j%Z in H1 by lia.
  lia.
Qed.

Lemma pow_sub_le_sub1: forall x (j i: Z),
  0 <= j ->
  0 <= i <= j ->
  (x <= 2^(j-i)-1)%Z ->
  (2^i * x <= 2^j - 2^i)%Z.
Proof.
  intros.
  apply Z.mul_le_mono_nonneg_l with (p:=(2^i)%Z) in H1; try nia.
  rewrite Z.mul_sub_distr_l in H1.
  rewrite <- Zpower_exp in H1 by lia.
  replace (i + (j - i))%Z with j%Z in H1 by lia.
  lia.
Qed.

Notation "| x |" := (Z.abs x) (at level 60).

Lemma le_2pow_add1: forall x y l,
  x <= 2^l ->
  y <= 2^l ->
  x+y <= 2^(l+1).
Admitted.

Lemma le_pow_trans: forall b x l1 l2,
  b > 0 ->
  0 <= l1 ->
  0 <= l2 ->
  x <= b^l1 ->
  l1 <= l2 ->
  x <= b^l2.
Proof.
  intros.
  transitivity (b^l1)%Z. lia.
  apply Zpow_facts.Zpower_le_monotone; try lia.
Qed.

Lemma pow_lt_trans: forall b x l1 l2,
  b > 1 ->
  0 <= l1 ->
  0 <= l2 ->
  l1 < l2 ->
  b^l2 <= x ->
  b^l1 < x.
Proof.
  intros.
  apply Z.lt_le_trans with (m:=(b^l2)%Z); try lia.
  apply Zpow_facts.Zpower_lt_monotone; try lia.
Qed.


Theorem soundness: forall (c: t), 
  1 <= n <= m ->
  2 <= k ->
  m <= C.k-2 ->
  Forall (fun x => |$x| <= 2^(m-1)%Z) ('c.(_in)) ->
  [| 'c.(_in) |] = 0%Z.
Proof.
  unwrap_C.
  intros c H_n H_k H_m H_xm.
  destruct c as [x _cons]. destruct _cons as [carry [check [iter last] ] ].
  simpl in *.
  rem_iter.
  pose_lengths.
  pose proof Signed.half_lb as half_lb.
  replace (m + 1 - n - 1)%N with (m-n)%N in * by lia.
  
  assert (Hnm: 0 <= 2^n <= 2^m). split. nia. apply Zpow_facts.Zpower_le_monotone; lia.
  assert (Hmr: 0 <= 2*2^m <= 2^C.k). split. nia. rewrite pow_S. apply Zpow_facts.Zpower_le_monotone; lia.
  (* assert (Hrk: 0 <= 2^r <= 2^C.k). split. nia. apply Zpow_facts.Zpower_le_monotone; lia. *)

  (* carry's are bounded by 2^(m-n) *)
  pose (Inv_carry_range := fun (i: nat) _cons => _cons ->
    forall (j: nat), j < i ->
      |$'carry!j| <= 2^(m-n)).
  assert (Hinv_carry_range: Inv_carry_range (k-1)%nat (D.iter f (k-1)%nat (True))). {
    apply D.iter_inv; unfold Inv_carry_range.
    - lia.
    - intros i _cons IH Hi Hstep j Hj. subst f.
      lift_to_list.
      assert (N2B_range: Num2Bits._in (' check ! i) | ((m + 1- n)%nat)). {
        apply (@Num2Bits.range_check _ (' check ! i)). lia.
      }
      lift_to_list.
      intuit.
      rewrite H8 in N2B_range.
      destruct (dec (j<i)). auto.
      assert (j=i) by lia. subst j.
      replace (Z.sub (Z.of_nat m) (Z.of_nat n)) with (Z.of_N (N.sub (N.of_nat m) (N.of_nat n))) by lia.
      apply Signed.range_check; try lia.
      transitivity (2^(m+1-n)%nat-1)%Z. auto.
      match goal with 
      | [ |- 2^?a - 1 <= 2^?b]  => assert (Hpow: a = b) by lia; rewrite Hpow
      end. lia.
  }

  (* prefix is equal to carry!j * 2^n(j+1) *)
  pose (Inv_sum := fun (i: nat) _cons => _cons ->
    forall (j: nat) , j<i ->
      (2^(n*(j+1)) * $'carry!j = [| 'x[:j+1] |])%Z).
  assert (Hinv_sum: Inv_sum (k-1)%nat (D.iter f (k-1)%nat (True))). {
    apply D.iter_inv; unfold Inv_sum.
    - lia.
    - intros i _cons IH Hi Hstep j Hj.
      assert (Hcarry: | $ ' carry ! j | <= 2 ^ (m - n)). apply Hinv_carry_range. auto. lia.
      assert (Hcarry': | $ ' carry ! (j-1)%nat | <= 2 ^ (m - n)). apply Hinv_carry_range. auto. lia.
      assert (Hcarry_2n: ($('carry!j * (1+1)^n) = $'carry!j * 2^n)%Z). {
        (* range check: distribute sum *)
        rewrite Signed.to_Z_mul, Signed.to_Z_2_pow, Signed.to_Z_2. nia. lia.
        rewrite Signed.to_Z_2_pow, Signed.to_Z_2 by lia.
        rewrite Signed.abs_nonneg with (x:=(Z.pow (Zpos (xO xH)) (Z.of_N (N.of_nat n)))) by lia.
        eapply Z.le_lt_trans.
        apply Z.mul_le_mono_nonneg_r. lia. eauto.
        rewrite <- Zpower_exp, nat_N_Z by lia.
        apply pow_lt_trans with ((C.k-1))%Z; try lia.
      }
      subst f. lift_to_list.
      split_dec.
      + assert (j = 0)%nat by lia. subst i j.
        simplify.
        erewrite firstn_1 by lia. fold_default. simpl. unfold RZ.ToZ.to_Z. simplify.
        intuit.
        rewrite H7.
        rewrite Hcarry_2n. lia.
      + destruct (dec (j<i)). intuit. auto.
        assert (j=i) by lia. subst j.
        intuit.
        specialize (H6 (i-1))%nat.
        apply f_equal with (f:=Signed.to_Z) in H7.
        rewrite Hcarry_2n in H7.
        rewrite Signed.to_Z_add in H7.

        rewrite RZ.as_le_split_last' with (i:=i).
        rewrite firstn_firstn. rewrite Nat.min_l by lia.
        unfold_default. rewrite firstn_nth by lia. fold_default.
        unfold RZ.ToZ.to_Z.
        replace (i-1+1)%nat with i in H6 by lia.
        rewrite <- H6 by lia.
        replace ((i - 1)%nat + 1)%Z with (Z.of_nat i) by lia.
        rewrite Z.mul_add_distr_l, Zpower_exp by lia.
        simplify.
        rewrite firstn_length_le; lia.

        (* range check: distribute sum *)
        eapply Z.le_lt_trans with (2^((m-1)+1))%Z.
        apply le_2pow_add1.
        (* |$'x!i| <= 2^(m-1) *)
        unfold_default. apply Forall_nth. auto. lia.
        apply le_pow_trans with (m-n)%Z; try lia.
        eapply pow_lt_trans with ((C.k-1)%Z); try lia.
  }
  (* last carry is in range *)
  assert (Hcarry_k_2_range: | $ ' carry ! (k - 2) | <= 2 ^ (m - n)). apply Hinv_carry_range. auto. lia.
  (* (k-1)-prefix *)
  assert (Hcarry_k_2: (2 ^ (n * ((k - 2)%nat + 1)) * $ ' carry ! (k - 2))%Z = [|' x [:k - 2 + 1]|]). apply Hinv_sum. auto. lia.
  replace (k - 2 + 1)%nat with (k-1)%nat in Hcarry_k_2 by lia.
  replace ((k - 2)%nat + 1)%Z with (k-1)%Z in Hcarry_k_2 by lia.
  lift_to_list.
  (* distribute sum *)
  apply f_equal with (f:=Signed.to_Z) in last.
  rewrite Signed.to_Z_add, Signed.to_Z_0 in last.
  rewrite RZ.as_le_split_last' with (i:=(k-1)%nat). unfold RZ.ToZ.to_Z.
  rewrite <- Hcarry_k_2.
  rewrite Nat2Z.inj_sub by lia. simpl. lia.
  lia.
  (* range check: distribute sum *)
  eapply Z.le_lt_trans with (2^((m-1)+1))%Z.
  apply le_2pow_add1.
  (* |$'x!i| <= 2^(m-1) *)
  unfold_default. apply Forall_nth. auto. lia.
  apply le_pow_trans with (m-n)%Z; try lia.
  eapply pow_lt_trans with ((C.k-1)%Z); try lia.
Unshelve. exact F.zero. 
Qed.

End _CheckCarryToZero.
End CheckCarryToZero.