Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.


Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.


Require Import Util.

(* Require Import Crypto.Spec.ModularArithmetic. *)
(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/bitify.circom
*)


Section _bitify.

Local Open Scope list_scope.
Local Open Scope F_scope.

Ltac fqsatz := fsatz_safe; autorewrite with core; auto.

Context (q:positive) (k:Z) {prime_q: prime q} {k_positive: 1 < k} {q_lb: 2^k < q}.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  apply Pos.ltb_lt. lia.
Qed.

Lemma q_gt_2: 2 < q.
Proof.
  replace 2%Z with (2^1)%Z by lia.
  apply Z.le_lt_trans with (m := (2 ^ k)%Z); try lia.
  eapply Zpow_facts.Zpower_le_monotone; try lia.
Qed.

Hint Rewrite q_gtb_1 : core.

(***********************
 *      Num2Bits
 ***********************)

Lemma length_nil {A: Type} : length (@nil A) = Nat.zero.
Proof. auto. Qed.

Lemma length_cons_end {A: Type} {n: nat} (w: A) (ws: list A ) (H_ws: length ws = n):
  length (app ws (w::nil)) = S n.
Proof.
  rewrite app_length. simpl. lia.
Qed.

Lemma length_cons (n: nat) {A: Type}  {ws} {ws'} {w: A} {_: ws' = w :: ws} (H_ws: length ws = n):
  length ws' = S n.
Proof. rewrite H. simpl. auto. Qed.

Definition binary (x: F q) := x = 0 \/ x = 1.
Definition two : F q := 1 + 1.
Notation "2" := two.

(* Aborted approach: Inductive prop (types get too complicated) *)
(* ws is a big-endian, length-n binary representation of x *)
(* Inductive repr_binary: forall (x: F q) (n: nat) (ws: list (F q)) (_: length ws = n), Prop :=
  | repr_binary_nil:
    repr_binary 0 0%nat nil eq_refl
  | repr_binary_cons:
    forall w x n ws H_ws y n' ws' (H_ws': length ws' = n'),
    binary w -> repr_binary x n ws H_ws ->
    y = x + w * F.pow two (BinNatDef.N.of_nat n) ->
    n' = S n ->
    ws' = w::ws ->
    repr_binary y n' ws' H_ws'. 
Lemma repr_binary_test (H: length (1::nil) = 1%nat): repr_binary 1 1%nat (1::nil) H.
Proof.
  eapply repr_binary_cons with (w := 1).
  right. reflexivity.
  eapply repr_binary_nil.
  - simpl. replace (two^N0) with (1:F q). Field.fsatz.
  admit.
Admitted.
*)

Fixpoint repr_to_num (ws: list (F q)) (i: nat) : F q :=
  match ws with
  | nil => 0
  | w::ws' => w * two^(N.of_nat i) + repr_to_num ws' (S i)
  end.

Definition repr_binary x n ws :=
  length ws = n /\
  (forall i, (i < n)%nat -> binary (nth i ws 0)) /\
  x = repr_to_num ws 0%nat.

Lemma repr_binary_base: repr_binary 0 0%nat nil.
Proof. unfold repr_binary.
  split; split.
  - intros. simpl. destruct i; unfold binary; auto.
  - reflexivity.
Qed.

Lemma pow_S_N: forall (x: F q) i,
  x ^ (N.of_nat (S i)) = x * x ^ (N.of_nat i).
Proof.
  intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.


Lemma pow_S_Z: forall (x: Z) i,
  (x ^ (Z.of_nat (S i)) = x * x ^ (Z.of_nat i))%Z.
Proof.
  intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.


Lemma repr_to_num_S: forall ws i,
  repr_to_num ws (S i) = 2 * repr_to_num ws i.
Proof.
  induction ws as [| w ws]; intros.
  - fqsatz.
  - unfold repr_to_num.
    rewrite IHws.
    replace (2 ^ N.of_nat (S i)) with (2 * 2 ^ N.of_nat i)
      by (rewrite pow_S_N; fqsatz).
    fqsatz.
Qed.

(* 
  Lemma repr_binary_ind: forall x n ws w,
  repr_binary x n ws ->
  binary w ->
  repr_binary (x + w * two^(BinNatDef.N.of_nat n)) (S n) (w::ws).
Proof.
  unfold repr_binary; intros; split; try split; destruct H; destruct H1.
  - simpl. auto.
  - intros.
    destruct i.
    + simpl. auto.
    + simpl. apply H1. lia.
  - simpl. *)

Definition lt (x y: F q) := F.to_Z x <= F.to_Z y.
Definition lt_z (x: F q) y := F.to_Z x <= y.
Definition geq_z (x: F q) y := F.to_Z x >= y.
Definition leq_z (x: F q) y := F.to_Z x <= y.

Lemma repr_to_num_trivial: forall ws,
  (forall i, (i < length ws)%nat -> binary (nth i ws 0)) ->
  repr_binary (repr_to_num ws 0) (length ws) ws.
Proof.
  induction ws; unfold repr_binary; split; try split; intros; auto.
Qed.

Theorem repr_binary_ub: forall ws x n,
  repr_binary x n ws ->
  Z.of_nat n <= k ->
  leq_z x (2^(Z.of_nat n)-1)%Z.
Proof with (lia || nia || eauto).
  unfold leq_z.
  induction ws as [| w ws]; intros x n H_repr H_n.
  - unfold repr_binary.
    destruct H_repr. destruct H0.
    subst. cbv. intros. inversion H.
  - (* analyze n: is has to be S n for some n *)
    pose proof H_repr as H_repr'.
    destruct n; destruct H_repr; destruct H0; simpl in H...
    inversion H. subst. clear H.
    (* lemma preparation starts here *)
    (* assert IHws's antecedent holds *)
    assert (H_repr_prev: repr_binary (repr_to_num ws 0) (length ws) ws). {
      apply repr_to_num_trivial.
      intros i Hi. 
      specialize (H0 (S i)). apply H0...
    }
    (* extract consequence of IHws *)
    assert (IH: F.to_Z (repr_to_num ws 0) <= 2 ^ Z.of_nat (length ws) - 1). {
      apply IHws...
    }
    (* introduce lemmas into scope *)
    pose proof q_gt_2.
    (* bound |w| *)
    assert (H_w: 0 <= F.to_Z w <= 1). {
      assert (H_w_binary: binary w) by (specialize (H0 O); apply H0; lia).
      destruct H_w_binary; subst; simpl; rewrite Z.mod_small...
    }
    (* peel off 1 from 2^(x+1) *)
    pose proof (pow_S_Z 2 (length ws)) as H_pow_S_Z.
    (* bound 2^|ws| *)
    assert (H_pow_ws: 0 <= 2 * 2 ^ (Z.of_nat (length ws)) <= 2 ^ k). {
        replace (2 * 2 ^ (Z.of_nat (length ws)))%Z with (2 ^ (Z.of_nat (length ws) + 1))%Z.
        split...
        apply Zpow_facts.Zpower_le_monotone...
        rewrite Zpower.Zpower_exp...
      }
    (* F.to_Z x is nonneg *)
    assert (0 <= F.to_Z (repr_to_num ws 0)). {
      apply F.to_Z_range...
    }
    (* lemma preparation ends here *)
    (* actual proof starts here *)
    cbn [repr_to_num].
    rewrite repr_to_num_S.
    (* get rid of mod and generate range goals *)
    cbn; repeat rewrite Z.mod_small...
Qed.

(* If the MSB of ws is 1, then x >= 2^n *)
(* Theorem repr_binary_lb: forall x n ws,
  repr_binary x (S n) ws ->
  nth 0%nat ws 0 = 1 -> 
  geq_n x (2^n)%nat.
Proof.
Admitted. *)

Definition Num2Bits (n: nat) (_in: F q) (_out: tuple (F q) n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (iter n (fun (i: nat) '(lc1, e2, _C) =>
    let out_i := (Tuple.nth_default 0 i _out) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C.


Theorem Num2Bits_correct n _in _out:
  Num2Bits n _in _out -> (forall i, (i < n)%nat -> binary (Tuple.nth_default 0 i _out)).
Proof.
  unfold Num2Bits.
  (* provide loop invariant *)
  pose (Inv := fun i '((lc1, e2, _C): (F.F q * F.F q * Prop)) =>
    (_C -> (forall j, Nat.lt j i -> binary (Tuple.nth_default 0 j _out)))).
  (* iter initialization *)
  remember (0, 1, True) as a0.
  intros prog i H_i_lt_n.
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?n ?f ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* invariant holds *)
  assert (Hinv: forall i, Inv i (iter i f a0)). {
  intros. apply iter_inv; unfold Inv.
  - (* base case *) 
    subst. intros _ j impossible. lia.
  - (* inductive case *)
    intros j res Hprev.
    destruct res. destruct p.
    rewrite Heqf.
    intros Hstep j0 H_j0_lt.
    destruct Hstep as [Hstep HP].
    specialize  (Hprev HP).
    assert (H_j0_leq: (j0 <= j)%nat) by lia.
    destruct (dec (j0 < j)%nat).
    + auto.
    + unfold binary.
      replace j0 with j by lia.
      destruct (dec (Tuple.nth_default 0 j _out = 0)).
      * auto.
      * right. fqsatz.
   }
  unfold Inv in Hinv.
  specialize (Hinv n).
  destruct (iter n f a0).
  destruct p.
  intuition.
Qed.

End _bitify.