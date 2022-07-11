Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.


Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.


Require Import Util.
(* From Coq Require Import Lia. *)

(* Require Import Crypto.Spec.ModularArithmetic. *)
(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/bitify.circom
*)


Section _bitify.

Local Open Scope list_scope.
Local Open Scope F_scope.


Context (q:positive) {prime_q:prime q}.


(***********************
 *      Num2Bits
 ***********************)

Definition F_q := F q.

Locate of_nat.

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

Definition binary (x: F_q) := x = 0 \/ x = 1.
Definition two : F_q := 1 + 1.

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
  - simpl. replace (two^N0) with (1:F_q). Field.fsatz.
  admit.
Admitted.
*)

Fixpoint repr_to_num (ws: list (F q)) (i: nat) : F q :=
  match ws with
  | nil => 0
  | w::ws' => w * two^(BinNat.N.of_nat i) + repr_to_num ws' (S i)
  end.

Definition repr_binary x n ws :=
  length ws = n /\
  (forall i, i < n -> binary (nth i ws 0)) /\
  x = repr_to_num ws 0%nat.

Lemma repr_binary_base: repr_binary 0 0%nat nil.
Proof. unfold repr_binary.
  split; split.
  - intros. simpl. destruct i; unfold binary; auto.
  - reflexivity.
Qed.

Lemma repr_to_num_S: forall ws i,
  repr_to_num ws (S i) = two * repr_to_num ws i.
Proof.
(* idea: should be a straight forward inductio *)
Admitted.


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

Definition lt (x y: F_q) := F.to_nat x <= F.to_nat y.
Definition lt_n (x: F_q) y := F.to_nat x < y.
Definition geq_n (x: F_q) y := F.to_nat x >= y.

Lemma repr_to_num_trivial: forall ws,
  (forall i, i < length ws -> binary (nth i ws 0)) ->
  repr_binary (repr_to_num ws 0) (length ws) ws.
Proof.
  induction ws; unfold repr_binary; split; try split; intros; auto.
Qed.

Theorem repr_binary_ub: forall ws x n,
  repr_binary x n ws ->
  lt_n x (2^n)%nat.
Proof.
  induction ws. 
  - unfold repr_binary; intros; simpl in *; destruct H; destruct H0. 
    subst. cbv. lia.
  - intros. destruct n; destruct H; destruct H0; simpl in H. lia.
    inversion H. subst.
    simpl.
    assert (H_a: binary a) by (apply (H0 0%nat); lia).
    destruct H_a; subst.
    + replace (0 * two ^ N0 + repr_to_num ws 1%nat) with (repr_to_num ws 1%nat) by Field.fsatz.
      replace (repr_to_num ws 1) with (two * (repr_to_num ws 0%nat)) by (rewrite repr_to_num_S; reflexivity).
      unfold lt_n.
      (* Need range check *)
      replace (F.to_nat (two * repr_to_num ws 0%nat)) with (Nat.add (F.to_nat (repr_to_num ws 0%nat)) (F.to_nat (repr_to_num ws 0%nat)))
        by admit.
      simpl.
      assert (F.to_nat (repr_to_num ws 0%nat) < 2 ^ length ws). {
        apply IHws.
        apply repr_to_num_trivial.
        intros.
        specialize (H0 (S i)).
        apply H0. lia.
      }
      lia.
    + (* w = 1 *)
    admit.
Admitted.


(* If the MSB of ws is 1, then x >= 2^n *)
Theorem repr_binary_lb: forall x n ws,
  repr_binary x (S n) ws ->
  nth 0%nat ws 0 = 1 -> 
  geq_n x (2^n)%nat.
Proof.
Admitted.


Definition Num2Bits n (_in: F_q) (_out: tuple F_q n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (iter n (fun i '(lc1, e2, _C) =>
    let out_i := (Tuple.nth_default 0 i _out) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C.


Theorem Num2Bits_correct n _in _out:
  Num2Bits n _in _out -> (forall i, Nat.lt i n -> binary (Tuple.nth_default 0 i _out)).
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
    assert (H_j0_leq: Nat.le j0 j) by lia.
    destruct (lt_dec j0 j).
    + auto.
    + unfold binary.
      replace j0 with j by lia.
      destruct (dec (Tuple.nth_default 0 j _out = 0)).
      * auto.
      * right.
      (* ideally we should use some version of [fsatz], but rn the proof wouldn't type check *)
      rewrite <- Ring.sub_zero_iff.
      apply Hierarchy.zero_product_zero_factor in Hstep.
      destruct (dec (nth_default 0 j _out = 0)); intuition.
  }
  unfold Inv in Hinv.
  specialize (Hinv n).
  destruct (iter n f a0).
  destruct p.
  intuition.
Qed.

End _bitify.