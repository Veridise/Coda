(** * DSL benchmark: ZK-SQL *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Coda.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

#[global]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[global]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[global]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[global]Hint Extern 10 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[global]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[global]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[global]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[global]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[global]Hint Extern 10 (_ < _) => lia: core.
#[global]Hint Extern 10 (_ < _)%nat => lia: core.
#[global]Hint Extern 10 (_ <= _) => lia: core.
#[global]Hint Extern 10 (_ <= _)%nat => lia: core.
#[global]Hint Extern 10 (_ > _) => lia: core.
#[global]Hint Extern 10 (_ > _)%nat => lia: core.
#[global]Hint Extern 10 (_ >= _) => lia: core.
#[global]Hint Extern 10 (_ >= _)%nat => lia: core.
#[global]Hint Extern 10 (S _ = S _) => f_equal: core.

(** Lists of binary field elements *)

Definition binary_F_list (l : list F) :=
  forall i,
    Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length l)) ->
    l ! i = 0%F \/ l ! i = 1%F.

(** A [binary_F_list] whose sum equals its length is all 1s *)

Lemma binary_sum_equals_length :
  forall l,
    binary_F_list l ->
    F.of_nat q (length l) = sum l ->
    forall i,
      Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length l)) ->
      l ! i = 1%F.
Proof. Admitted.

(** A [binary_F_list] whose sum does not equal its length contains a 0 *)

Lemma binary_sum_neq_length :
  forall l,
    binary_F_list l ->
    F.of_nat q (length l) <> sum l ->
    exists i,
      Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length l))
      /\ l ! i = 0%F.
Proof. Admitted.

(** A [binary_F_list] whose sum is nonzero contains a 1 *)

Lemma binary_sum_neq_0 :
  forall l,
    binary_F_list l ->
    sum l <> 0%F ->
    exists i,
       Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length l))
       /\ l ! i = 1%F.
Proof. Admitted.

(** A [binary_F_list] whose length is positive and less than the prime
that contains a 1 has a nonzero sum *)

Lemma binary_sum_nonzero :
  forall l i,
    binary_F_list l ->
    Z.of_N (N.of_nat 0) < Z.of_N (N.of_nat (length l)) < Z.pos q ->
    l ! i = 1%F ->
    sum l <> 0%F.
Proof. Admitted.

(** ** CalculateTotal *)

Lemma CalculateTotal_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x0 => True) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x1 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x2 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x3 => True) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (sum (take i _in))) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x4 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> (((v = (sum (take i _in))) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x5 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (_in!i)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x6 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (x + (_in!i))%F) -> (v = (sum (take (i + 1%nat)%nat _in)))).
Proof.
  unfold take; intros; subst.
  apply sum_step; auto.
Qed.

Lemma CalculateTotal_obligation7: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x7 => True) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (sum (take 0%nat _in)))).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation8: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x8 => True) _in -> ((length _in) = n) -> True -> ((v = (sum (take n _in))) -> (v = (sum _in))).
Proof.
  unfold take; intros; subst.
  rewrite firstn_all. auto.
Qed.

(** ** SumEquals *)

Lemma SumEquals_obligation0: forall (n : nat) (nums : (list F)) (s : F) (v : Z), Forall (fun x0 => True) nums -> ((length nums) = n) -> True -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma SumEquals_obligation1: forall (n : nat) (nums : (list F)) (s : F) (v : (list F)), Forall (fun x1 => True) nums -> ((length nums) = n) -> True -> Forall (fun x2 => True) v -> True -> ((((length v) = n) /\ (v = nums)) -> ((length v) = n)).
Proof. hammer. Qed.

Lemma SumEquals_obligation2_trivial: forall (n : nat) (nums : (list F)) (s : F) (x : F) (v : F), Forall (fun x3 => True) nums -> ((length nums) = n) -> True -> (x = (sum nums)) -> True -> (((v = (sum nums)) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma SumEquals_obligation3_trivial: forall (n : nat) (nums : (list F)) (s : F) (x : F) (v : F), Forall (fun x4 => True) nums -> ((length nums) = n) -> True -> (x = (sum nums)) -> True -> ((v = s) -> True).
Proof. hammer. Qed.

Lemma SumEquals_obligation4: forall (n : nat) (nums : (list F)) (s : F) (x : F) (v : F), Forall (fun x5 => True) nums -> ((length nums) = n) -> True -> (x = (sum nums)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (x = s)) /\ ((v = 0%F) -> ~(x = s)))) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

(** ** IsNotZero *)

Lemma IsNotZero_obligation0_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsNotZero_obligation1: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F)))) /\ (v = isz)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsNotZero_obligation2: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not isz)) /\ ((v = 0%F) -> ~(f_not isz)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ~(_in = 0%F)) /\ ((v = 0%F) -> ~~(_in = 0%F))))).
Proof. hammer. Qed.

(** ** IsFiltered *)

Lemma IsFiltered_obligation0_trivial: forall (x : F) (y : F) (op : F) (v : F), True -> True -> True -> True -> ((v = op) -> True).
Proof. hammer. Qed.

Lemma IsFiltered_obligation1_trivial: forall (x : F) (y : F) (op : F) (v : F), True -> True -> True -> True -> ((v = 0%F) -> True).
Proof. hammer. Qed.

Lemma IsFiltered_obligation2_trivial: forall (x : F) (y : F) (op : F) (a : F) (v : F), True -> True -> True -> (((a = 0%F) \/ (a = 1%F)) /\ (((a = 1%F) -> (op = 0%F)) /\ ((a = 0%F) -> ~(op = 0%F)))) -> True -> ((v = op) -> True).
Proof. hammer. Qed.

Lemma IsFiltered_obligation3_trivial: forall (x : F) (y : F) (op : F) (a : F) (v : F), True -> True -> True -> (((a = 0%F) \/ (a = 1%F)) /\ (((a = 1%F) -> (op = 0%F)) /\ ((a = 0%F) -> ~(op = 0%F)))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma IsFiltered_obligation4: forall (x : F) (y : F) (op : F) (a : F) (b : F) (v : Z), True -> True -> True -> (((a = 0%F) \/ (a = 1%F)) /\ (((a = 1%F) -> (op = 0%F)) /\ ((a = 0%F) -> ~(op = 0%F)))) -> (((b = 0%F) \/ (b = 1%F)) /\ (((b = 1%F) -> (op = 1%F)) /\ ((b = 0%F) -> ~(op = 1%F)))) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsFiltered_obligation5: forall (x : F) (y : F) (op : F) (a : F) (b : F) (v : (list F)), True -> True -> True -> (((a = 0%F) \/ (a = 1%F)) /\ (((a = 1%F) -> (op = 0%F)) /\ ((a = 0%F) -> ~(op = 0%F)))) -> (((b = 0%F) \/ (b = 1%F)) /\ (((b = 1%F) -> (op = 1%F)) /\ ((b = 0%F) -> ~(op = 1%F)))) -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = (x * a)%F)) /\ ((v!1%nat) = (y * b)%F)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma IsFiltered_obligation6_trivial: forall (x : F) (y : F) (op : F) (a : F) (b : F) (v : F), True -> True -> True -> (((a = 0%F) \/ (a = 1%F)) /\ (((a = 1%F) -> (op = 0%F)) /\ ((a = 0%F) -> ~(op = 0%F)))) -> (((b = 0%F) \/ (b = 1%F)) /\ (((b = 1%F) -> (op = 1%F)) /\ ((b = 0%F) -> ~(op = 1%F)))) -> True -> ((v = (sum ((x * a)%F :: ((y * b)%F :: nil)))) -> True).
Proof. hammer. Qed.

(** ** IsEqualWord *)

Lemma IsEqualWord_obligation0: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (v : Z), Forall (fun x0 => True) word -> ((length word) = n) -> Forall (fun x1 => True) test -> ((length test) = n) -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x5 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> True -> ((v = 32%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation1: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (v : Z), Forall (fun x6 => True) word -> ((length word) = n) -> Forall (fun x7 => True) test -> ((length test) = n) -> Forall (fun x10 => match x10 with (x8,x9) => True end) z -> Forall (fun x10 => match x10 with (x8,x9) => True end) z -> Forall (fun x10 => match x10 with (x8,x9) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x11 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation2: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (v : (list F)), Forall (fun x12 => True) word -> ((length word) = n) -> Forall (fun x13 => True) test -> ((length test) = n) -> Forall (fun x16 => match x16 with (x14,x15) => True end) z -> Forall (fun x16 => match x16 with (x14,x15) => True end) z -> Forall (fun x16 => match x16 with (x14,x15) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x17 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> Forall (fun x18 => True) v -> True -> ((((forall (im:nat), 0%nat <= im < (length z) -> ((((v!im) = 0%F) \/ ((v!im) = 1%F)) /\ ((((v!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((v!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length v) = (length z))) /\ (v = eqs)) -> ((length v) = n)).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation3: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (total : F) (v : Z), Forall (fun x19 => True) word -> ((length word) = n) -> Forall (fun x20 => True) test -> ((length test) = n) -> Forall (fun x23 => match x23 with (x21,x22) => True end) z -> Forall (fun x23 => match x23 with (x21,x22) => True end) z -> Forall (fun x23 => match x23 with (x21,x22) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x24 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> (total = (sum eqs)) -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation4_trivial: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (total : F) (v : F), Forall (fun x25 => True) word -> ((length word) = n) -> Forall (fun x26 => True) test -> ((length test) = n) -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x30 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> (total = (sum eqs)) -> True -> ((v = (F.of_nat q n)) -> True).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation5_trivial: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (total : F) (v : F), Forall (fun x31 => True) word -> ((length word) = n) -> Forall (fun x32 => True) test -> ((length test) = n) -> Forall (fun x35 => match x35 with (x33,x34) => True end) z -> Forall (fun x35 => match x35 with (x33,x34) => True end) z -> Forall (fun x35 => match x35 with (x33,x34) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x36 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> (total = (sum eqs)) -> True -> (((v = (sum eqs)) /\ (v = total)) -> True).
Proof. hammer. Qed.

Lemma IsEqualWord_obligation6: forall (n : nat) (word : (list F)) (test : (list F)) (z : (list (F * F))) (eqs : (list F)) (total : F) (v : F), Forall (fun x37 => True) word -> ((length word) = n) -> Forall (fun x38 => True) test -> ((length test) = n) -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length word) -> (((fst (z!iz)) = (word!iz)) /\ ((snd (z!iz)) = (test!iz)))) /\ ((length z) = (length word))) -> Forall (fun x42 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length z) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((fst (z!im)) = (snd (z!im)))) /\ (((eqs!im) = 0%F) -> ~((fst (z!im)) = (snd (z!im))))))) /\ ((length eqs) = (length z))) -> (total = (sum eqs)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((F.of_nat q n) = total)) /\ ((v = 0%F) -> ~((F.of_nat q n) = total)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (word = test)) /\ ((v = 0%F) -> ~((word = test)))))).
Proof.
  intros. subst. destruct H6, H8.
  assert (binary_F_list eqs). {
    unfold binary_F_list; intros.
    rewrite H9 in H12.
    apply H8 in H12 as [H12 _].
    assumption.
  }
  intuit; subst.
  - assert (
        exists i,
          Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length z))
          /\ eqs ! i = 0%F
      ). { rewrite <- H9; apply binary_sum_neq_length; auto. }
    destruct H14 as [i [H14 H14']].
    rewrite H6 in H14.
    apply H0 in H14 as H14''; destruct H14''.
    rewrite <- H17 in H16; clear H17.
    rewrite <- H6 in H14.
    apply H8 in H14 as [_ [_ H14]]. auto.
  - symmetry in H2.
    apply list_eq; try assumption; intros.
    apply H0 in H14 as H14'; destruct H14'.
    rewrite <- H16, <- H17.
    assert (
        forall i,
          Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length z)) ->
          eqs ! i = 1%F
      ). { rewrite <- H9; apply binary_sum_equals_length; auto. }
    rewrite <- H6 in H14.
    apply H8 in H14 as H14'.
    destruct H14' as [H' [H'' H''']].
    intuition.
Qed.

(** ** MultiOR *)

Lemma MultiOR_obligation0: forall (n : Z) (_in : (list F)) (v : Z), ((0%nat < n) /\ (n < C.q)) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) _in -> (Z.of_nat (length _in) = n) -> True -> ((((0%nat < v) /\ (v < C.q)) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MultiOR_obligation1: forall (n : Z) (_in : (list F)) (v : (list F)), ((0%nat < n) /\ (n < C.q)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) _in -> (Z.of_nat (length _in) = n) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) v -> True -> (((Z.of_nat (length v) = n) /\ (v = _in)) -> (Z.of_nat (length v) = n)).
Proof. hammer. Qed.

Lemma MultiOR_obligation2_trivial: forall (n : Z) (_in : (list F)) (v : F), ((0%nat < n) /\ (n < C.q)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) _in -> (Z.of_nat (length _in) = n) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma MultiOR_obligation3_trivial: forall (n : Z) (_in : (list F)) (total : F) (v : F), ((0%nat < n) /\ (n < C.q)) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) _in -> (Z.of_nat (length _in) = n) -> (total = (sum _in)) -> True -> (((v = (sum _in)) /\ (v = total)) -> True).
Proof. hammer. Qed.

Lemma MultiOR_obligation4: forall (n : Z) (_in : (list F)) (total : F) (v : F), ((0%nat < n) /\ (n < C.q)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) _in -> (Z.of_N (N.of_nat (length _in)) = n) -> (total = (sum _in)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ~(total = 0%F)) /\ ((v = 0%F) -> ~~(total = 0%F)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (exists (i:nat), 0%nat <= i < n /\ ((_in!i) = 1%F))) /\ ((v = 0%F) -> ~((exists (i:nat), 0%nat <= i < n /\ ((_in!i) = 1%F))))))).
Proof.
  intros. intuit; subst.
  - apply H; intro.
    destruct H9 as [i [H9 H10]].
    assert (sum _in <> 0%F). {
      apply binary_sum_nonzero with i; auto.
      unfold binary_F_list; auto.
    }
    contradiction.
  - apply binary_sum_neq_0; auto.
    unfold binary_F_list; auto.
Qed.
