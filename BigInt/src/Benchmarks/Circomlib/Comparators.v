(** * DSL benchmark: Comparators *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

(** ** IsZero *)

Lemma IsZero_obligation0_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = 1%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation1_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = 0%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation2_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = _in) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation3_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = inv) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation4_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = (_in * inv)%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation5_trivial: forall (_in : F) (inv : F) (out : F) (v : F), True -> True -> True -> True -> ((v = (0%F - (_in * inv)%F)%F) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation6_trivial: forall (_in : F) (inv : F) (out : F) (u1 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> True -> ((v = _in) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation7_trivial: forall (_in : F) (inv : F) (out : F) (u1 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> True -> ((v = out) -> True).
Proof. trivial. Qed.

Lemma IsZero_obligation8: forall (_in : F) (inv : F) (out : F) (u1 : unit) (u2 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> ((_in * out)%F = 0%F) -> True -> ((v = out) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F))))).
Proof.
  unwrap_C. intros.
  destruct (dec (_in = 0%F)).
  - subst. simplify; intuit. fqsatz.
  - subst v. simplify; intuit. left. 
  assert (_in <> 0)%F by intuit. fqsatz.
  fqsatz.
Qed.

(* TODO *)

(** ** IsEqual *)

(* print_endline (generate_lemmas c_is_equal (typecheck_circuit
(add_to_delta d_empty c_is_zero) c_is_equal));; *)

Lemma IsEqual_obligation0: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = x) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation1: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = y) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation2: forall (x : F) (y : F) (v : F), True -> True -> True -> ((v = (x - y)%F) -> True).
Proof. intuition. Qed.

Lemma IsEqual_obligation3: forall (x : F) (y : F) (v : F), True -> True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((x - y)%F = 0%F)) /\ ((v = 0%F) -> ~((x - y)%F = 0%F)))) -> (True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (x = y)) /\ ((v = 0%F) -> ~(x = y))))).
Proof.
  unwrap_C. intros. subst.
  destruct H1 as [H1 [H1' H1'']].
  intuit.
  - subst. apply H1. fqsatz.
  - fqsatz.
Qed.

Lemma IsEqual_obligation4: forall (x : F) (y : F) (v : F), True -> True -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((x - y)%F = 0%F)) /\ ((v = 0%F) -> ~((x - y)%F = 0%F)))) -> True).
Proof. intuition. Qed.

(** ** LessThan *)

Lemma LessThan_obligation0_trivial: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((((0%nat <= v)%Z /\ (v < (C.k - 1%nat)%Z)%Z) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation1_trivial: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation2: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = (n + 1%nat)%nat) -> (0%nat <= v)%Z).
Proof. intuit. Qed.

Lemma LessThan_obligation3_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> (((F.to_Z v < (2%nat ^ n)%Z)%Z /\ (v = x)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation4_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> (((F.to_Z v < (2%nat ^ n)%Z)%Z /\ (v = y)) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation5_trivial: 
  forall (n : nat) (x : F) (y : F) (v : F), 
  (n < (C.k - 1%nat)%Z)%Z -> 
  (F.to_Z x < (2%nat ^ n)%Z)%Z -> 
  (F.to_Z y < (2%nat ^ n)%Z)%Z -> 
  True -> 
  ((v = (x - y)%F) -> True).
  Proof. intuit. Qed.


Lemma LessThan_obligation6_trivial: 
  forall (n : nat) (x : F) (y : F) (v : F), 
  (n < (C.k - 1%nat)%Z)%Z -> 
  (F.to_Z x < (2%nat ^ n)%Z)%Z -> 
  (F.to_Z y < (2%nat ^ n)%Z)%Z -> 
  True -> 
  ((v = 2%F) -> True).
  Proof. intuit. Qed.

Lemma LessThan_obligation7: forall (n : nat) (x : F) (y : F) (v : Z), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((((0%nat <= v)%Z /\ (v < (C.k - 1%nat)%Z)%Z) /\ (v = n)) -> (0%nat <= v)%Z).
Proof. 
  intros.
  lia.
Qed.

Lemma LessThan_obligation8_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma LessThan_obligation9_trivial: forall (n : nat) (x : F) (y : F) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> True -> ((v = ((x - y)%F + (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Definition as_le_f := Repr.as_le 1%nat.


Lemma LessThan_obligation10: forall (n : nat) (x : F) (y : F) (z : (list F)) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) z -> (((as_le_f z) = ((x - y)%F + (2%F ^ n)%F)%F) /\ ((length z) = (n + 1%nat)%nat)) -> True -> ((v = (z!n)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. 
  intros.
  subst.
  unfold_default. apply Forall_nth; auto. lia.
Qed.
  
Definition f_not (x:F) := (x = 1)%F.

Lemma binary_not0: forall (x:F), ((x = 0 \/ x = 1) -> x <> 0 -> x = 1)%F.
Proof. intuit. Qed.

Lemma binary_not1: forall (x:F), ((x = 0 \/ x = 1) -> x <> 1 -> x = 0)%F.
Proof. intuit. Qed.
Ltac ind x :=
  match goal with
  | [H: (x = 0%F \/ x = 1 %F) /\ (x = 1%F -> ?P) /\ (x = 0%F -> ?Q) |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    destruct H as [H1 [H2 H3]];
    try match goal with
    | [ Hx: x <> 1%F |- _ ] =>
      apply binary_not1 in Hx; try apply H1
    | [ Hx: x <> 0%F |- _ ] =>
      apply binary_not0 in Hx; try apply H1
    end;
    match goal with
    | [ Hx: x = 1%F |- _] =>
      apply H2 in Hx
    | [ Hx: x = 0%F |- _] =>
      apply H3 in Hx
    end;
    clear H1; clear H2; clear H3
  end.

Lemma LessThan_obligation11: forall (n : nat) (x : F) (y : F) (z : (list F)) (v : F), (n < (C.k - 1%nat)%Z)%Z -> (F.to_Z x < (2%nat ^ n)%Z)%Z -> (F.to_Z y < (2%nat ^ n)%Z)%Z -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) z -> (((as_le_f z) = ((x - y)%F + (2%F ^ n)%F)%F) /\ ((length z) = (n + 1%nat)%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not (z!n))) /\ ((v = 0%F) -> ~(f_not (z!n))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z x < F.to_Z y)%Z) /\ ((v = 0%F) -> ~(F.to_Z x < F.to_Z y)%Z)))).
Proof.
  intros. unfold f_not, as_le_f in *.
  split;
  intuit; subst v.
  assert (z!n = 0)%F by admit.

Admitted.


(** ** GreaterThan *)

(* print_endline (generate_lemmas c_greater_than (typecheck_circuit
(add_to_deltas d_empty [num2bits; c_less_than]) c_greater_than));; *)

Lemma GreaterThan_obligation0: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x5 => True) _in -> ((length _in) = 2%nat) -> True -> (((0%nat <= v) /\ (v = n)) -> (0%nat <= v)).
Proof. Admitted.

Lemma GreaterThan_obligation1: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x6 => True) _in -> ((length _in) = 2%nat) -> True -> ((v = (_in!1%nat)) -> True).
Proof. Admitted.

Lemma GreaterThan_obligation2: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x7 => True) _in -> ((length _in) = 2%nat) -> True -> ((v = (_in!0%nat)) -> True).
Proof. Admitted.

Lemma GreaterThan_obligation3: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x8 => True) _in -> ((length _in) = 2%nat) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat))) /\ ((v = 0%F) -> ~(F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat))))) -> (True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat))) /\ ((v = 0%F) -> ~(F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat)))))).
Proof. Admitted.

Lemma GreaterThan_obligation4: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x9 => True) _in -> ((length _in) = 2%nat) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat))) /\ ((v = 0%F) -> ~(F.to_Z (_in!1%nat) < F.to_Z (_in!0%nat))))) -> True).
Proof. Admitted.
