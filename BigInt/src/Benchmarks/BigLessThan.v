(** * DSL benchmark: BigLessThan *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

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
From Circom.CircomLib Require Import Bitify Comparators Gates.
From Circom.BigInt.Definition Require Import BigLessThan.

Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.

Context {n k: nat}.

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Notation "[\ xs \]" := (RZ.as_be n xs).

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Definition f_and (x: F) (y: F) := x = 1%F /\ y = 1%F.
Definition f_or (x: F) (y: F) := x = 1%F \/ y = 1%F.

(** ** Helpers *)

Lemma binary_not0: forall (x:F), ((x = 0 \/ x = 1) -> x <> 0 -> x = 1)%F.
Proof. intuit. Qed.

Lemma binary_not1: forall (x:F), ((x = 0 \/ x = 1) -> x <> 1 -> x = 0)%F.
Proof. intuit. Qed.

Lemma big_lt_step: forall xs ys i,
  ([\ xs[:i] \] < [\ ys[:i] \] \/
  [\ xs[:i] \] = [\ ys[:i] \] /\
  F.to_Z (xs!i) < F.to_Z (ys!i)) <->
  [\ xs[:1+i] \] < [\ ys[:1+i] \].
Proof.
  (* this is an induction proof that we did in last summer *)
Admitted.

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

(** ** Proof obligations *)

Lemma _obligation1: forall (nu : Z) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x0 => (F.to_Z x0 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x1 => (F.to_Z x1 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True -> (nu = 0%nat) ->
    True.
Proof.
  auto.
Qed.

Lemma _obligation2: forall (nu : Z) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x2 => (F.to_Z x2 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x3 => (F.to_Z x3 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True -> ((0%nat <= nu) /\ (2%nat <= nu)) ->
    True.
Proof.
  auto.
Qed.

Lemma _obligation3: forall (nu : Z) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x4 => (F.to_Z x4 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x5 => (F.to_Z x5 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True -> ((0%nat <= nu) /\ (nu < k)) ->
    True.
Proof.
  auto.
Qed.

Lemma _obligation4: forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x6 => (F.to_Z x6 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x7 => (F.to_Z x7 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((nu = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    True.
Proof.
  auto.
Qed.

Lemma _obligation5: forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x8 => (F.to_Z x8 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x9 => (F.to_Z x9 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:i] \] = [\ ys[:i] \])) /\ ((nu = 0%F) -> ~([\ xs[:i] \] = [\ ys[:i] \])))) ->
    True.
Proof.
  auto.
Qed.

Lemma _obligation6:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x10 => (F.to_Z x10 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x11 => (F.to_Z x11 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\ (x = xs!i)) ->
    ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((nu = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((nu = 0%F) \/ (nu = 1%F)).
Proof.
  intros.
  destruct H16 as [H16 _].
  assumption.
Qed.

Lemma _obligation7:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x12 => (F.to_Z x12 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x13 => (F.to_Z x13 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\ (x = xs!i)) ->
    ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\ (((nu = 1%F) -> (f_and eq x_lt_y)) /\ ((nu = 0%F) -> ~(f_and eq x_lt_y)))) ->
    ((nu = 0%F) \/ (nu = 1%F)).
Proof.
  intros.
  destruct H16 as [H16 _].
  assumption.
Qed.

Lemma _obligation8:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x14 => (F.to_Z x14 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x15 => (F.to_Z x15 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\
       (x = xs!i)) -> ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((nu = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((nu = 0%F) \/ (nu = 1%F)).
Proof.
  intros.
  destruct H16 as [H16 _].
  assumption.
Qed.

Lemma _obligation9:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x16 => (F.to_Z x16 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x17 => (F.to_Z x17 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\
       (x = xs!i)) -> ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\ (((nu = 1%F) -> (x = y)) /\ ((nu = 0%F) -> ~(x = y)))) ->
    ((nu = 0%F) \/ (nu = 1%F)).
Proof.
  intros.
  destruct H16 as [H16 _].
  assumption.
Qed.

Lemma _obligation10:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x18 => (F.to_Z x18 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x19 => (F.to_Z x19 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\ (x = xs!i)) ->
    ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> (f_or lt xs_lt_ys)) /\ ((nu = 0%F) -> ~(f_or lt xs_lt_ys)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:(1%nat + i)] \] < [\ ys[:(1%nat + i)] \])) /\
          ((nu = 0%F) -> ~([\ xs[:(1%nat + i)] \] < [\ ys[:(1%nat + i)] \])))).
Proof.
Admitted.

Lemma _obligation11:
  forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (i : nat) (lt_eq : F * F)
         (lt : F) (eq : F) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x20 => (F.to_Z x20 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x21 => (F.to_Z x21 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (i < k) ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((lt = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    (((eq = 0%F) \/ (eq = 1%F)) /\
       (((eq = 1%F) -> ([\ xs[:i] \] < [\ ys[:i] \])) /\ ((eq = 0%F) -> ~([\ xs[:i] \] < [\ ys[:i] \])))) ->
    ((F.to_Z x <= ((2%nat ^ C.k) - 1%nat)) /\ (x = xs!i)) ->
    ((F.to_Z y <= ((2%nat ^ C.k) - 1%nat)) /\ (y = ys!i)) ->
    (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\
       (((x_lt_y = 1%F) -> (F.to_Z x < F.to_Z y)) /\ ((x_lt_y = 0%F) -> ~(F.to_Z x < F.to_Z y)))) ->
    (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\
       (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) ->
    (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\ (((nu = 1%F) -> (f_and eq x_eq_y)) /\ ((nu = 0%F) -> ~(f_and eq x_eq_y)))) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:(1%nat + i)] \] = [\ ys[:(1%nat + i)] \])) /\
          ((nu = 0%F) -> ~([\ xs[:(1%nat + i)] \] = [\ ys[:(1%nat + i)] \])))).
Proof.
  unfold f_and, f_or. intros.
  split. intuit. split; intros.
  - ind nu.
    destruct H17.
    ind eq. ind x_eq_y. skip.
  - ind nu.
    apply Decidable.not_and in H17.
    destruct H17.
    ind eq. skip.
    ind x_eq_y. skip.
    unfold Decidable.decidable. intuit.
Qed.

Lemma _obligation12: forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x22 => (F.to_Z x22 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x23 => (F.to_Z x23 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (nu = 0%F) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:0%nat] \] < [\ ys[:0%nat] \])) /\
          ((nu = 0%F) -> ~([\ xs[:0%nat] \] < [\ ys[:0%nat] \])))).
Proof.
  unwrap_C.
  intros. simpl.
  repeat split; auto.
  - intro. subst. fqsatz.
  - lia.
Qed.

Lemma _obligation13: forall (nu : F) (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x24 => (F.to_Z x24 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x25 => (F.to_Z x25 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (nu = 1%F) ->
    (((nu = 0%F) \/ (nu = 1%F)) /\
       (((nu = 1%F) -> ([\ xs[:0%nat] \] = [\ ys[:0%nat] \])) /\
          ((nu = 0%F) -> ~([\ xs[:0%nat] \] = [\ ys[:0%nat] \])))).
Proof.
  unwrap_C.
  intros. simpl.
  repeat split; auto.
  intro. subst. fqsatz.
Qed.

Lemma _obligation14: forall (n : nat) (k : nat) (xs : list F) (ys : list F) (out : F) (lt : F),
    (n <= (C.k - 1%nat)) ->
    (2%nat <= k) ->
    Forall (fun x26 => (F.to_Z x26 <= ((2%nat ^ C.k) - 1%nat))) xs -> True ->
    length xs = k ->
    Forall (fun x27 => (F.to_Z x27 <= ((2%nat ^ C.k) - 1%nat))) ys -> True ->
    length ys = k -> True ->
    (((lt = 0%F) \/ (lt = 1%F)) /\
       (((lt = 1%F) -> ([\ xs[:k] \] < [\ ys[:k] \])) /\ ((lt = 0%F) -> ~([\ xs[:k] \] < [\ ys[:k] \])))) ->
    (out = lt) ->
    (((out = 0%F) \/ (out = 1%F)) /\
       (((out = 1%F) -> ([\ xs \] < [\ ys \])) /\ ((out = 0%F) -> ~([\ xs \] < [\ ys \])))).
Proof.
  intros. subst.
  destruct H8 as [H8 [H8' H8'']].
  repeat split; try assumption;
    try (firstn_all; assumption).
Qed.
