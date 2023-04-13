(** * DSL benchmark: ZK-ML *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Signed Coda.
From Circom.CircomLib Require Import Bitify.

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

(** ** IsNegative *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (n2b : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = n2b)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsNegative_obligation3: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsNegative_obligation4: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z _in) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z _in) < 0%nat))))).
Proof. hammer. Qed.

(** ** IsPositive (fixed) *)

Lemma IsPositive_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsPositive_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation2: forall (_in : F) (n2b : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = n2b)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsPositive_obligation3: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsPositive_obligation4_trivial: forall (_in : F) (n2b : (list F)) (s : F) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation5_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation6_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) /\ (v = s)) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation7_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = (1%F - s)%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation8_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation9_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F)))) /\ (v = isz)) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation10_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = (1%F - isz)%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation11: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = ((1%F - s)%F * (1%F - isz)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in)))))).
Proof.
  unwrap_C; intuit; subst;
    try lia; try fqsatz;
    try (left; fqsatz);
    try (right; fqsatz).
  - admit.
  - admit.
Admitted.

(** ** ReLU *)

Lemma ReLU_obligation0_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation1_trivial: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation2_trivial: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) /\ (v = isp)) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation3: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = (_in * isp)%F) -> ((Signed.to_Z v) = (Z.max 0%nat (Signed.to_Z _in)))).
Proof.
  intros; intuit; subst; simpl in *.
  - assert ($ _in <= 0) by lia.
    rewrite Z.max_l; auto.
    rewrite Fmul_0_r.
    apply Signed.to_Z_0.
  - rewrite Z.max_r; try lia.
    rewrite Fmul_1_r; auto.
Qed.

(** ** Poly *)

Lemma Poly_obligation0_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation1_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation2_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (_in * _in)%F) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation3_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = n) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation4_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation5_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (n * _in)%F) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation6: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = ((_in * _in)%F + (n * _in)%F)%F) -> (v = (_in * (_in + n)%F)%F)).
Proof.
  unwrap_C; intros; fqsatz.
Qed.
