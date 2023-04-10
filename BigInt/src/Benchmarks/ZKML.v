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

(** ** Sign *)

(* print_endline (generate_lemmas sign (typecheck_circuit d_empty sign));; *)

(* TODO *)

(** ** IsNegative *)

(* print_endline (generate_lemmas is_negative (typecheck_circuit (add_to_delta d_empty sign) is_negative));; *)

(* TODO *)

(** ** IsPositive (fixed) *)

(* print_endline (generate_lemmas is_positive (typecheck_circuit (add_to_deltas d_empty [c_is_zero; sign]) is_positive));; *)

(* TODO *)

(** ** ReLU *)

(* print_endline (generate_lemmas relu (typecheck_circuit (add_to_delta d_empty is_positive) relu));; *)

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

(* print_endline (generate_lemmas poly (typecheck_circuit d_empty poly));; *)

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
