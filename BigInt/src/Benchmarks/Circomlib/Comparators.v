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

From Circom Require Import Circom Util Default Tuple LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope F_scope.

(** ** IsZero *)

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

(* TODO *)

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
