(** * DSL benchmark: Gates *)

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

Definition f_and (x: F) (y: F) := x = 1%F /\ y = 1%F.
Definition f_or (x: F) (y: F) := x = 1%F \/ y = 1%F.
Definition f_not (x: F) := x = 0%F.
Definition f_nand (x: F) (y: F) := ~(x = 1%F /\ y = 1%F).
Definition f_nor (x: F) (y: F) := ~(x = 1%F \/ y = 1%F).
Definition f_xor (x: F) (y: F) := x <> y.

(** ** NOT *)

(* print_endline (generate_lemmas cnot (typecheck_circuit d_empty cnot));; *)

Lemma Not_obligation0: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = _in)) -> True).
Proof. intuition. Qed.

Lemma Not_obligation1: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. intuition. Qed.

Lemma Not_obligation2: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = (_in + 1%F)%F) -> True).
Proof. intuition. Qed.

Lemma Not_obligation3: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = 2%F) -> True).
Proof. Admitted.

Lemma Not_obligation4: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = _in)) -> True).
Proof. intuition. Qed.

Lemma Not_obligation5: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = (2%F * _in)%F) -> True).
Proof. Admitted.

Lemma Not_obligation6: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = ((_in + 1%F)%F - (2%F * _in)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not _in)) /\ ((v = 0%F) -> ~(f_not _in))))).
Proof. Admitted.

(** ** XOR *)

(* print_endline (generate_lemmas cxor (typecheck_circuit d_empty cxor));; *)

Lemma Xor_obligation0: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation1: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation3: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 2%F) -> True).
Proof. Admitted.

Lemma Xor_obligation4: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation5: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation6: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. intuition. Qed.

Lemma Xor_obligation7: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (2%F * (a * b)%F)%F) -> True).
Proof. Admitted.

Lemma Xor_obligation8: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a + b)%F - (2%F * (a * b)%F)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_xor a b)) /\ ((v = 0%F) -> ~(f_xor a b))))).
Proof. Admitted.

(** ** AND *)

(* print_endline (generate_lemmas cand (typecheck_circuit d_empty cand));; *)

Lemma And_obligation0: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma And_obligation1: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma And_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_and a b)) /\ ((v = 0%F) -> ~(f_and a b))))).
Proof.
  unwrap_C. unfold f_and. intros.
  intuit; try fqsatz.
  - left; fqsatz.
  - left; fqsatz.
  - left; fqsatz.
  - right; fqsatz.
Qed.

(** ** NAND *)

(* print_endline (generate_lemmas cnand (typecheck_circuit d_empty cnand));; *)

Lemma Nand_obligation0: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. intuition. Qed.

Lemma Nand_obligation1: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Nand_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Nand_obligation3: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. intuition. Qed.

Lemma Nand_obligation4: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (1%F - (a * b)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_nand a b)) /\ ((v = 0%F) -> ~(f_nand a b))))).
Proof.
  unwrap_C. unfold f_nand. intros.
  intuit; try fqsatz.
  - right; fqsatz.
  - right; fqsatz.
  - right; fqsatz.
  - left; fqsatz.
Qed.

(** ** OR *)

(* print_endline (generate_lemmas cor (typecheck_circuit d_empty cor));; *)

Lemma Or_obligation0: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Or_obligation1: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Or_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuition. Qed.

Lemma Or_obligation3: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Or_obligation4: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Or_obligation5: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. intuition. Qed.

Lemma Or_obligation6: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a + b)%F - (a * b)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_or a b)) /\ ((v = 0%F) -> ~(f_or a b))))).
Proof.
  unwrap_C. unfold f_or. intros.
  intuit; try fqsatz.
  - left; fqsatz.
  - right; fqsatz.
  - right; fqsatz.
  - right; fqsatz.
Qed.

(** ** NOR *)

(* print_endline (generate_lemmas cnor (typecheck_circuit d_empty cnor));; *)

Lemma Nor_obligation0: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation1: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation3: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation4: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a * b)%F + 1%F)%F) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation5: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation6: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (((a * b)%F + 1%F)%F - a)%F) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation7: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. intuition. Qed.

Lemma Nor_obligation8: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((((a * b)%F + 1%F)%F - a)%F - b)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_nor a b)) /\ ((v = 0%F) -> ~(f_nor a b))))).
Proof.
  unwrap_C. unfold f_nor. intros.
  intuit; try fqsatz.
  - right; fqsatz.
  - left; fqsatz.
  - left; fqsatz.
  - left; fqsatz.
Qed.
