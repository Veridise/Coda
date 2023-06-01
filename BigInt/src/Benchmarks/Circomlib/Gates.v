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

From Circom Require Import Circom Util Default Tuple LibTactics Simplify ListUtil Repr Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

#[local]Hint Extern 1 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[local]Hint Extern 1  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[local]Hint Extern 1  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[local]Hint Extern 1 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[local]Hint Extern 1 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[local]Hint Extern 1 (Forall _ (_ :: _)) => constructor: core.
#[local]Hint Extern 1 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[local]Hint Extern 1  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[local]Hint Extern 1 (_ < _) => lia: core.
#[local]Hint Extern 1 (_ < _)%nat => lia: core.
#[local]Hint Extern 1 (_ <= _) => lia: core.
#[local]Hint Extern 1 (_ <= _)%nat => lia: core.
#[local]Hint Extern 1 (_ > _) => lia: core.
#[local]Hint Extern 1 (_ > _)%nat => lia: core.
#[local]Hint Extern 1 (_ >= _) => lia: core.
#[local]Hint Extern 1 (_ >= _)%nat => lia: core.
#[local]Hint Extern 1 (S _ = S _) => f_equal: core. 
#[local]Hint Extern 1 (@eq (F.F q) _ _) => fqsatz: core. 
#[local]Hint Extern 1 False => fqsatz: core. 


(** ** NOT *)
Lemma Not_obligation0_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma Not_obligation1_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma Not_obligation2_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = (_in + 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma Not_obligation3_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma Not_obligation4_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma Not_obligation5_trivial: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = (2%F * _in)%F) -> True).
Proof. hammer. Qed.

Lemma Not_obligation6: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = ((_in + 1%F)%F - (2%F * _in)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not _in)) /\ ((v = 0%F) -> ~(f_not _in))))).
Proof.
  unwrap_C. unfold f_not. intuit; auto.
Qed.

(** ** XOR *)

Lemma Xor_obligation0_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation1_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation2_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation3_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation4_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation5_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation6_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation7_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (2%F * (a * b)%F)%F) -> True).
Proof. hammer. Qed.

Lemma Xor_obligation8: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a + b)%F - (2%F * (a * b)%F)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_xor a b)) /\ ((v = 0%F) -> ~(f_xor a b))))).
Proof.
  unwrap_C. unfold f_xor. intuit; auto.
Qed.

(** ** AND *)

Lemma And_obligation0_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma And_obligation1_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma And_obligation2: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_and a b)) /\ ((v = 0%F) -> ~(f_and a b))))).
Proof.
  unwrap_C. unfold f_and. intuit; auto.
Qed.

(** ** NAND *)

Lemma Nand_obligation0_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma Nand_obligation1_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Nand_obligation2_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Nand_obligation3_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. hammer. Qed.

Lemma Nand_obligation4: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (1%F - (a * b)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_nand a b)) /\ ((v = 0%F) -> ~(f_nand a b))))).
Proof.
  unwrap_C. unfold f_nand. intuit; auto.
Qed.

(** ** OR *)

(* print_endline (generate_lemmas cor (typecheck_circuit d_empty cor));; *)
Lemma Or_obligation0_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Or_obligation1_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Or_obligation2_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. hammer. Qed.

Lemma Or_obligation3_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Or_obligation4_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Or_obligation5_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. hammer. Qed.

Lemma Or_obligation6: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a + b)%F - (a * b)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_or a b)) /\ ((v = 0%F) -> ~(f_or a b))))).
Proof. 
  unwrap_C. unfold f_or. intuit; auto.
Qed.


(** ** NOR *)


Lemma Nor_obligation0_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation1_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation2_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (a * b)%F) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation3_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation4_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((a * b)%F + 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation5_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = a)) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation6_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = (((a * b)%F + 1%F)%F - a)%F) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation7_trivial: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = b)) -> True).
Proof. hammer. Qed.

Lemma Nor_obligation8: forall (a : F) (b : F) (v : F), ((a = 0%F) \/ (a = 1%F)) -> ((b = 0%F) \/ (b = 1%F)) -> True -> ((v = ((((a * b)%F + 1%F)%F - a)%F - b)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_nor a b)) /\ ((v = 0%F) -> ~(f_nor a b))))).
Proof. unwrap_C. unfold f_nor. intuit; auto. Qed.
