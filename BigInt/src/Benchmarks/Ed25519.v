(** * DSL benchmark : Ed25519 *)

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

(** ** fulladder *)

Lemma fulladder_obligation0_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation1_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation2_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation3_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = (val - 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation4_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation5_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit1)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation6_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit2)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation7_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = (bit1 + bit2)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation8_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = carry)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation9_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = ((bit1 + bit2)%F + carry)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation10_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : Z), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = (^ ((bit1 + bit2)%F + carry)%F)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation11_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (v : Z), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = 2%nat) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation12_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation13_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation14_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation15_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = (carry_out - 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation16_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation17_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit1)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation18_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit2)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation19_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = (bit1 + bit2)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation20_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = carry)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation21_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = ((bit1 + bit2)%F + carry)%F) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation22_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : Z), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = (^ ((bit1 + bit2)%F + carry)%F)) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation23_trivial: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : Z), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = 2%nat) -> True).
Proof. hammer. Qed.

Lemma fulladder_obligation24: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ ((bit1 + bit2)%F + carry)%F) / 2%nat)%Z) -> True -> ((v = val) -> ((^ v) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z)).
Proof. hammer. Qed.

Lemma fulladder_obligation25: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit) (v : F), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ ((bit1 + bit2)%F + carry)%F) / 2%nat)%Z) -> True -> ((v = carry_out) -> ((^ v) = ((^ ((bit1 + bit2)%F + carry)%F) / 2%nat)%Z)).
Proof. hammer. Qed.

Lemma fulladder_obligation26: forall (bit1 : F) (bit2 : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit), ((bit1 = 0%F) \/ (bit1 = 1%F)) -> ((bit2 = 0%F) \/ (bit2 = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ ((bit1 + bit2)%F + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ ((bit1 + bit2)%F + carry)%F) / 2%nat)%Z) -> (True -> (((2%F * carry_out)%F + val)%F = ((bit1 + bit2)%F + carry)%F)).
Proof. Admitted.
