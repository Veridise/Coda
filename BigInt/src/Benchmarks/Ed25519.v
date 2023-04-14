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

(** ** onlycarry *)

Lemma onlycarry_obligation0_trivial: forall (bit : F) (carry : F) (val : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation1_trivial: forall (bit : F) (carry : F) (val : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation2_trivial: forall (bit : F) (carry : F) (val : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation3_trivial: forall (bit : F) (carry : F) (val : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> True -> ((v = (val - 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation4_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = val) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation5_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation6_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = carry)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation7_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = (bit + carry)%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation8_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : Z), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = (^ (bit + carry)%F)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation9_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (v : Z), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> True -> ((v = 2%nat) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation10_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation11_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation12_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation13_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> True -> ((v = (carry_out - 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation14_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = carry_out) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation15_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = bit)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation16_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = carry)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation17_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = (bit + carry)%F) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation18_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : Z), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = (^ (bit + carry)%F)) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation19_trivial: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (v : Z), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> True -> ((v = 2%nat) -> True).
Proof. hammer. Qed.

Lemma onlycarry_obligation20: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ (bit + carry)%F) / 2%nat)%Z) -> True -> ((v = val) -> ((^ v) = ((^ (bit + carry)%F) mod 2%nat)%Z)).
Proof. hammer. Qed.

Lemma onlycarry_obligation21: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit) (v : F), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ (bit + carry)%F) / 2%nat)%Z) -> True -> ((v = carry_out) -> ((^ v) = ((^ (bit + carry)%F) / 2%nat)%Z)).
Proof. hammer. Qed.

Lemma onlycarry_obligation22: forall (bit : F) (carry : F) (val : F) (u0 : unit) (u1 : unit) (carry_out : F) (u2 : unit) (u3 : unit), ((bit = 0%F) \/ (bit = 1%F)) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((val * (val - 1%F)%F)%F = 0%F) -> ((^ val) = ((^ (bit + carry)%F) mod 2%nat)%Z) -> True -> ((carry_out * (carry_out - 1%F)%F)%F = 0%F) -> ((^ carry_out) = ((^ (bit + carry)%F) / 2%nat)%Z) -> (True -> (((2%F * carry_out)%F + val)%F = (bit + carry)%F)).
Proof. Admitted.

(** ** BinAdd *)


Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).


Lemma BinAdd_obligation0_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : Z), Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) in1 -> ((length in1) = nBits) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation1_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : Z), Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) in1 -> ((length in1) = nBits) -> True -> (((0%nat <= v) /\ (v = nBits)) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation2_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : Z), Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) in1 -> ((length in1) = nBits) -> True -> (((0%nat <= v) /\ (v < nBits)) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation3_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (v : ((list F) * F)), Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match v with (x12,x13) => Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) x12 end -> match v with (x12,x13) => ((length x12) = i) end -> match v with (x12,x13) => ((x13 = 0%F) \/ (x13 = 1%F)) end -> match v with (x12,x13) => True end -> (((as_le_f ((fst v) ++ ((snd v) :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation4_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (v : (list F)), Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) v -> True -> (((length v) = i) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation5_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (v : F), Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation6_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (v : F), Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation7: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (v : F), Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x24,x25) => Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) x24 end -> match s_c with (x24,x25) => ((length x24) = i) end -> match s_c with (x24,x25) => ((x25 = 0%F) \/ (x25 = 1%F)) end -> match s_c with (x24,x25) => ((as_le_f (x24 ++ (x25 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x26 => ((x26 = 0%F) \/ (x26 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x28,x29) => Forall (fun x27 => True) x28 end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> True -> (((v = (in0!i)) /\ (v = b0)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma BinAdd_obligation8: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (v : F), Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x33,x34) => Forall (fun x32 => ((x32 = 0%F) \/ (x32 = 1%F))) x33 end -> match s_c with (x33,x34) => ((length x33) = i) end -> match s_c with (x33,x34) => ((x34 = 0%F) \/ (x34 = 1%F)) end -> match s_c with (x33,x34) => ((as_le_f (x33 ++ (x34 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x37,x38) => Forall (fun x36 => True) x37 end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> True -> (((v = (in1!i)) /\ (v = b1)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma BinAdd_obligation9: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (v : F), Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x40 => ((x40 = 0%F) \/ (x40 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x42,x43) => Forall (fun x41 => ((x41 = 0%F) \/ (x41 = 1%F))) x42 end -> match s_c with (x42,x43) => ((length x42) = i) end -> match s_c with (x42,x43) => ((x43 = 0%F) \/ (x43 = 1%F)) end -> match s_c with (x42,x43) => ((as_le_f (x42 ++ (x43 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x44 => ((x44 = 0%F) \/ (x44 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x46,x47) => Forall (fun x45 => True) x46 end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (v = (snd s_c))) /\ (v = c)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma BinAdd_obligation10: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (val_carry_out : (F * F)) (carry_out : F) (val : F) (_u1 : (F * F)) (v : (list F)), Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x49 => ((x49 = 0%F) \/ (x49 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x51,x52) => Forall (fun x50 => ((x50 = 0%F) \/ (x50 = 1%F))) x51 end -> match s_c with (x51,x52) => ((length x51) = i) end -> match s_c with (x51,x52) => ((x52 = 0%F) \/ (x52 = 1%F)) end -> match s_c with (x51,x52) => ((as_le_f (x51 ++ (x52 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x53 => ((x53 = 0%F) \/ (x53 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x55,x56) => Forall (fun x54 => True) x55 end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> match val_carry_out with (x57,x58) => ((x57 = 0%F) \/ (x57 = 1%F)) end -> match val_carry_out with (x57,x58) => ((x58 = 0%F) \/ (x58 = 1%F)) end -> match val_carry_out with (x57,x58) => (((2%F * x58)%F + x57)%F = ((b0 + b1)%F + c)%F) end -> (((carry_out = 0%F) \/ (carry_out = 1%F)) /\ (carry_out = (snd val_carry_out))) -> (((val = 0%F) \/ (val = 1%F)) /\ (val = (fst val_carry_out))) -> match _u1 with (x59,x60) => True end -> match _u1 with (x59,x60) => True end -> match _u1 with (x59,x60) => ((((2%F * carry_out)%F + val)%F = ((b0 + b1)%F + c)%F) /\ (val_carry_out = val_carry_out)) end -> Forall (fun x61 => ((x61 = 0%F) \/ (x61 = 1%F))) v -> True -> (((v = (s ++ (val :: nil))) /\ ((length v) = ((length s) + (length (val :: nil)))%nat)) -> (((length v) = (i + 1%nat)%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof. 
  unwrap_C. intros. destruct _u0. destruct _u1. destruct s_c as [_s _c]. destruct val_carry_out as [_val _carry_out]. simpl in *.
  clear H6. destruct H8. apply Repr.in_range_binary in H6. subst _c.
  clear H17.
  clear H18.
  destruct H20. destruct H21. subst _carry_out _val.
  apply Repr.in_range_binary in H8, H18. hammer.
Qed.


Lemma BinAdd_obligation11_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (val_carry_out : (F * F)) (carry_out : F) (val : F) (_u1 : (F * F)) (v : F), Forall (fun x62 => ((x62 = 0%F) \/ (x62 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x63 => ((x63 = 0%F) \/ (x63 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x65,x66) => Forall (fun x64 => ((x64 = 0%F) \/ (x64 = 1%F))) x65 end -> match s_c with (x65,x66) => ((length x65) = i) end -> match s_c with (x65,x66) => ((x66 = 0%F) \/ (x66 = 1%F)) end -> match s_c with (x65,x66) => ((as_le_f (x65 ++ (x66 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x67 => ((x67 = 0%F) \/ (x67 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x69,x70) => Forall (fun x68 => True) x69 end -> match _u0 with (x69,x70) => True end -> match _u0 with (x69,x70) => True end -> match _u0 with (x69,x70) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> match val_carry_out with (x71,x72) => ((x71 = 0%F) \/ (x71 = 1%F)) end -> match val_carry_out with (x71,x72) => ((x72 = 0%F) \/ (x72 = 1%F)) end -> match val_carry_out with (x71,x72) => (((2%F * x72)%F + x71)%F = ((b0 + b1)%F + c)%F) end -> (((carry_out = 0%F) \/ (carry_out = 1%F)) /\ (carry_out = (snd val_carry_out))) -> (((val = 0%F) \/ (val = 1%F)) /\ (val = (fst val_carry_out))) -> match _u1 with (x73,x74) => True end -> match _u1 with (x73,x74) => True end -> match _u1 with (x73,x74) => ((((2%F * carry_out)%F + val)%F = ((b0 + b1)%F + c)%F) /\ (val_carry_out = val_carry_out)) end -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation12: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (val_carry_out : (F * F)) (carry_out : F) (val : F) (_u1 : (F * F)) (v : F), Forall (fun x75 => ((x75 = 0%F) \/ (x75 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x76 => ((x76 = 0%F) \/ (x76 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x78,x79) => Forall (fun x77 => ((x77 = 0%F) \/ (x77 = 1%F))) x78 end -> match s_c with (x78,x79) => ((length x78) = i) end -> match s_c with (x78,x79) => ((x79 = 0%F) \/ (x79 = 1%F)) end -> match s_c with (x78,x79) => ((as_le_f (x78 ++ (x79 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x80 => ((x80 = 0%F) \/ (x80 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x82,x83) => Forall (fun x81 => True) x82 end -> match _u0 with (x82,x83) => True end -> match _u0 with (x82,x83) => True end -> match _u0 with (x82,x83) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> match val_carry_out with (x84,x85) => ((x84 = 0%F) \/ (x84 = 1%F)) end -> match val_carry_out with (x84,x85) => ((x85 = 0%F) \/ (x85 = 1%F)) end -> match val_carry_out with (x84,x85) => (((2%F * x85)%F + x84)%F = ((b0 + b1)%F + c)%F) end -> (((carry_out = 0%F) \/ (carry_out = 1%F)) /\ (carry_out = (snd val_carry_out))) -> (((val = 0%F) \/ (val = 1%F)) /\ (val = (fst val_carry_out))) -> match _u1 with (x86,x87) => True end -> match _u1 with (x86,x87) => True end -> match _u1 with (x86,x87) => ((((2%F * carry_out)%F + val)%F = ((b0 + b1)%F + c)%F) /\ (val_carry_out = val_carry_out)) end -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (v = (snd val_carry_out))) /\ (v = carry_out)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma BinAdd_obligation13: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (i : nat) (s_c : ((list F) * F)) (c : F) (s : (list F)) (_u0 : ((list F) * F)) (b0 : F) (b1 : F) (val_carry_out : (F * F)) (carry_out : F) (val : F) (_u1 : (F * F)), Forall (fun x88 => ((x88 = 0%F) \/ (x88 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x89 => ((x89 = 0%F) \/ (x89 = 1%F))) in1 -> ((length in1) = nBits) -> (i < nBits) -> match s_c with (x91,x92) => Forall (fun x90 => ((x90 = 0%F) \/ (x90 = 1%F))) x91 end -> match s_c with (x91,x92) => ((length x91) = i) end -> match s_c with (x91,x92) => ((x92 = 0%F) \/ (x92 = 1%F)) end -> match s_c with (x91,x92) => ((as_le_f (x91 ++ (x92 :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) end -> (((c = 0%F) \/ (c = 1%F)) /\ (c = (snd s_c))) -> Forall (fun x93 => ((x93 = 0%F) \/ (x93 = 1%F))) s -> (((length s) = i) /\ (s = (fst s_c))) -> match _u0 with (x95,x96) => Forall (fun x94 => True) x95 end -> match _u0 with (x95,x96) => True end -> match _u0 with (x95,x96) => True end -> match _u0 with (x95,x96) => (((as_le_f (s ++ (c :: nil))) = ((as_le_f (in0[:i])) + (as_le_f (in1[:i])))%F) /\ (s_c = s_c)) end -> (b0 = (in0!i)) -> (b1 = (in1!i)) -> match val_carry_out with (x97,x98) => ((x97 = 0%F) \/ (x97 = 1%F)) end -> match val_carry_out with (x97,x98) => ((x98 = 0%F) \/ (x98 = 1%F)) end -> match val_carry_out with (x97,x98) => (((2%F * x98)%F + x97)%F = ((b0 + b1)%F + c)%F) end -> (((carry_out = 0%F) \/ (carry_out = 1%F)) /\ (carry_out = (snd val_carry_out))) -> (((val = 0%F) \/ (val = 1%F)) /\ (val = (fst val_carry_out))) -> match _u1 with (x99,x100) => True end -> match _u1 with (x99,x100) => True end -> match _u1 with (x99,x100) => ((((2%F * carry_out)%F + val)%F = ((b0 + b1)%F + c)%F) /\ (val_carry_out = val_carry_out)) end -> (True -> ((as_le_f ((s ++ (val :: nil)) ++ (carry_out :: nil))) = ((as_le_f (in0[:(i + 1%nat)%nat])) + (as_le_f (in1[:(i + 1%nat)%nat])))%F)).
Proof. 
  unfold as_le_f.
  unwrap_C. intros. destruct _u0. destruct _u1. destruct s_c as [_s _c]. destruct val_carry_out as [_val _carry_out]. simpl in *.
  clear H6. destruct H8. apply Repr.in_range_binary in H6. destruct H10. subst _c _s.
  clear H17.
  clear H18.
  destruct H20. destruct H21. subst _carry_out _val.
  apply Repr.in_range_binary in H8, H18.
  do 2 rewrite firstn_plus1 by lia.
  repeat rewrite Repr.as_le_app. simplify.
  simpl. simplify.
  rewrite_length. rewrite app_length. simpl.
  repeat rewrite Repr.as_le_app in H14. simplify' H14. simpl in  H14. simplify' H14.
  destruct H14.
  destruct H24.
  subst b0 b1.
  rewrite H5 in *.
  replace ((N.of_nat (Init.Nat.add i (S O))))%N with (i+1)%N by lia.
  rewrite F.pow_add_r.
  simplify.
  fqsatz.
Qed.

Lemma BinAdd_obligation14: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : (list F)), Forall (fun x101 => ((x101 = 0%F) \/ (x101 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x102 => ((x102 = 0%F) \/ (x102 = 1%F))) in1 -> ((length in1) = nBits) -> Forall (fun x103 => True) v -> True -> ((v = nil) -> (((length v) = 0%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof. hammer. Qed.

Lemma BinAdd_obligation15_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : F), Forall (fun x104 => ((x104 = 0%F) \/ (x104 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x105 => ((x105 = 0%F) \/ (x105 = 1%F))) in1 -> ((length in1) = nBits) -> True -> (True -> True).
Proof. hammer. Qed.

Lemma BinAdd_obligation16: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (v : F), Forall (fun x106 => ((x106 = 0%F) \/ (x106 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x107 => ((x107 = 0%F) \/ (x107 = 1%F))) in1 -> ((length in1) = nBits) -> True -> ((v = 0%F) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma BinAdd_obligation17: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)), Forall (fun x108 => ((x108 = 0%F) \/ (x108 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x109 => ((x109 = 0%F) \/ (x109 = 1%F))) in1 -> ((length in1) = nBits) -> (True -> ((as_le_f (nil ++ (0%F :: nil))) = ((as_le_f (in0[:0%nat])) + (as_le_f (in1[:0%nat])))%F)).
Proof. unwrap_C. unfold as_le_f. simpl. intuit. simplify. fqsatz. Qed.

Lemma BinAdd_obligation18: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (sum_carry : ((list F) * F)) (carry : F) (sum : (list F)) (_u2 : ((list F) * F)) (v : (list F)), Forall (fun x110 => ((x110 = 0%F) \/ (x110 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x111 => ((x111 = 0%F) \/ (x111 = 1%F))) in1 -> ((length in1) = nBits) -> match sum_carry with (x113,x114) => Forall (fun x112 => ((x112 = 0%F) \/ (x112 = 1%F))) x113 end -> match sum_carry with (x113,x114) => ((length x113) = nBits) end -> match sum_carry with (x113,x114) => ((x114 = 0%F) \/ (x114 = 1%F)) end -> match sum_carry with (x113,x114) => ((as_le_f (x113 ++ (x114 :: nil))) = ((as_le_f (in0[:nBits])) + (as_le_f (in1[:nBits])))%F) end -> (((carry = 0%F) \/ (carry = 1%F)) /\ (carry = (snd sum_carry))) -> Forall (fun x115 => ((x115 = 0%F) \/ (x115 = 1%F))) sum -> (((length sum) = nBits) /\ (sum = (fst sum_carry))) -> match _u2 with (x117,x118) => Forall (fun x116 => True) x117 end -> match _u2 with (x117,x118) => True end -> match _u2 with (x117,x118) => True end -> match _u2 with (x117,x118) => (((as_le_f (sum ++ (carry :: nil))) = ((as_le_f (in0[:nBits])) + (as_le_f (in1[:nBits])))%F) /\ (sum_carry = sum_carry)) end -> Forall (fun x119 => ((x119 = 0%F) \/ (x119 = 1%F))) v -> True -> (((v = (sum ++ (carry :: nil))) /\ ((length v) = ((length sum) + (length (carry :: nil)))%nat)) -> ((((length v) = (nBits + 1%nat)%nat) /\ ((as_le_f v) = ((as_le_f in0) + (as_le_f in1))%F)) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof. Proof.
  unwrap_C. unfold as_le_f.
  intros. destruct sum_carry as [_sum _carry]. destruct _u2.
  destruct H7. clear H7. destruct H9. simpl in *. subst _carry _sum. apply Repr.in_range_binary in H5.
  intuit.
  subst. rewrite_length.
  subst v. rewrite H9. rewrite_length. do 2 rewrite firstn_all2 by lia. fqsatz.
  auto.
Qed.

Lemma BinAdd_obligation19_trivial: forall (nBits : nat) (in0 : (list F)) (in1 : (list F)) (sum_carry : ((list F) * F)) (carry : F) (sum : (list F)) (_u2 : ((list F) * F)) (v : F), Forall (fun x120 => ((x120 = 0%F) \/ (x120 = 1%F))) in0 -> ((length in0) = nBits) -> Forall (fun x121 => ((x121 = 0%F) \/ (x121 = 1%F))) in1 -> ((length in1) = nBits) -> match sum_carry with (x123,x124) => Forall (fun x122 => ((x122 = 0%F) \/ (x122 = 1%F))) x123 end -> match sum_carry with (x123,x124) => ((length x123) = nBits) end -> match sum_carry with (x123,x124) => ((x124 = 0%F) \/ (x124 = 1%F)) end -> match sum_carry with (x123,x124) => ((as_le_f (x123 ++ (x124 :: nil))) = ((as_le_f (in0[:nBits])) + (as_le_f (in1[:nBits])))%F) end -> (((carry = 0%F) \/ (carry = 1%F)) /\ (carry = (snd sum_carry))) -> Forall (fun x125 => ((x125 = 0%F) \/ (x125 = 1%F))) sum -> (((length sum) = nBits) /\ (sum = (fst sum_carry))) -> match _u2 with (x127,x128) => Forall (fun x126 => True) x127 end -> match _u2 with (x127,x128) => True end -> match _u2 with (x127,x128) => True end -> match _u2 with (x127,x128) => (((as_le_f (sum ++ (carry :: nil))) = ((as_le_f (in0[:nBits])) + (as_le_f (in1[:nBits])))%F) /\ (sum_carry = sum_carry)) end -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.


(** ** LessThanPower *)

Lemma LessThanPower_obligation0: forall (base : Z) (_in : F) (v : Z), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma LessThanPower_obligation1: forall (base : Z) (_in : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) /\ (v = _in)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanPower_obligation2_trivial: forall (base : Z) (_in : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma LessThanPower_obligation3: forall (base : Z) (_in : F) (v : Z), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= v) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) /\ (v = base)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma LessThanPower_obligation4: forall (base : Z) (_in : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((v = (2%F ^ Z.to_N base)%F) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanPower_obligation5: forall (base : Z) (_in : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ _in) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ _in) < (^ (2%F ^ Z.to_N base)%F))) /\ ((v = 0%F) -> ~((^ _in) < (^ (2%F ^ Z.to_N base)%F))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ _in) < (2%nat ^ Z.to_N base)%Z)) /\ ((v = 0%F) -> ~((^ _in) < (2%nat ^ Z.to_N base)%Z))))).
Proof. Admitted.

(** ** LessThanBounded *)

Lemma LessThanBounded_obligation0: forall (base : Z) (in0 : F) (in1 : F) (v : Z), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= v) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) /\ (v = base)) -> ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= v) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)))).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation1: forall (base : Z) (in0 : F) (in1 : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> True -> ((((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) /\ (v = in0)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation2: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (v : Z), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= v) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) /\ (v = base)) -> ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= v) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)))).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation3: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) /\ (v = in1)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation4: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (_y : F) (v : Z), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> (((_y = 0%F) \/ (_y = 1%F)) /\ (((_y = 1%F) -> ((^ in1) < (2%nat ^ Z.to_N base)%Z)) /\ ((_y = 0%F) -> ~((^ in1) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation5: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (_y : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> (((_y = 0%F) \/ (_y = 1%F)) /\ (((_y = 1%F) -> ((^ in1) < (2%nat ^ Z.to_N base)%Z)) /\ ((_y = 0%F) -> ~((^ in1) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) /\ (v = in0)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation6: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (_y : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> (((_y = 0%F) \/ (_y = 1%F)) /\ (((_y = 1%F) -> ((^ in1) < (2%nat ^ Z.to_N base)%Z)) /\ ((_y = 0%F) -> ~((^ in1) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) /\ (v = in1)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma LessThanBounded_obligation7: forall (base : Z) (in0 : F) (in1 : F) (_x : F) (_y : F) (v : F), ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat <= base) /\ ((^ (2%F ^ Z.to_N base)%F) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z))) -> ((^ in0) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> ((^ in1) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z) -> (((_x = 0%F) \/ (_x = 1%F)) /\ (((_x = 1%F) -> ((^ in0) < (2%nat ^ Z.to_N base)%Z)) /\ ((_x = 0%F) -> ~((^ in0) < (2%nat ^ Z.to_N base)%Z)))) -> (((_y = 0%F) \/ (_y = 1%F)) /\ (((_y = 1%F) -> ((^ in1) < (2%nat ^ Z.to_N base)%Z)) /\ ((_y = 0%F) -> ~((^ in1) < (2%nat ^ Z.to_N base)%Z)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ in0) < (^ in1))) /\ ((v = 0%F) -> ~((^ in0) < (^ in1))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ in0) < (^ in1))) /\ ((v = 0%F) -> ~((^ in0) < (^ in1)))))).
Proof. hammer. Qed.
