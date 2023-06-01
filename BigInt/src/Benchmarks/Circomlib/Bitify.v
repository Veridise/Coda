(** * DSL benchmark: Bitify *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Coda.

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
#[local]Hint Extern 1 False => fqsatz || lia : core. 

(** ** Num2Bits *)

Definition as_le_f := Repr.as_le 1%nat.
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

Lemma Num2Bits_obligation0_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation1_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation2_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation3_trivial: forall (n : nat) (_in : F) (i : nat) (v : (list F)), True -> (i < n) -> Forall (fun x0 => True) v -> True -> (((length v) = i) -> ((length v) = i)).
Proof. hammer. Qed.

Lemma Num2Bits_obligation4_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x1 => True) x -> ((length x) = i) -> True -> True -> ((v = star) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation5_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x2 => True) x -> ((length x) = i) -> True -> Forall (fun x3 => True) v -> True -> ((((length v) = i) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation6_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x4 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation7: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x5 => True) x -> ((length x) = i) -> True -> Forall (fun x6 => True) v -> True -> ((v = (star :: x)) -> ((length v) = (i + 1%nat)%nat)).
Proof. intuit; subst. simpl. lia. Qed.

Lemma Num2Bits_obligation8_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x7 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation9: forall (n : nat) (_in : F) (v : (list F)), True -> Forall (fun x8 => True) v -> True -> ((v = nil) -> ((length v) = 0%nat)).
Proof. hammer. Qed.

Lemma Num2Bits_obligation10_trivial: forall (n : nat) (_in : F) (v : F), True -> True -> (True -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation11_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x9 => True) out -> ((length out) = n) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation12_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x10 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation13_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x11 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation14_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x12 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (as_le_f (out[:i]))) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation15_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x13 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation16_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x14 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x15,x16) => (x15 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x15,x16) => (x16 = (2%F ^ i)%F) end -> match lc1_e2 with (x15,x16) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (out[:i]))) /\ (v = lc1)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation17_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x17 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x18,x19) => (x18 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x18,x19) => (x19 = (2%F ^ i)%F) end -> match lc1_e2 with (x18,x19) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (out!i)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation18_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x20 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x21,x22) => (x21 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x21,x22) => (x22 = (2%F ^ i)%F) end -> match lc1_e2 with (x21,x22) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation19_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x23 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x24,x25) => (x24 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x24,x25) => (x25 = (2%F ^ i)%F) end -> match lc1_e2 with (x24,x25) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((out!i) * e2)%F) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation20: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x26 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x27,x28) => (x27 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x27,x28) => (x28 = (2%F ^ i)%F) end -> match lc1_e2 with (x27,x28) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((out!i) * e2)%F)%F) -> (v = (as_le_f (out[:(i + 1%nat)%nat])))).
Proof. 
  unfold as_le_f. unwrap_C. intros. destruct lc1_e2. 
  rewrite firstn_plus1, Repr.as_le_app by lia. 
  cbn [Repr.as_le].
  hammer.
Qed.

Lemma Num2Bits_obligation21_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x29 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x30,x31) => (x30 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x30,x31) => (x31 = (2%F ^ i)%F) end -> match lc1_e2 with (x30,x31) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation22_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x32 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x33,x34) => (x33 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x33,x34) => (x34 = (2%F ^ i)%F) end -> match lc1_e2 with (x33,x34) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation23: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x35 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x36,x37) => (x36 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x36,x37) => (x37 = (2%F ^ i)%F) end -> match lc1_e2 with (x36,x37) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof. 
  unwrap_C. intros. destruct lc1_e2. 
  replace ((N.of_nat (Init.Nat.add i (S O)))) with (i+1)%N by lia.
  rewrite F.pow_add_r, F.pow_1_r. hammer.
 Qed.

Lemma Num2Bits_obligation24_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F), True -> Forall (fun x38 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x39,x40) => (x39 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x39,x40) => (x40 = (2%F ^ i)%F) end -> match lc1_e2 with (x39,x40) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> (True -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation25: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x41 => True) out -> ((length out) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (out[:0%nat])))).
Proof. hammer. Qed.

Lemma Num2Bits_obligation26: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x42 => True) out -> ((length out) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. hammer. Qed.

Lemma Num2Bits_obligation27_trivial: forall (n : nat) (_in : F) (out : (list F)), True -> Forall (fun x43 => True) out -> ((length out) = n) -> (True -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation28_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x44 => True) out -> ((length out) = n) -> match lc1_e2 with (x45,x46) => (x45 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x45,x46) => (x46 = (2%F ^ n)%F) end -> match lc1_e2 with (x45,x46) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation29_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x47 => True) out -> ((length out) = n) -> match lc1_e2 with (x48,x49) => (x48 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x48,x49) => (x49 = (2%F ^ n)%F) end -> match lc1_e2 with (x48,x49) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation30_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x50 => True) out -> ((length out) = n) -> match lc1_e2 with (x51,x52) => (x51 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x51,x52) => (x52 = (2%F ^ n)%F) end -> match lc1_e2 with (x51,x52) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation31_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (v : unit), True -> Forall (fun x53 => True) out -> ((length out) = n) -> match lc1_e2 with (x54,x55) => (x54 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x54,x55) => (x55 = (2%F ^ n)%F) end -> match lc1_e2 with (x54,x55) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> True -> ((forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation32_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x56 => True) out -> ((length out) = n) -> match lc1_e2 with (x57,x58) => (x57 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x57,x58) => (x58 = (2%F ^ n)%F) end -> match lc1_e2 with (x57,x58) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation33_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x59 => True) out -> ((length out) = n) -> match lc1_e2 with (x60,x61) => (x60 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x60,x61) => (x61 = (2%F ^ n)%F) end -> match lc1_e2 with (x60,x61) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation34_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x62 => True) out -> ((length out) = n) -> match lc1_e2 with (x63,x64) => (x63 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x63,x64) => (x64 = (2%F ^ n)%F) end -> match lc1_e2 with (x63,x64) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation35_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x65 => True) out -> ((length out) = n) -> match lc1_e2 with (x66,x67) => (x66 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x66,x67) => (x67 = (2%F ^ n)%F) end -> match lc1_e2 with (x66,x67) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = ((out!i) - 1%F)%F) -> True).
Proof. hammer. Qed.

Lemma Num2Bits_obligation36: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : unit), True -> Forall (fun x68 => True) out -> ((length out) = n) -> match lc1_e2 with (x69,x70) => (x69 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x69,x70) => (x70 = (2%F ^ n)%F) end -> match lc1_e2 with (x69,x70) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((((out!i) * ((out!i) - 1%F)%F)%F = 0%F) -> (forall (j:nat), 0%nat <= j < (i + 1%nat)%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof. 
  unwrap_C. intuit.
  destruct (dec (j < i)). auto.
  assert (j = i) by lia. subst j.
   destruct (dec (out ! i = 0))%F; auto.
Qed.

Lemma Num2Bits_obligation37: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit), True -> Forall (fun x71 => True) out -> ((length out) = n) -> match lc1_e2 with (x72,x73) => (x72 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x72,x73) => (x73 = (2%F ^ n)%F) end -> match lc1_e2 with (x72,x73) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (True -> (forall (j:nat), 0%nat <= j < 0%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof. hammer. Qed.

Lemma Num2Bits_obligation38: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (u0 : unit) (u : unit) (v : (list F)), True -> Forall (fun x74 => True) out -> ((length out) = n) -> match lc1_e2 with (x75,x76) => (x75 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x75,x76) => (x76 = (2%F ^ n)%F) end -> match lc1_e2 with (x75,x76) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (forall (j:nat), 0%nat <= j < n -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> Forall (fun x77 => True) v -> True -> ((((length v) = n) /\ (v = out)) -> ((((as_le_f v) = _in) /\ ((length v) = n)) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof.
  unfold as_le_f.
  intuit; subst. 
  rewrite firstn_all. reflexivity.
  auto.
Qed.


Lemma Bits2Num_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (as_le_f (_in[:i]))) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x6,x7) => (x6 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x6,x7) => (x7 = (2%F ^ i)%F) end -> match lc1_e2 with (x6,x7) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (_in[:i]))) /\ (v = lc1)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation6_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x9,x10) => (x9 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x9,x10) => (x10 = (2%F ^ i)%F) end -> match lc1_e2 with (x9,x10) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (_in!i)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation7_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x12,x13) => (x12 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x12,x13) => (x13 = (2%F ^ i)%F) end -> match lc1_e2 with (x12,x13) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation8_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x15,x16) => (x15 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x15,x16) => (x16 = (2%F ^ i)%F) end -> match lc1_e2 with (x15,x16) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((_in!i) * e2)%F) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation9: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x18,x19) => (x18 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x18,x19) => (x19 = (2%F ^ i)%F) end -> match lc1_e2 with (x18,x19) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((_in!i) * e2)%F)%F) -> (v = (as_le_f (_in[:(i + 1%nat)%nat])))).
Proof. 
  unfold as_le_f. unwrap_C.  destruct lc1_e2.
  intros.
  rewrite firstn_plus1, Repr.as_le_app by lia.
  simplify. rewrite firstn_length_le by lia. cbn [Repr.as_le].
  fqsatz.
Qed.

Lemma Bits2Num_obligation10_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x21,x22) => (x21 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x21,x22) => (x22 = (2%F ^ i)%F) end -> match lc1_e2 with (x21,x22) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation11_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x24,x25) => (x24 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x24,x25) => (x25 = (2%F ^ i)%F) end -> match lc1_e2 with (x24,x25) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation12: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x26 => ((x26 = 0%F) \/ (x26 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x27,x28) => (x27 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x27,x28) => (x28 = (2%F ^ i)%F) end -> match lc1_e2 with (x27,x28) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof. 
  unwrap_C. intros. destruct lc1_e2. 
  replace ((N.of_nat (Init.Nat.add i (S O)))) with (i+1)%N by lia.
  rewrite F.pow_add_r, F.pow_1_r. hammer.
 Qed.

Lemma Bits2Num_obligation13_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F), Forall (fun x29 => ((x29 = 0%F) \/ (x29 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x30,x31) => (x30 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x30,x31) => (x31 = (2%F ^ i)%F) end -> match lc1_e2 with (x30,x31) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> (True -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation14: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x32 => ((x32 = 0%F) \/ (x32 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (_in[:0%nat])))).
Proof. hammer. Qed.

Lemma Bits2Num_obligation15: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. hammer. Qed.

Lemma Bits2Num_obligation16_trivial: forall (n : nat) (_in : (list F)), Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) _in -> ((length _in) = n) -> (True -> True).
Proof. hammer. Qed.

Lemma Bits2Num_obligation17: forall (n : nat) (_in : (list F)) (lc1_e2 : (F * F)) (lc1 : F) (e2 : F) (v : F), Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) _in -> ((length _in) = n) -> match lc1_e2 with (x36,x37) => (x36 = (as_le_f (_in[:n]))) end -> match lc1_e2 with (x36,x37) => (x37 = (2%F ^ n)%F) end -> match lc1_e2 with (x36,x37) => True end -> (lc1 = (as_le_f (_in[:n]))) -> (e2 = (2%F ^ n)%F) -> True -> (((v = (as_le_f (_in[:n]))) /\ (v = lc1)) -> (v = (as_le_f _in))).
Proof. intros. rewrite firstn_all2 in H7 by lia. hammer. Qed.

