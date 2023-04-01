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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

(** ** Num2Bits *)

Definition as_le_f := Repr.as_le 1%nat.
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

Lemma Num2Bits_obligation0_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> ((v = 0%nat) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation1_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation2_trivial: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation3_trivial: forall (n : nat) (_in : F) (i : nat) (v : (list F)), True -> (i < n) -> Forall (fun x0 => True) v -> True -> (((length v) = i) -> ((length v) = i)).
Proof. auto. Qed.

Lemma Num2Bits_obligation4_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x1 => True) x -> ((length x) = i) -> True -> True -> ((v = star) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation5_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x2 => True) x -> ((length x) = i) -> True -> Forall (fun x3 => True) v -> True -> ((((length v) = i) /\ (v = x)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation6_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x4 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation7: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x5 => True) x -> ((length x) = i) -> True -> Forall (fun x6 => True) v -> True -> ((v = (star :: x)) -> ((length v) = (i + 1%nat)%nat)).
Proof. intuit. subst v. simpl. lia. Qed.

Lemma Num2Bits_obligation8_trivial: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x7 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation9_trivial: forall (n : nat) (_in : F), True -> (((length v) = 0%nat) -> ((length v) = 0%nat)).
Proof. auto. Qed.

Lemma Num2Bits_obligation10_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x8 => True) out -> ((length out) = n) -> True -> ((v = 0%nat) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation11_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x9 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation12_trivial: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x10 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation13_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x11 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (as_le_f (out[:i]))) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation14_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x12 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation15_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x13 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x14,x15) => (x14 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x14,x15) => (x15 = (2%F ^ i)%F) end -> match lc1_e2 with (x14,x15) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (out[:i]))) /\ (v = lc1)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation16_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x16 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x17,x18) => (x17 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x17,x18) => (x18 = (2%F ^ i)%F) end -> match lc1_e2 with (x17,x18) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (out!i)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation17_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x19 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x20,x21) => (x20 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x20,x21) => (x21 = (2%F ^ i)%F) end -> match lc1_e2 with (x20,x21) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation18_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x22 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x23,x24) => (x23 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x23,x24) => (x24 = (2%F ^ i)%F) end -> match lc1_e2 with (x23,x24) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((out!i) * e2)%F) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation19_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x25 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x26,x27) => (x26 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x26,x27) => (x27 = (2%F ^ i)%F) end -> match lc1_e2 with (x26,x27) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation20_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x28 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x29,x30) => (x29 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x29,x30) => (x30 = (2%F ^ i)%F) end -> match lc1_e2 with (x29,x30) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation21_trivial: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F * F), True -> Forall (fun x31 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x32,x33) => (x32 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x32,x33) => (x33 = (2%F ^ i)%F) end -> match lc1_e2 with (x32,x33) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> match v with (x34,x35) => (x34 = (lc1 + ((out!i) * e2)%F)%F) end -> match v with (x34,x35) => (x35 = (e2 + e2)%F) end -> match v with (x34,x35) => True end -> (True -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation22: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x36 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x37,x38) => (x37 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x37,x38) => (x38 = (2%F ^ i)%F) end -> match lc1_e2 with (x37,x38) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((out!i) * e2)%F)%F) -> (v = (as_le_f (out[:(i + 1%nat)%nat])))).
Proof. 
  unwrap_C. unfold as_le_f. intuit. subst.
  symmetry.
  erewrite Repr.as_le_split_last' with (i:=i).
  simplify. 
  rewrite firstn_firstn. rewrite Nat.min_l by lia.
  unfold_default. rewrite firstn_nth by lia. fold_default. fqsatz.
  rewrite firstn_length_le; lia.
Qed.

Lemma Num2Bits_obligation23: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x39 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x40,x41) => (x40 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x40,x41) => (x41 = (2%F ^ i)%F) end -> match lc1_e2 with (x40,x41) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof.
  unwrap_C. unfold as_le_f. intuit. subst.
  replace (N.of_nat (Init.Nat.add i (S O))) with (i%N + 1%N)%N by lia.
  rewrite F.pow_add_r, F.pow_1_r. fqsatz.
Qed.

Lemma Num2Bits_obligation24: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x42 => True) out -> ((length out) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (out[:0%nat])))).
Proof. auto. Qed.

Lemma Num2Bits_obligation25: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x43 => True) out -> ((length out) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. unwrap_C. intuit. rewrite F.pow_0_r. fqsatz. Qed.

Lemma Num2Bits_obligation26_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x44 => True) out -> ((length out) = n) -> match lc1_e2 with (x45,x46) => (x45 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x45,x46) => (x46 = (2%F ^ n)%F) end -> match lc1_e2 with (x45,x46) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> ((v = 0%nat) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation27_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x47 => True) out -> ((length out) = n) -> match lc1_e2 with (x48,x49) => (x48 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x48,x49) => (x49 = (2%F ^ n)%F) end -> match lc1_e2 with (x48,x49) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation28_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x50 => True) out -> ((length out) = n) -> match lc1_e2 with (x51,x52) => (x51 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x51,x52) => (x52 = (2%F ^ n)%F) end -> match lc1_e2 with (x51,x52) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation29_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (v : unit), True -> Forall (fun x53 => True) out -> ((length out) = n) -> match lc1_e2 with (x54,x55) => (x54 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x54,x55) => (x55 = (2%F ^ n)%F) end -> match lc1_e2 with (x54,x55) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> True -> ((forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation30_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x56 => True) out -> ((length out) = n) -> match lc1_e2 with (x57,x58) => (x57 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x57,x58) => (x58 = (2%F ^ n)%F) end -> match lc1_e2 with (x57,x58) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation31_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x59 => True) out -> ((length out) = n) -> match lc1_e2 with (x60,x61) => (x60 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x60,x61) => (x61 = (2%F ^ n)%F) end -> match lc1_e2 with (x60,x61) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation32_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x62 => True) out -> ((length out) = n) -> match lc1_e2 with (x63,x64) => (x63 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x63,x64) => (x64 = (2%F ^ n)%F) end -> match lc1_e2 with (x63,x64) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = 1%F) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation33_trivial: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x65 => True) out -> ((length out) = n) -> match lc1_e2 with (x66,x67) => (x66 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x66,x67) => (x67 = (2%F ^ n)%F) end -> match lc1_e2 with (x66,x67) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = ((out!i) - 1%F)%F) -> True).
Proof. auto. Qed.

Lemma Num2Bits_obligation34: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : unit), True -> Forall (fun x68 => True) out -> ((length out) = n) -> match lc1_e2 with (x69,x70) => (x69 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x69,x70) => (x70 = (2%F ^ n)%F) end -> match lc1_e2 with (x69,x70) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((((out!i) * ((out!i) - 1%F)%F)%F = 0%F) -> (forall (j:nat), 0%nat <= j < (i + 1%nat)%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof.
  unwrap_C.
  intuit.
  destruct (dec (j < i)). auto.
  assert (j = i) by lia. subst j.
   destruct (dec (out ! i = 0))%F.
   left. auto.
   right. fqsatz.
Qed.

Lemma Num2Bits_obligation35: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : unit), True -> Forall (fun x71 => True) out -> ((length out) = n) -> match lc1_e2 with (x72,x73) => (x72 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x72,x73) => (x73 = (2%F ^ n)%F) end -> match lc1_e2 with (x72,x73) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (True -> (forall (j:nat), 0%nat <= j < 0%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof. intuit. lia. Qed.

Lemma Num2Bits_obligation36: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (u : unit) (v : (list F)), True -> Forall (fun x74 => True) out -> ((length out) = n) -> match lc1_e2 with (x75,x76) => (x75 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x75,x76) => (x76 = (2%F ^ n)%F) end -> match lc1_e2 with (x75,x76) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (forall (j:nat), 0%nat <= j < n -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> Forall (fun x77 => True) v -> True -> ((((length v) = n) /\ (v = out)) -> ((((as_le_f v) = _in) /\ ((length v) = n)) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof. 
  unfold as_le_f.
  intuit; subst. 
  rewrite firstn_all. reflexivity.
  auto.
Qed.
  


Lemma Bits2Num_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (as_le_f (_in[:i]))) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x6,x7) => (x6 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x6,x7) => (x7 = (2%F ^ i)%F) end -> match lc1_e2 with (x6,x7) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (_in[:i]))) /\ (v = lc1)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation6_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x9,x10) => (x9 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x9,x10) => (x10 = (2%F ^ i)%F) end -> match lc1_e2 with (x9,x10) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (_in!i)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation7_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x12,x13) => (x12 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x12,x13) => (x13 = (2%F ^ i)%F) end -> match lc1_e2 with (x12,x13) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation8_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x15,x16) => (x15 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x15,x16) => (x16 = (2%F ^ i)%F) end -> match lc1_e2 with (x15,x16) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((_in!i) * e2)%F) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation9_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x18,x19) => (x18 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x18,x19) => (x19 = (2%F ^ i)%F) end -> match lc1_e2 with (x18,x19) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation10_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x21,x22) => (x21 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x21,x22) => (x22 = (2%F ^ i)%F) end -> match lc1_e2 with (x21,x22) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation11_trivial: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F * F), Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x24,x25) => (x24 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x24,x25) => (x25 = (2%F ^ i)%F) end -> match lc1_e2 with (x24,x25) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> match v with (x26,x27) => (x26 = (lc1 + ((_in!i) * e2)%F)%F) end -> match v with (x26,x27) => (x27 = (e2 + e2)%F) end -> match v with (x26,x27) => True end -> (True -> True).
Proof. auto. Qed.

Lemma Bits2Num_obligation12: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x29,x30) => (x29 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x29,x30) => (x30 = (2%F ^ i)%F) end -> match lc1_e2 with (x29,x30) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((_in!i) * e2)%F)%F) -> (v = (as_le_f (_in[:(i + 1%nat)%nat])))).
Proof. 
  unwrap_C.
  unfold as_le_f. intuit. subst.
  symmetry. rewrite Repr.as_le_split_last' with (i:=i).
  simplify. unfold_default. rewrite firstn_nth by lia. 
  rewrite firstn_firstn. rewrite Nat.min_l by lia. fqsatz.
  rewrite firstn_length_le by lia. lia.
Qed.


Lemma Bits2Num_obligation13: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x32,x33) => (x32 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x32,x33) => (x33 = (2%F ^ i)%F) end -> match lc1_e2 with (x32,x33) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof.
  unwrap_C. unfold as_le_f. intuit. subst.
  replace (N.of_nat (Init.Nat.add i (S O))) with (i%N + 1%N)%N by lia.
  rewrite F.pow_add_r, F.pow_1_r. fqsatz.
Qed.

Lemma Bits2Num_obligation14: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (_in[:0%nat])))).
Proof. unwrap_C. unfold as_le_f. intuit. Qed.


Lemma Bits2Num_obligation15: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. unwrap_C. unfold as_le_f. intuit.
rewrite F.pow_0_r. auto. Qed.

Lemma Bits2Num_obligation16: forall (n : nat) (_in : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) _in -> ((length _in) = n) -> match lc1_e2 with (x37,x38) => (x37 = (as_le_f (_in[:n]))) end -> match lc1_e2 with (x37,x38) => (x38 = (2%F ^ n)%F) end -> match lc1_e2 with (x37,x38) => True end -> (lc1 = (as_le_f (_in[:n]))) -> (e2 = (2%F ^ n)%F) -> True -> (((v = (as_le_f (_in[:n]))) /\ (v = lc1)) -> (v = (as_le_f _in))).
Proof. unwrap_C. unfold as_le_f. intuit. subst.
  rewrite firstn_all by lia. reflexivity.
Qed.
