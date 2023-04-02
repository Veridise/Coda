(** * DSL benchmark: ModSumThree, BigAdd, BigAddModP *)

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

Definition as_le_f := Repr.as_le 1%nat.

(** ** ModSumThree *)

(* print_endline (generate_lemmas mod_sum_three (typecheck_circuit (add_to_delta d_empty num2bits) mod_sum_three));; *)

Lemma ModSumThree_obligation0_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : Z), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((1%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation1_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : Z), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = 2%nat) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation2: forall (n : Z) (a : F) (b : F) (c : F) (v : Z), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (n + 2%nat)%Z) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSumThree_obligation3_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((F.to_Z v <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation4_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((F.to_Z v <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation5_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation6_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation7_trivial: forall (n : Z) (a : F) (b : F) (c : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation8_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> True -> ((v = (n2b!n)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation9_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation10_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> True -> ((v = (n2b!(n + 1%nat)%Z)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation11_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> True -> ((v = (2%F * (n2b!(n + 1%nat)%Z))%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation12_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> (((F.to_Z v <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation13_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> (((F.to_Z v <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation14_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation15_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation16_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation17_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> (((v = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) /\ (v = carry)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation18_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation19: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : Z), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((((1%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> (0%nat <= v)).
Proof. Admitted.

Lemma ModSumThree_obligation20_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation21_trivial: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = (carry * (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation22: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F * F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> match v with (x15,x16) => (x15 = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) end -> match v with (x15,x16) => ((x16 = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) /\ (x16 = carry)) end -> match v with (x15,x16) => True end -> (True -> ((fst (v) + (snd (v) * (2%F ^ n)%F)%F)%F = ((a + b)%F + c)%F)).
Proof. Admitted.

Lemma ModSumThree_obligation23: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> ((v = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> (F.to_Z v <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma ModSumThree_obligation24: forall (n : Z) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((1%nat <= n) /\ (n <= (C.k - 1%nat)%Z)) -> (F.to_Z a <= ((2%nat ^ n)%Z - 1%nat)%Z) -> (F.to_Z b <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 2%nat)%Z)) -> (carry = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) -> True -> (((v = ((n2b!n) + (2%F * (n2b!(n + 1%nat)%Z))%F)%F) /\ (v = carry)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. Admitted.

(** ** BigAdd *)

(* print_endline (generate_lemmas big_add (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three]) big_add));; *)

(* TODO *)

(** ** BigAddModP *)

(* print_endline (generate_lemmas big_add_mod_p (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three; big_add; c_is_equal; c_less_than; cand; cor; c_big_lt; c_mod_sub_three; big_sub]) big_add_mod_p));; *)

(* TODO *)
