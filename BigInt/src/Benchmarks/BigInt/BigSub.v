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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr ReprZ Coda.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Definition as_le := RZ.as_le.
Local Notation "[| xs | n ]" := (RZ.as_le n xs).
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

Lemma ModSubThree_obligation0_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((v = n) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation1_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation2: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (n + 1%nat)%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed.

Lemma ModSubThree_obligation3: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((v = a) /\ True) -> ((^ v) < (2%nat ^ (n + 1%nat)%nat)%Z)).
Proof. 
  intros. apply Repr.in_range_binary in H2. intuit. subst.
  replace (Z.of_N (N.of_nat (Init.Nat.add n (S O)))) with (n+1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.

Lemma ModSubThree_obligation4_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((v = b) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation5_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> (((v = c) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation6: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (b + c)%F) -> ((^ v) < (2%nat ^ (n + 1%nat)%nat)%Z)).
Proof.
  unwrap_C. intros. subst. 
  assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
    replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  replace (Z.of_N (N.of_nat (Init.Nat.add n (S O)))) with (n+1)%Z by lia. rewrite Zpower_exp by lia. simplify.
  pose proof (F_to_Z_nonneg b). pose proof (F_to_Z_nonneg c).
  apply Repr.in_range_binary in H2.
  autorewrite with F_to_Z; try lia.
Qed.

Lemma ModSubThree_obligation7_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = borrow) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation8_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation9: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = n) /\ True) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSubThree_obligation10_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation11_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (borrow * (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation12_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = a) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation13_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = ((borrow * (2%F ^ n)%F)%F + a)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation14_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = b) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation15_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = c) /\ True) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation16_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (b + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation17_trivial: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> ((v = (((borrow * (2%F ^ n)%F)%F + a)%F - (b + c)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSubThree_obligation18: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> True -> (((v = borrow) /\ True) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((v = 0%F) -> ~((^ a) < (^ (b + c)%F)))))).
Proof. intuit; subst; intuit. Qed.

Lemma ModSubThree_obligation19: forall (n : nat) (a : F) (b : F) (c : F) (borrow : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> (((borrow = 0%F) \/ (borrow = 1%F)) /\ (((borrow = 1%F) -> ((^ a) < (^ (b + c)%F))) /\ ((borrow = 0%F) -> ~((^ a) < (^ (b + c)%F))))) -> (True -> ((((borrow * (2%F ^ n)%F)%F + a)%F - (b + c)%F)%F = (((borrow * (2%F ^ n)%F)%F + a)%F - (b + c)%F)%F)).
Proof. intros. intuit. Qed.


(* BigSub *)


Lemma BigSub_obligation0_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x3 => ((^ x3) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x4 => ((^ x4) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation1_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x5 => ((^ x5) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x6 => ((^ x6) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (((v = k) /\ True) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation2_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x7 => ((^ x7) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x8 => ((^ x8) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (((0%nat <= v) /\ (v < k)) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation3_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : ((list F) * F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x9 => ((^ x9) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x10 => ((^ x10) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match v with (x12,x13) => Forall (fun x11 => ((^ x11) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x12 end -> match v with (x12,x13) => ((length x12) = i) end -> match v with (x12,x13) => (((x13 = 0%F) \/ (x13 = 1%F)) /\ (((x13 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x13 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match v with (x12,x13) => True end -> (((as_le n (fst v)) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ (snd v)))%Z)%Z) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation4_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : (list F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x14 => ((^ x14) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x15 => ((^ x15) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> Forall (fun x16 => ((^ x16) <= ((2%nat ^ n)%Z - 1%nat)%Z)) v -> True -> (((length v) = i) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation5_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x17 => ((^ x17) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x18 => ((^ x18) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation6_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x19 => ((^ x19) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x20 => ((^ x20) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((v = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation7: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (v : Z), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x21 => ((^ x21) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x22 => ((^ x22) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x24,x25) => Forall (fun x23 => ((^ x23) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x24 end -> match s'_br' with (x24,x25) => ((length x24) = i) end -> match s'_br' with (x24,x25) => (((x25 = 0%F) \/ (x25 = 1%F)) /\ (((x25 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x25 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x24,x25) => ((as_le n x24) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x25))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x26 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x28,x29) => Forall (fun x27 => True) x28 end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = n) /\ True) -> ((0%nat <= v) /\ ((v <= (C.k - 2%nat)%Z) /\ ((1%nat <= v) /\ True)))).
Proof. lia. Qed.

Lemma BigSub_obligation8: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x30 => ((^ x30) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x31 => ((^ x31) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x33,x34) => Forall (fun x32 => ((^ x32) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x33 end -> match s'_br' with (x33,x34) => ((length x33) = i) end -> match s'_br' with (x33,x34) => (((x34 = 0%F) \/ (x34 = 1%F)) /\ (((x34 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x34 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x33,x34) => ((as_le n x33) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x34))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x35 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x37,x38) => Forall (fun x36 => True) x37 end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = ai) /\ True) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
  intros.
  destruct H20. subst. unfold_default. apply Forall_nth; auto; lia.
Qed.

Lemma BigSub_obligation9: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x39 => ((^ x39) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x40 => ((^ x40) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x42,x43) => Forall (fun x41 => ((^ x41) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x42 end -> match s'_br' with (x42,x43) => ((length x42) = i) end -> match s'_br' with (x42,x43) => (((x43 = 0%F) \/ (x43 = 1%F)) /\ (((x43 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x43 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x42,x43) => ((as_le n x42) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x43))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x44 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x46,x47) => Forall (fun x45 => True) x46 end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = bi) /\ True) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
  intros.
  destruct H20. subst. unfold_default. apply Forall_nth; auto; lia.
Qed.

Lemma BigSub_obligation10: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x48 => ((^ x48) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x49 => ((^ x49) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x51,x52) => Forall (fun x50 => ((^ x50) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x51 end -> match s'_br' with (x51,x52) => ((length x51) = i) end -> match s'_br' with (x51,x52) => (((x52 = 0%F) \/ (x52 = 1%F)) /\ (((x52 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x52 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x51,x52) => ((as_le n x51) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x52))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x53 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x55,x56) => Forall (fun x54 => True) x55 end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = br') /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; intuit. Qed.

Lemma BigSub_obligation11: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (s_br : (F * F)) (br : F) (s : F) (_u1 : (F * F)) (v : (list F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x57 => ((^ x57) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x58 => ((^ x58) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x60,x61) => Forall (fun x59 => ((^ x59) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x60 end -> match s'_br' with (x60,x61) => ((length x60) = i) end -> match s'_br' with (x60,x61) => (((x61 = 0%F) \/ (x61 = 1%F)) /\ (((x61 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x61 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x60,x61) => ((as_le n x60) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x61))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x62 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x64,x65) => Forall (fun x63 => True) x64 end -> match _u0 with (x64,x65) => True end -> match _u0 with (x64,x65) => True end -> match _u0 with (x64,x65) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> match s_br with (x66,x67) => True end -> match s_br with (x66,x67) => (((x67 = 0%F) \/ (x67 = 1%F)) /\ (((x67 = 1%F) -> ((^ ai) < (^ (bi + br')%F))) /\ ((x67 = 0%F) -> ~((^ ai) < (^ (bi + br')%F))))) end -> match s_br with (x66,x67) => (x66 = (((x67 * (2%F ^ n)%F)%F + ai)%F - (bi + br')%F)%F) end -> (br = (snd s_br)) -> (s = (fst s_br)) -> match _u1 with (x68,x69) => True end -> match _u1 with (x68,x69) => True end -> match _u1 with (x68,x69) => ((s_br = s_br) /\ True) end -> Forall (fun x70 => True) v -> True -> (((v = (s' ++ (s :: nil))) /\ ((length v) = ((length s') + (length (s :: nil)))%nat)) -> (((length v) = (i + 1%nat)%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof.
  unwrap_C.
  intros. destruct s_br as [_s _br]. destruct s'_br' as [_s' _br']. destruct _u0. destruct _u1. cbn -[F.to_Z] in *. subst _s' _br' _br _s.
  destruct H29. subst v. rewrite app_length. simpl.
  split. lia.
  intros j ?. destruct (dec (j < length s')); unfold_default.
  - rewrite app_nth1 by lia. apply Forall_nth; auto; lia.
  - assert (j=length s') by lia. subst j. rewrite app_nth2 by lia. simplify. simpl.
    subst s.

  destruct H20. apply Repr.in_range_binary in H20.
  destruct H8. apply Repr.in_range_binary in H8.
  assert (H_pow_nk: (4 * 2^n <= 2^k)%Z). {
    replace (4 * 2^n)%Z with (2 ^ (n + 2))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  assert (Hbi: ^bi <= 2^n - 1). { subst. unfold_default. apply Forall_nth. auto. lia. }
  assert (Hai: ^ai <= 2^n - 1). { subst. unfold_default. apply Forall_nth. auto. lia. }
  pose proof H20. apply Repr.in_range_binary in H23. destruct H23; intuit; subst br; simplify; autorewrite with F_to_Z in H30; try (pose_nonneg; lia);
  (* apply f_equal with (f:=F.to_Z). *)
  autorewrite with F_to_Z; try lia;
  repeat autorewrite with F_to_Z; simpl; try (pose_nonneg; (lia || nia)).
Qed.

Lemma BigSub_obligation12_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : (list F) * F) (br' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (s_br : F * F) (br : F) (s : F) (_u1 : F * F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x71 => ((^ x71) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x72 => ((^ x72) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x74,x75) => Forall (fun x73 => ((^ x73) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x74 end -> match s'_br' with (x74,x75) => ((length x74) = i) end -> match s'_br' with (x74,x75) => (((x75 = 0%F) \/ (x75 = 1%F)) /\ (((x75 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x75 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x74,x75) => ((as_le n x74) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x75))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x76 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x78,x79) => Forall (fun x77 => True) x78 end -> match _u0 with (x78,x79) => True end -> match _u0 with (x78,x79) => True end -> match _u0 with (x78,x79) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> match s_br with (x80,x81) => True end -> match s_br with (x80,x81) => (((x81 = 0%F) \/ (x81 = 1%F)) /\ (((x81 = 1%F) -> ((^ ai) < (^ (bi + br')%F))) /\ ((x81 = 0%F) -> ~((^ ai) < (^ (bi + br')%F))))) end -> match s_br with (x80,x81) => (x80 = ((((x81 * 2%F)%F ^ n)%F + ai)%F - (bi + br')%F)%F) end -> (br = (snd s_br)) -> (s = (fst s_br)) -> match _u1 with (x82,x83) => True end -> match _u1 with (x82,x83) => True end -> match _u1 with (x82,x83) => ((s_br = s_br) /\ True) end -> True -> (True -> True).
Proof. intuit. Qed.

#[local]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn : core.
#[local]Hint Extern 10 (Forall _ (nth_Default _ _)) => unfold_default; apply Forall_nth: core.
#[local]Hint Extern 10 => match goal with 
  [ |- context[length _] ] => rewrite_length end : core.
#[local]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn : core.
#[local]Hint Extern 10 (Forall _ (rev _)) => apply Forall_rev : core.
#[local]Hint Extern 10 (Forall _ (_ :: _)) => constructor : core.
#[local]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z : core.
#[local]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end : core.
#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ < _)%nat => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ <= _)%nat => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ > _)%nat => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core. 
#[local]Hint Extern 10 (_ >= _)%nat => lia : core. 
#[local]Hint Extern 10 (S _ = S _) => f_equal : core. 

Ltac ind' x :=
    let Hbin := fresh "Hin" in
    let Hbin' := fresh "Hin" in
  assert (Hbin: binary x) by (unfold binary; intuit);
  destruct Hbin; ind x.

Lemma BigSub_obligation13: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : (list F) * F) (br' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (s_br : F * F) (br : F) (s : F) (_u1 : F * F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x84 => ((^ x84) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x85 => ((^ x85) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x87,x88) => Forall (fun x86 => ((^ x86) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x87 end -> match s'_br' with (x87,x88) => ((length x87) = i) end -> match s'_br' with (x87,x88) => (((x88 = 0%F) \/ (x88 = 1%F)) /\ (((x88 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x88 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x87,x88) => ((as_le n x87) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ n)%Z * (^ x88))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x89 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x91,x92) => Forall (fun x90 => True) x91 end -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> match s_br with (x93,x94) => True end -> match s_br with (x93,x94) => (((x94 = 0%F) \/ (x94 = 1%F)) /\ (((x94 = 1%F) -> ((^ ai) < (^ (bi + br')%F))) /\ ((x94 = 0%F) -> ~((^ ai) < (^ (bi + br')%F))))) end -> match s_br with (x93,x94) => (x93 = ((((x94 * 2%F)%F ^ n)%F + ai)%F - (bi + br')%F)%F) end -> (br = (snd s_br)) -> (s = (fst s_br)) -> match _u1 with (x95,x96) => True end -> match _u1 with (x95,x96) => True end -> match _u1 with (x95,x96) => ((s_br = s_br) /\ True) end -> True -> (((v = br) /\ True) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_le n (a[:(i + 1%nat)%nat])) < (as_le n (b[:(i + 1%nat)%nat])))) /\ ((v = 0%F) -> ~((as_le n (a[:(i + 1%nat)%nat])) < (as_le n (b[:(i + 1%nat)%nat]))))))).
Proof.
  unfold as_le.
  unwrap_C.
  intros. 
  assert (H_pow_nk: (4 * 2^n <= 2^k)%Z). {
    replace (4 * 2^n)%Z with (2 ^ (n + 2))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  assert (Hbi: ^bi <= 2^n - 1). { subst.  unfold_default. apply Forall_nth. auto. auto. }
  assert (Hai: ^ai <= 2^n - 1). { subst. unfold_default. apply Forall_nth. auto. lia. }
  destruct s_br as [_s _br]. destruct s'_br' as [_s' _br']. destruct _u0. destruct _u1. cbn -[F.to_Z Z.pow Z.mul] in *. subst _s' _br' _br _s.
  destruct H28. subst v.
  split. intuit.
  do 2 rewrite firstn_plus1 by lia.
  rewrite RZU.big_lt_dec_le'; try lia; auto; try (solve [unfold_default; apply Forall_nth; auto]).
  subst ai bi;
  split; intro;
  ind br; ind' br';
  autorewrite with F_to_Z in H10; try (pose_nonneg; lia); autorewrite with F_to_Z; try (pose_nonneg; lia).
Qed.

Lemma BigSub_obligation14: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s'_br' : ((list F) * F)) (br' : F) (s' : (list F)) (_u0 : ((list F) * F)) (ai : F) (bi : F) (s_br : (F * F)) (br : F) (s : F) (_u1 : (F * F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x97 => ((^ x97) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x98 => ((^ x98) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s'_br' with (x100,x101) => Forall (fun x99 => ((^ x99) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x100 end -> match s'_br' with (x100,x101) => ((length x100) = i) end -> match s'_br' with (x100,x101) => (((x101 = 0%F) \/ (x101 = 1%F)) /\ (((x101 = 1%F) -> ((as_le n (a[:i])) < (as_le n (b[:i])))) /\ ((x101 = 0%F) -> ~((as_le n (a[:i])) < (as_le n (b[:i])))))) end -> match s'_br' with (x100,x101) => ((as_le n x100) = (((as_le n (a[:i])) - (as_le n (b[:i])))%Z + ((2%nat ^ (n * i)%Z)%Z * (^ x101))%Z)%Z) end -> (br' = (snd s'_br')) -> Forall (fun x102 => True) s' -> (s' = (fst s'_br')) -> match _u0 with (x104,x105) => Forall (fun x103 => True) x104 end -> match _u0 with (x104,x105) => True end -> match _u0 with (x104,x105) => True end -> match _u0 with (x104,x105) => ((s'_br' = s'_br') /\ True) end -> (ai = (a!i)) -> (bi = (b!i)) -> match s_br with (x106,x107) => True end -> match s_br with (x106,x107) => (((x107 = 0%F) \/ (x107 = 1%F)) /\ (((x107 = 1%F) -> ((^ ai) < (^ (bi + br')%F))) /\ ((x107 = 0%F) -> ~((^ ai) < (^ (bi + br')%F))))) end -> match s_br with (x106,x107) => (x106 = (((x107 * (2%F ^ n)%F)%F + ai)%F - (bi + br')%F)%F) end -> (br = (snd s_br)) -> (s = (fst s_br)) -> match _u1 with (x108,x109) => True end -> match _u1 with (x108,x109) => True end -> match _u1 with (x108,x109) => ((s_br = s_br) /\ True) end -> (True -> ((as_le n (s' ++ (s :: nil))) = (((as_le n (a[:(i + 1%nat)%nat])) - (as_le n (b[:(i + 1%nat)%nat])))%Z + ((2%nat ^ (n * (i + 1%nat)%nat)%Z)%Z * (^ br))%Z)%Z)).

Proof.
  unwrap_C. unfold as_le. intros. 
  assert (H_pow_nk: (4 * 2^n <= 2^k)%Z). {
    replace (4 * 2^n)%Z with (2 ^ (n + 2))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  assert (Hbi: ^bi <= 2^n - 1). { subst.  unfold_default. apply Forall_nth. auto. auto. }
  assert (Hai: ^ai <= 2^n - 1). { subst. unfold_default. apply Forall_nth. auto. lia. }
  destruct s_br as [_s _br]. destruct s'_br' as [_s' _br']. destruct _u0. destruct _u1. cbn -[F.to_Z Z.pow Z.mul] in *. subst _s' _br' _br _s ai bi.
  destruct H8. apply Repr.in_range_binary in H8.
  destruct H20. apply Repr.in_range_binary in H12.
  repeat rewrite firstn_plus1 by lia. repeat rewrite RZ.as_le_app. rewrite_length.
  apply f_equal with (f:=F.to_Z) in H23;
    autorewrite with F_to_Z in H23; try lia;
    repeat autorewrite with F_to_Z; simpl; try (pose_nonneg; (lia || nia)).
  unfold RZ.ToZ.to_Z.
  simplify.
  simpl in H23.
  replace (Z.mul (Z.of_N (N.of_nat n))
  (Z.of_N (N.add (N.of_nat i) (Npos xH)))) with (n+n*i)%Z by lia.
  rewrite Zpower_exp by lia. nia.
  pose proof H12.
  apply Repr.in_range_binary in H18.
  destruct H18;
  intuit;
  autorewrite with F_to_Z in H21; try lia;
    repeat (autorewrite with F_to_Z; simpl; try (pose_nonneg; (lia || nia))).
  subst br. autorewrite with F_to_Z; try lia. simplify.
  pose_nonneg. lia.
Qed.
  
  
  

Lemma BigSub_obligation15: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : (list F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x110 => ((^ x110) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x111 => ((^ x111) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> Forall (fun x112 => True) v -> True -> ((v = nil) -> (((length v) = 0%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof.
  intros. subst. simpl. split. auto.
  intros. lia.
Qed.


Lemma BigSub_obligation16_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x113 => ((^ x113) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x114 => ((^ x114) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma BigSub_obligation17: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x115 => ((^ x115) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x116 => ((^ x116) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_le n (a[:0%nat])) < (as_le n (b[:0%nat])))) /\ ((v = 0%F) -> ~((as_le n (a[:0%nat])) < (as_le n (b[:0%nat]))))))).
Proof.
  unwrap_C. simpl. intros. subst v. intuit. fqsatz. lia.
Qed.

Lemma BigSub_obligation18: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x117 => ((^ x117) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x118 => ((^ x118) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (True -> ((as_le n nil) = (((as_le n (a[:0%nat])) - (as_le n (b[:0%nat])))%Z + ((2%nat ^ n)%Z * (^ 0%F))%Z)%Z)).
Proof.
  unwrap_C. simpl. intros. autorewrite with F_to_Z; try lia.
Qed.

Lemma BigSub_obligation19: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (s_br : (list F) * F) (br : F) (s : (list F)) (_u2 : (list F) * F) (v : (list F)), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x119 => ((^ x119) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x120 => ((^ x120) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match s_br with (x122,x123) => Forall (fun x121 => ((^ x121) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x122 end -> match s_br with (x122,x123) => ((length x122) = k) end -> match s_br with (x122,x123) => (((x123 = 0%F) \/ (x123 = 1%F)) /\ (((x123 = 1%F) -> ((as_le n (a[:k])) < (as_le n (b[:k])))) /\ ((x123 = 0%F) -> ~((as_le n (a[:k])) < (as_le n (b[:k])))))) end -> match s_br with (x122,x123) => ((as_le n x122) = (((as_le n (a[:k])) - (as_le n (b[:k])))%Z + ((2%nat ^ n)%Z * (^ x123))%Z)%Z) end -> (br = (snd s_br)) -> Forall (fun x124 => True) s -> (s = (fst s_br)) -> match _u2 with (x126,x127) => Forall (fun x125 => True) x126 end -> match _u2 with (x126,x127) => True end -> match _u2 with (x126,x127) => True end -> match _u2 with (x126,x127) => ((s_br = s_br) /\ True) end -> Forall (fun x128 => True) v -> True -> (((v = s) /\ True) -> (((length v) = k) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof.
  intros. 
  destruct s_br as [_s _br]. cbn -[F.to_Z Z.pow Z.mul] in *. intuit; subst; try lia;
  (* FIXME *)
  unfold_default; apply Forall_nth; auto.
Qed.

Lemma BigSub_obligation20: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (s_br : (list F) * F) (br : F) (s : (list F)) (_u2 : (list F) * F) (v : F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x129 => ((^ x129) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x130 => ((^ x130) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match s_br with (x132,x133) => Forall (fun x131 => ((^ x131) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x132 end -> match s_br with (x132,x133) => ((length x132) = k) end -> match s_br with (x132,x133) => (((x133 = 0%F) \/ (x133 = 1%F)) /\ (((x133 = 1%F) -> ((as_le n (a[:k])) < (as_le n (b[:k])))) /\ ((x133 = 0%F) -> ~((as_le n (a[:k])) < (as_le n (b[:k])))))) end -> match s_br with (x132,x133) => ((as_le n x132) = (((as_le n (a[:k])) - (as_le n (b[:k])))%Z + ((2%nat ^ n)%Z * (^ x133))%Z)%Z) end -> (br = (snd s_br)) -> Forall (fun x134 => True) s -> (s = (fst s_br)) -> match _u2 with (x136,x137) => Forall (fun x135 => True) x136 end -> match _u2 with (x136,x137) => True end -> match _u2 with (x136,x137) => True end -> match _u2 with (x136,x137) => ((s_br = s_br) /\ True) end -> True -> (((v = br) /\ True) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_le n a) < (as_le n b))) /\ ((v = 0%F) -> ~((as_le n a) < (as_le n b)))))).
Proof. 
  intros. 
  destruct s_br as [_s _br]. cbn -[F.to_Z Z.pow Z.mul] in *.
  split. intuit; subst; intuit.
  split; intro; subst _br;
  destruct H17; subst v br;
  do 2 rewrite firstn_all2 in H7; try lia; intuit; try lia.
Qed.
  

Lemma BigSub_obligation21: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (s_br : (list F) * F) (br : F) (s : (list F)) (_u2 : (list F) * F), ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x138 => ((^ x138) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x139 => ((^ x139) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match s_br with (x141,x142) => Forall (fun x140 => ((^ x140) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x141 end -> match s_br with (x141,x142) => ((length x141) = k) end -> match s_br with (x141,x142) => (((x142 = 0%F) \/ (x142 = 1%F)) /\ (((x142 = 1%F) -> ((as_le n (a[:k])) < (as_le n (b[:k])))) /\ ((x142 = 0%F) -> ~((as_le n (a[:k])) < (as_le n (b[:k])))))) end -> match s_br with (x141,x142) => ((as_le n x141) = (((as_le n (a[:k])) - (as_le n (b[:k])))%Z + ((2%nat ^ n)%Z * (^ x142))%Z)%Z) end -> (br = (snd s_br)) -> Forall (fun x143 => True) s -> (s = (fst s_br)) -> match _u2 with (x145,x146) => Forall (fun x144 => True) x145 end -> match _u2 with (x145,x146) => True end -> match _u2 with (x145,x146) => True end -> match _u2 with (x145,x146) => ((s_br = s_br) /\ True) end -> (True -> ((as_le n s) = (((as_le n a) - (as_le n b))%Z + ((2%nat ^ n)%Z * (^ br))%Z)%Z)).
Proof. 
  intros.
  destruct s_br as [_s _br]. cbn -[F.to_Z Z.pow Z.mul] in *.
  do 2 rewrite firstn_all2 in H8 by lia.
  subst _br _s. auto.
Qed.
  