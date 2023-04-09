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

(** ** ModSumThree *)

(* print_endline (generate_lemmas mod_sum_three (typecheck_circuit (add_to_delta d_empty num2bits) mod_sum_three));; *)
Lemma ModSumThree_obligation0_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation1_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation2: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (n + 1%nat)%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSumThree_obligation3_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation4_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation5_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation6_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation7_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation8_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation9_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation10_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation11_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation12_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation13_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> (((v = (n2b!n)) /\ (v = carry)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation14_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation15: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSumThree_obligation16_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation17_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (carry * (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation18: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (sum : F) (v : F * F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> (sum = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> match v with (x11,x12) => ((x11 = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) /\ (x11 = sum)) end -> match v with (x11,x12) => ((x12 = (n2b!n)) /\ (x12 = carry)) end -> match v with (x11,x12) => True end -> (True -> ((fst (v) + ((2%F ^ n)%F * snd (v))%F)%F = ((a + b)%F + c)%F)).
Proof. unwrap_C. intros. destruct v. intuit; subst; simpl. fqsatz. fqsatz. Qed.

Lemma ModSumThree_obligation19: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (sum : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> (sum = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> True -> (((v = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) /\ (v = sum)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. 
  unwrap_C. unfold as_le_f. intros. 
  assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
    replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  assert (H_x_nonneg: (0 <= F.to_Z a)%Z). apply F.to_Z_range. lia.
  assert (H_y_nonneg: (0 <= F.to_Z b)%Z). apply F.to_Z_range. lia.  
  assert (H_n2b_nonneg: (0 <= ^(n2b!n) <= 1)%Z). {
    split. apply F.to_Z_range. lia.
    apply Repr.in_range_binary. unfold_default. apply Forall_nth; try lia. auto.
  }
  assert ([|n2b|] | (n+1)). {
    rewrite nat_N_Z.
    applys_eq Repr.as_le_ub'. repeat f_equal. lia.
    auto. lia.
  }
  assert (2^(n+1) = 2*2^n) by (rewrite Zpower_exp; lia).
  assert (Hbin: binary (n2b!n)). unfold_default. apply Forall_nth. apply H3. lia.
  assert (Hmsb0: n2b!n = 0%F -> ^[|n2b|] <= 2^n-1). {
    intro. 
    applys_eq Repr.as_le_msb0; auto; try lia; repeat f_equal; try lia.
    rewrite <- H11. f_equal. lia.
  }
  assert (Hmsb1: n2b!n = 1%F -> [|n2b|] >=z 2^n).
  {
    intro.
    applys_eq Repr.as_le_msb1; auto; try lia; repeat f_equal; try lia.
    rewrite <- H11. f_equal. lia.
  }
  intuit; subst; simplify;
  apply f_equal with (f:=F.to_Z) in H11;
  destruct Hbin; rewrite H2; intuit;
  autorewrite with F_to_Z in H11;
  repeat (try lia; autorewrite with F_to_Z;
    simplify;
    try replace (1+1)%Z with 2%Z;
    try (simpl; (lia || nia))).
Qed.


Lemma ModSumThree_obligation20: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (sum : F) (v : F), (n <= (C.k - 1)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> (sum = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> True -> (((v = (n2b!n)) /\ (v = carry)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intros. intuit; subst; unfold_default; apply Forall_nth; auto; try lia. Qed.




(** ** BigAdd *)

Lemma BigAdd_obligation0_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x3 => ((^ x3) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x4 => ((^ x4) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation1_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x5 => ((^ x5) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x6 => ((^ x6) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = k) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation2_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x7 => ((^ x7) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x8 => ((^ x8) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (((0%nat <= v) /\ (v < k)) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation3_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : (list F) * F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x9 => ((^ x9) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x10 => ((^ x10) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match v with (x12,x13) => Forall (fun x11 => ((^ x11) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x12 end -> match v with (x12,x13) => ((length x12) = i) end -> match v with (x12,x13) => ((x13 = 0%F) \/ (x13 = 1%F)) end -> match v with (x12,x13) => True end -> (((as_le n (fst (v) ++ (snd (v) :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation4_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : (list F)), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x14 => ((^ x14) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x15 => ((^ x15) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> Forall (fun x16 => ((^ x16) <= ((2%nat ^ n)%Z - 1%nat)%Z)) v -> True -> (((length v) = i) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation5_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x17 => ((^ x17) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x18 => ((^ x18) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation6_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x19 => ((^ x19) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x20 => ((^ x20) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation7: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (v : Z), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x21 => ((^ x21) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x22 => ((^ x22) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x24,x25) => Forall (fun x23 => ((^ x23) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x24 end -> match ss_cc with (x24,x25) => ((length x24) = i) end -> match ss_cc with (x24,x25) => ((x25 = 0%F) \/ (x25 = 1%F)) end -> match ss_cc with (x24,x25) => ((as_le n (x24 ++ (x25 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x26 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x28,x29) => Forall (fun x27 => True) x28 end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => True end -> match _u0 with (x28,x29) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((v = n) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed.

Lemma BigAdd_obligation8: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x30 => ((^ x30) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x31 => ((^ x31) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x33,x34) => Forall (fun x32 => ((^ x32) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x33 end -> match ss_cc with (x33,x34) => ((length x33) = i) end -> match ss_cc with (x33,x34) => ((x34 = 0%F) \/ (x34 = 1%F)) end -> match ss_cc with (x33,x34) => ((as_le n (x33 ++ (x34 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x35 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x37,x38) => Forall (fun x36 => True) x37 end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => True end -> match _u0 with (x37,x38) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((v = ai) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
  intuit; subst; unfold_default; apply Forall_nth; auto; lia.
Qed.

Lemma BigAdd_obligation9: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x39 => ((^ x39) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x40 => ((^ x40) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x42,x43) => Forall (fun x41 => ((^ x41) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x42 end -> match ss_cc with (x42,x43) => ((length x42) = i) end -> match ss_cc with (x42,x43) => ((x43 = 0%F) \/ (x43 = 1%F)) end -> match ss_cc with (x42,x43) => ((as_le n (x42 ++ (x43 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x44 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x46,x47) => Forall (fun x45 => True) x46 end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => True end -> match _u0 with (x46,x47) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((v = bi) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. 
  intuit; subst; unfold_default; apply Forall_nth; auto; lia.
Qed.


Lemma BigAdd_obligation10: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x48 => ((^ x48) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x49 => ((^ x49) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x51,x52) => Forall (fun x50 => ((^ x50) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x51 end -> match ss_cc with (x51,x52) => ((length x51) = i) end -> match ss_cc with (x51,x52) => ((x52 = 0%F) \/ (x52 = 1%F)) end -> match ss_cc with (x51,x52) => ((as_le n (x51 ++ (x52 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x53 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x55,x56) => Forall (fun x54 => True) x55 end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => True end -> match _u0 with (x55,x56) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((v = c') -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; cbn in *; subst; intuit. Qed.

Lemma BigAdd_obligation11: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (mst : F * F) (carry : F) (sum : F) (_u1 : F * F) (v : (list F)), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x57 => ((^ x57) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x58 => ((^ x58) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x60,x61) => Forall (fun x59 => ((^ x59) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x60 end -> match ss_cc with (x60,x61) => ((length x60) = i) end -> match ss_cc with (x60,x61) => ((x61 = 0%F) \/ (x61 = 1%F)) end -> match ss_cc with (x60,x61) => ((as_le n (x60 ++ (x61 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x62 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x64,x65) => Forall (fun x63 => True) x64 end -> match _u0 with (x64,x65) => True end -> match _u0 with (x64,x65) => True end -> match _u0 with (x64,x65) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> match mst with (x66,x67) => ((^ x66) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match mst with (x66,x67) => ((x67 = 0%F) \/ (x67 = 1%F)) end -> match mst with (x66,x67) => ((x66 + ((2%F ^ n)%F * x67)%F)%F = ((ai + bi)%F + c')%F) end -> (carry = snd (mst)) -> (sum = fst (mst)) -> match _u1 with (x68,x69) => True end -> match _u1 with (x68,x69) => True end -> match _u1 with (x68,x69) => (mst = mst) end -> Forall (fun x70 => True) v -> True -> (((v = (s' ++ (sum :: nil))) /\ ((length v) = ((length s') + (length (sum :: nil)))%nat)) -> (((length v) = (i + 1%nat)%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof.
  intros. destruct ss_cc as [ss cc]. destruct mst  as [s c]. simpl in *. apply Repr.in_range_binary in H8. intuit; subst;
  try apply app_length;
  unfold_default; apply Forall_nth; try lia; auto;
  apply Forall_app; simpl; intuit;
  constructor; auto.
Qed.

Lemma BigAdd_obligation12_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (mst : F * F) (carry : F) (sum : F) (_u1 : F * F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x71 => ((^ x71) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x72 => ((^ x72) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x74,x75) => Forall (fun x73 => ((^ x73) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x74 end -> match ss_cc with (x74,x75) => ((length x74) = i) end -> match ss_cc with (x74,x75) => ((x75 = 0%F) \/ (x75 = 1%F)) end -> match ss_cc with (x74,x75) => ((as_le n (x74 ++ (x75 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x76 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x78,x79) => Forall (fun x77 => True) x78 end -> match _u0 with (x78,x79) => True end -> match _u0 with (x78,x79) => True end -> match _u0 with (x78,x79) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> match mst with (x80,x81) => ((^ x80) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match mst with (x80,x81) => ((x81 = 0%F) \/ (x81 = 1%F)) end -> match mst with (x80,x81) => ((x80 + ((2%F ^ n)%F * x81)%F)%F = ((ai + bi)%F + c')%F) end -> (carry = snd (mst)) -> (sum = fst (mst)) -> match _u1 with (x82,x83) => True end -> match _u1 with (x82,x83) => True end -> match _u1 with (x82,x83) => (mst = mst) end -> True -> (True -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation13: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (mst : F * F) (carry : F) (sum : F) (_u1 : F * F) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x84 => ((^ x84) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x85 => ((^ x85) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x87,x88) => Forall (fun x86 => ((^ x86) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x87 end -> match ss_cc with (x87,x88) => ((length x87) = i) end -> match ss_cc with (x87,x88) => ((x88 = 0%F) \/ (x88 = 1%F)) end -> match ss_cc with (x87,x88) => ((as_le n (x87 ++ (x88 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x89 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x91,x92) => Forall (fun x90 => True) x91 end -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> match mst with (x93,x94) => ((^ x93) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match mst with (x93,x94) => ((x94 = 0%F) \/ (x94 = 1%F)) end -> match mst with (x93,x94) => ((x93 + ((2%F ^ n)%F * x94)%F)%F = ((ai + bi)%F + c')%F) end -> (carry = snd (mst)) -> (sum = fst (mst)) -> match _u1 with (x95,x96) => True end -> match _u1 with (x95,x96) => True end -> match _u1 with (x95,x96) => (mst = mst) end -> True -> ((v = carry) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; simpl; intuit. Qed.



Lemma BigAdd_obligation14: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (ss_cc : (list F) * F) (c' : F) (s' : (list F)) (_u0 : (list F) * F) (ai : F) (bi : F) (mst : F * F) (carry : F) (sum : F) (_u1 : F * F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x97 => ((^ x97) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x98 => ((^ x98) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match ss_cc with (x100,x101) => Forall (fun x99 => ((^ x99) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x100 end -> match ss_cc with (x100,x101) => ((length x100) = i) end -> match ss_cc with (x100,x101) => ((x101 = 0%F) \/ (x101 = 1%F)) end -> match ss_cc with (x100,x101) => ((as_le n (x100 ++ (x101 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> (c' = snd (ss_cc)) -> Forall (fun x102 => True) s' -> (s' = fst (ss_cc)) -> match _u0 with (x104,x105) => Forall (fun x103 => True) x104 end -> match _u0 with (x104,x105) => True end -> match _u0 with (x104,x105) => True end -> match _u0 with (x104,x105) => (ss_cc = ss_cc) end -> (ai = (a!i)) -> (bi = (b!i)) -> match mst with (x106,x107) => ((^ x106) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match mst with (x106,x107) => ((x107 = 0%F) \/ (x107 = 1%F)) end -> match mst with (x106,x107) => ((x106 + ((2%F ^ n)%F * x107)%F)%F = ((ai + bi)%F + c')%F) end -> (carry = snd (mst)) -> (sum = fst (mst)) -> match _u1 with (x108,x109) => True end -> match _u1 with (x108,x109) => True end -> match _u1 with (x108,x109) => (mst = mst) end -> (True -> ((as_le n ((s' ++ (sum :: nil)) ++ (carry :: nil))) = ((as_le n (a[:(i + 1%nat)%nat])) + (as_le n (b[:(i + 1%nat)%nat])))%Z)).
Proof. 
  unwrap_C.
  unfold as_le.
  intros. destruct ss_cc as [ss cc]. destruct mst  as [s c]. simpl in *. apply Repr.in_range_binary in H8, H20.
  intuit. subst.
  rewrite RZ.as_le_app.
  repeat rewrite firstn_plus1 by lia.
  repeat rewrite RZ.as_le_app.

  simpl. rewrite app_length. simpl. simplify.
  repeat rewrite firstn_length_le by lia.
  
  rewrite RZ.as_le_app in H9. simpl in H9. simplify' H9.
  replace 
     (Z.mul (Z.of_nat n)
        (Z.add (Z.of_nat (@length (F.F q) ss))
           (Z.of_nat (S O)))) with (n*length ss + n)%Z by lia.
  rewrite Zpower_exp by lia.
  apply f_equal with (f:=F.to_Z) in H21.
  assert (H_pow_nk: (2 * 2^n <= 2^k)%Z). {
    replace (2 * 2^n)%Z with (2 ^ (n + 1))%Z by (rewrite Zpower_exp; lia).
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  assert (^ a!length ss <= 2^n -1). unfold_default. apply Forall_nth; auto; lia.
  assert (^ b!length ss <= 2^n -1). unfold_default. apply Forall_nth; auto; lia.
  autorewrite with F_to_Z in H21; try lia;
  repeat (autorewrite with F_to_Z); simpl; pose_nonneg; try (lia || nia).
  simpl in H21.
  unfold RZ.ToZ.to_Z in *.
  nia.
Qed.

Lemma BigAdd_obligation15: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : (list F)), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x110 => ((^ x110) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x111 => ((^ x111) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> Forall (fun x112 => True) v -> True -> ((v = nil) -> (((length v) = 0%nat) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof. 
  intuit; subst; simpl in *; try lia.
Qed.

Lemma BigAdd_obligation16_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x113 => ((^ x113) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x114 => ((^ x114) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation17: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x115 => ((^ x115) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x116 => ((^ x116) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%F) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit. Qed.

Lemma BigAdd_obligation18: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x117 => ((^ x117) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x118 => ((^ x118) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (True -> ((as_le n (nil ++ (0%F :: nil))) = ((as_le n (a[:0%nat])) + (as_le n (b[:0%nat])))%Z)).
Proof. unwrap_C. intuit; simpl. simplify. Qed.

Lemma BigAdd_obligation19: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (sum_carry : ((list F) * F)) (carry : F) (sum : (list F)) (_u2 : ((list F) * F)) (v : (list F)), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x119 => ((^ x119) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x120 => ((^ x120) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match sum_carry with (x122,x123) => Forall (fun x121 => ((^ x121) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x122 end -> match sum_carry with (x122,x123) => ((length x122) = k) end -> match sum_carry with (x122,x123) => ((x123 = 0%F) \/ (x123 = 1%F)) end -> match sum_carry with (x122,x123) => ((as_le n (x122 ++ (x123 :: nil))) = ((as_le n (a[:k])) + (as_le n (b[:k])))%Z) end -> (carry = (snd sum_carry)) -> Forall (fun x124 => True) sum -> (sum = (fst sum_carry)) -> match _u2 with (x126,x127) => Forall (fun x125 => True) x126 end -> match _u2 with (x126,x127) => True end -> match _u2 with (x126,x127) => True end -> match _u2 with (x126,x127) => ((sum_carry = sum_carry) /\ True) end -> Forall (fun x128 => True) v -> True -> (((v = (sum ++ (carry :: nil))) /\ ((length v) = ((length sum) + (length (carry :: nil)))%nat)) -> ((((length v) = (k + 1%nat)%nat) /\ ((as_le n v) = ((as_le n a) + (as_le n b))%Z)) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
Proof.
  unwrap_C.
  intros.
  destruct (sum_carry) as [_sum _carry]. destruct _u2. simpl in *. subst _sum _carry.
  do 2 rewrite firstn_all2 in H8 by lia. apply Repr.in_range_binary in H7.
  intuit; subst v;
  rewrite app_length in *; simpl in *; try lia.
  unfold_default; apply Forall_nth; try (rewrite app_length; simpl; lia);
  apply Forall_app; intuit; constructor; auto; autorewrite with F_to_Z; try lia.
  assert (2^1 <= 2^n). apply Zpow_facts.Zpower_le_monotone; lia.
  lia.
Qed.

Lemma BigAdd_obligation20_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (sum_carry : ((list F) * F)) (carry : F) (sum : (list F)) (_u2 : ((list F) * F)) (v : F), ((n <= (C.k - 1%nat)%Z) /\ ((1%nat <= n) /\ True)) -> (1%nat <= k) -> Forall (fun x129 => ((^ x129) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x130 => ((^ x130) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match sum_carry with (x132,x133) => Forall (fun x131 => ((^ x131) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x132 end -> match sum_carry with (x132,x133) => ((length x132) = k) end -> match sum_carry with (x132,x133) => ((x133 = 0%F) \/ (x133 = 1%F)) end -> match sum_carry with (x132,x133) => ((as_le n (x132 ++ (x133 :: nil))) = ((as_le n (a[:k])) + (as_le n (b[:k])))%Z) end -> (carry = (snd sum_carry)) -> Forall (fun x134 => True) sum -> (sum = (fst sum_carry)) -> match _u2 with (x136,x137) => Forall (fun x135 => True) x136 end -> match _u2 with (x136,x137) => True end -> match _u2 with (x136,x137) => True end -> match _u2 with (x136,x137) => ((sum_carry = sum_carry) /\ True) end -> True -> (True -> True).
Proof. intuit. Qed.


(* TODO *)

(** ** BigAddModP *)

(* print_endline (generate_lemmas big_add_mod_p (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three; big_add; c_is_equal; c_less_than; cand; cor; c_big_lt; c_mod_sub_three; big_sub]) big_add_mod_p));; *)

(* TODO *)
