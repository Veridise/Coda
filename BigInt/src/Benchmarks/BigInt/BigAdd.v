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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr ReprZ.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition as_le_f := Repr.as_le 1%nat.
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

(** ** ModSumThree *)

(* print_endline (generate_lemmas mod_sum_three (typecheck_circuit (add_to_delta d_empty num2bits) mod_sum_three));; *)
Lemma ModSumThree_obligation0_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation1_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = 1%nat) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation2: forall (n : nat) (a : F) (b : F) (c : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (n + 1%nat)%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSumThree_obligation3_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation4_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation5_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation6_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation7_trivial: forall (n : nat) (a : F) (b : F) (c : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation8_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = a)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation9_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((^ v) <= ((2%nat ^ n)%nat - 1%nat)%Z) /\ (v = b)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation10_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (a + b)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation11_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation12_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = ((a + b)%F + c)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation13_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> (((v = (n2b!n)) /\ (v = carry)) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation14_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation15: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma ModSumThree_obligation16_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (2%F ^ n)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation17_trivial: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> True -> ((v = (carry * (2%F ^ n)%F)%F) -> True).
Proof. intuit. Qed.

Lemma ModSumThree_obligation18: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (sum : F) (v : F * F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%nat - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> (sum = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> match v with (x11,x12) => ((x11 = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) /\ (x11 = sum)) end -> match v with (x11,x12) => ((x12 = (n2b!n)) /\ (x12 = carry)) end -> match v with (x11,x12) => True end -> (True -> ((fst (v) + ((2%F ^ n)%F * snd (v))%F)%F = ((a + b)%F + c)%F)).
Proof. unwrap_C. intros. destruct v. intuit; subst; simpl. fqsatz. fqsatz. Qed.

Lemma ModSumThree_obligation19: forall (n : nat) (a : F) (b : F) (c : F) (n2b : (list F)) (carry : F) (sum : F) (v : F), (n <= (C.k - 1%nat)%Z) -> ((^ a) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ b) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((c = 0%F) \/ (c = 1%F)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = ((a + b)%F + c)%F) /\ ((length n2b) = (n + 1%nat)%nat)) -> (carry = (n2b!n)) -> (sum = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) -> True -> (((v = (((a + b)%F + c)%F - (carry * (2%F ^ n)%F)%F)%F) /\ (v = sum)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
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

Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Local Notation "[| xs | n ]" := (RZ.as_le n xs).
Definition as_le := RZ.as_le.

Lemma BigAdd_obligation0_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x0 => ((^ x0) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x1 => ((^ x1) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation1_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : nat), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x2 => ((^ x2) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x3 => ((^ x3) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (((1%nat <= v) /\ (v = k)) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation2_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x4 => ((^ x4) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x5 => ((^ x5) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((0%nat <= v) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation3_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x6 => ((^ x6) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x7 => ((^ x7) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (((0%nat <= v) /\ (v < k)) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation4_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : (list F) * F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x8 => ((^ x8) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x9 => ((^ x9) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match v with (x11,x12) => Forall (fun x10 => ((^ x10) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x11 end -> match v with (x11,x12) => ((length x11) = i) end -> match v with (x11,x12) => ((x12 = 0%F) \/ (x12 = 1%F)) end -> match v with (x11,x12) => True end -> (((as_le n (fst (v) ++ (snd (v) :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation5_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : (list F)), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x13 => ((^ x13) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x14 => ((^ x14) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> Forall (fun x15 => ((^ x15) <= ((2%nat ^ n)%Z - 1%nat)%Z)) v -> True -> (((length v) = i) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation6_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x16 => ((^ x16) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x17 => ((^ x17) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation7_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x18 => ((^ x18) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x19 => ((^ x19) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. intuit. Qed.

Lemma BigAdd_obligation8: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x20 => ((^ x20) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x21 => ((^ x21) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x23,x24) => Forall (fun x22 => ((^ x22) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x23 end -> match s_c with (x23,x24) => ((length x23) = i) end -> match s_c with (x23,x24) => ((x24 = 0%F) \/ (x24 = 1%F)) end -> match s_c with (x23,x24) => ((as_le n (x23 ++ (x24 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x25 => ((^ x25) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z)) /\ (v = n)) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed.

Lemma BigAdd_obligation9: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x26 => ((^ x26) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x27 => ((^ x27) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x29,x30) => Forall (fun x28 => ((^ x28) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x29 end -> match s_c with (x29,x30) => ((length x29) = i) end -> match s_c with (x29,x30) => ((x30 = 0%F) \/ (x30 = 1%F)) end -> match s_c with (x29,x30) => ((as_le n (x29 ++ (x30 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x31 => ((^ x31) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = (a!i)) /\ (v = ai)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma BigAdd_obligation10: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x32 => ((^ x32) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x33 => ((^ x33) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x35,x36) => Forall (fun x34 => ((^ x34) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x35 end -> match s_c with (x35,x36) => ((length x35) = i) end -> match s_c with (x35,x36) => ((x36 = 0%F) \/ (x36 = 1%F)) end -> match s_c with (x35,x36) => ((as_le n (x35 ++ (x36 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x37 => ((^ x37) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> True -> (((v = (b!i)) /\ (v = bi)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma BigAdd_obligation11: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x38 => ((^ x38) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x39 => ((^ x39) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x41,x42) => Forall (fun x40 => ((^ x40) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x41 end -> match s_c with (x41,x42) => ((length x41) = i) end -> match s_c with (x41,x42) => ((x42 = 0%F) \/ (x42 = 1%F)) end -> match s_c with (x41,x42) => ((as_le n (x41 ++ (x42 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x43 => ((^ x43) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = c)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit. Qed.

Lemma BigAdd_obligation12: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (sum_carry : F * F) (sum : F) (carry : F) (v : (list F)), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x44 => ((^ x44) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x45 => ((^ x45) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x47,x48) => Forall (fun x46 => ((^ x46) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x47 end -> match s_c with (x47,x48) => ((length x47) = i) end -> match s_c with (x47,x48) => ((x48 = 0%F) \/ (x48 = 1%F)) end -> match s_c with (x47,x48) => ((as_le n (x47 ++ (x48 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x49 => ((^ x49) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> match sum_carry with (x50,x51) => ((^ x50) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match sum_carry with (x50,x51) => ((x51 = 0%F) \/ (x51 = 1%F)) end -> match sum_carry with (x50,x51) => ((x50 + ((2%F ^ n)%F * x51)%F)%F = ((ai + bi)%F + c)%F) end -> ((^ sum) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((carry = 0%F) \/ (carry = 1%F)) -> Forall (fun x52 => ((^ x52) <= ((2%nat ^ n)%Z - 1%nat)%Z)) v -> True -> (((v = (s ++ (sum :: nil))) /\ ((length v) = ((length s) + (length (sum :: nil)))%nat)) -> ((length v) = (i + 1%nat)%nat)).
Proof. simpl. lia. Qed.

Lemma BigAdd_obligation13_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (sum_carry : F * F) (sum : F) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x53 => ((^ x53) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x54 => ((^ x54) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x56,x57) => Forall (fun x55 => ((^ x55) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x56 end -> match s_c with (x56,x57) => ((length x56) = i) end -> match s_c with (x56,x57) => ((x57 = 0%F) \/ (x57 = 1%F)) end -> match s_c with (x56,x57) => ((as_le n (x56 ++ (x57 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x58 => ((^ x58) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> match sum_carry with (x59,x60) => ((^ x59) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match sum_carry with (x59,x60) => ((x60 = 0%F) \/ (x60 = 1%F)) end -> match sum_carry with (x59,x60) => ((x59 + ((2%F ^ n)%F * x60)%F)%F = ((ai + bi)%F + c)%F) end -> ((^ sum) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. intuit. Qed.

Lemma BigAdd_obligation14: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (sum_carry : F * F) (sum : F) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x61 => ((^ x61) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x62 => ((^ x62) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x64,x65) => Forall (fun x63 => ((^ x63) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x64 end -> match s_c with (x64,x65) => ((length x64) = i) end -> match s_c with (x64,x65) => ((x65 = 0%F) \/ (x65 = 1%F)) end -> match s_c with (x64,x65) => ((as_le n (x64 ++ (x65 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x66 => ((^ x66) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> match sum_carry with (x67,x68) => ((^ x67) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match sum_carry with (x67,x68) => ((x68 = 0%F) \/ (x68 = 1%F)) end -> match sum_carry with (x67,x68) => ((x67 + ((2%F ^ n)%F * x68)%F)%F = ((ai + bi)%F + c)%F) end -> ((^ sum) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = carry)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit. Qed.

Lemma BigAdd_obligation15: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (i : nat) (s_c : (list F) * F) (s : (list F)) (c : F) (ai : F) (bi : F) (sum_carry : F * F) (sum : F) (carry : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x69 => ((^ x69) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x70 => ((^ x70) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (i < k) -> match s_c with (x72,x73) => Forall (fun x71 => ((^ x71) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x72 end -> match s_c with (x72,x73) => ((length x72) = i) end -> match s_c with (x72,x73) => ((x73 = 0%F) \/ (x73 = 1%F)) end -> match s_c with (x72,x73) => ((as_le n (x72 ++ (x73 :: nil))) = ((as_le n (a[:i])) + (as_le n (b[:i])))%Z) end -> Forall (fun x74 => ((^ x74) <= ((2%nat ^ n)%Z - 1%nat)%Z)) s -> ((length s) = i) -> ((c = 0%F) \/ (c = 1%F)) -> (ai = (a!i)) -> (bi = (b!i)) -> match sum_carry with (x75,x76) => ((^ x75) <= ((2%nat ^ n)%Z - 1%nat)%Z) end -> match sum_carry with (x75,x76) => ((x76 = 0%F) \/ (x76 = 1%F)) end -> match sum_carry with (x75,x76) => ((x75 + ((2%F ^ n)%F * x76)%F)%F = ((ai + bi)%F + c)%F) end -> ((^ sum) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((carry = 0%F) \/ (carry = 1%F)) -> (True -> ((as_le n ((s ++ (sum :: nil)) ++ (carry :: nil))) = ((as_le n (a[:(i + 1%nat)%nat])) + (as_le n (b[:(i + 1%nat)%nat])))%Z)).
Proof. Admitted.

Lemma BigAdd_obligation16: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : (list F)), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x77 => ((^ x77) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x78 => ((^ x78) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> Forall (fun x79 => True) v -> True -> ((v = nil) -> ((length v) = 0%nat)).
Proof. intuit; subst; simpl; lia. Qed.

Lemma BigAdd_obligation17: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x80 => ((^ x80) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x81 => ((^ x81) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> (True -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma BigAdd_obligation18: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x82 => ((^ x82) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x83 => ((^ x83) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> True -> ((v = 0%F) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit. Qed.

Lemma BigAdd_obligation19: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x84 => ((^ x84) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x85 => ((^ x85) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> (True -> ((as_le n (nil ++ (0%F :: nil))) = ((as_le n (a[:0%nat])) + (as_le n (b[:0%nat])))%Z)).
Proof. unwrap_C. intuit. simpl. simplify. Qed.

Lemma BigAdd_obligation20: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (sum_carry : (list F) * F) (sum : (list F)) (carry : F) (v : (list F)), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x86 => ((^ x86) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x87 => ((^ x87) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match sum_carry with (x89,x90) => Forall (fun x88 => ((^ x88) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x89 end -> match sum_carry with (x89,x90) => ((length x89) = k) end -> match sum_carry with (x89,x90) => ((x90 = 0%F) \/ (x90 = 1%F)) end -> match sum_carry with (x89,x90) => ((as_le n (x89 ++ (x90 :: nil))) = ((as_le n (a[:k])) + (as_le n (b[:k])))%Z) end -> Forall (fun x91 => ((^ x91) <= ((2%nat ^ n)%Z - 1%nat)%Z)) sum -> ((length sum) = k) -> ((carry = 0%F) \/ (carry = 1%F)) -> Forall (fun x92 => ((^ x92) <= ((2%nat ^ n)%Z - 1%nat)%Z)) v -> True -> (((v = (sum ++ (carry :: nil))) /\ ((length v) = ((length sum) + (length (carry :: nil)))%nat)) -> ((length v) = (k + 1%nat)%nat)).
Proof. simpl. lia. Qed.

Lemma BigAdd_obligation21_trivial: forall (n : nat) (k : nat) (a : (list F)) (b : (list F)) (sum_carry : (list F) * F) (sum : (list F)) (carry : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (1%nat <= k) -> Forall (fun x93 => ((^ x93) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> ((length a) = k) -> Forall (fun x94 => ((^ x94) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> ((length b) = k) -> match sum_carry with (x96,x97) => Forall (fun x95 => ((^ x95) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x96 end -> match sum_carry with (x96,x97) => ((length x96) = k) end -> match sum_carry with (x96,x97) => ((x97 = 0%F) \/ (x97 = 1%F)) end -> match sum_carry with (x96,x97) => ((as_le n (x96 ++ (x97 :: nil))) = ((as_le n (a[:k])) + (as_le n (b[:k])))%Z) end -> Forall (fun x98 => ((^ x98) <= ((2%nat ^ n)%Z - 1%nat)%Z)) sum -> ((length sum) = k) -> ((carry = 0%F) \/ (carry = 1%F)) -> True -> (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. intuit. Qed.



(* TODO *)

(** ** BigAddModP *)

(* print_endline (generate_lemmas big_add_mod_p (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three; big_add; c_is_equal; c_less_than; cand; cor; c_big_lt; c_mod_sub_three; big_sub]) big_add_mod_p));; *)

(* TODO *)
