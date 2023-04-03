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
Proof. Admitted.

(** ** BigAdd *)

(* print_endline (generate_lemmas big_add (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three]) big_add));; *)

(* TODO *)

(** ** BigAddModP *)

(* print_endline (generate_lemmas big_add_mod_p (typecheck_circuit (add_to_deltas d_empty [num2bits; mod_sum_three; big_add; c_is_equal; c_less_than; cand; cor; c_big_lt; c_mod_sub_three; big_sub]) big_add_mod_p));; *)

(* TODO *)
