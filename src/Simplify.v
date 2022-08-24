Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Circom.Circom.

Local Open Scope circom_scope.


(* Base 2^n representations *)
Lemma to_Z_2: |^2| = 2%Z.
Proof. unwrap_C. simpl. repeat rewrite Z.mod_small; lia. Qed.

Lemma to_Z_sub: forall x y, (F.to_Z y < q)%Z ->
@F.to_Z q (x - y) = ((F.to_Z x - F.to_Z y mod q) mod q)%Z.
Proof.
  unwrap_C.
  intros ? ? Hy. unfold F.sub. rewrite F.to_Z_add. rewrite F.to_Z_opp.
  destruct (dec (F.to_Z y = 0)%Z).
  - rewrite e. rewrite Z_mod_zero_opp_full. replace (F.to_Z x + 0)%Z with (F.to_Z x - 0)%Z by lia. reflexivity.
    apply Zmod_0_l.
  - rewrite Z_mod_nz_opp_full.
    replace (F.to_Z x + (q - F.to_Z y mod q))%Z with ((F.to_Z x - F.to_Z y mod q) + 1 * q)%Z by lia.
    rewrite Z_mod_plus by lia.
    reflexivity.
    rewrite Z.mod_small. auto.
    apply F.to_Z_range. lia.
Qed.

Create HintDb F_to_Z discriminated.
#[export] Hint Rewrite (to_Z_2) : F_to_Z.
#[export] Hint Rewrite (@F.to_Z_add q) : F_to_Z.
#[export] Hint Rewrite (@F.to_Z_mul q) : F_to_Z.
#[export] Hint Rewrite (@F.to_Z_pow q) : F_to_Z.
#[export] Hint Rewrite (@F.to_Z_0 q) : F_to_Z.
#[export] Hint Rewrite (@F.to_Z_1 q) : F_to_Z.
#[export] Hint Rewrite (@F.pow_1_r q) : F_to_Z.
#[export] Hint Rewrite to_Z_sub : F_to_Z.
#[export] Hint Rewrite Z.mod_small : F_to_Z.

Create HintDb simplify_F discriminated.
Local Open Scope circom_scope.
Local Open Scope F_scope.
Lemma Fmul_0_r: forall (x: F), x * 0 = 0.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_0_l: forall (x: F), 0 * x = 0.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_1_r: forall (x: F), x * 1 = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fmul_1_l: forall (x: F), 1 * x = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fadd_0_r: forall (x: F), x + 0 = x.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fadd_0_l: forall (x: F), 0 + x = x.
Proof. unwrap_C. intros. fqsatz. Qed.

#[export] Hint Rewrite (Fmul_0_r) : simplify_F.
#[export] Hint Rewrite (Fmul_0_l) : simplify_F.
#[export] Hint Rewrite (Fmul_1_r) : simplify_F.
#[export] Hint Rewrite (Fmul_1_l) : simplify_F.
#[export] Hint Rewrite (Fadd_0_r) : simplify_F.
#[export] Hint Rewrite (Fadd_0_l) : simplify_F.
#[export] Hint Rewrite (@F.pow_0_l) : simplify_F.
#[export] Hint Rewrite (@F.pow_0_r) : simplify_F.
#[export] Hint Rewrite (@F.pow_1_l) : simplify_F.
#[export] Hint Rewrite (@F.pow_1_r) : simplify_F.
#[export] Hint Rewrite (@F.pow_add_r) : simplify_F.

Create HintDb simplify_NZ discriminated.
#[export] Hint Rewrite Nat2N.inj_mul : simplify_NZ.
#[export] Hint Rewrite Nat2N.inj_add : simplify_NZ.
#[export] Hint Rewrite Nat2Z.inj_mul : simplify_NZ.
#[export] Hint Rewrite Nat2Z.inj_add : simplify_NZ.
#[export] Hint Rewrite (Nat.mul_1_l) : simplify_NZ.
#[export] Hint Rewrite (Nat.mul_1_r): simplify_NZ.
#[export] Hint Rewrite (Nat.mul_0_l): simplify_NZ.
#[export] Hint Rewrite (Nat.mul_0_r): simplify_NZ.
#[export] Hint Rewrite (Nat.add_0_r): simplify_NZ.
#[export] Hint Rewrite (Nat.add_0_l): simplify_NZ.
#[export] Hint Rewrite (Nat.mul_succ_r): simplify_NZ.
#[export] Hint Rewrite (Nat.mul_add_distr_l): simplify_NZ.
#[export] Hint Rewrite (Nat.mul_add_distr_r): simplify_NZ.
#[export] Hint Rewrite (Z.add_0_r): simplify_NZ.
#[export] Hint Rewrite (Z.add_0_l): simplify_NZ.
#[export] Hint Rewrite (Z.mul_1_l) : simplify_NZ.
#[export] Hint Rewrite (Z.mul_1_r): simplify_NZ.
#[export] Hint Rewrite (Z.mul_0_l): simplify_NZ.
#[export] Hint Rewrite (Z.mul_0_r): simplify_NZ.
#[export] Hint Rewrite (Z.mul_succ_r): simplify_NZ.
#[export] Hint Rewrite (Zpow_facts.Zpower_1_r): simplify_NZ.
#[export] Hint Rewrite (Zpow_facts.Zpower_1_l): simplify_NZ.
#[export] Hint Rewrite (Zpow_facts.Zpower_0_l): simplify_NZ.
#[export] Hint Rewrite (Zpow_facts.Zpower_0_r): simplify_NZ.
#[export] Hint Rewrite (Zpower_exp): simplify_NZ.

#[export] Hint Rewrite (N.mul_1_l) : simplify_NZ.
#[export] Hint Rewrite (N.mul_1_r): simplify_NZ.
#[export] Hint Rewrite (N.mul_0_l): simplify_NZ.
#[export] Hint Rewrite (N.mul_0_r): simplify_NZ.
#[export] Hint Rewrite (N.add_0_r): simplify_NZ.
#[export] Hint Rewrite (N.add_0_l): simplify_NZ.
#[export] Hint Rewrite (N.mul_succ_r): simplify_NZ.
#[export] Hint Rewrite (N.mul_add_distr_l): simplify_NZ.
#[export] Hint Rewrite (N.mul_add_distr_r): simplify_NZ.


Ltac simplify := autorewrite with simplify_NZ simplify_F natsimplify; try lia.
Ltac simplify' H := autorewrite with simplify_NZ simplify_F natsimplify in H; try lia.
