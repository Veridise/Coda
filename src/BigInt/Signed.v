Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.ZArith.Znat.


Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.


From Circom Require Import Circom Util LibTactics Simplify.


Module Signed.
Local Open Scope circom_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.

Definition to_Z (x: F) :=
    if dec (|^x| <= 2^r - 1) then |^x| else |^x| - q.

Lemma pow_r: 2 * 2^r <= 2^k.
Proof.
  unwrap_C. pose proof r_k.
  replace (2*2^r) with (2^(r+1)).
  apply Zpow_facts.Zpower_le_monotone; try lia.
  rewrite Zpower_exp; simplify.
Qed.

Lemma add_mod: forall a b,
  (a + b) mod b = a mod b.
Admitted.

Lemma sub_mod: forall a b,
  (a - b) mod b = a mod b.
Admitted.

Local Notation "|% x |" := (to_Z x).
Lemma to_Z_add: forall x y,
  |% x + y| = |%x| + |%y|.
Proof with (lia || eauto).
  unwrap_C.
  intros. unfold to_Z.
  pose proof pow_r.
  assert (0 <= |^x| < q). apply F.to_Z_range. lia.
  assert (0 <= |^y| < q). apply F.to_Z_range. lia.
  (* destruct (dec (x|(r))); destruct (dec (y|(r))). *)
  split_dec; rewrite F.to_Z_add.
  rewrite Zmod_small...
  rewrite <- sub_mod.
  rewrite Zmod_small...
  
  
  
  



