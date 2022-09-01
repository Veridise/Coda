Require Import Circom.Config.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Zdiv.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List.

From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.
From Coqprime.examples Require Import BasePrimes.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.

Local Open Scope positive_scope.

Import ListNotations. 

Module BabyJubjub.

Definition p := 21888242871839275222246405745257275088548364400416034343698204186575808495617.

Lemma is_prime : prime p.
Proof.
  apply (Pocklington_refl
    (Pock_certif 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 ((405928799, 1)::(11003, 1)::(983, 1)::(13, 1)::(3, 1)::(2,28)::nil) 61188133433000256669356882)
    ((Pock_certif 405928799 11 ((4999, 1)::(2,1)::nil) 608) ::
      (Proof_certif 11003 prime11003) ::
      (Proof_certif 4999 prime4999) ::
      (Proof_certif 983 prime983) ::
      (Proof_certif 13 prime13) ::
      (Proof_certif 3 prime3) ::
      (Proof_certif 2 prime2) ::
      nil)).
  native_cast_no_check (refl_equal true).
Qed.


Definition half : F p.
Proof.
  unfold F, p.
  exists 10944121435919637611123202872628637544274182200208017171849102093287904247808.
  rewrite Z.mod_small; lia.
Defined.

Definition half_Z := F.to_Z half.

Open Scope Z_scope.

Lemma is_half : 2 * half_Z <= p /\ 2 * (half_Z + 1) > p.
Proof.
  unfold half_Z, p. simpl. split; lia.
Qed.

Definition lt (x: F p) (y: F p) := F.to_Z x < F.to_Z y.
Definition leq (x: F p) (y: F p) := F.to_Z x <= F.to_Z y.
Definition gt (x: F p) (y: F p) := F.to_Z x > F.to_Z y.
Definition geq (x: F p) (y: F p) := F.to_Z x >= F.to_Z y.

End BabyJubjub.

Declare Scope BabyJubjub_scope.
Infix "<" :=  BabyJubjub.lt  : BabyJubjub_scope.
Infix "<=" := BabyJubjub.leq : BabyJubjub_scope.
Infix ">" := BabyJubjub.gt   : BabyJubjub_scope.
Infix ">=" := BabyJubjub.geq : BabyJubjub_scope.

Local Open Scope BabyJubjub_scope.
Definition Fbj := F BabyJubjub.p.

Theorem test: 1 < BabyJubjub.half.
Proof.
  Unset Printing Notations.
  unfold BabyJubjub.lt, BabyJubjub.p, BabyJubjub.half; simpl.
  rewrite Z.mod_small; lia.
Qed.
