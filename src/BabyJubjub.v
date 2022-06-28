Require Import Coq.PArith.BinPosDef.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.
From Coqprime.examples Require Import BasePrimes.
Local Open Scope positive_scope.

Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations. 

Definition babyJubjub := 21888242871839275222246405745257275088548364400416034343698204186575808495617. 

Lemma babyJubjub_prime : prime (Zpos babyJubjub).
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

