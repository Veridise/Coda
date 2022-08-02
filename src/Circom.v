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

(* Require Import Crypto.Util.Tuple. *)
(* Require Import Crypto.Util.Decidable Crypto.Util.Notations. *)
(* Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac. *)

Module Type CIRCOM.
  Parameter (q: positive).
  Parameter (k: Z).
  Axioms
    (prime_q: prime q) 
    (two_lt_q: 2 < q)
    (k_positive: 1 < k)
    (q_lb: 2^k < q).
  
  Global Ltac unwrap_C :=
      pose proof prime_q as prime_q;
      pose proof two_lt_q as two_lt_q;
      pose proof k_positive as k_positive;
      pose proof q_lb as q_lb.
    
  Lemma q_gtb_1: (1 <? q)%positive = true.
  Proof.
    pose proof prime_q.
    unwrap_C.
    apply Pos.ltb_lt. lia.
  Qed.
  
  Lemma q_gt_2: 2 < q.
  Proof.
    unwrap_C.
    replace 2%Z with (2^1)%Z by lia.
    apply Z.le_lt_trans with (m := (2 ^ k)%Z); try lia.
    eapply Zpow_facts.Zpower_le_monotone; try lia.
  Qed.
  
  Global Hint Rewrite q_gtb_1 : core.
  Global Hint Rewrite two_lt_q : core.
  
  Global Ltac fqsatz := fsatz_safe; autorewrite with core; auto.
  
  Global Notation F := (F q).
  
  Global Ltac split_eqns :=
    repeat match goal with
    | [ |- _ /\ _ ] => split
    | [ H: exists _, _ |- _ ] => destruct H
    | [ H: {s | _ } |- _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ _: _ |- _ -> _ ] => intros
    end.
  
  (* Global Notation "2" := (1 + 1 : F) : Circom_scope. *)
End CIRCOM.