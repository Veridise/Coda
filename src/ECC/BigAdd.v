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

Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Util DSL.
Require Import Circom.circomlib.Bitify Circom.circomlib.Comparators.

(* Require Import VST.zlist.Zlist. *)

Require Import Circom.Circom.
Require Import Circom.ECC.Polynom.

(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)

Module BigAdd (C: CIRCOM).

Module B := Bitify C.
Module Cmp := Comparators C.
Import C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.


Local Notation "x [ i ]" := (nth_default 0 i x).

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Module ModSumThree.
(* template ModSumThree(n) {
    assert(n + 2 <= 253);
    signal input a;
    signal input b;
    signal input c;
    signal output sum;
    signal output carry;

    component n2b = Num2Bits(n + 2);
    n2b.in <== a + b + c;
    carry <== n2b.out[n] + 2 * n2b.out[n + 1];
    sum <== a + b + c - carry * (1 << n);
} *)

Import B.
(* Note: this is a simplified version from circom-pairing *)
Definition cons (n: nat) (a b c sum carry: F) :=
  exists (n2b: Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits._out)[n] /\
    sum = a + b + c - carry * 2^n.

Class t (n: nat) : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons n a b c sum carry;
}.



(* x is a valid digit in base-2^n representation *)
Local Notation "x | ( n )" := (in_range n x) (at level 40).

Module Comparators := Comparators C.
Create HintDb F_to_Z discriminated.
Hint Rewrite (to_Z_2) : F_to_Z.
Hint Rewrite (@F.to_Z_add q) : F_to_Z.
Hint Rewrite (@F.to_Z_mul q) : F_to_Z.
Hint Rewrite (@F.to_Z_pow q) : F_to_Z.
Hint Rewrite (@F.to_Z_0 q) : F_to_Z.
Hint Rewrite (@F.to_Z_1 q) : F_to_Z.
Hint Rewrite (@F.pow_1_r q) : F_to_Z.
Hint Rewrite Cmp.LessThan.to_Z_sub : F_to_Z.
Hint Rewrite Z.mod_small : F_to_Z.

Lemma Fmul_0_r: forall (x: F), x * 0 = 0.
Proof. unwrap_C. intros. fqsatz. Qed.
Lemma Fadd_0_r: forall (x: F), x + 0 = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Create HintDb Fsimplify discriminated.
Hint Rewrite (@F.to_Z_0 q) : Fsimplify.
Hint Rewrite (@F.to_Z_1 q) : Fsimplify.
Hint Rewrite (Fmul_0_r) : Fsimplify.
Hint Rewrite (Fadd_0_r) : Fsimplify.
Hint Rewrite (Nat.mul_1_l) : Fsimplify.
Hint Rewrite <- (Nat2N.inj_mul) : Fsimplify.


Definition spec (n: nat) (w: t n) :=
  ( S n <= k )%Z ->
  w.(a) | (n) -> w.(b) | (n) -> binary c ->
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  w.(sum) | (n) /\
  binary w.(carry).

Lemma add_0_r: forall (x z: F), z = 0 -> x + z= x.
Proof. unwrap_C. intros. fqsatz. Qed.

Theorem soundness: forall n w, spec n w.
Proof.
  unwrap_C. intros.
  destruct w as [a b c sum carry _cons].
  unfold spec, cons in *. destruct _cons as [n2b [H_in [H_carry H_sum] ] ].
  simpl. intros Hnk Ha Hb Hc.
  apply in_range_binary in Hc.
  intuition.
  - fqsatz.
  - subst.
  unfold in_range in *.
  remember (Num2Bits._out [n] ) as out_n.
  pose proof (Num2Bits.soundness _ n2b) as H_n2b. unfold Num2Bits.spec, repr_le2 in *.
  rewrite <- H_in.
  pose proof H_n2b as H_n2b'. unfold repr_le in H_n2b. destruct H_n2b as [_ [_ H_as_le] ].
  rewrite H_as_le.
  (* rewrite [| out |] as [| out[:n] |] + 2^n * out[n] *)
  erewrite <- firstn_split_last with (l := (to_list (S n) Num2Bits._out)) (n:=n) (d:=0) by (rewrite length_to_list; lia).
  rewrite <- nth_default_eq, nth_default_to_list.
  rewrite as_le_app. cbn [as_le].
  rewrite <- Heqout_n, firstn_length_le by (rewrite length_to_list; lia).
  autorewrite with Fsimplify.
  replace (as_le 1 (firstn n (to_list (S n) Num2Bits._out)) + (1 + 1) ^ n * out_n -
    out_n * (1 + 1) ^ n) with (as_le 1 (firstn n (to_list (S n) Num2Bits._out))) by fqsatz.
  eapply repr_le_ub; try lia.
  unfold repr_le2. 
  eapply repr_le_prefix; eauto.
  rewrite firstn_length_le. lia. rewrite length_to_list. lia.
  assert ((to_list (S n) Num2Bits._out) = (to_list (S n) Num2Bits._out)) by auto.
  erewrite <- firstn_split_last in H.
  rewrite <- H in *.
  rewrite length_to_list. rewrite <- H_as_le. auto.
  rewrite length_to_list. auto.
  lia.

  - rewrite H_carry.
  pose proof (Num2Bits.soundness _ n2b) as H_n2b. unfold Num2Bits.spec, repr_le2, repr_le in *.
  intuition.
  rewrite <- nth_default_to_list, nth_default_eq.
  apply Forall_nth.
  apply Forall_in_range.
  auto. 
  rewrite length_to_list.
  lia.
  Unshelve. auto. (* ??? what is this *)
Qed.
End ModSumThree.
End BigAdd.

(* // addition mod 2**n with carry bit
template ModSum(n) {
    assert(n <= 252);
    signal input a;
    signal input b;
    signal output sum;
    signal output carry;

    component n2b = Num2Bits(n + 1);
    n2b.in <== a + b;
    carry <== n2b.out[n];
    sum <== a + b - carry * (1 << n);
} *)
(* Definition ModSum_cons (n: nat) (a b sum carry: F) :=
  exists (n2b: Num2Bits.t),
    n2b.(Num2Bits._in) = a+b /\
    n2b.(Num2Bits._out)[n] = carry /\
    sum = a + b - carry * 2^n.

(* TODO: define mod and quotient in F *)
Definition ModSum_spec (n: nat) (a b sum carry: F) :=
  sum + carry * 2^n = a + b.

Lemma ModSum_sound (n: nat) (a b sum carry: F):
  ModSum_cons n a b sum carry ->
  ModSum_spec n a b sum carry.
Proof.
  unwrap_C.
  unfold ModSum_cons, ModSum_spec.
  intros H. destruct H as [n2b H]. intuition idtac.
  pose proof Num2Bits.soundness as Hn2b. specialize (Hn2b n2b). unfold Num2Bits.spec, Num2Bits.repr_binary in Hn2b.
  intuition idtac.
  fqsatz.
Qed. *)