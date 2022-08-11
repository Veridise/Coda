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
Import B C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Notation "x [ i ]" := (nth_default 0 i x).
Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Module ModSumThree.
(* Note: this is a simplified version from circom-pairing *)
(* 
template ModSumThree(n) {
  assert(n + 1 <= 253);
  signal input a;
  signal input b;
  signal input c;
  signal output sum;
  signal output carry;

  component n2b = Num2Bits(n + 1);
  n2b.in <== a + b + c;
  carry <== n2b.out[n];
  sum <== a + b + c - carry * (1 << n);
} 
*)

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
  (* pre-conditions *)
  ( S n <= k )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary c ->
  (* post-conditions *)
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
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

Instance wgen (n: nat) : t n.
Admitted.

End ModSumThree.

Module _BigAdd.
(* template BigAdd(n, k) {
    assert(n <= 252);
    signal input a[k];
    signal input b[k];
    signal output out[k + 1];

    component unit0 = ModSum(n);
    unit0.a <== a[0];
    unit0.b <== b[0];
    out[0] <== unit0.sum;

    component unit[k - 1];
    for (var i = 1; i < k; i++) {
        unit[i - 1] = ModSumThree(n);
        unit[i - 1].a <== a[i];
        unit[i - 1].b <== b[i];
        if (i == 1) {
            unit[i - 1].c <== unit0.carry;
        } else {
            unit[i - 1].c <== unit[i - 2].carry;
        }
        out[i] <== unit[i - 1].sum;
    }
    out[k] <== unit[k - 2].carry;
} *)

Variables a b carry: F.
Variable n: nat.
Check (ex_proj1 (exists (w: ModSumThree.t n),
      w.(ModSumThree.a) = a /\ w.(ModSumThree.b) = b /\ w.(ModSumThree.c) = carry)).

Print mapi_with.
Definition cons (n k: nat) (a b: tuple F k) (out: tuple F (S k)) :=
  mapi_with (fun i '(carry, _cons) '(a,b) =>
    exists (w: ModSumThree.t n),
      w.(ModSumThree.a) = a /\ w.(ModSumThree.b) = b /\ w.(ModSumThree.c) = carry /\
      

  



End _BigAdd.

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