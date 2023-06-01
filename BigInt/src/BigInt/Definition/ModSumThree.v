
From Coq.ZArith Require Import BinInt ZArith Zdiv Znumtheory. (* import Zdiv before Znumtheory *)
From Coq.NArith Require Import NArith. 
Require Import Coq.micromega.Lia Coq.Lists.List.
From Crypto.Spec Require Import ModularArithmetic.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr.
From Circom.CircomLib Require Import Bitify.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module ModSumThree.

Module N2B := Bitify.Num2Bits.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.
Local Coercion N.of_nat: nat >-> N.
Local Coercion Z.of_nat: nat >-> Z.

Section _ModSumThree.
Context {n: nat}.

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

Definition cons (a b c sum carry: F) :=
  exists (n2b: @N2B.t (S n)),
    n2b.(N2B._in) = a + b + c /\
    carry = n2b.(N2B.out) [n] /\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance Default : Default t := { default := wgen }.

Theorem soundness: forall w,
  (* pre-conditions *)
  ( n <= C.k - 1 )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary w.(c) ->
  (* post-conditions *)
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
  w.(sum) | (n) /\
  binary w.(carry).
Proof.
  unwrap_C.
  intros c Hnk Ha Hb Hc.
  destruct c as [a b c sum carry _cons].
  simpl in *. unfold cons in *.
  destruct _cons as [n2b [H_in [H_carry H_sum] ] ].
  pose_lengths.
  apply Repr.in_range_binary in Hc.
  intuition.
  - (* sum + 2^n * carry = a + b + c *)
    fqsatz.
  - (* sum <= 2^n-1 *)
    subst.
    remember (N2B.out n2b [n] ) as out_n.
    destruct (N2B.soundness' n2b) as [N2B_range N2B_eq].
    rewrite <- H_in.
    rewrite N2B_eq.

    erewrite Repr.as_le_split_last; eauto.

    lift_to_list.
    rewrite <- Heqout_n.
    simplify.
    match goal with
    | [ |- context[?x + ?y - ?z] ] => replace (x+y-z) with x by fqsatz
    end.
    applys_eq Repr.repr_le_ub'. repeat f_equal. rewrite firstn_length_le; try lia.
    apply Forall_firstn. auto.
    rewrite firstn_length_le; lia.
  - (* carry is binary *)
    rewrite H_carry.
    destruct (N2B.soundness' n2b) as [N2B_range _].
    lift_to_list. unfold_default.
    apply Repr.in_range_binary.
    apply Forall_nth; try lia.
    auto.
Qed.

End _ModSumThree.
End ModSumThree.