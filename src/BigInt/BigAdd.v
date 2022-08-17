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

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.


Require Import Util DSL.
Require Import Circom.Circom Circom.Default.
Require Import Circom.LibTactics.
Require Import Circom.Tuple.
Require Import Circom.circomlib.Bitify Circom.circomlib.Comparators.
Require Import Circom.ListUtil.

(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigAdd (C: CIRCOM).
Context {n: nat}.

Module B := Bitify C.
Module Cmp := Comparators C.
Import B C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

(* x is a valid digit in base-2^n representation *)
Local Notation "x | ( n )" := (in_range n x) (at level 40).
Local Notation "xs |: ( n )" := (tforall (in_range n) xs) (at level 40).

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (as_le n xs).
Local Notation "[|| xs ||]" := (as_le n (to_list _ xs)).

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


Create HintDb F_pow.
Hint Rewrite @F.pow_2_r : F_pow.
Hint Rewrite @F.pow_add_r : F_pow.
Hint Rewrite @F.pow_mul_l : F_pow.
Hint Rewrite <- @F.pow_pow_l : F_pow.
Hint Rewrite @F.pow_1_r : F_pow.
Hint Rewrite @F.pow_3_r : F_pow.

Create HintDb simplify_F discriminated.
Hint Rewrite (Fmul_0_r) : simplify_F.
Hint Rewrite (Fmul_0_l) : simplify_F.
Hint Rewrite (Fmul_1_r) : simplify_F.
Hint Rewrite (Fmul_1_l) : simplify_F.
Hint Rewrite (Fadd_0_r) : simplify_F.
Hint Rewrite (Fadd_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_r) : simplify_F.
Hint Rewrite (@F.pow_1_l) : simplify_F.
Hint Rewrite (@F.pow_1_r) : simplify_F.
Hint Rewrite (Nat.mul_1_l) : simplify_F.
Hint Rewrite <- (Nat2N.inj_mul) : simplify_F.


Lemma fold_nth {T} `{Default T}: forall (i:nat) d l,
  i < length l ->
  List.nth i l d = List_nth_Default i l.
Proof. intros. unfold List_nth_Default. rewrite nth_default_eq. erewrite nth_oblivious; eauto.  Qed.

Ltac unfold_default := unfold List_nth_Default; rewrite nth_default_eq.
Ltac fold_default := rewrite fold_nth; try lia.
Ltac simpl_default := repeat unfold_default; simpl; repeat fold_default; try lia.
Ltac default_apply L := repeat unfold_default; L; repeat fold_default; try lia.



Lemma nth_Default_List_tuple {T n} `{Default T} (xs: tuple T n) i:
  (to_list n xs) ! i = xs [i].
Proof.
  unfold List_nth_Default. unfold nth_Default, nth. rewrite nth_default_to_list. reflexivity.
Qed.


Module ModSumThree.

Section ModSumThree.

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
  exists (n2b: Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits._out) [n] /\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

Definition spec (w: t) :=
  (* pre-conditions *)
  ( S n <= C.k )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary w.(c) ->
  (* post-conditions *)
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
  w.(sum) | (n) /\
  binary w.(carry).

Lemma add_0_r: forall (x z: F), z = 0 -> x + z= x.
Proof. unwrap_C. intros. fqsatz. Qed.

Ltac unwrap_Default H _default := rewrite nth_Default_nth_default in H; unfold default in H; cbn [_default] in H.
Ltac unwrap_Default_goal _default := rewrite nth_Default_nth_default; unfold default; cbn [_default].

Theorem soundness: forall w, spec w.
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
  remember (Num2Bits._out [n] ) as out_n. pose proof (length_to_list Num2Bits._out).
  pose proof (Num2Bits.soundness _ n2b) as H_n2b. unfold Num2Bits.spec, repr_le2 in *.
  rewrite <- H_in.
  pose proof H_n2b as H_n2b'. unfold repr_le in H_n2b. destruct H_n2b as [_ [_ H_as_le] ].
  rewrite H_as_le.
  erewrite as_le_split_last; eauto.

  rewrite nth_Default_List_tuple.
  rewrite <- Heqout_n.
  autorewrite with simplify_F.
  
  replace (as_le 1 ((to_list (S n) Num2Bits._out)[:n]) + (1 + 1) ^ n * out_n -
    out_n * (1 + 1) ^ n) with (as_le 1 (firstn n (to_list (S n) Num2Bits._out))) by fqsatz.
  eapply repr_le_ub; try lia.
  eapply repr_le_firstn; eauto.
  rewrite firstn_length_le; lia.
  rewrite H. auto.

  - rewrite H_carry.
  pose proof (Num2Bits.soundness _ n2b) as H_n2b. 
  unfold Num2Bits.spec, repr_le2, repr_le in *.
  intuition.
  rewrite <- nth_Default_List_tuple. unfold_default.
  apply Forall_nth.
  apply Forall_in_range.
  auto. 
  lia.
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance ModSumThree_default : Default (ModSumThree.t) := { default := wgen }.

End ModSumThree.
End ModSumThree.



Module _BigAdd.

Context {k: nat}.

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

Module D := DSL C.

Module M := ModSumThree.

Definition cons (a b: tuple F k) (out: tuple F (S k)) :=
  exists (unit: tuple M.t k),
  D.iter (fun i _cons =>
    _cons /\
    unit [i].(M.a) = a [i] /\
    unit [i].(M.b) = b [i] /\
    (if (dec (i = 0%nat)) then
    unit [i].(M.c) = 0
    else
    unit [i].(M.c) = unit [i-1].(M.carry)) /\
    out [i] = unit [i].(M.sum)
    ) k True /\ 
  out [k] = unit [k-1].(M.carry).


Record t := {
  a: tuple F k;
  b: tuple F k;
  out: tuple F (S k);
  _cons: cons a b out
}.

Definition spec (w: t) :=
  (* pre-condition *)
  (n> 0)%Z ->
  (k > 0)%Z ->
  (S n <= C.k)%Z ->
  w.(a) |: (n) ->
  w.(b) |: (n) ->
  (* post-condition *)
  [|| w.(out) ||] = [|| w.(a) ||] + [|| w.(b) ||] /\
  w.(out) |: (n).



Create HintDb simplify_F discriminated.
Hint Rewrite (Fmul_0_r) : simplify_F.
Hint Rewrite (Fmul_0_l) : simplify_F.
Hint Rewrite (Fmul_1_r) : simplify_F.
Hint Rewrite (Fmul_1_l) : simplify_F.
Hint Rewrite (Fadd_0_r) : simplify_F.
Hint Rewrite (Fadd_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_l) : simplify_F.
Hint Rewrite (@F.pow_0_r) : simplify_F.
Hint Rewrite (@F.pow_1_l) : simplify_F.
Hint Rewrite (@F.pow_1_r) : simplify_F.
Hint Rewrite (@F.pow_add_r) : simplify_F.
Hint Rewrite <- (Nat2N.inj_mul) : natsimplify.
Hint Rewrite (Nat.mul_1_l) : natsimplify.
Hint Rewrite (Nat.mul_1_r): natsimplify.
Hint Rewrite (Nat.mul_0_l): natsimplify.
Hint Rewrite (Nat.mul_0_r): natsimplify.
Hint Rewrite (Nat.add_0_r): natsimplify.
Hint Rewrite (Nat.add_0_l): natsimplify.
Hint Rewrite (Nat.mul_succ_r): natsimplify.


Ltac split_as_le xs i := 
  erewrite as_le_split_last with (ws:=xs[:S i]) (i:=i);
  try rewrite firstn_firstn; autorewrite with natsimplify;
  try rewrite firstn_nth by lia.


Ltac lift_to_list := repeat match goal with
| [H: context[nth_Default _ _] |- _] => rewrite <-nth_Default_List_tuple in H; try lia
| [ |- context[nth_Default _ _] ] => rewrite <-nth_Default_List_tuple; try lia
| [H: tforall _ _ |- _] => apply tforall_Forall in H
| [ |- tforall _ _] => apply tforall_Forall
end.

Lemma binary_in_range: forall n x,
  (n > 0)%nat ->
  binary x -> x | (n).
Proof.
  unwrap_C. intros n x Hn Hbin. unfold in_range.
  destruct (dec (n>1)).
  destruct Hbin; subst; autorewrite with F_to_Z. lia.
  assert (2^1 < 2^n)%Z. apply Zpow_facts.Zpower_lt_monotone. lia. lia.
  transitivity (2^1)%Z. simpl. lia. lia. lia.
  assert (n=1)%nat by lia. subst. simpl. destruct Hbin; subst; autorewrite with F_to_Z; lia.
Qed.

Local Notation "' xs" := (to_list _ xs) (at level 20).

Theorem soundness: forall (w: t), spec w.
Proof.
  unwrap_C.
  intros. destruct w as [a b out _cons]. unfold spec.
  intros. cbn [_BigAdd.out _BigAdd.a _BigAdd.b] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  lift_to_list.
  remember (fun (i : nat) (_cons : Prop) =>
      _cons /\
      M.a (unit [i] ) = a [i] /\
      M.b (unit [i] ) = b [i] /\
      (if dec (i = 0%nat)
      then M.c (unit [i] ) = 0
      else M.c (unit [i] ) = M.carry (unit [i - 1] )) /\
      out [i] = M.sum (unit [i] )) as f.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_k].
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
    (* carry bits are binary *)
    (forall (j: nat), j < i -> binary (('unit ! j).(M.carry))) /\
    (* out are in range *)
    Forall (in_range n) ('out [:i]) /\
    (* addition is ok for prefix *)
    [| 'out [:i] |] +  2^(n*i)%nat * (if dec (i = 0)%nat then 0 else ('unit ! (i-1)).(M.carry))
      = [| 'a [:i] |] +  [| 'b [:i] |]).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + simpl. constructor.
    + destruct (dec (0=0)%nat). simpl. fqsatz. lia.
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    lift_to_list.
    pose proof (ModSumThree.soundness ('unit ! i )) as M0. unfold ModSumThree.spec in M0.
    destruct IH as [IH_bin IH_eq]. auto.
    destruct M0 as [M_eq [M_sum M_bin] ]. lia.
    rewrite Hai. unfold_default. apply Forall_nth. auto. lia.
    rewrite Hbi. unfold_default. apply Forall_nth. auto. lia.
    destruct (dec (i=0%nat)). rewrite Hci. left. fqsatz.
    rewrite Hci. apply IH_bin. lia.
    destruct (dec (S i = 0%nat)). discriminate.
    split_as_le ('out) i. split_as_le ('a) i. split_as_le ('b) i.
    intuition idtac.
    (* binary *)
    + destruct (dec (j < i)). auto.
      assert (Hij: j=i) by lia. rewrite Hij in *. intuition.
    (* out[:i] |: (n) *)
    + eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le; eauto. lia.
      rewrite firstn_firstn. autorewrite with natsimplify. auto.
      rewrite firstn_nth by lia.
      fold_default. rewrite Houti. auto.
    + destruct (dec (i=0%nat)) as [].
      * (* i = 0 *) rewrite e in *.
        autorewrite with simplify_F natsimplify.
        repeat erewrite firstn_1; try lia.
        repeat fold_default.
        fqsatz.
      * (* i > 0 *) 
        rewrite Nat2N.inj_add. autorewrite with natsimplify simplify_F.
        repeat (unfold_default; rewrite firstn_nth; try lia; fold_default).
        default_apply ltac:(repeat rewrite firstn_nth; try lia).
        fqsatz.
    + eapply repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using repr_trivial.
    + eapply repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using repr_trivial.
    + unfold repr_le. intuition. rewrite firstn_length_le; lia.
      eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le. reflexivity. lia.
      rewrite firstn_firstn. autorewrite with natsimplify. auto.
      rewrite firstn_nth by lia.
      fold_default.
      rewrite Houti. auto.
  - unfold Inv in HInv.
    replace ('a) with ('a[:k]) by (applys_eq firstn_all; f_equal; lia).
    replace ('b) with ('b[:k]) by (applys_eq firstn_all; f_equal; lia).
    destruct (dec (k=0)%nat). lia.
    assert (H_out_inrange: Forall (in_range n) (' out)). {
      intuition.
      apply Forall_firstn_S with (i:=k) (d:=0); try eauto.
    fold_default. apply binary_in_range; try lia. rewrite out_k. apply H5; lia.
    }
    intuition; auto.
    * rewrite <- H7. rewrite <- out_k.
    apply as_le_split_last with (x:=[|' out|]).
    applys_eq repr_trivial; auto.
    * lift_to_list. auto.
  Unshelve. exact F.zero. exact F.zero. exact F.zero.
Qed.


End _BigAdd.

End BigAdd.
