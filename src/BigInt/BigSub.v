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
Require Import Circom.Repr Circom.ReprZ.

(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigSub (C: CIRCOM).
Context {n: nat}.

Module B := Bitify C.
Module RZUnsigned := ReprZUnsigned C.
Module RZ := RZUnsigned.RZ.
Module R := Repr C.
Module Cmp := Comparators C.
Import B C.
Import Cmp C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Module Comparators := Comparators C.
Create HintDb F_to_Z discriminated.
#[local] Hint Rewrite (to_Z_2) : F_to_Z.
#[local] Hint Rewrite (@F.to_Z_add q) : F_to_Z.
#[local] Hint Rewrite (@F.to_Z_mul q) : F_to_Z.
#[local] Hint Rewrite (@F.to_Z_pow q) : F_to_Z.
#[local] Hint Rewrite (@F.to_Z_0 q) : F_to_Z.
#[local] Hint Rewrite (@F.to_Z_1 q) : F_to_Z.
#[local] Hint Rewrite (@F.pow_1_r q) : F_to_Z.
#[local] Hint Rewrite Cmp.LessThan.to_Z_sub : F_to_Z.
#[local] Hint Rewrite Cmp.LessThan.to_Z_add : F_to_Z.
#[local] Hint Rewrite Z.mod_small : F_to_Z.


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


Create HintDb simplify_F discriminated.
#[local] Hint Rewrite (Fmul_0_r) : simplify_F.
#[local] Hint Rewrite (Fmul_0_l) : simplify_F.
#[local] Hint Rewrite (Fmul_1_r) : simplify_F.
#[local] Hint Rewrite (Fmul_1_l) : simplify_F.
#[local] Hint Rewrite (Fadd_0_r) : simplify_F.
#[local] Hint Rewrite (Fadd_0_l) : simplify_F.
#[local] Hint Rewrite (@F.pow_0_l) : simplify_F.
#[local] Hint Rewrite (@F.pow_0_r) : simplify_F.
#[local] Hint Rewrite (@F.pow_1_l) : simplify_F.
#[local] Hint Rewrite (@F.pow_1_r) : simplify_F.
#[local] Hint Rewrite (@F.pow_add_r) : simplify_F.
Create HintDb simplify_NZ discriminated.
#[local] Hint Rewrite Nat2N.inj_mul : simplify_NZ.
#[local] Hint Rewrite Nat2N.inj_add : simplify_NZ.
#[local] Hint Rewrite Nat2Z.inj_mul : simplify_NZ.
#[local] Hint Rewrite Nat2Z.inj_add : simplify_NZ.
#[local] Hint Rewrite (Nat.mul_1_l) : simplify_NZ.
#[local] Hint Rewrite (Nat.mul_1_r): simplify_NZ.
#[local] Hint Rewrite (Nat.mul_0_l): simplify_NZ.
#[local] Hint Rewrite (Nat.mul_0_r): simplify_NZ.
#[local] Hint Rewrite (Nat.add_0_r): simplify_NZ.
#[local] Hint Rewrite (Nat.add_0_l): simplify_NZ.
#[local] Hint Rewrite (Nat.mul_succ_r): simplify_NZ.
#[local] Hint Rewrite (Z.mul_1_l) : simplify_NZ.
#[local] Hint Rewrite (Z.mul_1_r): simplify_NZ.
#[local] Hint Rewrite (Z.mul_0_l): simplify_NZ.
#[local] Hint Rewrite (Z.mul_0_r): simplify_NZ.
#[local] Hint Rewrite (Z.add_0_r): simplify_NZ.
#[local] Hint Rewrite (Z.add_0_l): simplify_NZ.
#[local] Hint Rewrite (Z.mul_succ_r): simplify_NZ.
#[local] Hint Rewrite (Zpower_exp): simplify_NZ.

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

Module ModSubThree.

Section ModSubThree.

Import R.


(* 
// a - b - c
// assume a - b - c + 2**n >= 0
template ModSubThree(n) {
    assert(n + 2 <= 253);
    signal input a;
    signal input b;
    signal input c;
    assert(a - b - c + (1 << n) >= 0);
    signal output out;
    signal output borrow;
    signal b_plus_c;
    b_plus_c <== b + c;
    component lt = LessThan(n + 1);
    lt.in[0] <== a;
    lt.in[1] <== b_plus_c;
    borrow <== lt.out;
    out <== borrow * (1 << n) + a - b_plus_c;
}
*)

Definition cons (a b c out borrow: F) :=
  exists (lt: @LessThan.t (S n)),
    let b_plus_c := b + c in
    lt.(LessThan._in) [0] = a /\
    lt.(LessThan._in) [1] = b_plus_c /\
    borrow = lt.(LessThan.out) /\
    out = borrow * 2^n + a - b_plus_c /\
    a - b - c + 2^n >=z 0.

Record t : Type := {
  a: F; b: F; c: F;
  out: F; borrow: F;
  _cons: cons a b c out borrow;
}.

Definition spec (w: t) :=
  (* pre-conditions *)
  ( S n <= C.k - 1 )%Z ->
    (* a and b are n-bits, i.e., <= 2^n-1 *)
    w.(a) | (n) -> 
    w.(b) | (n) -> 
    binary w.(c) ->
  ( w.(a) - w.(b) - w.(c) + 2^n >=z 0 ) /\
  (* post-conditions *)
  w.(out) - w.(borrow) * 2^n = w.(a) - w.(b) - w.(c) /\
  w.(out) | (n) /\
  binary w.(borrow).

Lemma add_0_r: forall (x z: F), z = 0 -> x + z = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Ltac unwrap_Default H _default := rewrite nth_Default_nth_default in H; unfold default in H; cbn [_default] in H.
Ltac unwrap_Default_goal _default := rewrite nth_Default_nth_default; unfold default; cbn [_default].

Theorem soundness: forall w, spec w.
Proof.
  unwrap_C. intros.
  destruct w as [a b c out borrow _cons].
  unfold spec, cons in *. destruct _cons as [lt [H_in0 [H_in1 [H_borrow [H_out H_assert]]] ] ].
  simpl. intros Hnk Ha Hb Hc. 
  unfold in_range in *. 
  apply in_range_binary in Hc.
  assert (lt_range_1: LessThan._in lt [0] <=z 2 ^ S n).
  { rewrite H_in0. rewrite Ha. replace (2 ^ (S n))%Z with (2 ^ (n + 1))%Z. 
    rewrite Zpower_exp;lia. lia. }
  assert (lt_range_2: LessThan._in lt [1] <=z 2 ^ S n).
  { rewrite H_in1. apply in_range_binary in Hc. destruct Hc;subst;
    autorewrite with simplify_F simplify_NZ. 
    + rewrite Hb. replace (2 ^ (S n))%Z with (2 ^ (n + 1))%Z. rewrite Zpower_exp;lia. lia.
    + replace (2 ^ (S n))%Z with (2 ^ (n + 1))%Z;try lia. rewrite Zpower_exp;try lia.
      assert ((b + 1) <=z (2 ^ n)). 
      { repeat (autorewrite with F_to_Z; try lia; try nia).
        replace (|^ b | + 1)%Z with (|^ b + 1|).
        2:{
          simpl;repeat rewrite Z.mod_small;try lia. 
          pose proof (@F.to_Z_range q b). destruct H;try lia. split;try lia.
          assert((2 ^ n - 1) < 2 ^ k)%Z;try lia.
          assert (n+2 <= k)%Z. lia.
          assert(2^(n+2) <= 2^k)%Z. apply Zpow_facts.Zpower_le_monotone; lia.
          autorewrite with simplify_NZ in *;lia.
        }
        apply F.to_Z_range;lia. }
      rewrite H;lia. }
  pose proof (LessThan.soundness lt Hnk lt_range_1 lt_range_2) as [H_lt_b H_lt].
  intuition;auto; try fqsatz.
  - subst.
    unfold in_range in *. 
    rewrite H_in1 in *.
    destruct (dec (LessThan.out lt = 1)).
    + rewrite e. 
      assert ((|^ LessThan._in lt [0] |) - (|^b| + |^c|) <= -1)%Z. skip. (* TODO *)
      assert (1 * (1 + 1) ^ n = (2 ^ n)). fqsatz. 
      rewrite H0. skip. (* TODO *)
    + assert(LessThan.out lt = 0).
      {
      apply R.binary_Z in H_lt_b. destruct H_lt_b;try easy. 
      2:{ exfalso. apply n0. replace 1%Z with (@F.to_Z q 1) in H. rewrite <- F.eq_to_Z_iff in H;auto. eapply F.to_Z_1. }
          replace 0%Z with (@F.to_Z q 0) in H. rewrite <- F.eq_to_Z_iff in H;auto. eapply F.to_Z_0. }
      rewrite H. autorewrite with simplify_F simplify_NZ. skip. (* TODO *)
  - rewrite H_borrow;auto.
Unshelve. lia.
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance ModSubThree_default : Default (ModSubThree.t) := { default := wgen }.

End ModSubThree.
End ModSubThree.


Module _BigSub.

Context {k: nat}.

(* /*
Inputs:
    - BigInts a, b
    - Assume a >= b
Output:
    - BigInt out = a - b
    - underflow = how much is borrowed at the highest digit of subtraction, only nonzero if a < b
*/
template BigSub(n, k) {
    assert(n <= 252);
    signal input a[k];
    signal input b[k];
    signal output out[k];
    signal output underflow;

    component unit0 = ModSub(n);
    unit0.a <== a[0];
    unit0.b <== b[0];
    out[0] <== unit0.out;

    component unit[k - 1];
    for (var i = 1; i < k; i++) {
        unit[i - 1] = ModSubThree(n);
        unit[i - 1].a <== a[i];
        unit[i - 1].b <== b[i];
        if (i == 1) {
            unit[i - 1].c <== unit0.borrow;
        } else {
            unit[i - 1].c <== unit[i - 2].borrow;
        }
        out[i] <== unit[i - 1].out;
    }
    underflow <== unit[k - 2].borrow;
} *)

Module D := DSL C.

Module M := ModSubThree.

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Local Notation "[|| xs ||]" := (RZ.as_le n (to_list _ xs)).

Definition cons (a b: tuple F k) (out: tuple F k) (underflow: F) :=
  exists (unit: tuple M.t k),
  D.iter (fun i _cons =>
    _cons /\
    unit [i].(M.a) = a [i] /\
    unit [i].(M.b) = b [i] /\
    (if (dec (i = 0%nat)) then
    unit [i].(M.c) = 0
    else
    unit [i].(M.c) = unit [i-1].(M.borrow)) /\
    out [i] = unit [i].(M.out)
    ) k True /\ 
  underflow = unit [k-1].(M.borrow).


Record t := {
  a: tuple F k;
  b: tuple F k;
  out: tuple F k;
  underflow: F;
  _cons: cons a b out underflow
}.

Definition spec (w: t) :=
  (* pre-condition *)
  (n > 0)%Z ->
  (k > 0)%Z ->
  (S n <= C.k - 1)%Z ->
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  ([|| w.(a) ||] >= [|| w.(b) ||])%Z ->
  (* post-condition *)
  ([|| w.(out) ||] = [|| w.(a) ||] - [|| w.(b) ||])%Z /\
  ( w.(underflow) = 0) /\
  'w.(out) |: (n).


Ltac simplify := autorewrite with simplify_NZ simplify_F natsimplify; try lia.
Ltac simplify' H := autorewrite with simplify_NZ simplify_F natsimplify in H; try lia.


Ltac split_as_le xs i := 
  erewrite RZ.as_le_split_last with (ws:=xs[:S i]) (i:=i);
  try rewrite firstn_firstn; simplify;
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

Lemma nth_0 {T} `{Default T}: forall (x: T), (x :: nil) ! 0 = x.
Proof.
  intro x.
  erewrite <- fold_nth with (d:=x);eauto. 
Qed.

Theorem soundness: forall (w: t), spec w.
Proof.
  unwrap_C.
  intros. destruct w as [a b out underflow _cons]. unfold spec.
  intros. cbn [_BigSub.out _BigSub.a _BigSub.b _BigSub.underflow] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  lift_to_list.
  remember (fun (i : nat) (_cons : Prop) =>
      _cons /\
      M.a (unit [i] ) = a [i] /\
      M.b (unit [i] ) = b [i] /\
      (if dec (i = 0%nat)
      then M.c (unit [i] ) = 0
      else M.c (unit [i] ) = M.borrow (unit [i - 1] )) /\
      out [i] = M.out (unit [i] )) as f.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_borrow].
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
    (* borrow bits are binary *)
    (forall (j: nat), j < i -> binary (('unit ! j).(M.borrow))) /\
    (* out are in range *)
    'out [:i] |: (n) /\
    (* addition is ok for prefix *)
    ([| 'out [:i] |] = [| 'a [:i] |] -  [| 'b [:i] |])%Z).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + simpl. constructor.
    (* + destruct (dec (0=0)%nat). simpl. nia. lia. *)
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    lift_to_list.
    pose proof (ModSubThree.soundness ('unit ! i )) as M0. unfold ModSubThree.spec in M0.
    destruct IH as [IH_bin IH_eq]. auto.
    destruct M0 as [M_rng M_eq]; try lia.
    { rewrite Hai. unfold_default. apply Forall_nth. auto. lia. }
    { rewrite Hbi. unfold_default. apply Forall_nth. auto. lia. }
    { destruct (dec (i=0%nat)). rewrite Hci. left. fqsatz.
      rewrite Hci. apply IH_bin. lia. }
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
        simplify.
        repeat erewrite firstn_1; try lia.
        repeat (fold_default; rewrite nth_0).
        (* range proof *)
        assert (|^'out!0| = |^'a!0| - |^'b!0|)%Z by admit.
        unfold RZ.ToZ.to_Z.
        (* TODO: simplify this *)
        nia.
      * (* i > 0 *) 
        simplify.
        repeat (unfold_default; rewrite firstn_nth; try lia; fold_default).
        unfold RZ.ToZ.to_Z.
        default_apply ltac:(repeat rewrite firstn_nth; try lia).
        (* range proof *)
        assert (|^'out!i| = |^'a!i| - |^'b!i|)%Z by admit.
        nia.
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + unfold RZ.repr_le. intuition. rewrite firstn_length_le; lia.
      eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le. reflexivity. lia.
      rewrite firstn_firstn. simplify. auto.
      rewrite firstn_nth by lia.
      fold_default.
      rewrite Houti. auto.
  - unfold Inv in HInv.
    replace ('a) with ('a[:k]) by (applys_eq firstn_all; f_equal; lia).
    replace ('b) with ('b[:k]) by (applys_eq firstn_all; f_equal; lia).
    destruct (dec (k=0)%nat). lia.
    assert (H_out_inrange: ' out |: (n)). {
      intuition.
      apply Forall_firstn_S with (i:=(k-1)%nat) (d:=0); try eauto. lia. 
      apply Forall_firstn. rewrite firstn_to_list in H5;auto. 
      fold_default. rewrite firstn_to_list in H5;auto. 
      rewrite Forall_nth in H5.
      unfold "!". rewrite nth_default_eq. apply H5;lia. 
    }
    intuition; auto.
    * rewrite <- H8. 
      assert (H_out: (' out) [:k] = (' out)).  
      { rewrite <- firstn_all. rewrite Hlen_out;auto. }
      rewrite H_out;auto.
    * skip. (* TODO *)
Unshelve. exact F.zero. exact F.zero. exact F.zero.
Admitted.


End _BigSub.

End BigSub.
