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

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigAdd.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.


Module ModSumThree.
Section ModSumThree.
Context {n: nat}.
Import B R.

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
  exists (n2b: @Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits.out) [n] /\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

Lemma add_sub: forall (x y: F), x + y - y = x.
Proof. unwrap_C. intros. fqsatz. Qed.

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
  apply R.in_range_binary in Hc.
  intuition.
  - fqsatz.
  - subst.
  remember (Num2Bits.out [n] ) as out_n. pose proof (length_to_list Num2Bits.out).
  pose proof (Num2Bits.soundness n2b) as H_n2b. unfold repr_le2 in *.
  rewrite <- H_in.
  pose proof H_n2b as H_n2b'. unfold repr_le in H_n2b. destruct H_n2b as [_ [_ H_as_le] ].
  rewrite H_as_le.
  erewrite as_le_split_last; eauto.

  lift_to_list.
  rewrite <- Heqout_n.
  simplify.
  match goal with
  | [ |- context[?x + ?y - ?z] ] => replace (x+y-z) with x by fqsatz
  end.
  eapply repr_le_ub; try lia.
  eapply repr_le_firstn; eauto.
  rewrite firstn_length_le; lia.
  rewrite H. auto.
  - rewrite H_carry.
  pose proof (Num2Bits.soundness n2b) as H_n2b. 
  unfold repr_le2, repr_le in *.
  intuition.
  lift_to_list. unfold_default.
  apply Forall_nth; try lia.
  apply Forall_in_range.
  auto.
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance Default : Default (ModSumThree.t) := { default := wgen }.

End ModSumThree.
End ModSumThree.

Module M := ModSumThree.

Section _BigAdd.
Context {n k: nat}.

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

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Local Notation "[|| xs ||]" := (RZ.as_le n ('xs)).

Definition cons (a b: tuple F k) (out: tuple F (S k)) :=
  exists (unit: tuple (@M.t n) k),
  D.iter (fun i _cons =>
    _cons /\
    unit [i].(M.a) = a [i] /\
    unit [i].(M.b) = b [i] /\
    (if (dec (i = 0)%nat) then
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
  n > 0 ->
  k > 0 ->
  (n + 1 <= C.k)%Z ->
  (* a and b are proper big int *)
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  (* post-condition *)
  ([|| w.(out) ||] = [|| w.(a) ||] + [|| w.(b) ||])%Z /\
  'w.(out) |: (n).

Ltac split_as_le xs i := 
  erewrite RZ.as_le_split_last with (ws:=xs[:S i]) (i:=i);
  try rewrite firstn_firstn; simplify;
  try rewrite firstn_nth by lia.

Lemma nth_0 {T} `{Default T}: forall (x: T), (x :: nil) ! 0 = x.
Proof. intro x. erewrite <- fold_nth with (d:=x); auto. Qed.

Theorem soundness: forall (w: t), spec w.
Proof.
  unwrap_C.
  intros. destruct w as [a b out _cons]. unfold spec.
  intros. cbn [_BigAdd.out _BigAdd.a _BigAdd.b] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  lift_to_list.
  rem_iter.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_k].
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
    (* carry bits are binary *)
    (forall (j: nat), j < i -> binary (('unit ! j).(M.carry))) /\
    (* out are in range *)
    ('out [:i]) |: (n) /\
    (* addition is ok for prefix *)
    (([| 'out [:i] |] +  2^(n*i)%nat * (if dec (i = 0)%nat then 0 else F.to_Z ('unit ! (i-1)).(M.carry))
      = [| 'a [:i] |] +  [| 'b [:i] |]))%Z).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + simpl. constructor.
    + destruct (dec (0=0)%nat). simpl. nia. lia.
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    symmetry in Houti.
    lift_to_list.
    pose proof (ModSumThree.soundness ('unit ! i )) as M0.
    destruct IH as [IH_bin IH_eq]. auto.
    destruct M0 as [M_eq [M_sum M_bin] ]. lia.
    rewrite Hai. unfold_default. apply Forall_nth. auto. lia.
    rewrite Hbi. unfold_default. apply Forall_nth. auto. lia.
    destruct (dec (i=0%nat)). rewrite Hci. left. fqsatz.
    rewrite Hci. apply IH_bin. lia.
    destruct (dec (S i = 0%nat)). discriminate.
    split_as_le ('out) i. split_as_le ('a) i. split_as_le ('b) i.
    repeat (apply conj_use; split); intuition idtac.
    (* binary *)
    + destruct (dec (j < i)). auto.
      assert (Hij: j=i) by lia. rewrite Hij in *. intuition.
    (* out[:i] |: (n) *)
    + eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le; eauto. lia.
      rewrite firstn_firstn. autorewrite with natsimplify. auto.
      rewrite firstn_nth by lia.
      fold_default. rewrite <- Houti. auto.
    + 
      (* push if-then-else inside equality *)
      assert (Hci': M.c ('unit!i) = if dec (i=0)%nat then 0 else M.carry ('unit!(i-1)))
        by (destruct (dec (i=0)%nat); auto).
      clear Hci.
      rewrite Hai, Hbi, Hci', Houti in *. clear Hai Hbi Hci' Houti.
      remember (M.carry ('unit!i)) as ci.
      remember (M.carry ('unit!(i-1))) as ci'.
      (* prepare ranges *)
      assert (0 <= |^ 'a!i|)%Z. apply F.to_Z_range; lia.
      assert (0 <= |^ 'b!i|)%Z. apply F.to_Z_range; lia.
      assert (0 <= |^ 'out!i|)%Z. apply F.to_Z_range; lia.
      assert (|^ 'a ! i | <= 2^n-1)%Z. erewrite <- fold_nth; try lia. apply Forall_nth; auto. lia.
      assert (|^ 'b ! i | <= 2^n-1)%Z. erewrite <- fold_nth; try lia. apply Forall_nth; auto. lia.
      assert (|^ 'out ! i | <= 2^n-1)%Z. auto.
      assert (2*2^n <= 2^C.k)%Z. replace (2*2^n)%Z with (2^(n+1))%Z. apply Zpow_facts.Zpower_le_monotone; try lia. rewrite Zpower_exp; try lia.
      assert (Hci_bin: (0 <= |^ci| <= 1)%Z). destruct M_bin as [M_bin|M_bin]; rewrite M_bin in *; autorewrite with F_to_Z; lia.
      assert (Hci'_bin: (0 <= |^ci'| <= 1)%Z). specialize (H4 (i-1)%nat). destruct H4 as [M_bin'|M_bin']; try lia; rewrite Heqci', M_bin' in *; autorewrite with F_to_Z; lia.
      (* push F.to_Z *)
      assert (Hl: (|^' out ! i + (1 + 1) ^ n * ci| = |^'out!i| + 2^n*|^ci|)%Z). repeat (autorewrite with F_to_Z; cbn -[to_list F.pow]; try lia; try nia).
      assert (Hr: (|^' a ! i + ' b ! i + (if dec (i = 0)%nat then 0 else ci')| 
        = |^'a!i| + |^'b!i| + |^(if dec (i = 0)%nat then 0 else ci')|)%Z). 
        { destruct (dec (i=0)%nat); simplify; repeat (autorewrite with F_to_Z; try lia; try nia). }
      symmetry in Hl, Hr, M_eq.
      apply f_equal with (f:=F.to_Z) in M_eq.
      destruct (dec (i=0%nat)) as []; simplify' M_eq; simplify' Hl; simplify' Hr.
      * rewrite e in *. simplify. unfold RZ.ToZ.to_Z.
        repeat erewrite firstn_1; try lia.
        repeat (fold_default; rewrite nth_0).
      * simplify.
        default_apply ltac:(repeat (rewrite firstn_nth; try lia)).
        unfold RZ.ToZ.to_Z.
        default_apply ltac:(repeat rewrite firstn_nth; try lia).
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + unfold RZ.repr_le. intuition. rewrite firstn_length_le; lia.
      eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le. reflexivity. lia.
      rewrite firstn_firstn. simplify. auto.
      rewrite firstn_nth by lia.
      fold_default.
      rewrite <- Houti. auto.
  - unfold Inv in HInv.
    replace ('a) with ('a[:k]) by (applys_eq firstn_all; f_equal; lia).
    replace ('b) with ('b[:k]) by (applys_eq firstn_all; f_equal; lia).
    destruct (dec (k=0)%nat). lia.
    assert (H_out_inrange: 'out |: (n)). {
      intuition.
      apply Forall_firstn_S with (i:=k) (d:=0); try eauto.
      fold_default. apply binary_in_range; try lia. rewrite out_k. apply H5; lia.
    }
    intuition; auto.
    rewrite <- H7. rewrite <- out_k.
    simplify.
    apply RZ.as_le_split_last with (x:=[|' out|]).
    applys_eq RZ.repr_trivial; auto.
  Unshelve. exact F.zero. exact F.zero. exact F.zero. exact F.zero. exact F.zero. 
Qed.

End _BigAdd.
End BigAdd.
