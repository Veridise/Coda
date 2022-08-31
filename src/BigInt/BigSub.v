Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigSub.

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

Module ModSubThree.
Section ModSubThree.
Context {n: nat}.

Import Cmp R.

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


Local Notation "2" := (1 + 1: F).

Definition cons (a b c out borrow: F) :=
  exists (lt: @LessThan.t (S n)),
    let b_plus_c := b + c in
    lt.(LessThan._in) [0] = a /\
    lt.(LessThan._in) [1] = b_plus_c /\
    borrow = lt.(LessThan.out) /\
    out = borrow * 2^n + a - b_plus_c.

Record t : Type := {
  a: F; b: F; c: F;
  out: F; borrow: F;
  _cons: cons a b c out borrow;
}.

Lemma F_to_Z_nonneg: forall (x: F), (0 <= |^x|).
Proof. intros. apply F.to_Z_range. lia. Qed.

Theorem soundness: forall w,
  (* pre-conditions *)
  n + 2 <= C.k ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary w.(c) ->
  (* a - b - c + 2^n >= 0 *)
  (0 <= |^w.(a)| - |^w.(b)| - |^w.(c)| + 2^n) ->
  0 <= |^ w.(a) - w.(b) - w.(c) + 2^n | ->
  (* post-conditions *)
  w.(out) - w.(borrow) * 2^n = w.(a) - w.(b) - w.(c) /\
  w.(out) | (n) /\
  binary w.(borrow).
Proof.
  unwrap_C. intros w Hnk Ha Hb Hc Habc Habc'.
  assert (Hnk_pow': (0 <= 4 * 2^n <= 2^C.k)). {
    replace 4 with (2^2)%Z by lia.
    rewrite <- Zpower_exp; try lia. 
    split. lia.
    apply Zpow_facts.Zpower_le_monotone; lia.
  }
  destruct w as [a b c out borrow _cons].
  unfold cons in *. destruct _cons as [lt [H_in0 [H_in1 [H_borrow H_out]]]].
  cbn [ModSubThree.a ModSubThree.b ModSubThree.c ModSubThree.borrow ModSubThree.out] in *.

  apply in_range_binary in Hc.
  pose proof (F_to_Z_nonneg a).
  pose proof (F_to_Z_nonneg b).
  pose proof (F_to_Z_nonneg c).

  assert (lt_range_1: LessThan._in lt [0] <=z (2 ^ S n -1)). { 
    rewrite H_in0. rewrite Ha. replace (2 ^ (S n))%Z with (2 ^ (n + 1))%Z. 
    rewrite Zpower_exp;lia. lia. 
  }
  assert (lt_range_2: LessThan._in lt [1] <=z (2 ^ S n -1)). {
    rewrite H_in1.
    replace (S n) with (n+1)%nat by lia.
    rewrite Nat2Z.inj_add. simpl.
    rewrite Z.mod_small. simplify. nia.
  }
  destruct (LessThan.soundness lt) as [H_lt_b H_lt]; try lia.
  symmetry in H_borrow.
  rewrite H_in0, H_in1, H_out, H_borrow in *. clear H_in0 H_in1 H_out H_borrow.
  intuition; auto; try fqsatz.
  assert (0 <= |^ b | + |^ c | <= 2^n). { 
    pose proof (F_to_Z_nonneg b). pose proof (F_to_Z_nonneg c). lia.
  }
  destruct H_lt_b; subst borrow; split_dec; try fqsatz;
  autorewrite with F_to_Z in H_lt; simplify; try (simpl; lia).
  + repeat (autorewrite with F_to_Z; simplify; try (simpl; lia)).
  + repeat (autorewrite with F_to_Z; simplify; try (simpl; lia)). 
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance ModSubThree_default : Default (ModSubThree.t) := { default := wgen }.

End ModSubThree.
End ModSubThree.

Module M := ModSubThree.

Section _BigSub.
Context {n k: nat}.

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

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).

Definition cons (a b: tuple F k) (out: tuple F k) (underflow: F) :=
  exists (unit: tuple (@M.t n) k),
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
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  [|' w.(a) |] >= [|' w.(b) |] ->
  (* post-condition *)
  ([|' w.(out) |] = [|' w.(a) |] - [| 'w.(b) |])%Z /\
  w.(underflow) = 0 /\
  'w.(out) |: (n).

Definition spec_weak (w: t) :=
  (* pre-condition *)
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  (* post-condition *)
  ([|' w.(out) |] - |^ w.(underflow) | * 2^(n*k) = [|' w.(a) |] - [|' w.(b) |])%Z /\
  binary w.(underflow) /\
  'w.(out) |: (n).


Lemma soundness_ite: forall (w: t),
  (* pre-conditions *)
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  (* post-conditions *)
  binary w.(underflow) /\
  'w.(out) |: (n) /\
  if dec ([|'w.(a)|] >= [|'w.(b)|]) then
    w.(underflow) = 0 /\
    ([|' w.(out) |] = [|' w.(a) |] - [|' w.(b) |])%Z
  else
    w.(underflow) = 1 /\
    ([|' w.(out) |] = 2^(n*k) * |^w.(underflow) | + [|' w.(a) |] - [|' w.(b) |])%Z
  .
Admitted.

Ltac split_as_le xs i := 
  erewrite RZ.as_le_split_last with (ws:=xs[:S i]) (i:=i);
  try rewrite firstn_firstn; simplify;
  try rewrite firstn_nth by lia.


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
  rem_iter.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_borrow].
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
    (* borrow bits are binary *)
    (forall (j: nat), j < i -> binary (('unit ! j).(M.borrow))) /\
    (* borrow bits are 0 *)
    (forall (j: nat), j < i -> (('unit ! j).(M.borrow)) = 0) /\
    (* out are in range *)
    'out [:i] |: (n) /\
    (* sub is ok for prefix *)
    ([| 'out [:i] |] = [| 'a [:i] |] -  [| 'b [:i] |])%Z).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + lia.
    + simpl. constructor.
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    lift_to_list.
    pose proof (ModSubThree.soundness ('unit ! i )) as M0. 
    destruct IH as [IH_bin IH_eq]. auto.
    destruct M0 as [M_rng M_eq]; try lia.
    { rewrite Hai. unfold_default. apply Forall_nth. auto. lia. }
    { rewrite Hbi. unfold_default. apply Forall_nth. auto. lia. }
    { destruct (dec (i=0%nat)). rewrite Hci. left. fqsatz.
      rewrite Hci. apply IH_bin. lia. }
    destruct (dec (S i = 0%nat)). discriminate. 
    admit. (* TODO: modsubthree has an additional pre-condition *)
    split_as_le ('out) i. split_as_le ('a) i. split_as_le ('b) i.
    intuition idtac.
    (* binary *)
    + destruct (dec (j < i)). auto.
      assert (Hij: j=i) by lia. rewrite Hij in *. intuition.
    + destruct (dec (j < i)). auto.
      assert (Hij: j=i) by lia. rewrite Hij in *. 
      assert (M.c (' unit ! i) = 0).
      { destruct (dec (i = 0)%nat);auto. rewrite Hci. apply H5. lia. }
      rewrite H12 in *. destruct H11;subst;auto. rewrite H11 in *.
      assert ((ModSubThree.out (' unit ! i) - 1 * (1 + 1) ^ N.of_nat n) <q
              (ModSubThree.a (' unit ! i) - ModSubThree.b (' unit ! i) - 0) )%F.
      { skip. (* TODO *) } 
      rewrite H7 in H13. lia.
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
        nia.
      * (* i > 0 *) 
        simplify.
        default_apply ltac:(rewrite firstn_nth; try lia); try (rewrite firstn_length_le; try lia).
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
      apply Forall_firstn. rewrite firstn_to_list in H7;auto. 
      fold_default. rewrite firstn_to_list in H7;auto. 
      rewrite Forall_nth in H7.
      unfold "!". rewrite nth_default_eq. apply H7;lia. 
    }
    intuition; auto.
    * rewrite <- H9. 
      assert (H_out: (' out) [:k] = (' out)).  
      { rewrite <- firstn_all. rewrite Hlen_out;auto. }
      rewrite H_out;auto.
    * rewrite out_borrow. apply H5;lia.
Unshelve. exact F.zero. exact F.zero. exact F.zero.
Admitted.

Theorem soundness_weak: forall (w: t), spec_weak w.
Proof.
  unwrap_C.
  intros. destruct w as [a b out underflow _cons]. unfold spec_weak.
  intros. cbn [_BigSub.out _BigSub.a _BigSub.b _BigSub.underflow] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  lift_to_list.
  rem_iter.
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
    (* sub is ok for prefix *)
    ([| 'out [:i] |] -  2^(n*i)%nat * (if dec (i = 0)%nat then 0 else F.to_Z ('unit ! (i-1)).(M.borrow)) 
      = [| 'a [:i] |] -  [| 'b [:i] |])%Z).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + simpl. constructor.
    + destruct (dec (0=0)%nat). simpl. nia. lia.
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    lift_to_list.
    pose proof (ModSubThree.soundness ('unit ! i )) as M0.
    destruct IH as [IH_bin IH_eq]. auto.
    destruct M0 as [M_rng M_eq]; try lia.
    { rewrite Hai. unfold_default. apply Forall_nth. auto. lia. }
    { rewrite Hbi. unfold_default. apply Forall_nth. auto. lia. }
    { destruct (dec (i=0%nat)). rewrite Hci. left. fqsatz.
      rewrite Hci. apply IH_bin. lia. }
    destruct (dec (S i = 0%nat)). discriminate.
    admit. (* TODO: modsubthree has an additional pre-condition *)
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
    + assert (Hci': M.c ('unit!i) = if dec (i=0)%nat then 0 else M.borrow ('unit!(i-1)))
        by (destruct (dec (i=0)%nat); auto). rewrite Hci' in *.
      destruct (dec (i=0%nat)) as [].
      * (* i = 0 *) rewrite e in *.
        simplify.
        repeat erewrite firstn_1; try lia.
        repeat (fold_default; rewrite nth_0).
        (* range proof *)
        assert (|^'out!0| - 2 ^ n * |^ M.borrow (' unit ! 0) | = |^'a!0| - |^'b!0|)%Z by admit.
        unfold RZ.ToZ.to_Z.
        destruct (dec (1=0)%nat). discriminate.
        nia.
      * (* i > 0 *) 
        simplify.
        default_apply ltac:(repeat rewrite firstn_nth; try lia).
        (* range proof *)
        remember (M.borrow ('unit!i)) as ci.
        remember (M.borrow ('unit!(i-1))) as ci'.
        (* range proof *)
        assert (|^'out!i| - 2^n * |^ ci| = |^'a!i| - |^'b!i| - |^ ci'|)%Z by admit. 
        unfold RZ.ToZ.to_Z. 
        destruct (dec (S i = 0)%nat). discriminate.
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
      apply Forall_firstn. rewrite firstn_to_list in H4;auto. 
      fold_default. rewrite firstn_to_list in H4;auto. 
      rewrite Forall_nth in H4.
      unfold "!". rewrite nth_default_eq. apply H4;lia. 
    }
    intuition; auto.
    * rewrite <- H7. 
      assert (H_out: (' out) [:k] = (' out)).  
      { rewrite <- firstn_all. rewrite Hlen_out;auto. }
      rewrite H_out,out_borrow;auto. nia.
    * rewrite out_borrow. apply H5;lia.
Unshelve. exact F.zero. exact F.zero. exact F.zero.
Admitted.

End _BigSub.

End BigSub.