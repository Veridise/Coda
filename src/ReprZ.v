Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Crypto.Algebra.Nsatz.

Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable.
(* Require Import Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Circom.Circom Circom.DSL Circom.Util Circom.ListUtil.
Require Import Circom.Default.


Module Type TO_Z.
  Axiom to_Z: F -> Z.
  Axiom to_Z_0: to_Z 0%F = 0%Z.
  Axiom to_Z_1: to_Z 1%F = 1%Z.
  Axiom to_Z_2: to_Z (1+1)%F = 2%Z.
  Axiom to_Z_nonneg: forall x, 0 <= to_Z x.
  (* Variable add_hyp: F -> F -> Prop. *)
  (* Variable mul_hyp: F -> F -> Prop. *)
  (* Axiom to_Z_add: forall x y, add_hyp x y -> to_Z (x + y) = to_Z x + to_Z y. *)
  (* Axiom to_Z_mul: forall x y, add_hyp x y -> to_Z (x + y) = to_Z x + to_Z y.  *)
End TO_Z.


Local Coercion Z.of_nat : nat >-> Z.
Local Coercion N.of_nat : nat >-> N.

Module ReprZ (TO_Z: TO_Z).

Module ToZ := TO_Z.
Import C ToZ.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.


(* Base 2^n representations *)
Section Base2n.

(* Little- and big-endian *)
Section Endianness.

Context (n: nat).

(* interpret a list of weights as representing a little-endian base-2 number *)
Fixpoint as_le_acc (i: nat) (ws: list F) : Z :=
  match ws with
  | nil => 0
  | w::ws' => ToZ.to_Z w * 2^(n * i) + as_le_acc (S i) ws'
  end.

Lemma as_le_acc_S: forall ws i,
  as_le_acc (S i) ws = 2^n * as_le_acc i ws.
Proof.
  unwrap_C. induction ws as [| w ws]; intros; cbn [as_le_acc].
  - lia.
  - rewrite IHws.
    replace (n * S i)%Z with (n * i + n)%Z by lia.
    rewrite Zpower_exp by nia.
    lia.
Qed.

Definition as_le' := as_le_acc 0%nat.

Fixpoint as_le (ws: list F) : Z :=
  match ws with
  | nil => 0
  | w::ws' => ToZ.to_Z w + 2^n * (as_le ws')
  end.

Notation "[| xs |]" := (as_le xs).

Lemma as_le_as_le': forall ws,
  [| ws |] = as_le' ws.
Proof.
  unwrap_C. unfold as_le'.
  induction ws; simpl.
  - reflexivity.
  - rewrite as_le_acc_S, IHws, Z.mul_0_r, Z.pow_0_r.
    lia.
Qed.

(* repr func lemma: multi-step index change *)
(* Lemma as_le'_n: forall ws (i j: nat),
  as_le' (i+j)%nat ws = 2^i * as_le' j ws.
Proof.
  unwrap_C. induction i; intros; simpl.
  - rewrite F.pow_0_r. fqsatz.
  - rewrite as_le'_S. rewrite IHi.
    replace (N.pos (Pos.of_succ_nat i)) with (1 + N.of_nat i)%N.
    rewrite F.pow_add_r.
    rewrite F.pow_1_r.
    fqsatz.
    lia.
Qed. *)

Lemma as_le_app: forall ws1 ws2,
  [| ws1 ++ ws2 |] = [| ws1 |] + 2^(n * length ws1) * [| ws2 |].
Proof.
  unwrap_C. induction ws1; intros; cbn [as_le length app].
  - rewrite Z.mul_0_r, Z.pow_0_r. lia.
  - rewrite IHws1.
    remember (length ws1) as l.
    replace (n * S l) with (n * l + n) by lia.
    rewrite Zpower_exp by nia. lia.
Qed.

(* Fixpoint as_be_acc (i: nat) ws :=
  match ws with
  | nil => 0
  | w::ws' => 2^(n*i) * ToZ.to_Z w + as_be_acc (i-1)%nat ws'
  end. *)

Fixpoint as_be ws :=
  match ws with
  | nil => 0
  | w::ws' => 2^(n*length ws') * ToZ.to_Z w + as_be ws'
  end.

Lemma be__rev_le: forall l,
  as_be l = as_le (rev l).
Proof.
  unwrap_C.
  induction l.
  - reflexivity.
  - simpl. rewrite as_le_app. simpl.
    rewrite Z.mul_0_r, Z.add_0_r.
    rewrite IHl.
    rewrite rev_length.
    lia.
Qed.

Lemma le__rev_be: forall l,
  as_le l = as_be (rev l).
Proof.
  unwrap_C. intros.
  remember (rev l) as l'.
  replace l with (rev (rev l)). rewrite be__rev_le. subst. reflexivity.
  apply rev_involutive.
Qed.

End Endianness.

Section BigEndian.

(* Lemma as_be_acc_S: forall (l: list F) (n a: nat),
  a >= length l ->
  as_be_acc n (S a) l = 2^n * as_be_acc n a l.
Proof.
  induction l as [| x l]; intros.
  - simpl. autorewrite with zsimplify. reflexivity.
  - cbn [as_be_acc length] in *.
    destruct a. lia.
    replace (S a - 1)%nat with a by lia.
    replace (S (S a) - 1)%nat with (S a) by lia.
    rewrite IHl by lia.
    remember (S a) as a'.
    replace (n * S a') with (n + n * a') by lia.
    rewrite Zpower_exp by lia. lia.
Qed. *)

End BigEndian.

Section Representation.
Context (n: nat).
Notation "[| xs |]" := (as_le n xs).
Notation "[\ xs \]" := (as_be n xs).

Definition repr_le x m ws :=
  length ws = m /\
  ws |: (n) /\
  x = [| ws |].

Definition repr_be x m ws :=
  length ws = m /\
  ws |: (n) /\
  x = [\ ws \].

Lemma repr_rev: forall x m ws, repr_le x m ws <-> repr_be x m (rev ws).
Proof.
  split; intros; unfold repr_le, repr_be in *.
  - intuition.
    + rewrite rev_length. auto.
    + apply Forall_rev. auto.
    + rewrite <- le__rev_be. auto.
  - intuition.
    + rewrite <- rev_length. auto. 
    + rewrite <- rev_involutive. apply Forall_rev. auto.
    + rewrite le__rev_be. auto.
Qed.

(* repr inv: base case *)
Lemma repr_le_base: repr_le 0 0%nat nil.
Proof. unfold repr_le. intuition. Qed.

(* repr inv: invert weight list *)
Lemma repr_le_invert: forall w ws,
  repr_le [| w::ws |] (S (length ws)) (w::ws) ->
  repr_le [| ws |] (length ws) ws.
Proof.
  unfold repr_le.
  intros. intuition.
  invert H. auto.
Qed.

Lemma as_be_0: forall ws, [\ 0%F :: ws \] = [\ ws \].
Proof. 
  intros. unfold as_be. simpl. 
  rewrite to_Z_0. 
  autorewrite with natsimplify. nia.
Qed.

Lemma repr_le_last0: forall ws x n,
  repr_le x (S n) (ws ++ 0%F :: nil) ->
  repr_le x n ws.
Proof.
  unwrap_C.
  intros. rewrite repr_rev in *. rewrite rev_unit in H.
  destruct H as [H_len [ H_bin H_le] ].
  unfold repr_be. intuition idtac.
  auto.
  invert H_bin. auto.
  rewrite <- as_be_0. auto.
Qed.

Lemma repr_le_last0': forall ws x i,
  List.nth i ws 0%F = 0%F ->
  repr_le x (S i) ws ->
  repr_le x i (firstn i ws).
Proof.
  intros.
  pose proof H0 as H_repr. unfold repr_le in H0.
  apply repr_le_last0.
  rewrite <- H.
  erewrite firstn_split_last by lia.
  auto.
Qed.

(* repr inv: trivial satisfaction *)
Lemma repr_trivial: forall ws,
  ws |: (n) ->
  repr_le [| ws |] (length ws) ws.
Proof.
  induction ws; unfold repr_le; intuition idtac.
Qed.

(* repr inv: any prefix of weights also satisfies the inv *)
Lemma repr_le_prefix: forall ws1 ws2 x x1 l l1 ws,
  ws = ws1 ++ ws2 ->
  x = [| ws |] ->
  x1 = [| ws1 |] ->
  l = length ws ->
  l1 = length ws1 ->
  repr_le x l ws ->
  repr_le x1 l1 ws1.
Proof.
  unwrap_C. unfold repr_le. 
  induction ws1; intros; subst; simpl in *; intuition.
  invert H1.
  constructor; auto.
  apply Forall_app in H5. intuition.
Qed.

Lemma repr_le_firstn: forall x x' l l' ws ws' i,
  x = [| ws |] ->
  x' = [| ws' |] ->
  l' = length ws' ->
  l = length ws ->
  ws' = firstn i ws ->
  repr_le x l ws ->
  repr_le x' l' ws'.
Proof.
  intros. eapply repr_le_prefix with (ws2:=skipn i ws); subst; eauto.
  rewrite firstn_skipn. auto.
Qed.

Lemma as_le_split_last : forall i x ws,
  repr_le x (S i) ws ->
  [| ws |] = [| ws[:i] |] + 2^(n*i) * ToZ.to_Z (ws ! i).
Proof.
  unwrap_C.
  intros. pose proof H as H'.
  unfold repr_le in H. intuition.
  subst.
  assert (exists ws', ws = ws'). exists ws. reflexivity.
  destruct H1 as [ws' Hws]. pose proof Hws as Hws'.
  erewrite <- firstn_split_last with (l:=ws) (n:=i)(d:=0%F) in Hws; auto.
  pose proof (as_le_app n (ws[:i]) (ws!i::nil)).
  rewrite firstn_length_le in H1 by lia.
  replace ([| ws ! i :: nil |]) with (ToZ.to_Z (ws ! i)) in H1 by (simpl; nia).
  rewrite <- H1.
  subst.
  f_equal.
  unfold List_nth_Default. rewrite nth_default_eq. auto.
Qed.

Lemma as_be_nonneg: forall l,
  0 <= as_be n l.
Proof.
  induction l; intros; unfold as_be; cbn.
  - lia.
  - autorewrite with natsimplify. unfold as_be in *.
    specialize (to_Z_nonneg a).
    nia.
Qed.

Lemma as_le_nonneg: forall l,
  0 <= as_le n l.
Proof.
  intros.
  rewrite le__rev_be. apply as_be_nonneg.
Qed.

End Representation.

End Base2n.

End ReprZ.

Module ToZUnsigned <: TO_Z.
Local Open Scope circom_scope.

Definition to_Z : F -> Z := @F.to_Z q.

Lemma to_Z_0: to_Z 0 = 0.
Proof. exact F.to_Z_0. Qed.

Lemma to_Z_1: to_Z 1 = 1.
Proof. unwrap_C. unfold to_Z. rewrite @F.to_Z_1; lia. Qed.

Lemma to_Z_2: to_Z 2 = 2%Z.
Proof. unwrap_C. unfold to_Z. rewrite F.to_Z_add, @F.to_Z_1, Zmod_small; lia. Qed.

Lemma to_Z_nonneg: forall x, 0 <= to_Z x.
Proof. unwrap_C. intros. unfold to_Z. apply F.to_Z_range. lia. Qed.

End ToZUnsigned.



Module ReprZUnsigned.

Module RZ := (ReprZ ToZUnsigned).

Import RZ.

Section _ReprZUnsigned.
Context (n: nat) (n_leq_k: n <= C.k).

Notation "[| xs |]" := (RZ.as_le n xs).
Notation "[\ xs \]" := (RZ.as_be n xs).

Local Open Scope circom_scope.

Theorem repr_be_ub: forall ws x l,
  repr_be n x l ws ->
  (* n <= k -> *)
  x <= (2^(n*l) - 1)%Z.
Proof with (lia || nia || eauto).
  unwrap_C.
  induction ws as [ | w ws]; intros x l H_repr.
  - unfold repr_be, as_be in *. intuition. subst. simpl. lia.
  - destruct H_repr as [H_l [H_range H]]. subst.
    cbn [length as_be]. autorewrite with natsimplify.
    remember (length ws) as l.
    assert (H_ws: as_be n ws <= (2^(n * l) - 1)%Z). {
      apply IHws. invert H_range. unfold repr_be; intuition.
    }
    pose proof (as_be_nonneg 0) ws.
    assert (0 <= |^ w| <= 2^n-1). split. apply F.to_Z_range; try lia. invert H_range. auto.
    replace (n * S l) with (n * l + n) by lia. rewrite Zpower_exp by lia.
    unfold RZ.ToZ.to_Z.
    nia.
Qed.



Theorem repr_le_ub: forall xs x m,
  repr_le n x m xs ->
  x <= (2^(n*m) - 1)%Z.
Proof.
  intros.
  eapply repr_be_ub with (ws:=(rev xs)).
  apply repr_rev.
  auto.
Qed.

Lemma repr_le_ub': forall xs,
  xs |: (n) ->
  [| xs |] <= (2^(n*length xs) - 1)%Z.
Proof.
  intros.
  assert ([|xs|] <= 2 ^ (n * length xs) - 1). eapply repr_le_ub. apply repr_trivial. auto.
  lia.
Qed.


Fixpoint big_lt (xs ys: list F) :=
  match xs, ys with
  | nil, nil => false
  | x::xs', y::ys' =>
    if (x <q y)? then true
    else if (x = y)? then big_lt xs' ys'
    else false
  | _, _ => false
  end.

Lemma big_lt_sound: forall xs ys,
  length xs = length ys ->
  xs |: (n) ->
  ys |: (n) ->
  big_lt xs ys = true ->
  [\xs\] < [\ys\].
Proof.
  induction xs as [ | x xs]; intros ys Hlen Hxs Hys Hlt; 
  destruct ys as [ |y ys]; simpl in Hlen; try discriminate.
  simpl in *.
  pose proof (as_be_nonneg n xs) as Hxs_lb.
  pose proof (as_be_nonneg n ys) as Hys_lb.
  invert Hxs.
  invert Hys.
  assert (Hxs_ub: [\xs \] <= 2 ^ (n * length xs) - 1). eapply repr_be_ub; subst; unfold repr_be; intuition.
  assert (Hys_ub: [\ys \] <= 2 ^ (n * length ys) - 1). eapply repr_be_ub; subst; unfold repr_be; intuition.
  unfold RZ.ToZ.to_Z in *.
  invert Hlen.
  destruct (dec (x <q y)).
  (* x <q y *) nia.

  destruct (dec (x = y)).
  (* x=y *)
  assert (IH: [\xs \] < [\ys \]). apply IHxs; eauto. 
  apply f_equal with (f:=F.to_Z) in e. nia.

  (* x>y *)
  nia.
Qed.

Lemma F_to_Z_inj: forall x y,
  |^x| = |^y| -> x = y.
Proof.
  intros. apply f_equal with (f:=@F.of_Z q) in H.
  repeat rewrite F.of_Z_to_Z in H.
  auto.
Qed.

Lemma big_lt_complete: forall xs ys,
  length xs = length ys ->
  xs |: (n) ->
  ys |: (n) ->
  [\xs\] < [\ys\] ->
  big_lt xs ys = true.
Proof.
  unwrap_C.
  induction xs as [ | x xs]; intros ys Hlen Hxs Hys Hlt; 
  destruct ys as [ |y ys]; simpl in Hlen; try discriminate.
  simpl in *.
  pose proof (as_be_nonneg n xs) as Hxs_lb.
  pose proof (as_be_nonneg n ys) as Hys_lb.
  invert Hxs.
  invert Hys.
  assert (Hxs_ub: [\xs \] <= 2 ^ (n * length xs) - 1). eapply repr_be_ub; subst; unfold repr_be; intuition.
  assert (Hys_ub: [\ys \] <= 2 ^ (n * length ys) - 1). eapply repr_be_ub; subst; unfold repr_be; intuition.
  unfold RZ.ToZ.to_Z in *.
  invert Hlen.
  destruct (dec (x <q y)). reflexivity.
  destruct (dec (x=y)). apply IHxs; eauto. apply f_equal with (f:=F.to_Z) in e.
  rewrite H0 in *. nia.
  assert (Hgt: |^x| > |^y|). {
    pose proof n_leq_k. assert (2^n <= 2^k). apply Zpow_facts.Zpower_le_monotone; lia.
    assert (|^x| <> |^y|). { intros ?. apply n1. apply F_to_Z_inj; auto; lia. }
    lia.
  }
  rewrite H0 in *. nia.
Qed.

Lemma big_lt_dec: forall xs ys,
  length xs = length ys ->
  xs |: (n) ->
  ys |: (n) ->
  big_lt xs ys = true <-> [\xs\] < [\ys\].
Proof.
  intros. split.
  apply big_lt_sound; auto.
  apply big_lt_complete; auto.
Qed.

Lemma big_lt_firstn: forall i xs ys,
  length xs = length ys ->
  xs |: (n) ->
  ys |: (n) ->
  big_lt (xs[:i]) (ys[:i]) = true -> big_lt xs ys = true.
Proof.
  intros i xs.
  destruct (dec (i <= length xs)).
  generalize dependent xs.
  induction i; simpl; intuition.
  discriminate.
  destruct xs as [ | x xs]; destruct ys as [ | y ys]; simpl in *; try lia.
  invert H0. invert H1.
  destruct (dec (x <q y)); 
  destruct (dec (x=y)); auto;
  apply IHi; auto; lia.
  (* i > length xs *)
  intros.
  do 2 rewrite firstn_all2 in H2 by lia.
  auto.
Qed.

Lemma F_eq_dec: forall (x y: F), {x=y} + {x<>y}.
Proof. intros. destruct (dec (x=y)); firstorder. Qed.

Global Instance dec_F_list : DecidableRel (@eq (list F)) := list_eq_dec F_eq_dec.

Lemma big_lt_postfix: forall xs ys ys',
  big_lt (xs ++ ys) (xs ++ ys') = big_lt ys ys'.
Proof.
  induction xs as [ | x xs]; intros; simpl; auto.
  destruct (dec (x <q x)). lia.
  destruct (dec (x=x)); easy.
Qed.

Lemma big_lt_nonreflexive: forall xs,
  big_lt xs xs = false.
Proof.
  induction xs as [ | x xs]; simpl; auto.
  destruct (dec (x <q x)). lia.
  destruct (dec (x = x)); easy.
Qed.

Lemma big_lt_app: forall xs xs' ys ys',
  length xs = length xs' ->
  length ys = length ys' ->
  (big_lt xs xs' || if dec (xs = xs') then big_lt ys ys' else false) =
  big_lt (xs ++ ys) (xs' ++ ys').
Proof.
  induction xs as [ | x xs]; destruct xs' as [ | x' xs']; intros; simpl in H; try lia.
  - simpl. destruct (dec (nil = nil)). auto. exfalso. apply n0. auto.
  - simpl. destruct (dec (x <q x')); auto.
    specialize (IHxs xs' ys ys').
    destruct (dec (x = x'));
    destruct (dec (xs = xs'));
    destruct (dec (x::xs = x'::xs')); subst; auto.
    exfalso. apply n1; auto.
    invert e0. rewrite big_lt_postfix, big_lt_nonreflexive. auto.
    invert e0. exfalso. apply n1. auto.
    invert e. exfalso. apply n1. auto.
Qed.

Lemma big_lt_single: forall x y,
  big_lt (x::nil) (y::nil) = true <-> x <q y.
Proof.
  intros. simpl.
  destruct (dec (x<q y)); destruct (dec (x=y)); intuition; discriminate.
Qed.

Lemma big_lt_app': forall xs xs' ys ys',
length xs = length xs' ->
length ys = length ys' ->
(big_lt xs xs' = true \/ xs = xs' /\ big_lt ys ys' = true) <->
big_lt (xs ++ ys) (xs' ++ ys') = true.
Proof.
  intros.
  rewrite <- big_lt_app; auto.
  intuition; destruct (dec (xs=xs')); subst; repeat first [
    rewrite big_lt_nonreflexive in *
    | discriminate
    | rewrite H3; auto
    | rewrite H2; auto
    | rewrite orb_false_r in *
    | auto
    | simpl
  ].
Qed.

End _ReprZUnsigned.

End ReprZUnsigned.