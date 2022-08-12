Require Import Coq.Lists.List Coq.Arith.PeanoNat.
Require Import Crypto.Util.NatUtil.
Require Import Lia.
Require Import Util.


Lemma firstn_nth {A: Type}: forall l i j (d: A),
  (i < j)%nat ->
  nth i (firstn j l) d = nth i l d.
Proof.
  induction l; simpl; intros.
  - rewrite firstn_nil. destruct i; reflexivity.
  - destruct j. lia. destruct i.
    + rewrite firstn_cons. reflexivity.
    + simpl. rewrite IHl. auto. lia.
Qed.

Lemma fistn_prev {A: Type}: forall l i j (d: A),
  (i < j)%nat ->
  (j < length l)%nat ->
  nth i (firstn (S j) l) d = nth i (firstn j l) d.
Proof.
  induction l; intros.
  - simpl in *. lia.
  - simpl. destruct i. destruct j. lia. reflexivity.
    destruct j. lia.
    rewrite IHl. simpl. reflexivity.
    lia.
    simpl in H0. lia.
Qed.

Lemma firstn_1 {A: Type}: forall l (d: A),
  (length l > 0)%nat ->
  firstn 1 l = nth 0 l d :: nil.
Proof.
  destruct l; simpl; intros. lia. reflexivity.
Qed.


Lemma nth_skipn {A: Type}: forall l i j (d: A),
  (i+j < length l)%nat ->
  nth i (skipn j l) d = nth (i+j) l d.
Proof.
  induction l; simpl; intros.
  - destruct i; destruct j; lia.
  - destruct i; destruct j; simpl; repeat first [
        reflexivity
      | progress rewrite IHl by lia
      | progress rewrite Nat.add_0_r
      | progress rewrite Nat.add_succ_r
    ].
Qed.

Lemma firstn_S {A: Type}: forall i l (d: A),
  (i < length l)%nat ->
  firstn (S i) l = firstn i l ++ (nth i l d :: nil).
Proof.
  intros.
  replace (firstn (S i) l) with (firstn (S i) (firstn i l ++ skipn i l)).
  rewrite firstn_app. rewrite firstn_firstn.
  rewrite firstn_length_le by lia.
  replace (min (S i) i) with i by lia.
  replace (S i - i)%nat with 1%nat by lia.
  erewrite firstn_1.
  erewrite nth_skipn by lia.
  simpl. reflexivity.
  rewrite skipn_length. lia.
  rewrite firstn_skipn. reflexivity.
Qed.

Lemma skipn_nth_last: forall {A: Type} i xs (d: A),
  length xs = S i ->
  skipn i xs = nth i xs d :: nil.
Proof.
  intros.
  rewrite <- rev_involutive with (l:=xs).
  rewrite skipn_rev. rewrite rev_length. rewrite H. autorewrite with natsimplify.
  erewrite firstn_1.
  simpl.
  rewrite rev_involutive.
  rewrite rev_nth by lia.
  rewrite H. autorewrite  with natsimplify. reflexivity.
  rewrite rev_length. lia.
Qed.

Lemma firstn_split_last {A: Type}: forall (l: list A) n d,
  length l = S n ->
  firstn n l ++ nth n l d :: nil = l.
Proof.
  intros l m d Hlen.
  assert (l=l) by reflexivity.
  rewrite <- firstn_skipn with (n:=m) in H.
  erewrite skipn_nth_last in H by lia.
  rewrite <- H. reflexivity.
Qed.

Lemma skipn_skipn {A: Type}: forall (j i: nat) (l: list A),
  skipn i (skipn j l) = skipn (i+j)%nat l.
Proof.
  induction j; simpl; intros.
  autorewrite with natsimplify. reflexivity.
  destruct l. repeat rewrite skipn_nil. reflexivity.
  rewrite Nat.add_succ_r. simpl. rewrite IHj. reflexivity.
Qed.

Lemma Forall_firstn {A: Type}: forall (l: list A) i P,
  Forall P l -> Forall P (firstn i l).
Proof.
  induction l; intros.
  - rewrite firstn_nil. constructor.
  - invert H. 
    destruct i. simpl. constructor.
    simpl. constructor; auto.
Qed.

Lemma Forall_firstn_S {A: Type}: forall (l: list A) i P d,
  S i = length l ->
  Forall P (firstn i l) ->
  P (nth i l d) ->
  Forall P l.
Proof.
  intros. erewrite <- firstn_split_last by eauto. apply Forall_app; eauto.
Qed.

Lemma Forall_skipn {A: Type}: forall (l: list A) i P,
  Forall P l -> Forall P (skipn i l).
Proof.
  induction l; intros.
  - rewrite skipn_nil. auto.
  - invert H.
    destruct i; simpl. auto.
    auto.
Qed.
