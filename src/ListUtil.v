Require Import Coq.Lists.List Coq.Arith.PeanoNat.
Require Import Crypto.Util.NatUtil.
Require Import Lia.
Require Import Circom.Util.
Require Import Circom.Default.
Require Import Circom.LibTactics.


Lemma nth_oblivious: forall {A: Type} l (i: nat) (d1 d2: A),
  i < length l ->  
  List.nth i l d1 = List.nth i l d2.
Proof.
  induction l; intros; destruct i; cbn [nth length] in *; try lia; auto.
  simpl. erewrite IHl. reflexivity. lia.
Qed.

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



Definition List_nth_Default {T} `{Default T} i xs := List.nth_default default xs i.



Global Notation "xs ! i " := (List_nth_Default i xs) (at level 20) : list_scope.
Global Notation "xs [: i ]" := (List.firstn i xs) (at level 20) : list_scope.

Lemma fold_nth {T} `{Default T}: forall (i:nat) d l,
  i < length l ->
  List.nth i l d = List_nth_Default i l.
Proof. intros. unfold List_nth_Default. rewrite nth_default_eq. erewrite nth_oblivious; eauto.  Qed.

Ltac unfold_default := unfold List_nth_Default; repeat rewrite nth_default_eq.
Ltac unfold_default' H := unfold List_nth_Default in H; repeat rewrite nth_default_eq in H.
Ltac fold_default := repeat rewrite fold_nth; try lia.
Ltac fold_default' H := repeat rewrite fold_nth in H; try lia.
Ltac simpl_default := unfold_default; simpl; fold_default; try lia.
Ltac default_apply L := unfold_default; L; fold_default; try lia.
Ltac default_apply' H L := unfold_default' H; L; fold_default' H; try lia.

Require Import Circom.Tuple.

Local Open Scope tuple_scope.
Lemma nth_Default_List_tuple {T n} `{Default T} (xs: tuple T n) i:
  (to_list n xs) ! i = xs [i].
Proof.
  unfold List_nth_Default. unfold nth_Default, nth. rewrite nth_default_to_list. reflexivity.
Qed.

Ltac lift_to_list := repeat match goal with
| [H: context[nth_Default _ _] |- _] => rewrite <-nth_Default_List_tuple in H; try lia
| [ |- context[nth_Default _ _] ] => rewrite <-nth_Default_List_tuple; try lia
| [H: tforall _ _ |- _] => apply tforall_Forall in H
| [ |- tforall _ _] => apply tforall_Forall
end.



Lemma Forall_rev_iff {A: Type}: forall P (l: list A),
  Forall P l <-> Forall P (rev l).
Proof.
  induction l;split;simpl;intros;auto;rewrite Forall_forall in *;intros.
  - apply H.
    apply in_app_or in H0. destruct H0.
    + right. apply in_rev;auto.
    + simpl in *. left. destruct H0; easy.
  - apply H. apply in_or_app. inversion H0;subst. 
    + simpl;right;auto.
    + left. rewrite <- in_rev;auto.
Qed.

Lemma rev_nth' {A: Type}: forall i (l: list A) d,
  i < length l ->
  List.nth i l d = List.nth (length l - S i)%nat (rev l) d.
Proof.
  intros. remember (rev l) as l'. 
  applys_eq rev_nth.
  f_equal. rewrite <- rev_involutive with (l:=l). rewrite <- Heql'. reflexivity.
  rewrite Heql'. rewrite rev_length. reflexivity.
  rewrite Heql'. rewrite rev_length. lia.
Qed.

Lemma app_congruence: forall {A: Type} (l1 l2 l1' l2': list A),
  l1 = l1' ->
  l2 = l2' ->
  l1 ++ l2 = l1' ++ l2'.
Proof.
  intros. rewrite H, H0. easy.
Qed.

Lemma app_congruence_iff_strong: forall {A: Set} (l1 l2 l1' l2': list A),
  length l1 = length l1' ->
  (l1 = l1' /\ l2 = l2') <-> 
  l1 ++ l2 = l1' ++ l2'.
Proof.
  split;intros.
  - apply app_congruence;easy.
  - pose proof (ListAux.map_length_decompose A A (fun x=>x) l1 l1' l2 l2' H).
    rewrite map_id in *. apply H1 in H0. destruct H0. rewrite map_id in *;auto.
Qed.

Lemma app_congruence_iff: forall {A: Set} (l1 l2 l1' l2': list A),
  length l1 = length l1' ->
  length l2 = length l2' ->
  (l1 = l1' /\ l2 = l2') <-> 
  l1 ++ l2 = l1' ++ l2'.
Proof.
  intros;apply app_congruence_iff_strong;auto.
Qed.