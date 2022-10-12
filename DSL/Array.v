Require Import BinPosDef.
Require Import Crypto.Spec.ModularArithmetic.
Require Import List.

Context {q : positive}.

Definition sig := F q.

Definition sigArray := list sig.

Module Get.

  Inductive iget : sigArray -> sig -> nat -> Prop :=
  | iget_frst: forall ss s, iget (s :: ss) s 0
  | iget_step: forall ss s s' i, iget ss s i -> iget (s' :: ss) s (S i).

  Fixpoint get (ss : sigArray) (s : sig) (i : nat) : Prop :=
    match ss, i with
    | nil, _ => False
    | s' :: _, O => s' = s
    | _ :: ss', S i' => get ss' s i'
    end.

End Get.

Module Init.

  Inductive iinit : sigArray -> sig -> nat -> Prop :=
  | iinit_zero: forall s, iinit nil s 0
  | iinit_succ: forall ss s i, iinit ss s i -> iinit (s :: ss) s (S i).

  Fixpoint init (ss : sigArray) (s : sig) (n : nat) : Prop :=
    match ss, n with
    | nil, O => True
    | s' :: ss', S n' => s' = s /\ init ss' s n'
    | _, _ => False
    end.

End Init.

Module Scale.

  Definition scale_fn (c : sig) := List.map (F.mul c).

  Inductive iscale : sig -> sigArray -> sigArray -> Prop :=
  | iscale_nil: forall c, iscale c nil nil
  | iscale_cons: forall c ss ss' s, iscale c ss ss' -> iscale c (s :: ss) (F.mul c s :: ss').

  Fixpoint scale (c : sig) (s1 s2 : sigArray) : Prop :=
    match s1, s2 with
    | nil, nil => True
    | s' :: s1', s'' :: s2' => s'' = F.mul c s' /\ scale c s1' s2'
    | _, _ => False
    end.

End Scale.

Module Sum.

  Definition sum_fn (ss : sigArray) := fold_left F.add ss F.zero.

  Inductive isum : sigArray -> sig -> Prop :=
  | isum_nil: isum nil F.zero
  | isum_cons: forall ss s s', isum ss s -> isum (s' :: ss) (F.add s' s).

  Fixpoint sum (ss : sigArray) (s : sig) : Prop :=
    match ss with
    | nil => s = F.zero
    | s' :: ss' => sum ss' (F.sub s s')
    end.

End Sum.

Module Map.

  Inductive imap {A : Type} : (sig -> A) -> sigArray -> list A -> Prop :=
  | imap_nil: forall f, imap f nil nil
  | imap_cons: forall f ss a s, imap f ss a -> imap f (s :: ss) (f s :: a).

  Fixpoint map {A : Type} (f : sig -> A) (ss : sigArray) (l : list A) : Prop :=
    match ss, l with
    | nil, nil => True
    | s' :: ss', a :: l' => a = f s' /\ map f ss' l'
    | _, _ => False
    end.

  Lemma map_sound: forall A (f : sig -> A) ss l, map f ss l -> List.map f ss = l.
  Proof.
    intros A f.
    induction ss; intros; simpl in H; simpl; destruct l; intuition.
    - apply IHss in H1. rewrite <- H0, H1. reflexivity.
  Qed.

  Lemma map_complete: forall A (f : sig -> A) ss, map f ss (List.map f ss).
  Proof.
    intros A f. induction ss; simpl; auto.
  Qed.

End Map.

Module Fold.

  Inductive ifoldl {A : Type} : (A -> sig -> A) -> sigArray -> A -> A -> Prop :=
  | ifoldl_nil: forall f a, ifoldl f nil a a
  | ifoldl_app: forall f ss a a' s, ifoldl f ss a a' -> ifoldl f (ss ++ (cons s nil)) a (f a' s).

  Fixpoint foldl {A : Type} (f : A -> sig -> A) (ss : sigArray) (acc a : A) : Prop :=
    match ss with
    | nil => a = acc
    | s' :: ss' =>
        let acc' := f acc s' in
        foldl f ss' acc' a
    end.

  Lemma foldl_sound: forall A (f : A -> sig -> A) ss acc a,
      foldl f ss acc a -> fold_left f ss acc = a.
  Proof.
    intros A f. induction ss; intros; simpl in H; simpl; auto.
  Qed.

  Lemma foldl_complete: forall A (f : A -> sig -> A) ss acc,
      foldl f ss acc (fold_left f ss acc).
  Proof.
    intros A f. induction ss; intros; simpl; auto.
  Qed.

  Inductive ifoldr {A : Type} : (sig -> A -> A) -> A -> sigArray -> A -> Prop :=
  | ifoldr_nil: forall f a, ifoldr f a nil a
  | ifoldr_cons: forall f ss a a' s, ifoldr f a ss a' -> ifoldr f a (s :: ss) (f s a').

  Definition foldr {A : Type} (f : sig -> A -> A) (acc : A) (ss : sigArray) (a : A) : Prop :=
    foldl (fun acc s => f s acc) (rev ss) acc a.

  Lemma foldr_sound: forall A (f : sig -> A -> A) acc ss a,
      foldr f acc ss a -> fold_right f acc ss = a.
  Proof.
    intros A f acc ss. revert acc.
    induction ss; intros; unfold foldr in H; simpl in H; simpl.
    - auto.
    - apply foldl_sound in H. rewrite fold_left_app in H. simpl in H.
      assert (H0: foldl (fun (acc : A) (s : sig) => f s acc) (rev ss) acc
                    (fold_left (fun (acc : A) (s : sig) => f s acc) (rev ss) acc)).
      { apply foldl_complete. }
      unfold foldr in IHss. apply IHss in H0. rewrite <- H0 in H. apply H.
  Qed.

  Lemma foldr_complete: forall A (f : sig -> A -> A) acc ss,
      foldr f acc ss (fold_right f acc ss).
  Proof.
    intros A f acc ss. revert acc.
    induction ss; intros; unfold foldr; simpl.
    - auto.
    - assert (H0: fold_left (fun (acc0 : A) (s : sig) => f s acc0)
                    (rev ss ++ a :: nil) acc = (f a (fold_right f acc ss))).
      { rewrite fold_left_app. simpl. unfold foldr in IHss.
        specialize IHss with (acc := acc) as H0'.
        apply foldl_sound in H0'. rewrite H0'. reflexivity. }
      rewrite <- H0. apply foldl_complete.
  Qed.

End Fold.

Module Map2.

  Fixpoint map2_fn {A : Type} (f : sig -> sig -> A) (s1 s2 : sigArray) : list A :=
    match s1, s2 with
    | s' :: s1', s'' :: s2' =>
        (f s' s'') :: map2_fn f s1' s2'
    | _, _ => nil
    end.

  Inductive imap2 {A : Type} : (sig -> sig -> A) -> sigArray -> sigArray -> list A -> Prop :=
  | imap2_nil_l: forall f ss, imap2 f nil ss nil
  | imap2_nil_r: forall f ss, imap2 f ss nil nil
  | imap2_cons: forall f ss1 ss2 a s1 s2, imap2 f ss1 ss2 a -> imap2 f (s1 :: ss1) (s2 :: ss2) (f s1 s2 :: a).

  Fixpoint map2 {A : Type} (f : sig -> sig -> A) (s1 s2 : sigArray) (l : list A) : Prop :=
    match s1, s2, l with
    | nil, nil, nil => True
    | s' :: s1', s'' :: s2', a :: l' =>
        a = f s' s'' /\ map2 f s1' s2' l'
    | _, _, _ => False
    end.

End Map2.

Module Fold2.

  Fixpoint foldl2_fn {A : Type} (f : A -> sig -> sig -> A) (s1 s2 : sigArray) (acc : A) : A :=
    match s1, s2 with
    | s' :: s1', s'' :: s2' =>
        foldl2_fn f s1' s2' (f acc s' s'')
    | _, _ => acc
    end.

  Inductive ifoldl2 {A : Type} : (A -> sig -> sig -> A) -> sigArray -> sigArray -> A -> A -> Prop :=
  | ifoldl2_nil_l: forall f ss a, ifoldl2 f nil ss a a
  | ifoldl2_nil_r: forall f ss a, ifoldl2 f ss nil a a
  | ifoldl2_app: forall f ss1 ss2 a a' s1 s2,
      ifoldl2 f ss1 ss2 a a' -> ifoldl2 f (ss1 ++ (cons s1 nil)) (ss2 ++ (cons s2 nil)) a (f a' s1 s2).

  Fixpoint foldl2 {A : Type} (f : A -> sig -> sig -> A) (s1 s2 : sigArray) (acc a : A) : Prop :=
    match s1, s2 with
    | nil, nil => a = acc
    | s' :: s1', s'' :: s2' =>
        let acc' := f acc s' s'' in
        foldl2 f s1' s2' acc' a
    | _, _ => False
    end.

  Fixpoint foldr2_fn {A : Type} (f : sig -> sig -> A -> A) (acc : A) (s1 s2 : sigArray) : A :=
    match s1, s2 with
    | s' :: s1', s'' :: s2' =>
        foldr2_fn f (f s' s'' acc) s1' s2'
    | _, _ => acc
    end.

  Inductive ifoldr2 {A : Type} : (sig -> sig -> A -> A) -> A -> sigArray -> sigArray -> A -> Prop :=
  | ifoldr2_nil_l: forall f ss a, ifoldr2 f a nil ss a
  | ifoldr2_nil_r: forall f ss a, ifoldr2 f a ss nil a
  | ifoldr2_cons: forall f ss1 ss2 a a' s1 s2,
      ifoldr2 f a ss1 ss2 a' -> ifoldr2 f a (s1 :: ss1) (s2 :: ss2) (f s1 s2 a').

  Definition foldr2 {A : Type} (f : sig -> sig -> A -> A) (acc : A) (s1 s2 : sigArray) (a : A) : Prop :=
    foldl2 (fun acc s' s'' => f s' s'' acc) (rev s1) (rev s2) acc a.

End Fold2.

Module Elem.

  Definition ielem_add := Map2.imap2 F.add.
  Definition ielem_sub := Map2.imap2 F.sub.
  Definition ielem_mul := Map2.imap2 F.mul.

  Definition elem_add := Map2.map2 F.add.
  Definition elem_sub := Map2.map2 F.sub.
  Definition elem_mul := Map2.map2 F.mul.

  Inductive ielem_eq : sigArray -> sigArray -> Prop :=
  | ielem_eq_nil: ielem_eq nil nil
  | ielem_eq_cons: forall s1 s2 s, ielem_eq s1 s2 -> ielem_eq (s :: s1) (s :: s2).

  Fixpoint elem_eq (s1 s2 : sigArray) : Prop :=
    match s1, s2 with
    | nil, nil => True
    | s' :: s1', s'' :: s2' =>
        s' = s'' /\ elem_eq s1' s2'
    | _, _ => False
    end.

End Elem.
