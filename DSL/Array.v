Require Import BinPosDef.
Require Import Crypto.Spec.ModularArithmetic.
Require Import List.

Context {q : positive}.

Definition sig := F q.

Definition sigArray := list sig.

Inductive get : sigArray -> sig -> nat -> Prop :=
| get_frst: forall ss s, get (s :: ss) s 0
| get_step: forall ss s s' i, get ss s i -> get (s' :: ss) s (S i).

Fixpoint fget (ss : sigArray) (s : sig) (i : nat) : Prop :=
  match ss, i with
  | nil, _ => False
  | s' :: _, O => s' = s
  | _ :: ss', S i' => fget ss' s i'
  end.

Inductive init : sigArray -> sig -> nat -> Prop :=
| init_zero: forall s, init nil s 0
| init_succ: forall ss s i, init ss s i -> init (s :: ss) s (S i).

Fixpoint finit (ss : sigArray) (s : sig) (n : nat) : Prop :=
  match ss, n with
  | nil, O => True
  | s' :: ss', S n' => s' = s /\ finit ss' s n'
  | _, _ => False
  end.

Inductive scale : sig -> sigArray -> sigArray -> Prop :=
| scale_nil: forall c, scale c nil nil
| scale_cons: forall c ss ss' s, scale c ss ss' -> scale c (s :: ss) (F.mul c s :: ss').

Fixpoint fscale (c : sig) (s1 s2 : sigArray) : Prop :=
  match s1, s2 with
  | nil, nil => True
  | s' :: s1', s'' :: s2' => s'' = F.mul c s' /\ fscale c s1' s2'
  | _, _ => False
  end.

Inductive sum : sigArray -> sig -> Prop :=
| sum_nil: sum nil F.zero
| sum_cons: forall ss s s', sum ss s -> sum (s' :: ss) (F.add s' s).

Fixpoint fsum (ss : sigArray) (s : sig) : Prop :=
  match ss with
  | nil => s = F.zero
  | s' :: ss' => fsum ss' (F.sub s s')
  end.

Inductive map {A : Type} : (sig -> A) -> sigArray -> list A -> Prop :=
| map_nil: forall f, map f nil nil
| map_cons: forall f ss a s, map f ss a -> map f (s :: ss) (f s :: a).

Fixpoint fmap {A : Type} (f : sig -> A) (ss : sigArray) (l : list A) : Prop :=
  match ss, l with
  | nil, nil => True
  | s' :: ss', a :: l' => a = f s' /\ fmap f ss' l'
  | _, _ => False
  end.

Lemma fmap_sound: forall A (f : sig -> A) ss l, fmap f ss l -> List.map f ss = l.
Proof.
  intros A f.
  induction ss; intros; simpl in H; simpl; destruct l; intuition.
  - apply IHss in H1. rewrite <- H0, H1. reflexivity.
Qed.

Lemma fmap_complete: forall A (f : sig -> A) ss, fmap f ss (List.map f ss).
Proof.
  intros A f. induction ss; simpl; auto.
Qed.

Inductive foldl {A : Type} : (A -> sig -> A) -> sigArray -> A -> A -> Prop :=
| foldl_nil: forall f a, foldl f nil a a
| foldl_app: forall f ss a a' s, foldl f ss a a' -> foldl f (ss ++ (cons s nil)) a (f a' s).

Fixpoint ffoldl {A : Type} (f : A -> sig -> A) (ss : sigArray) (acc a : A) : Prop :=
  match ss with
  | nil => a = acc
  | s' :: ss' =>
      let acc' := f acc s' in
      ffoldl f ss' acc' a
  end.

Lemma ffoldl_sound: forall A (f : A -> sig -> A) ss acc a,
    ffoldl f ss acc a -> List.fold_left f ss acc = a.
Proof.
  intros A f. induction ss; intros; simpl in H; simpl; auto.
Qed.

Lemma ffoldl_complete: forall A (f : A -> sig -> A) ss acc,
    ffoldl f ss acc (List.fold_left f ss acc).
Proof.
  intros A f. induction ss; intros; simpl; auto.
Qed.

Inductive foldr {A : Type} : (sig -> A -> A) -> A -> sigArray -> A -> Prop :=
| foldr_nil: forall f a, foldr f a nil a
| foldr_cons: forall f ss a a' s, foldr f a ss a' -> foldr f a (s :: ss) (f s a').

Definition ffoldr {A : Type} (f : sig -> A -> A) (acc : A) (ss : sigArray) (a : A) : Prop :=
  ffoldl (fun acc s => f s acc) (rev ss) acc a.

Inductive map2 {A : Type} : (sig -> sig -> A) -> sigArray -> sigArray -> list A -> Prop :=
| map2_nil_l: forall f ss, map2 f nil ss nil
| map2_nil_r: forall f ss, map2 f ss nil nil
| map2_cons: forall f ss1 ss2 a s1 s2, map2 f ss1 ss2 a -> map2 f (s1 :: ss1) (s2 :: ss2) (f s1 s2 :: a).

Fixpoint fmap2 {A : Type} (f : sig -> sig -> A) (s1 s2 : sigArray) (l : list A) : Prop :=
  match s1, s2, l with
  | nil, nil, nil => True
  | s' :: s1', s'' :: s2', a :: l' =>
      a = f s' s'' /\ fmap2 f s1' s2' l'
  | _, _, _ => False
  end.

Inductive foldl2 {A : Type} : (A -> sig -> sig -> A) -> sigArray -> sigArray -> A -> A -> Prop :=
| foldl2_nil_l: forall f ss a, foldl2 f nil ss a a
| foldl2_nil_r: forall f ss a, foldl2 f ss nil a a
| foldl2_app: forall f ss1 ss2 a a' s1 s2,
    foldl2 f ss1 ss2 a a' -> foldl2 f (ss1 ++ (cons s1 nil)) (ss2 ++ (cons s2 nil)) a (f a' s1 s2).

Fixpoint ffoldl2 {A : Type} (f : A -> sig -> sig -> A) (s1 s2 : sigArray) (acc a : A) : Prop :=
  match s1, s2 with
  | nil, nil => a = acc
  | s' :: s1', s'' :: s2' =>
      let acc' := f acc s' s'' in
      ffoldl2 f s1' s2' acc' a
  | _, _ => False
  end.

Inductive foldr2 {A : Type} : (sig -> sig -> A -> A) -> A -> sigArray -> sigArray -> A -> Prop :=
| foldr2_nil_l: forall f ss a, foldr2 f a nil ss a
| foldr2_nil_r: forall f ss a, foldr2 f a ss nil a
| foldr2_cons: forall f ss1 ss2 a a' s1 s2,
    foldr2 f a ss1 ss2 a' -> foldr2 f a (s1 :: ss1) (s2 :: ss2) (f s1 s2 a').

Definition ffoldr2 {A : Type} (f : sig -> sig -> A -> A) (acc : A) (s1 s2 : sigArray) (a : A) : Prop :=
  ffoldl2 (fun acc s' s'' => f s' s'' acc) (rev s1) (rev s2) acc a.

Definition elem_add := map2 F.add.
Definition elem_sub := map2 F.sub.
Definition elem_mul := map2 F.mul.

Definition felem_add := fmap2 F.add.
Definition felem_sub := fmap2 F.sub.
Definition felem_mul := fmap2 F.mul.

Inductive elem_eq : sigArray -> sigArray -> Prop :=
| elem_eq_nil: elem_eq nil nil
| elem_eq_cons: forall s1 s2 s, elem_eq s1 s2 -> elem_eq (s :: s1) (s :: s2).

Fixpoint felem_eq (s1 s2 : sigArray) : Prop :=
  match s1, s2 with
  | nil, nil => True
  | s' :: s1', s'' :: s2' =>
      s' = s'' /\ felem_eq s1' s2'
  | _, _ => False
  end.
