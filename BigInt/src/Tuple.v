Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Export Crypto.Util.FixCoqMistakes.

Require Import Circom.Default.

Ltac invert H := inversion H; subst; clear H.

(* left associative by default *)
Fixpoint tuple (T: Type) n : Type :=
  match n with
  | O => unit
  | S n' => tuple T n' * T
  end.

(** right-associated tuples *)
Fixpoint rtuple T n : Type :=
  match n with
  | O => unit
  | S n' => (T * rtuple T n')%type
  end.

Fixpoint rsnoc T n {struct n} : rtuple T n -> T -> rtuple T (S n) := 
  match n return rtuple T n -> T -> rtuple T (S n) with
  | O => fun x y => (y, x)
  | S n' => fun x y => (fst x, @rsnoc T n' (snd x) y)
  end.
Global Arguments rsnoc {T n} _ _.

Fixpoint cons T n {struct n} : T -> tuple T n -> tuple T (S n) := 
  match n return T -> tuple T n -> tuple T (S n) with
  | O => fun y x => (x, y)
  | S n' => fun y x => (@cons T n' y (fst x), snd x)
  end.
Global Arguments cons {T n} _ _.

Fixpoint assoc_right {n T} {struct n} : tuple T n -> rtuple T n := 
  match n return tuple T n -> rtuple T n with
  | O => fun x => x
  | S n' => fun ts => 
    let xs := @assoc_right n' T (fst ts) in
    let x := snd ts in
    rsnoc xs x
  end.

Fixpoint assoc_left {n T} {struct n} : rtuple T n -> tuple T n := 
  match n return rtuple T n -> tuple T n with
  | 0 => fun x => x
  | S n' => fun ts => 
    let xs := @assoc_left n' T (snd ts) in
    let x := fst ts in
    cons x xs
  end.

Definition tl {T n} : tuple T (S n) -> tuple T n := @fst _ _.
Definition hd {T n} : tuple T (S n) -> T.
Proof. intros t. destruct t. trivial. Defined.

Section ToFromList.

Fixpoint to_list {T} (n:nat) {struct n} : tuple T n -> list T :=
  match n return tuple T n -> list T with
  | O => fun _ => nil%list
  | S n' => fun xs => let (xs', x) := xs in (x :: to_list n' xs')%list
  end.

Program Fixpoint from_list {T} (n:nat) (xs:list T) : length xs = n -> tuple T n :=
  match n return _ with
  | 0 =>
    match xs return (length xs = 0 -> tuple T 0) with
    | nil => fun _ => tt
    | _ => _ (* impossible *)
    end
  | S n' =>
    match xs return (length xs = S n' -> tuple T (S n')) with
    | List.cons x xs' => fun _ => (from_list n' xs' _, x)
    | _ => _ (* impossible *)
    end
  end.

Definition from_list' {T} (xs: list T) : tuple T (length xs).
Proof. induction xs; simpl. exact tt. auto. Defined.

Lemma to_list_from_list : forall {T} (n:nat) (xs:list T) pf, to_list n (from_list n xs pf) = xs.
Proof.
  destruct xs as [|t xs]; simpl; intros; subst; auto.
  generalize dependent t. simpl in *.
  induction xs; simpl in *; intros; congruence.
Qed.

Lemma length_to_list {T n} t : length (@to_list T n t) = n.
Proof using Type. induction n; simpl in *; trivial; destruct t; simpl; congruence. Qed.

Lemma from_list_to_list : forall {T n} (xs:tuple T n) pf, from_list n (to_list n xs) pf = xs.
Proof using Type.
  induction n as [|n]; auto; intros xs pf.
  simpl in *. destruct xs. auto.
  simpl. destruct xs. simpl in *. rewrite IHn. reflexivity.
Qed.

End ToFromList.

Fixpoint repeat {T} (x: T) (n: nat) : tuple T n :=
  match n with
  | O => tt
  | S n' => cons x (repeat x n')
  end.

Fixpoint nth_default {T n} (d: T) (i: nat) : tuple T n -> T :=
  match n with
  | O => fun _ => d
  | S n' => fun '(xs',x) => 
    match i with
    | O => x
    | S i' => nth_default d i' xs'
    end
  end.

Definition nth {n T} i (xs: tuple T n) d := nth_default d i xs.

Lemma nth_default_to_list {A} n (xs : tuple A n) (d : A) :
  forall i, List.nth_default d (to_list n xs) i = @nth_default A n d i xs.
Proof using Type.
  revert xs; induction n, i; cbn; break_match; intros;
    rewrite ?ListUtil.nth_default_cons_S; try reflexivity; rewrite ?IHn; eauto using ListUtil.nth_default_nil.
Qed.


Lemma nth_default_oblivious: forall {A n} (xs: tuple A n) (i: nat) (d1 d2: A),
  i < n ->  
  nth_default d1 i xs = nth_default d2 i xs.
Proof.
  induction n; simpl; intros. lia.
  destruct xs; destruct i. auto. apply IHn. lia.
Qed.

Definition nth_Default {T n} `{Default T} i (xs: tuple T n) := nth i xs default.

Lemma nth_Default_nth_default {T n} `{H: Default T}: forall i (xs: tuple T n),
  nth_Default i xs = nth_default default i xs.
Proof.
  induction n; intros; firstorder || destruct i; firstorder.
Qed.

Lemma nth_Default_to_list {A} `{Default A} n (xs : tuple A n) (d: A):
  forall i, i < n ->
    List.nth_default d (to_list n xs) i = nth_Default i xs.
Proof using Type.
  intros. unfold nth_Default, nth. erewrite nth_default_oblivious.
  apply nth_default_to_list. lia.
Qed.




Section tforall.

  Context {T: Type} (P: T -> Prop).

  Fixpoint tforall {n} : tuple T n -> Prop :=
    match n return tuple T n -> Prop with
    | O => fun _ => True
    | S n' => fun '(xs',x) => P x /\ tforall xs'
    end.

  Lemma tforall_Forall: forall n (xs: tuple T n), tforall xs <-> List.Forall P (to_list n xs).
  Proof.
    induction n; simpl; split; intros; auto; 
    destruct xs as [x xs].
    - constructor; firstorder.
    - invert H. firstorder.
  Qed.

  Lemma tforall_inv : forall n (xs: tuple T n) x, @tforall (S n) (xs, x) -> P x.
  Proof. firstorder. Qed.

  Theorem tforall_inv_tail : forall n (xs: tuple T n) x, @tforall (S n) (xs, x) -> @tforall n xs.
  Proof. firstorder. Qed.

  Lemma tforall_nth_default: forall n (xs: tuple T n),
    tforall xs <-> forall i d, i < n -> P (nth_default d i xs).
  Proof.
    split; induction n; simpl; intros; auto; try lia;
    destruct xs as [x xs].
    - destruct i. firstorder. apply IHn. firstorder. lia.
    - firstorder. specialize (H 0). apply H. auto. lia.
      apply IHn. intros. specialize (H (S i)). apply H. lia.
  Qed.

  Lemma tforall_nth_Default `{H: Default T}: forall n (xs: tuple T n),
    tforall xs <-> forall i, i < n -> P (nth_Default i xs).
  Proof.
    intros. unfold nth_Default, nth. split; intros.
    apply tforall_nth_default; auto.
    apply tforall_nth_default. intros. 
    erewrite nth_default_oblivious.
    eauto. lia.
  Qed.

End tforall.

Lemma firstn_to_list {T}: forall m (x: tuple T m),
  firstn m (to_list m x) = to_list m x.
Proof.
  intros. apply firstn_all2. rewrite length_to_list; lia.
Qed.

Fixpoint map {n A B} (f:A -> B) : tuple A n -> tuple B n
  := match n return tuple A n -> tuple B n with
     | 0 => fun _ => tt
     | S n' => fun '(xs,x) => (map f xs, f x)
     end.

Definition on_tuple2 {A B C} (f : list A -> list B -> list C) {a b c : nat}
           (Hlength : forall la lb, length la = a -> length lb = b -> length (f la lb) = c)
           (ta:tuple A a) (tb:tuple B b) : tuple C c
  := from_list c (f (to_list a ta) (to_list b tb))
               (Hlength (to_list a ta) (to_list b tb) (length_to_list ta) (length_to_list tb)).

Definition map2 {n A B C} (f:A -> B -> C) (xs:tuple A n) (ys:tuple B n) : tuple C n
  := on_tuple2 (map2 f) (fun la lb pfa pfb => eq_trans (@map2_length _ _ _ _ la lb) (eq_trans (f_equal2 _ pfa pfb) (Min.min_idempotent _))) xs ys.

Fixpoint fold_right {A B: Type} (n:nat) (f: A -> B -> B) (b0: B) : tuple A n -> B :=
  match n return tuple A n -> B with
  | O => fun _ => b0
  | S n' => fun '(aa,a) => fold_right n' f (f a b0) aa
  end.




(* 

Lemma to_list_S {A n} (x : tuple A (S n)) (a:A)
  : to_list (T:=A) (S (S n)) (x,a) = a :: to_list (S n) x.
Proof using Type. reflexivity. Qed.

Fixpoint curry'T (R T : Type) (n : nat) : Type
  := match n with
     | 0 => T -> R
     | S n' => curry'T (T -> R) T n'
     end.
Definition curryT (R T : Type) (n : nat) : Type
  := match n with
     | 0 => R
     | S n' => curry'T R T n'
     end.

Fixpoint uncurry' {R T n} : (tuple' T n -> R) -> curry'T R T n
  := match n return (tuple' T n -> R) -> curry'T R T n with
     | 0 => fun f x => f x
     | S n' => fun f => @uncurry' (T -> R) T n' (fun xs x => f (xs, x))
     end.

Definition uncurry {R T n} : (tuple T n -> R) -> curryT R T n
  := match n return (tuple T n -> R) -> curryT R T n with
     | 0 => fun f => f tt
     | S n' => @uncurry' R T n'
     end.

Fixpoint curry' {R T n} : curry'T R T n -> (tuple' T n -> R)
  := match n return curry'T R T n -> (tuple' T n -> R) with
     | 0 => fun f x => f x
     | S n' => fun f xs_x => @curry' (T -> R) T n' f (fst xs_x) (snd xs_x)
     end.

Definition curry {R T n} : curryT R T n -> (tuple T n -> R)
  := match n return curryT R T n -> (tuple T n -> R) with
     | 0 => fun r _ => r
     | S n' => @curry' R T n'
     end.

Fixpoint eta' {n A B} : (tuple' A n -> B) -> tuple' A n -> B
  := match n with
     | 0 => fun f => f
     | S n' => fun (f : tuple' A n' * A -> B)
                   (xy : tuple' A n' * A)
               => let '(x, y) := xy in
                  eta' (fun x => f (x, y)) x
     end.

Definition eta {n A B} : (tuple A n -> B) -> tuple A n -> B
  := match n with
     | 0 => fun f => f
     | S n' => @eta' n' A B
     end.

Definition on_tuple {A B} (f:list A -> list B)
           {n m:nat} (H:forall xs, length xs = n -> length (f xs) = m)
           (xs:tuple A n) : tuple B m :=
  from_list m (f (to_list n xs))
            (H (to_list n xs) (length_to_list xs)).

Section map.
  (* Put the types and function in the context, so that the fixpoint doesn't depend on them *)
  Context {A B} (f:A -> B).

  Fixpoint map' {n} : tuple' A n -> tuple' B n
    := match n with
       | 0 => f
       | S n' => fun x : tuple' _ _ * _ => (@map' n' (fst x), f (snd x))
       end.
End map.

Definition map {n A B} (f:A -> B) : tuple A n -> tuple B n
  := match n with
     | 0 => fun x => x
     | S n' => map' f
     end.

Definition on_tuple2 {A B C} (f : list A -> list B -> list C) {a b c : nat}
           (Hlength : forall la lb, length la = a -> length lb = b -> length (f la lb) = c)
           (ta:tuple A a) (tb:tuple B b) : tuple C c
  := from_list c (f (to_list a ta) (to_list b tb))
               (Hlength (to_list a ta) (to_list b tb) (length_to_list ta) (length_to_list tb)).

Definition map2 {n A B C} (f:A -> B -> C) (xs:tuple A n) (ys:tuple B n) : tuple C n
  := on_tuple2 (map2 f) (fun la lb pfa pfb => eq_trans (@map2_length _ _ _ _ la lb) (eq_trans (f_equal2 _ pfa pfb) (Min.min_idempotent _))) xs ys.

Lemma to_list'_ext {n A} (xs ys:tuple' A n) : to_list' n xs = to_list' n ys -> xs = ys.
Proof using Type.
  induction n; simpl in *; [cbv; congruence|]; destruct_head' prod.
  intro Hp; injection Hp; clear Hp; intros; subst; eauto using f_equal2.
Qed.

Lemma to_list_ext {n A} (xs ys:tuple A n) : to_list n xs = to_list n ys -> xs = ys.
Proof using Type.
  destruct n; simpl in *; destruct_head unit; eauto using to_list'_ext.
Qed.

Lemma from_list'_complete {A n} (xs:tuple' A n) : exists x ls pf, xs = from_list' x n ls pf.
Proof using Type.
  destruct n; simpl in xs.
  {  exists xs. exists nil. exists eq_refl. reflexivity. }
  { destruct xs as [xs' x]. exists x. exists (to_list' _ xs'). eexists (length_to_list' _ _ _).
    symmetry; eapply from_list'_to_list'. reflexivity. }
Qed.

Lemma from_list_complete {A n} (xs:tuple A n) : exists ls pf, xs = from_list n ls pf.
Proof using Type.
  exists (to_list n xs). exists (length_to_list _). symmetry; eapply from_list_to_list.
Qed.

Ltac tuples_from_lists :=
  repeat match goal with
         | [xs:tuple ?A _ |- _] =>
           let ls := fresh "l" xs in
           destruct (from_list_complete xs) as [ls [? ?]]; subst
         | [xs:tuple' ?A _ |- _] =>
           let a := fresh A in
           let ls := fresh "l" xs in
           destruct (from_list'_complete xs) as [a [ls [? ?]]]; subst
         end.

Lemma map_to_list {A B n ts} (f : A -> B)
  : List.map f (@to_list A n ts) = @to_list B n (map f ts).
Proof using Type.
  destruct n; simpl; [ reflexivity | ].
  induction n; simpl in *; [ reflexivity | ].
  destruct ts; simpl; congruence.
Qed.

Lemma to_list_map2 {A B C n xs ys} (f : A -> B -> C)
  : ListUtil.map2 f (@to_list A n xs) (@to_list B n ys) = @to_list C n (map2 f xs ys).
Proof using Type.
  tuples_from_lists; unfold map2, on_tuple2.
  repeat (rewrite to_list_from_list || rewrite from_list_to_list).
  reflexivity.
Qed.

Ltac tuple_maps_to_list_maps :=
  try eapply to_list_ext;
  tuples_from_lists;
  repeat (rewrite <-@map_to_list || rewrite <-@to_list_map2 ||
          rewrite @to_list_from_list || rewrite @from_list_to_list).

Lemma map_map2 {n A B C D} (f:A -> B -> C) (g:C -> D) (xs:tuple A n) (ys:tuple B n)
  : map g (map2 f xs ys) = map2 (fun a b => g (f a b)) xs ys.
Proof using Type.
  tuple_maps_to_list_maps; eauto using ListUtil.map_map2.
Qed.

Lemma map2_fst {n A B C} (f:A -> C) (xs:tuple A n) (ys:tuple B n)
  : map2 (fun a b => f a) xs ys = map f xs.
Proof using Type.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_fst.
Qed.

Lemma map2_snd {n A B C} (f:B -> C) (xs:tuple A n) (ys:tuple B n)
  : map2 (fun a b => f b) xs ys = map f ys.
Proof using Type.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_snd.
Qed.

Lemma map_id_ext {n A} (f : A -> A) (xs:tuple A n)
  : (forall x, f x = x) -> map f xs = xs.
Proof using Type.
  intros; tuple_maps_to_list_maps.
  transitivity (List.map (fun x => x) lxs).
  { eapply ListUtil.pointwise_map; cbv [pointwise_relation]; eauto. }
  { eapply List.map_id. }
Qed.

Lemma map_id {n A} (xs:tuple A n)
  : map (fun x => x) xs = xs.
Proof using Type. eapply map_id_ext; intros; reflexivity. Qed.

Lemma map2_map {n A B C A' B'} (f:A -> B -> C) (g:A' -> A) (h:B' -> B) (xs:tuple A' n) (ys:tuple B' n)
  : map2 f (map g xs) (map h ys) = map2 (fun a b => f (g a) (h b)) xs ys.
Proof using Type.
  tuple_maps_to_list_maps; eauto using ListUtil.map2_map.
Qed.

Lemma map_S' {n A B} (f:A -> B) (xs:tuple A (S n)) (x:A)
  : map (n:=S (S n)) f (xs, x) = (map (n:=S n) f xs, f x).
Proof using Type.
  tuple_maps_to_list_maps.
  let lxs := match goal with lxs : list _ |- _ => lxs end in
  destruct lxs as [|x' lxs']; [simpl in *; discriminate|].
  let x0 := match goal with H : _ = _ |- _ => H end in
  change ( f x :: List.map f (to_list (S n) (from_list (S n) (x' :: lxs') x0)) = f x :: to_list (S n) (map f (from_list (S n) (x' :: lxs') x0)) ).
  tuple_maps_to_list_maps.
  reflexivity.
Qed.

Definition map_S {n A B} (f:A -> B) (xs:tuple' A n) (x:A)
  : map (n:=S (S n)) f (xs, x) = (map (n:=S n) f xs, f x) := map_S' _ _ _.

Lemma map2_S' {n A B C} (f:A -> B -> C) (xs:tuple A (S n)) (ys:tuple B (S n)) (x:A) (y:B)
  : map2 (n:=S (S n)) f (xs, x) (ys, y) = (map2 (n:=S n) f xs ys, f x y).
Proof using Type.
  tuple_maps_to_list_maps.
  let lxs := match goal with lxs : list A |- _ => lxs end in
  destruct lxs as [|x' lxs']; [simpl in *; discriminate|].
  let lys := match goal with lxs : list B |- _ => lxs end in
  destruct lys as [|y' lys']; [simpl in *; discriminate|].
  change ( f x y ::  ListUtil.map2 f (to_list (S n) (from_list (S n) (x' :: lxs') x1))
    (to_list (S n) (from_list (S n) (y' :: lys') x0)) = f x y :: to_list (S n) (map2 f (from_list (S n) (x' :: lxs') x1) (from_list (S n) (y' :: lys') x0)) ).
  tuple_maps_to_list_maps.
  reflexivity.
Qed.

Definition map2_S {n A B C} (f:A -> B -> C) (xs:tuple' A n) (ys:tuple' B n) (x:A) (y:B)
  : map2 (n:=S (S n)) f (xs, x) (ys, y) = (map2 (n:=S n) f xs ys, f x y) := map2_S' _ _ _ _ _.

Lemma map2_map_fst {n A B C A'} (f:A -> B -> C) (g:A' -> A) (xs:tuple A' n) (ys:tuple B n)
  : map2 f (map g xs) ys = map2 (fun a b => f (g a) b) xs ys.
Proof using Type.
  rewrite <- (map2_map f g (fun x => x)), map_id; reflexivity.
Qed.

Lemma map2_map_snd {n A B C B'} (f:A -> B -> C) (g:B' -> B) (xs:tuple A n) (ys:tuple B' n)
  : map2 f xs (map g ys) = map2 (fun a b => f a (g b)) xs ys.
Proof using Type.
  rewrite <- (map2_map f (fun x => x) g), map_id; reflexivity.
Qed.

Lemma map_map {n A B C} (g : B -> C) (f : A -> B) (xs:tuple A n)
  : map g (map f xs) = map (fun x => g (f x)) xs.
Proof using Type. tuple_maps_to_list_maps; eapply List.map_map. Qed.

Section monad.
  Context (M : Type -> Type) (bind : forall X Y, M X -> (X -> M Y) -> M Y) (ret : forall X, X -> M X).
  Fixpoint lift_monad' {n A} {struct n}
    : tuple' (M A) n -> M (tuple' A n)
    := match n return tuple' (M A) n -> M (tuple' A n) with
       | 0 => fun t => t
       | S n' => fun xy => bind _ _ (@lift_monad' n' _ (fst xy)) (fun x' => bind _ _ (snd xy) (fun y' => ret _ (x', y')))
       end.
  Fixpoint push_monad' {n A} {struct n}
    : M (tuple' A n) -> tuple' (M A) n
    := match n return M (tuple' A n) -> tuple' (M A) n with
       | 0 => fun t => t
       | S n' => fun xy => (@push_monad' n' _ (bind _ _ xy (fun xy' => ret _ (fst xy'))),
                            bind _ _ xy (fun xy' => ret _ (snd xy')))
       end.
  Definition lift_monad {n A}
    : tuple (M A) n -> M (tuple A n)
    := match n return tuple (M A) n -> M (tuple A n) with
       | 0 => ret _
       | S n' => @lift_monad' n' A
       end.
  Definition push_monad {n A}
    : M (tuple A n) -> tuple (M A) n
    := match n return M (tuple A n) -> tuple (M A) n with
       | 0 => fun _ => tt
       | S n' => @push_monad' n' A
       end.
End monad.
Local Notation option_bind
  := (fun A B (x : option A) f => match x with
                                  | Some x' => f x'
                                  | None => None
                                  end).
Definition lift_option {n A} (xs : tuple (option A) n) : option (tuple A n)
  := lift_monad (fun T => option T) option_bind (fun T v => @Some T v) xs.
Definition push_option {n A} (xs : option (tuple A n)) : tuple (option A) n
  := push_monad (fun T => option T) option_bind (fun T v => @Some T v) xs.

Lemma lift_push_option {n A} (xs : option (tuple A (S n))) : lift_option (push_option xs) = xs.
Proof using Type.
  simpl in *.
  induction n; [ reflexivity | ].
  simpl in *; rewrite IHn; clear IHn.
  destruct xs as [ [? ?] | ]; reflexivity.
Qed.

Lemma push_lift_option {n A} {xs : tuple (option A) (S n)} {v}
  : lift_option xs = Some v <-> xs = push_option (Some v).
Proof using Type.
  simpl in *.
  induction n; [ reflexivity | ].
  specialize (IHn (fst xs) (fst v)).
  repeat first [ progress destruct_head_hnf' prod
               | progress destruct_head_hnf' and
               | progress destruct_head_hnf' iff
               | progress destruct_head_hnf' option
               | progress inversion_option
               | progress inversion_prod
               | progress subst
               | progress break_match
               | progress simpl in *
               | progress specialize_by exact eq_refl
               | reflexivity
               | split
               | intro ].
Qed.

Fixpoint fieldwise' {A B} (n:nat) (R:A -> B -> Prop) : tuple' A n -> tuple' B n -> Prop
  := match n with
     | 0 => R
     | S n' => fun (x y : tuple' _ _ * _)
               => @fieldwise' A B n' R (fst x) (fst y) /\ R (snd x) (snd y)
     end.
Definition fieldwise {A B} (n:nat) (R:A -> B -> Prop) : tuple A n -> tuple B n -> Prop
  := match n with
     | 0 => fun _ _ => True
     | S n' => fieldwise' n' R
     end.

Local Ltac Equivalence_fieldwise'_t :=
  let n := match goal with |- ?R (fieldwise' ?n _) => n end in
  let IHn := fresh in
  (* could use [dintuition] in 8.5 only, and remove the [destruct] *)
  repeat match goal with
         | [ H : Equivalence _ |- _ ] => destruct H
         | [ |- Equivalence _ ] => constructor
         end;
  induction n as [|? IHn]; [solve [auto]|];
  simpl; constructor; repeat intro; repeat intuition eauto.

Section Equivalence.
  Context {A} {R:relation A}.
  Global Instance Reflexive_fieldwise' {R_Reflexive:Reflexive R} {n:nat} : Reflexive (fieldwise' n R) | 5.
  Proof using Type. Equivalence_fieldwise'_t. Qed.
  Global Instance Symmetric_fieldwise' {R_Symmetric:Symmetric R} {n:nat} : Symmetric (fieldwise' n R) | 5.
  Proof using Type. Equivalence_fieldwise'_t. Qed.
  Global Instance Transitive_fieldwise' {R_Transitive:Transitive R} {n:nat} : Transitive (fieldwise' n R) | 5.
  Proof using Type. Equivalence_fieldwise'_t. Qed.
  Global Instance Equivalence_fieldwise' {R_equiv:Equivalence R} {n:nat} : Equivalence (fieldwise' n R).
  Proof using Type. constructor; exact _. Qed.

  Global Instance Reflexive_fieldwise {R_Reflexive:Reflexive R} : forall {n:nat}, Reflexive (fieldwise n R) | 5.
  Proof using Type. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Symmetric_fieldwise {R_Symmetric:Symmetric R} : forall {n:nat}, Symmetric (fieldwise n R) | 5.
  Proof using Type. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Transitive_fieldwise {R_Transitive:Transitive R} : forall {n:nat}, Transitive (fieldwise n R) | 5.
  Proof using Type. destruct n; (repeat constructor || exact _). Qed.
  Global Instance Equivalence_fieldwise {R_equiv:Equivalence R} : forall {n:nat}, Equivalence (fieldwise n R).
  Proof using Type. constructor; exact _. Qed.
End Equivalence.

Arguments fieldwise' {A B n} _ _ _.
Arguments fieldwise {A B n} _ _ _.

Global Instance dec_fieldwise' {A B R} {H : forall a b, Decidable (R a b)} : forall {n}, DecidableRel (@fieldwise' A B n R) | 10.
Proof.
  induction n; simpl @fieldwise'.
  { exact _. }
  { intros ??.
    exact _. }
Defined.

Global Instance dec_fieldwise {A B R} {H : forall a b, Decidable (R a b)} : forall {n}, DecidableRel (@fieldwise A B n R) | 10.
Proof.
  destruct n; unfold fieldwise; exact _.
Defined.

Global Instance dec_eq' {A} {HA : DecidableRel (@eq A)} : forall {n}, DecidableRel (@eq (tuple' A n)) | 10.
Proof.
  induction n; typeclasses eauto.
Defined.

Global Instance dec_eq {A} {HA : DecidableRel (@eq A)} : forall {n}, DecidableRel (@eq (tuple A n)) | 10.
Proof.
  destruct n; typeclasses eauto.
Defined.

Section fieldwise_map.
  Local Arguments map : simpl never.
  Lemma fieldwise'_map_eq {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple' A n) (t2:tuple' B n)
    : fieldwise' R (map (n:=S n) f t1) (map (n:=S n) g t2)
      = fieldwise' (fun x y => R (f x) (g y)) t1 t2.
  Proof using Type.
    induction n; [ reflexivity | ].
    destruct t1, t2.
    rewrite !map_S.
    simpl @fieldwise'; rewrite IHn; reflexivity.
  Qed.

  Lemma fieldwise_map_eq {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple A n) (t2:tuple B n)
    : fieldwise R (map f t1) (map g t2)
      = fieldwise (fun x y => R (f x) (g y)) t1 t2.
  Proof using Type.
    destruct n; [ reflexivity | apply fieldwise'_map_eq ].
  Qed.

  Lemma fieldwise'_map_iff {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple' A n) (t2:tuple' B n)
    : fieldwise' R (map (n:=S n) f t1) (map (n:=S n) g t2)
      <-> fieldwise' (fun x y => R (f x) (g y)) t1 t2.
  Proof using Type. rewrite fieldwise'_map_eq; reflexivity. Qed.

  Lemma fieldwise_map_iff {A A' B B' n} R (f:A -> A') (g:B -> B') (t1:tuple A n) (t2:tuple B n)
    : fieldwise R (map f t1) (map g t2)
      <-> fieldwise (fun x y => R (f x) (g y)) t1 t2.
  Proof using Type. rewrite fieldwise_map_eq; reflexivity. Qed.
End fieldwise_map.

Lemma fieldwise'_eq_iff {A n} x y : fieldwise' (@eq A) x y <-> @eq (tuple' A n) x y.
Proof using Type.
  induction n as [|n IHn]; [ reflexivity | ].
  simpl; rewrite IHn; split; [ destruct x, y | ]; simpl; intuition (subst; auto).
Qed.

Lemma fieldwise_eq_iff {A n} x y : fieldwise (@eq A) x y <-> @eq (tuple A n) x y.
Proof using Type.
  destruct n; [ destruct x, y | apply fieldwise'_eq_iff ]; simpl.
  tauto.
Qed.

Fixpoint fieldwiseb' {A B} (n:nat) (R:A->B->bool) (a:tuple' A n) (b:tuple' B n) {struct n} : bool.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (fieldwiseb' _ _ n R (fst a) (fst b) && R (snd a) (snd b))%bool. }
Defined.

Definition fieldwiseb {A B} (n:nat) (R:A->B->bool) (a:tuple A n) (b:tuple B n) : bool.
  destruct n; simpl @tuple in *.
  { exact true. }
  { exact (fieldwiseb' _ R a b). }
Defined.

Arguments fieldwiseb' {A B n} _ _ _.
Arguments fieldwiseb {A B n} _ _ _.

Lemma fieldwiseb'_fieldwise' :forall {A B} n R Rb
                                   (a:tuple' A n) (b:tuple' B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb' Rb a b = true <-> fieldwise' R a b).
Proof using Type.
  intros A B n R Rb a b H.
  revert n a b;
  induction n; intros; simpl @tuple' in *;
    simpl fieldwiseb'; simpl fieldwise'; auto.
  cbv beta.
  rewrite Bool.andb_true_iff.
  f_equiv; auto.
Qed.

Lemma fieldwiseb_fieldwise :forall {A B} n R Rb
                                   (a:tuple A n) (b:tuple B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb Rb a b = true <-> fieldwise R a b).
Proof using Type.
  intros A B n R Rb a b H; destruct n; simpl @tuple in *;
    simpl @fieldwiseb; simpl @fieldwise; try tauto.
  auto using fieldwiseb'_fieldwise'.
Qed.

Lemma map_ext {A B} (f g : A -> B) n (t : tuple A n) :
  (forall x : A, f x = g x) ->
  map f t = map g t.
Proof using Type.
  destruct n; [reflexivity|]; cbn in *.
  induction n; cbn in *; intro H; auto; [ ].
  rewrite IHn by assumption.
  rewrite H; reflexivity.
Qed.

Lemma map_ext_In {A B} (f g : A -> B) n (t : tuple A n) :
  (forall x, In x (to_list n t) -> f x = g x) ->
  map f t = map g t.
Proof using Type.
  destruct n; [reflexivity|]; cbn in *.
  induction n; cbn in *; intro H; auto; [ ].
  destruct t.
  rewrite IHn by auto using in_cons.
  rewrite H; auto using in_eq.
Qed.


Fixpoint from_list_default' {T} (d y:T) (n:nat) (xs:list T) : tuple' T n :=
  match n return tuple' T n with
  | 0 => y (* ignore high digits *)
  | S n' =>
         match xs return _ with
         | cons x xs' => (from_list_default' d x n' xs', y)
         | nil => (from_list_default' d d n' nil, y)
         end
  end.

Definition from_list_default {T} d (n:nat) (xs:list T) : tuple T n :=
match n return tuple T n with
| 0 => tt
| S n' =>
    match xs return _ with
    | cons x xs' => (from_list_default' d x n' xs')
    | nil => (from_list_default' d d n' nil)
    end
end.

Lemma from_list_default'_eq : forall {T} (d : T) xs n y pf,
  from_list_default' d y n xs = from_list' y n xs pf.
Proof using Type.
  induction xs as [|?? IHxs]; destruct n; intros; simpl in *;
    solve [ congruence (* 8.5 *)
          | erewrite IHxs; reflexivity ]. (* 8.4 *)
Qed.

Lemma from_list_default_eq : forall {T} (d : T) xs n pf,
  from_list_default d n xs = from_list n xs pf.
Proof using Type.
  induction xs; destruct n; intros; try solve [simpl in *; congruence].
  apply from_list_default'_eq.
Qed.

Fixpoint function R T n : Type :=
  match n with
  | O => R
  | S n' => T -> function R T n'
  end.

Fixpoint apply' {R T} (n:nat) : (T -> function R T n) -> tuple' T n -> R :=
  match n with
  | 0 => id
  | S n' => fun f x => apply' n' (f (snd x)) (fst x)
  end.

Definition apply {R T} (n:nat) : function R T n -> tuple T n -> R :=
  match n with
  | O => fun r _ => r
  | S n' => fun f x =>  apply' n' f x
  end.

Lemma fieldwise_to_list_iff : forall {T T' n} R (s : tuple T n) (t : tuple T' n),
    (fieldwise R s t <-> Forall2 R (to_list _ s) (to_list _ t)).
Proof using Type.
  induction n as [|n IHn]; intros R s t; split; intros.
  + constructor.
  + cbv [fieldwise]. auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [to_list']; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      constructor; intuition auto.
      apply IHn; auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [fieldwise']; auto.
      cbv [to_list'] in *; inversion H; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      inversion H; subst.
      split; try assumption.
      apply IHn; auto.
Qed.

Lemma fieldwise_map_from_list_iff
      {T0 T T'} R ls {n} pf1 pf2 (f : T0 -> T) (g : T0 -> T')
  : ((fieldwise R (map f (from_list n ls pf1))
                (map g (from_list n ls pf2)))
     <-> List.Forall (fun x => R (f x) (g x)) ls).
Proof using Type.
  split; intro H; revert H; revert dependent n;
    (induction ls as [|x xs IHxs]; intro n; [ | specialize (IHxs (pred n)) ]);
    destruct n as [|[|n]]; try destruct xs; simpl in *; auto;
      try congruence; intros; destruct_head'_and; eauto.
  { inversion H; auto. }
  { inversion H; auto. }
Qed.

Fixpoint eta_tuple'_dep {T n} : forall (P : tuple' T n -> Type),
    (forall ts : tuple' T n, P ts) -> forall ts : tuple' T n, P ts
  := match n with
     | 0 => fun P f => f
     | S n' => fun P f (ts : tuple' T n' * T)
               => let '(ts', x) := ts in
                  @eta_tuple'_dep T n' (fun ts' => P (ts', x)) (fun ts'' => f (ts'', x)) ts'
     end.
Definition eta_tuple' {T n B} : (tuple' T n -> B) -> (tuple' T n -> B)
  := @eta_tuple'_dep T n (fun _ => B).
Global Arguments eta_tuple' {T !n B} / _ _.
Definition eta_tuple_dep {T n} : forall (P : tuple T n -> Type),
    (forall ts : tuple T n, P ts) -> forall ts : tuple T n, P ts
  := match n with
     | 0 => fun P f => f
     | S n' => @eta_tuple'_dep T n'
     end.
Global Arguments eta_tuple_dep {T !n} P / _ _.
Definition eta_tuple {T n B} : (tuple T n -> B) -> (tuple T n -> B)
  := @eta_tuple_dep T n (fun _ => B).
Global Arguments eta_tuple {T !n B} / _ _.

Fixpoint eta_rtuple'_dep {T n} : forall (P : rtuple' T n -> Type),
    (forall ts : rtuple' T n, P ts) -> forall ts : rtuple' T n, P ts
  := match n with
     | 0 => fun P f => f
     | S n' => fun P f (ts : T * rtuple' T n')
               => let '(x, ts') := ts in
                  @eta_rtuple'_dep T n' (fun ts' => P (x, ts')) (fun ts'' => f (x, ts'')) ts'
     end.
Definition eta_rtuple' {T n B} : (rtuple' T n -> B) -> (rtuple' T n -> B)
  := @eta_rtuple'_dep T n (fun _ => B).
Global Arguments eta_rtuple' {T !n B} / _ _.
Definition eta_rtuple_dep {T n} : forall (P : rtuple T n -> Type),
    (forall ts : rtuple T n, P ts) -> forall ts : rtuple T n, P ts
  := match n with
     | 0 => fun P f => f
     | S n' => @eta_rtuple'_dep T n'
     end.
Global Arguments eta_rtuple_dep {T !n} P / _ _.
Definition eta_rtuple {T n B} : (rtuple T n -> B) -> (rtuple T n -> B)
  := @eta_rtuple_dep T n (fun _ => B).
Global Arguments eta_rtuple {T !n B} / _ _.

Lemma strip_eta_tuple'_dep {T n} P (f : forall ts : tuple' T n, P ts) ts
  : eta_tuple'_dep P f ts = f ts.
Proof using Type.
  revert dependent P; induction n; simpl in *; [ reflexivity | intros ].
  destruct_head prod.
  rewrite IHn; reflexivity.
Qed.
Lemma strip_eta_tuple' {T n B} (f : tuple' T n -> B) ts
  : eta_tuple' f ts = f ts.
Proof using Type. exact (strip_eta_tuple'_dep _ _ _). Qed.
Lemma strip_eta_tuple_dep {T n} P (f : forall ts : tuple T n, P ts) ts
  : eta_tuple_dep P f ts = f ts.
Proof using Type. destruct n; [ reflexivity | exact (strip_eta_tuple'_dep _ _ _) ]. Qed.
Lemma strip_eta_tuple {T n B} (f : tuple T n -> B) ts
  : eta_tuple f ts = f ts.
Proof using Type. exact (strip_eta_tuple_dep _ _ _). Qed.

Lemma strip_eta_rtuple'_dep {T n} P (f : forall ts : rtuple' T n, P ts) ts
  : eta_rtuple'_dep P f ts = f ts.
Proof using Type.
  revert dependent P; induction n; simpl in *; [ reflexivity | intros ].
  destruct_head prod.
  rewrite IHn; reflexivity.
Qed.
Lemma strip_eta_rtuple' {T n B} (f : rtuple' T n -> B) ts
  : eta_rtuple' f ts = f ts.
Proof using Type. exact (strip_eta_rtuple'_dep _ _ _). Qed.
Lemma strip_eta_rtuple_dep {T n} P (f : forall ts : rtuple T n, P ts) ts
  : eta_rtuple_dep P f ts = f ts.
Proof using Type. destruct n; [ reflexivity | exact (strip_eta_rtuple'_dep _ _ _) ]. Qed.
Lemma strip_eta_rtuple {T n B} (f : rtuple T n -> B) ts
  : eta_rtuple f ts = f ts.
Proof using Type. exact (strip_eta_rtuple_dep _ _ _). Qed.

Definition append {A n} (a : A) : tuple A n -> tuple A (S n) :=
  match n as n0 return (tuple A n0 -> tuple A (S n0)) with
  | O => fun t => a
  | S n' => fun t => (t,a)
  end.

Lemma hd_append {A n} (x: tuple A n) (a:A) : hd (append a x) = a.
Proof using Type. destruct n; reflexivity. Qed.

Lemma tl_append {A n} (x: tuple A n) (a:A) : tl (append a x) = x.
Proof using Type. destruct n; try destruct x; reflexivity. Qed.

Lemma subst_append {A n} (x : tuple A (S n)) : x = append (hd x) (tl x).
Proof using Type. destruct n; try destruct x; reflexivity. Qed.

Lemma to_list_append {A n} (x : tuple A n) (a : A) :
  to_list (S n) (append a x) = a :: to_list n x.
Proof using Type. destruct n; try destruct x; reflexivity. Qed.

Lemma from_list'_cons {A n} (a0 a1:A) (xs:list A) H :
  from_list' a0 (S n) (a1::xs) H = append (n:=S n) a0 (from_list' a1 n xs (length_cons_full _ _ _ H)).
Proof using Type. simpl; rewrite <-!from_list_default'_eq with (d:=a0); eauto. Qed.

Lemma from_list_cons {A n}:
  forall (xs : list A) a (H:length (a::xs)=S n),
  from_list (S n) (a :: xs) H = append a (from_list n xs (length_cons_full _ _ _ H)).
Proof using Type.
  destruct n; intros xs a H; destruct xs; distr_length; [reflexivity|].
  cbv [from_list]; rewrite !from_list'_cons.
  rewrite <-!from_list_default'_eq with (d:=a).
  reflexivity.
Qed.

Lemma map_append' {A B n} (f:A->B) : forall (x:tuple' A n) (a:A),
  map f (append (n:=S n) a x) = append (f a) (map (n:=S n) f x).
Proof using Type. reflexivity. Qed.

Lemma map_append {A B n} (f:A->B) : forall (x:tuple A n) (a:A),
  map f (append a x) = append (f a) (map f x).
Proof using Type. destruct n; auto using map_append'. Qed.

Lemma map2_append n A B C f xs ys x y :
  @map2 (S n) A B C f (append x xs) (append y ys)
  = append (f x y) (map2 f xs ys).
Proof using Type. destruct n; [reflexivity|]. apply map2_S'. Qed.

Fixpoint nth_default {A m} (d:A) n : tuple A m -> A :=
  match m, n with
  | O, _ => fun _ => d
  | S m', O => hd
  | S m', S n' => fun x => nth_default d n' (tl x)
  end.

Fixpoint left_tl {T n} : tuple T (S n) -> tuple T n :=
  match n with
  | O => fun _ => tt
  | S n' => fun xs => append (hd xs) (left_tl (tl xs))
  end.

Fixpoint left_hd {T n} : tuple T (S n) -> T :=
  match n with
  | O => fun x => x
  | S n' => fun xs => left_hd (tl xs)
  end.

Fixpoint left_append {T n} (x : T) : tuple T n -> tuple T (S n) :=
  match n with
  | O => fun _ => x
  | S n' => fun xs => append (hd xs) (left_append x (tl xs))
  end.

Lemma left_append_left_hd {T n} (xs : tuple T n) x :
  left_hd (left_append x xs) = x.
Proof using Type. induction n; [reflexivity | apply IHn]. Qed.

Lemma left_append_left_tl {T n} (xs : tuple T n) x :
  left_tl (left_append x xs) = xs.
Proof using Type.
  induction n; [destruct xs; reflexivity|].
  simpl. rewrite IHn.
  symmetry; apply subst_append.
Qed.

Lemma left_append_append {T n} (xs : tuple T n) r l :
  left_append l (append r xs) = append r (left_append l xs).
Proof using Type. destruct n; reflexivity. Qed.

Lemma left_tl_append {T n} (xs : tuple T (S n)) x:
  left_tl (append x xs) = append x (left_tl xs).
Proof using Type. reflexivity. Qed.

Lemma left_hd_append {T n} (xs : tuple T (S n)) x:
  left_hd (append x xs) = left_hd xs.
Proof using Type. reflexivity. Qed.

Lemma tl_left_append {T n} (xs : tuple T (S n)) x :
  tl (left_append x xs) = left_append x (tl xs).
Proof using Type. destruct n; reflexivity. Qed.

Lemma hd_left_append {T n} (xs : tuple T (S n)) x :
  hd (left_append x xs) = hd xs.
Proof using Type. destruct n; reflexivity. Qed.

Lemma map'_left_append {A B n} f xs x0 :
    @map' A B f (S n) (left_append (n:=S n) x0 xs)
    = left_append (n:=S n) (f x0) (map' f xs).
Proof using Type.
    induction n; try reflexivity.
    transitivity (map' f (tl (left_append x0 xs)), f (hd (left_append x0 xs))); [reflexivity|].
    rewrite tl_left_append, IHn. reflexivity.
Qed.

Lemma map_left_append {A B n} f xs x0 :
  @map (S n) A B f (left_append x0 xs)
  = left_append (f x0) (map f xs).
Proof using Type.
  destruct n; [ destruct xs; reflexivity| apply map'_left_append].
Qed.

Lemma subst_left_append {T n} (xs : tuple T (S n)) :
  xs = left_append (left_hd xs) (left_tl xs).
Proof using Type.
  induction n; [reflexivity|].
  simpl tuple in *; destruct xs as [xs x0].
  simpl; rewrite hd_append, tl_append.
  rewrite <-IHn; reflexivity.
Qed.

(* map operation that carries state *)
(* first argument to f is index in tuple *)
Fixpoint mapi_with' {T A B n} i (f: nat->T->A->T*B) (start:T)
  : tuple' A n -> T * tuple' B n :=
  match n as n0 return (tuple' A n0 -> T * tuple' B n0) with
  | O => fun ys => f i start ys
  | S n' => fun ys =>
              (fst (mapi_with' (S i) f (fst (f i start (hd ys))) (tl ys)),
               (snd (mapi_with' (S i) f (fst (f i start (hd ys))) (tl ys)),
               snd (f i start (hd ys))))
  end.

Definition mapi_with {T A B n} (f: nat->T->A->T*B) (start:T)
  : tuple A n -> T * tuple B n :=
  match n as n0 return (tuple A n0 -> T * tuple B n0) with
  | O => fun ys => (start, tt)
  | S n' => fun ys => mapi_with' 0 f start ys
  end.

Lemma mapi_with'_step {T A B n} i f start inp :
  @mapi_with' T A B (S n) i f start inp =
  (fst (mapi_with' (S i) f (fst (f i start (hd inp))) (tl inp)),
   (snd (mapi_with'(S i) f (fst (f i start (hd inp))) (tl inp)), snd (f i start (hd inp)))).
Proof using Type. reflexivity. Qed.

Lemma mapi_with'_left_step {T A B n} f a0:
  forall i start (xs : tuple' A n),
    @mapi_with' T A B (S n) i f start (left_append (n:=S n) a0 xs)
    = (fst (f (i + S n)%nat (fst (mapi_with' i f start xs)) a0),
       left_append (n:=S n)
                   (snd (f (i + S n)%nat
                           (fst (mapi_with' i f start xs)) a0))
                   (snd (mapi_with' i f start xs))).
Proof using Type.
  induction n as [|? IHn]; intros; [subst; simpl; repeat f_equal; lia|].
  rewrite mapi_with'_step; autorewrite with cancel_pair.
  rewrite tl_left_append, hd_left_append.
  erewrite IHn by reflexivity; subst; autorewrite with cancel_pair.
  match goal with |- context [(?xs ,?x0)] =>
                  change (xs, x0) with (append x0 xs) end.
  rewrite <-left_append_append.
  repeat (f_equal; try lia).
Qed.

Lemma mapi_with'_linvariant {T A B n} start f
      (P : forall n, T -> tuple A n -> tuple B n -> Prop)
      (P_holds : forall n st x0 xs ys,
          (st = fst (mapi_with f start xs)) ->
          (ys = snd (mapi_with f start xs)) ->
          P n st xs ys ->
          P (S n) (fst (f n st x0))
            (left_append x0 xs)
            (left_append (snd (f n st x0)) ys))
      (P_base : P 0%nat start tt tt) (inp : tuple A n):
  P n (fst (mapi_with f start inp)) inp (snd (mapi_with f start inp)).
Proof using Type.
  induction n; [destruct inp; apply P_base |].
  rewrite (subst_left_append inp).
  cbv [mapi_with]. specialize (P_holds n).
  destruct n.
  { apply (P_holds _ inp tt tt (eq_refl _) (eq_refl _)).
    apply P_base. }
  { rewrite mapi_with'_left_step.
    autorewrite with cancel_pair natsimplify.
    apply P_holds; try apply IHn; reflexivity. }
Qed.


Fixpoint repeat {A} (a:A) n : tuple A n :=
  match n with
  | O => tt
  | S n' => append a (repeat a n')
  end.

Lemma map_repeat {A B} (f:A->B) (a: A) n :
  map f (repeat a n) = repeat (f a) n.
Proof using Type.
  induction n; simpl repeat; [reflexivity|rewrite map_append; congruence].
Qed.

Lemma to_list_repeat {A} (a:A) n : to_list _ (repeat a n) = List.repeat a n.
Proof using Type. induction n as [|n]; [reflexivity|destruct n; simpl in *; congruence]. Qed.


Local Ltac fieldwise_t :=
  repeat first [ progress simpl in *
               | apply conj
               | intro
               | progress subst
               | assumption
               | solve [ auto ]
               | match goal with
                 | [ H : _ * _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : _ <-> _ |- _ ] => destruct H
                 | [ H : False |- _ ] => exfalso; assumption
                 | [ H : Forall2 _ (_::_) (_::_) |- _ ] => inversion H; clear H
                 | [ |- Forall2 _ (_::_) (_::_) ] => constructor
                 | [ H : _ \/ _ |- _ ] => destruct H
                 | [ H : tuple' _ ?n, IH : forall x : tuple' _ ?n, _ |- _ ]
                   => specialize (IH H)
                 end ].
Lemma fieldwise_In_to_list_repeat_l_iff {T T' n} R (s : tuple T n) (t : T')
  : fieldwise R (repeat t n) s <-> (forall x, List.In x (to_list _ s) -> R t x).
Proof using Type.
  rewrite fieldwise_to_list_iff; destruct n as [|n]; [ | induction n ]; fieldwise_t.
Qed.
Lemma fieldwise_In_to_list_repeat_r_iff {T T' n} R (s : tuple T n) (t : T')
  : fieldwise R s (repeat t n) <-> (forall x, List.In x (to_list _ s) -> R x t).
Proof using Type.
  rewrite fieldwise_to_list_iff; destruct n as [|n]; [ | induction n ]; fieldwise_t.
Qed.

Global Instance map'_Proper : forall {n A B}, Proper (pointwise_relation _ eq ==> eq ==> eq) (fun f => @map' A B f n) | 10.
Proof using Type.
  induction n as [|n IHn]; intros.
  { compute; intros; subst; auto. }
  { cbv [pointwise_relation Proper respectful] in *.
    intros f g Hfg x y ?; subst y.
    simpl; erewrite IHn by first [ eassumption | eauto ].
    congruence. }
Qed.

Global Instance map_Proper : forall {n A B}, Proper (pointwise_relation _ eq ==> eq ==> eq) (@map n A B) | 10.
Proof using Type.
  destruct n; intros; [ | apply map'_Proper ].
  { repeat (intros [] || intro); auto. }
Qed.

Lemma fieldwise'_lift_and {n A B R1 R2} x y
  : (@fieldwise' A B n R1 x y /\ @fieldwise' A B n R2 x y)
    <-> (@fieldwise' A B n (fun a b => R1 a b /\ R2 a b) x y).
Proof using Type.
  induction n as [|n IHn]; intros.
  { compute; intros; subst; auto. }
  { simpl; rewrite <- IHn; tauto. }
Qed.

Lemma fieldwise_lift_and {n A B R1 R2} x y
  : (@fieldwise A B n R1 x y /\ @fieldwise A B n R2 x y)
    <-> (@fieldwise A B n (fun a b => R1 a b /\ R2 a b) x y).
Proof using Type.
  destruct n; [ compute; tauto | apply fieldwise'_lift_and ].
Qed.


Lemma fieldwise'_Proper_gen_dep {A B A' B'} {RA RB : _ -> _ -> Prop} {R}
       {R_Proper_and : Proper (R ==> R ==> R) and}
  : forall {n},
    forall
      (f : A -> B -> Prop)
      (g : A' -> B' -> Prop)
      (Hfg : forall a a', RA a a' -> forall b b', RB b b' -> R (f a b) (g a' b'))
      x x'
      (Hx : fieldwise' RA x x')
      y y'
      (Hy : fieldwise' RB y y'),
      R (@fieldwise' A B n f x y) (@fieldwise' A' B' n g x' y').
Proof using Type.
  induction n as [|n IHn].
  { compute; intros; subst; auto. }
  { cbv [pointwise_relation Proper respectful] in *.
    intros f g Hfg x y H x' y' H'.
    simpl in *; apply R_Proper_and; destruct H, H'; auto. }
Qed.

Lemma fieldwise_Proper_gen_dep {A B A' B'} {RA RB : _ -> _ -> Prop} {R}
      {R_Proper_and : Proper (R ==> R ==> R) and}
      (R_True : R True True)
  : forall {n},
    forall
      (f : A -> B -> Prop)
      (g : A' -> B' -> Prop)
      (Hfg : forall a a', RA a a' -> forall b b', RB b b' -> R (f a b) (g a' b'))
      x x'
      (Hx : fieldwise RA x x')
      y y'
      (Hy : fieldwise RB y y'),
      R (@fieldwise A B n f x y) (@fieldwise A' B' n g x' y').
Proof using Type.
  destruct n; intros; [ | eapply fieldwise'_Proper_gen_dep; eauto ].
  compute; trivial.
Qed.

Global Instance fieldwise'_Proper_gen {A B RA RB R}
       {R_Proper_and : Proper (R ==> R ==> R) and}
  : forall {n}, Proper ((RA ==> RB ==> R) ==> fieldwise' RA ==> fieldwise' RB ==> R) (@fieldwise' A B n) | 10.
Proof using Type.
  cbv [Proper respectful].
  eapply (@fieldwise'_Proper_gen_dep A B A B RA RB R); assumption.
Qed.

Global Instance fieldwise_Proper_gen {A B RA RB R}
       {R_Proper_and : Proper (R ==> R ==> R) and}
       (R_True : R True True)
  : forall {n}, Proper ((RA ==> RB ==> R) ==> fieldwise RA ==> fieldwise RB ==> R) (@fieldwise A B n) | 10.
Proof using Type.
  cbv [Proper respectful].
  eapply (@fieldwise_Proper_gen_dep A B A B RA RB R); assumption.
Qed.

Global Instance fieldwise'_Proper_gen_eq {A B R}
       {R_Proper_and : Proper (R ==> R ==> R) and}
  : forall {n}, Proper (pointwise_relation _ (pointwise_relation _ R) ==> eq ==> eq ==> R) (@fieldwise' A B n) | 10.
Proof using Type.
  cbv [pointwise_relation].
  repeat intro; subst; apply (@fieldwise'_Proper_gen A B eq eq); try assumption;
    repeat intro; subst; auto; reflexivity.
Qed.

Global Instance fieldwise_Proper_gen_eq {A B R}
       {R_Proper_and : Proper (R ==> R ==> R) and}
       (R_True : R True True)
  : forall {n}, Proper (pointwise_relation _ (pointwise_relation _ R) ==> eq ==> eq ==> R) (@fieldwise A B n) | 10.
Proof using Type.
  cbv [pointwise_relation].
  repeat intro; subst; apply (@fieldwise_Proper_gen A B eq eq); try assumption;
    repeat intro; subst; auto; reflexivity.
Qed.

Lemma nth_default_to_list' {A} n (xs : tuple' A n) (d : A) :
  forall i, List.nth_default d (to_list' n xs) i = @nth_default A (S n) d i xs.
Proof using Type.
  revert xs; induction n, i; cbn; break_match; intros;
    rewrite ?ListUtil.nth_default_cons_S; try reflexivity; rewrite ?IHn; eauto using ListUtil.nth_default_nil.
Qed.
Lemma nth_default_to_list {A} n (xs : tuple A n) (d : A) :
  forall i, List.nth_default d (to_list _ xs) i = nth_default d i xs.
Proof using Type.
  destruct n; cbv [Tuple.tuple Tuple.to_list] in *.
  { destruct i; reflexivity. }
  eapply nth_default_to_list'.
Qed.

Require Import Coq.Lists.SetoidList.

Global Instance fieldwise'_Proper
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ impl) ==> eq ==> eq ==> impl) (@fieldwise' A B n) | 10.
Proof using Type. intros; apply fieldwise'_Proper_gen_eq. Qed.

Global Instance fieldwise_Proper
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ impl) ==> eq ==> eq ==> impl) (@fieldwise A B n) | 10.
Proof using Type. intros; now apply fieldwise_Proper_gen_eq. Qed.

Global Instance fieldwise'_Proper_iff
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@fieldwise' A B n) | 10.
Proof using Type. intros; apply fieldwise'_Proper_gen_eq. Qed.

Global Instance fieldwise_Proper_iff
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@fieldwise A B n) | 10.
Proof using Type. intros; now apply fieldwise_Proper_gen_eq. Qed.

Global Instance fieldwise'_Proper_flip_impl
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ (flip impl)) ==> eq ==> eq ==> flip impl) (@fieldwise' A B n) | 10.
Proof using Type. intros; apply @fieldwise'_Proper_gen_eq; compute; tauto. Qed.

Global Instance fieldwise_Proper_flip_impl
  : forall {n A B}, Proper (pointwise_relation _ (pointwise_relation _ (flip impl)) ==> eq ==> eq ==> flip impl) (@fieldwise A B n) | 10.
Proof using Type. intros; apply @fieldwise_Proper_gen_eq; compute; tauto. Qed.
 *)

(* right-assciated by default *)
(* Fixpoint tuple (T: Type) n : Type :=
  match n with
  | O => unit
  | S n' => T * tuple T n'
  end.

(** left-associated tuples *)
Fixpoint ltuple T n : Type :=
  match n with
  | O => unit
  | S n' => (ltuple T n' * T)%type
  end.

Fixpoint consl T n {struct n} : ltuple T n -> T -> ltuple T (S n) := 
  match n return ltuple T n -> T -> ltuple T (S n) with
  | O => fun x y => (x, y)
  | S n' => fun x y => (@consl T n' (fst x) y, snd x)
  end.
Global Arguments consl {T n} _ _.

Fixpoint cons T n {struct n} : T -> tuple T n -> tuple T (S n) := 
  match n return T -> tuple T n -> tuple T (S n) with
  | O => fun x xs => (x, xs)
  | S n' => fun x xs => (fst xs, @cons T n' x (snd xs))
  end.
Global Arguments cons {T n} _ _.

Fixpoint assoc_left {n T} {struct n} : tuple T n -> ltuple T n := 
  match n return tuple T n -> ltuple T n with
  | O => fun x => x
  | S n' => fun ts => 
    let xs := @assoc_left n' T (snd ts) in
    let x := fst ts in
    consl xs x
  end.

Fixpoint assoc_right {n T} {struct n} : ltuple T n -> tuple T n := 
  match n return ltuple T n -> tuple T n with
  | 0 => fun x => x
  | S n' => fun ts => 
    let xs := @assoc_right n' T (fst ts) in
    let x := snd ts in
    cons x xs
  end.

Definition tl {T n} : tuple T (S n) -> tuple T n := @snd _ _.
Definition hd {T n} : tuple T (S n) -> T.
Proof. intros t. destruct t. trivial. Defined.

Fixpoint to_list {T} (n:nat) {struct n} : tuple T n -> list T :=
  match n return tuple T n -> list T with
  | O => fun _ => nil%list
  | S n' => fun '(x, xs') => (x :: to_list n' xs')%list
  end.

Program Fixpoint from_list {T} (n:nat) (xs:list T) : length xs = n -> tuple T n :=
  match n return _ with
  | 0 =>
    match xs return (length xs = 0 -> tuple T 0) with
    | nil => fun _ => tt
    | _ => _ (* impossible *)
    end
  | S n' =>
    match xs return (length xs = S n' -> tuple T (S n')) with
    | List.cons x xs' => fun _ => (x, from_list n' xs' _)
    | _ => _ (* impossible *)
    end
  end.
Definition from_list' {T} (xs: list T) : tuple T (length xs).
Proof. induction xs; simpl. exact tt. auto. Defined.
Compute (from_list' (1::2::3::nil)). *)

Declare Scope tuple_scope.
Delimit Scope tuple_scope with tuple.
Global Notation "T ^ n" := (tuple T n) : type_scope.
Global Notation "w [ i ]" := (Tuple.nth_Default i w) (at level 20) : tuple_scope.
Global Notation "' xs" := (to_list _ xs) (at level 19) : tuple_scope.

Require Import Circom.Circom.
Ltac pose_lengths :=
  repeat match goal with
    | [ _: context[?xs] |- _ ] =>
    lazymatch type of xs with
    | tuple Circom.F ?k =>
      let t := type of (length_to_list xs) in
      lazymatch goal with
      (* already posed *)
      | [ _: t |- _] => fail
      | _ => 
        let Hlen := fresh "_Hlen" in
        pose proof (length_to_list xs) as Hlen;
        move Hlen at top
      end
    | _ => fail
    end
  end.