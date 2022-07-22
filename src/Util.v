Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Create HintDb iter discriminated.

Fixpoint iter' (A: Type) (m n: nat) (f: nat -> A -> A) (a: A) : A :=
  match m with
  | O => a
  | S m' => iter' A m' n f (f (n-m) a)
  end.
  
Lemma iter'_S:
  forall A f i j (a: A),
  iter' A (S i) (S j) f a = f j (iter' A i j f a).
Proof.
  induction i; intros.
  - simpl. replace (j - 0) with j by lia. reflexivity.
  - eauto.
Qed.

Local Hint Rewrite iter'_S : iter.
Definition iter (A: Type) (n: nat) := @iter' A n n.
Local Hint Unfold iter : iter.

Theorem iter_inv {A: Type} (Inv: nat -> A -> Prop):
  forall f a i,
  Inv 0 a ->
  (forall j b, Inv j b -> j < i -> Inv (S j) (f j b)) ->
  Inv i (iter A i f a).
Proof.
  intros f a.
  induction i; intros H0 Hind; eauto.
  - replace (iter A (S i) f a) with (f i (iter A i f a)) by
      (unfold iter; rewrite iter'_S; reflexivity).
    apply Hind. apply IHi; auto. lia.
Qed.

Arguments iter {A}.


(* Section _iter.
Print iter.
Definition xs := [0;1;2;3].
Definition arith_sum := iter (length xs) (fun i x => x + nth i xs 0) 0.
Compute arith_sum.
Theorem arith_sum_correct:
End _iter. *)