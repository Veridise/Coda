Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Fixpoint iter' {A: Type} (m n: nat) (f: nat -> A -> A) (a: A) : A :=
  match m with
  | O => a
  | S m' => iter' m' n f (f (n-m) a)
  end.

Definition iter {A: Type} (n: nat) := @iter' A n n.


Hint Unfold iter.

Lemma iter'_S {A: Type}:
  forall f i j (a: A),
    iter' (S i) (S j) f a = f j (iter' i j f a).
Proof.
  induction i; intros.
  - simpl. replace (j - 0) with j by lia. reflexivity.
  - simpl. apply IHi.
Qed.

Theorem iter_inv {A: Type}:
  forall (P: nat -> A -> Prop) f a,
  P 0 a ->
  (forall j b, P j b -> P (S j) (f j b)) ->
  (forall i, P i (iter i f a)).
Proof.
  intros. induction i; intros.
  - auto.
  - apply H0 in IHi.
    replace (iter (S i) f a) with (f i (iter i f a)); auto.
    unfold iter. rewrite iter'_S. reflexivity.
Qed.


(* Section _iter.
Definition arith_sum := iter (length xs) (fun i x => x + nth i xs 0) 0.
Compute arith_sum.
Theorem arith_sum_correct:
End _iter. *)