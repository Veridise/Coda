Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.ZUtil Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Circom.Circom.

Module DSL (C: CIRCOM).

Import C.

Import ListNotations.

Create HintDb iter discriminated.

Local Open Scope nat_scope.

Section iter.

Variable A: Type.
Variable f: nat -> A -> A.

(* functional iteration *)

Fixpoint iter' (m n: nat) (a: A) : A :=
  match m with
  | O => a
  | S m' => iter' m' n (f (n-m) a)
  end.
  
Lemma iter'_S:
  forall i j a,
  iter' (S i) (S j) a = f j (iter' i j a).
Proof.
  induction i; intros.
  - simpl. replace (j - 0) with j by lia. reflexivity.
  - eauto.
Qed.

Local Hint Rewrite iter'_S : iter.
Definition iter (n: nat) := iter' n n.
Local Hint Unfold iter : iter.

Theorem iter_inv (Inv: nat -> A -> Prop):
  forall a i,
  Inv 0 a ->
  (forall j b, Inv j b -> j < i -> Inv (S j) (f j b)) ->
  Inv i (iter i a).
Proof.
  intros a.
  induction i; intros H0 Hind; eauto.
  - replace (iter (S i) a) with (f i (iter i a)) by
      (unfold iter; rewrite iter'_S; reflexivity).
    apply Hind. apply IHi; auto. lia.
Qed.

End iter.

Arguments iter' {A}.
Arguments iter {A}.


Section init.

Variable A: Type.
Variable f: nat -> A.

Fixpoint init' (i n m: nat) : list A :=
  match m with
  | O => nil
  | S m' => if dec (i >= n) then nil else f i :: init' (S i) n m'
  end.

Definition init (i n: nat) := init' i n n.

Lemma init'_length: forall m i n, length (init' i n m) = min m (n-i).
Proof.
  induction m; simpl; intros.
  reflexivity.
  destruct (dec (i>=n)).
  subst. replace (n-i) with O by lia. auto.
  destruct (n-i) eqn:E. lia.
  simpl. rewrite IHm. lia.
Qed.
  

Lemma init_length: forall i n, length (init i n) = n - i.
Proof.
  intros. unfold init. rewrite init'_length. lia.
Qed.

Definition initT (i n: nat) := from_list (n-i) (init i n).
Definition initT0 (n: nat) := from_list (n) (init O n).

End init.

Arguments init {A}.
Arguments initT {A}.
Arguments initT0 {A}.

Section opsT.

Local Open Scope F_scope.
Definition opT {n} (op: F -> F -> F) (xs ys: tuple F n) := map2 op xs ys.
Definition addT {n} := @opT n (fun x y => x + y : F).
Definition mulT {n} := @opT n (fun x y => x * y : F).
Definition scaleT {n} (k: F) (xs: tuple F n) := map (fun x => k * x) xs.
Definition eqT {A n} (xs ys: tuple A n) := xs = ys.
End opsT.

End DSL.