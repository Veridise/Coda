(** * DSL benchmark utilities *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

From Circom Require Import Circom DSL Util Default Tuple ListUtil LibTactics Simplify Repr ReprZ Signed.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.


Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Definition as_le := RZ.as_le.
Definition as_be := RZ.as_be.
Definition as_le_f := Repr.as_le 1%nat.
Local Notation "[| xs | n ]" := (RZ.as_le n xs).
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).

(* TODO *)
Definition to_le_f (n : nat) (f : F) : list F := nil.


Definition f_and (x: F) (y: F) := x = 1%F /\ y = 1%F.
Definition f_or (x: F) (y: F) := x = 1%F \/ y = 1%F.
Definition f_not (x: F) := x = 0%F.
Definition f_nand (x: F) (y: F) := ~(x = 1%F /\ y = 1%F).
Definition f_nor (x: F) (y: F) := ~(x = 1%F \/ y = 1%F).
Definition f_xor (x: F) (y: F) := x <> y.

Ltac unwrap_coda := unwrap_C; unfold as_le, as_be, f_and, f_or, f_nor, f_xor, f_not in *.


Definition sum := DSLL.sumL_F.
Definition take {A} i (xs : list A) := xs[:i].
Definition drop {A} i (xs : list A) := xs[i:].


Lemma binary_not0: forall (x:F), ((x = 0 \/ x = 1) -> x <> 0 -> x = 1)%F.
Proof. intuit. Qed.

Lemma binary_not1: forall (x:F), ((x = 0 \/ x = 1) -> x <> 1 -> x = 0)%F.
Proof. intuit. Qed.
Ltac ind x :=
  match goal with
  | [H: (x = 0%F \/ x = 1 %F) /\ (x = 1%F -> ?P) /\ (x = 0%F -> ?Q) |- _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    let Hx' := fresh "H" in
    destruct H as [H1 [H2 H3]];
    try match goal with
    | [ Hx: x <> 1%F |- _ ] =>
      apply binary_not1 in Hx; try apply H1
    | [ Hx: x <> 0%F |- _ ] =>
      apply binary_not0 in Hx; try apply H1
    end;
    match goal with
    | [ Hx: x = 1%F |- _] =>
      pose proof Hx as Hx';
      apply H2 in Hx;
      subst x
    | [ Hx: x = 0%F |- _] =>
      pose proof Hx as Hx';
      apply H3 in Hx;
      subst x
    end;
    clear H1; clear H2; clear H3
  end.
Ltac ind' x :=
    let Hbin := fresh "Hin" in
  assert (Hbin: binary x) by intuit;
  destruct Hbin; ind x.


Ltac assert_consequence H :=
  match type of H with
  | ?P -> ?Q -> ?R => assert R
  end.


Lemma F_to_Z_nonneg: forall (x:F), 0 <= ^x.
Proof.
  intros. apply F.to_Z_range. lia.
Qed.

Ltac pose_nonneg := repeat match goal with
| [ |- context[F.to_Z ?x ] ] =>
  let t := type of (F_to_Z_nonneg x) in
  lazymatch goal with
  (* already posed *)
  | [ _: t |- _] => fail
  | _ => 
    let Hnonneg := fresh "_Hnonneg" in
    pose proof (F_to_Z_nonneg x) as Hnonneg
    ; move Hnonneg at top
  end
| _ => fail
end.


Ltac pose_as_le_nonneg := repeat match goal with
| [ H: context[RZ.as_le ?n ?xs ] |- _ ] =>
let t := type of (RZU.as_le_nonneg n xs) in
lazymatch goal with
(* already posed *)
| [ _: t |- _] => fail
| _ => 
  let Hnonneg := fresh "_Hnonneg" in
  pose proof (RZU.as_le_nonneg n xs) as Hnonneg
  ;move Hnonneg at top
end
| [ |- context[RZ.as_le ?n ?xs ] ] =>
  let t := type of (RZU.as_le_nonneg n xs) in
  lazymatch goal with
  (* already posed *)
  | [ _: t |- _] => fail
  | _ => 
    let Hnonneg := fresh "_Hnonneg" in
    pose proof (RZU.as_le_nonneg n xs) as Hnonneg
    ;move Hnonneg at top
  end
| _ => fail
end.

Ltac switch dst l :=
  let H := fresh "H" in
  match goal with
  | [ |- ?G ] =>
    assert (H: G <-> dst) by l;
    apply H;
    clear H
  end.


Lemma sum_step :
  forall (xs : list F) (i : nat),
    i < length xs ->
    (sum (xs [:i]) + xs ! i)%F = sum (xs [:i + 1]).
Proof.
  unwrap_C.
  induction xs; intros;
    try (simpl in H; lia).
  destruct i; simpl; try fqsatz.
  assert (i < length xs).
  { simpl in H; lia. }
  simpl_default; auto.
  rewrite <- IHxs; auto.
  fqsatz.
Qed.


Lemma Forall_nth_default :
  forall [A] [H : Default A] (P : A -> Prop) (xs : list A),
    (Forall P xs <-> forall (i : nat), i < length xs -> P (xs ! i)).
Proof.
  unfold "!"; split; intros.
  - rewrite nth_default_eq.
    apply Forall_nth; auto; lia.
  - induction xs.
    + apply Forall_nil.
    + apply Forall_cons.
      * apply (H0 0%nat). simpl; lia.
      * apply IHxs; intros.
        assert (
            S i < length (a :: xs)
          ) by (simpl; lia).
        apply H0 in H2.
        rewrite nth_default_eq in *.
        simpl in H2; auto.
Qed.


(* #[global]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[global]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[global]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[global]Hint Extern 10 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[global]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[global]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[global]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[global]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[global]Hint Extern 10 (_ < _) => lia: core.
#[global]Hint Extern 10 (_ < _)%nat => lia: core.
#[global]Hint Extern 10 (_ <= _) => lia: core.
#[global]Hint Extern 10 (_ <= _)%nat => lia: core.
#[global]Hint Extern 10 (_ > _) => lia: core.
#[global]Hint Extern 10 (_ > _)%nat => lia: core.
#[global]Hint Extern 10 (_ >= _) => lia: core.
#[global]Hint Extern 10 (_ >= _)%nat => lia: core.
#[global]Hint Extern 10 (S _ = S _) => f_equal: core.  *)


Ltac lift := apply f_equal with (f:=F.to_Z); Signed.solve_to_Z.
Ltac lift' H := apply f_equal with (f:=F.to_Z) in H; Signed.solve_to_Z' H.

Lemma list_eq: forall {A: Type} {H: Default A} (l1 l2: list A),
  length l1 = length l2 ->
  (forall (i: nat), 0 <= i < length l1 -> l1!i = l2!i) -> l1 = l2.
Admitted.

Lemma Zmod_once: forall a b c,
  0 <= a < c ->
  0 <= b < c ->
  c <= a + b ->
  ((a + b) mod c = (a + b) - c)%Z.
Proof.
  intros a b c. intros.
  rewrite Zmod_eq by lia.
  assert ((a+b)/c < 2). apply Zdiv_lt_upper_bound. lia. lia.
  assert (1 <= (a+b)/c). apply Zdiv_le_lower_bound; lia.
  nia.
Qed.

Lemma mod_sub_lt: forall a b c,
  0 <= a < c ->
  0 <= b < c ->
  a < b ->
  ((a-b) mod c = a-b+c)%Z.
Proof.
  intros a b c. intros.
  replace ((a - b) mod c) with (((a-b)+c) mod c).
  rewrite Zmod_small. auto.
  lia.
  rewrite Zplus_mod.
  rewrite Z_mod_same_full. simplify.
  rewrite Zmod_mod.
  auto.
Qed.

Lemma ub_as_le: forall xs n (k:nat),
  [| xs |n] <= 2^(n*k)-1 ->
  (forall (i: nat), i >= k -> xs!i = 0%F).
Admitted.

Ltac hammer := solve [trivial | (intuit; subst; auto)].
