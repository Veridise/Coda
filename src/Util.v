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

Module Util.

Import Circom.

Import ListNotations.

(* pigeon hole principle *)

Lemma list_gen_ind_rec {X : Type} (P : list X -> Prop) 
(HP : forall l, (forall m, length m < length l -> P m)%nat -> P l)
n : forall l, (length l < n)%nat -> P l.
Proof.
  induction n as [ | n IHn ]; intros l Hl.
  exfalso; revert Hl. intros; lia.
  apply HP.
  intros m Hm.
  apply IHn.
  lia.
Qed.

Theorem list_gen_ind {X : Type}(P : list X -> Prop)
(HP : forall l, (forall m, length m < length l -> P m)%nat -> P l): forall l, P l.
Proof.
  intros l. 
  apply list_gen_ind_rec with (n := S (length l)).
  intros. auto.
  lia.
Qed.

Inductive perm {X:Type} : list X -> list X -> Prop :=
| perm_nil   :                   perm nil nil
| perm_cons  : forall x l1 l2,    perm l1 l2 
                           ->   perm (x::l1) (x::l2)
| perm_swap  : forall x y l,  perm (x::y::l) (y::x::l)
| perm_trans : forall l1 l2 l3,    perm l1 l2 
                           ->      perm l2 l3 
                           ->      perm l1 l3.
Notation "x '~p' y " := (perm x y) (at level 70, no associativity).

Fact perm_incl {X : Type} (l m: list X ): l ~p m -> incl l m.
Proof.
  intros H.
  induction H as [ 
                 | x l1 l2 H1 IH1 
                 | x y l 
                 | l1 l2 l3 H1 IH1 H2 IH2 
                 ]. 
  intros Hyp1 Hyp2 .
  apply Hyp2.
  intros Hyp1 Hyp2 .
  destruct Hyp2.
  left.
  apply H.
  right.
  apply IH1.
  apply H.
  intros ? ?.
  revert H.
  simpl.
  tauto.
  revert IH2.
  revert IH1.
  apply incl_tran.
Qed.

Fact perm_refl {A:Type} (l:list A) : l ~p l.
Proof.
 induction l as [ |list head IH].
 apply perm_nil.
 apply perm_cons.
 apply IH.
Qed.

Fact perm_middle {A:Type}x (l r:list A) : x::l++r ~p l++x::r.
Proof.
  induction l as [ | y list IHl ].
  simpl. 
  apply perm_refl.
  simpl. 
  apply perm_trans with (1 := perm_swap _ _ _).
  apply perm_cons.
  apply IHl.
Qed.

Fact incl_right_app {A:Type} (l m p:list A) : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
Proof.
  induction m as [ | x m IHm ].
  exists nil, nil; simpl; repeat split;intros;try easy.
  apply perm_nil.
  intros H.
  apply incl_cons_inv in H. 
  destruct H as (H1 & H2).    
  apply IHm in H2.
  destruct H2 as (m1 & m2 & H3 & H4 & H5).
  destruct IHm.
  apply perm_incl in H3.
  apply incl_appl with(m:=p) in H4.
  apply incl_appr with(m:=l) in H5.
  apply incl_app with(l:=m1) (m:=m2) (n:=l++p) in H4.
  apply incl_tran with(l:=m) in H4.
  apply H4.
  apply H3.
  apply H5.
  destruct H.
  destruct H.
  destruct H0.
  apply in_app_or in H1.
  destruct H1.
  exists (x::x0).
  exists (x1).
  split.
  apply perm_cons with(x:=x) in H.
  apply H.
  split.
  apply incl_cons with(a:=x) in H0.
  apply H0.
  apply H1.
  apply H2.
  exists (x0).
  exists (x::x1).
  split.
  apply perm_cons with(x:=x) in H.
  apply perm_trans with(l2:=(x::x0++x1)) (l3:= (x0++x::x1)) in H.
  apply H.
  apply perm_middle.
  split.
  apply H0.
  apply incl_cons with(a:=x) in H2.
  apply H2.
  apply H1.
Qed. 

Fact incl_right_cons_split {X : Type}  x (l m:list X) : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ (forall a, In a m1 -> a = x) /\ incl m2 l.
Proof.
  intros H.
  apply (incl_right_app (x::nil) _ l) in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  exists x0.
  exists x1.
  split.
  apply H.
  split.
  2: apply H1.
  intros.
  apply perm_incl in H.
  apply incl_cons with(l:=nil) in H2.
  apply incl_tran with(l:=a::nil) in H0.
  2: apply H2.
  2: intros;easy.
  apply incl_cons_inv in H0.
  destruct H0.
  induction H0.
  subst.
  trivial.
  exfalso.
  apply H0.
Qed.

Fact perm_sym {A:Type} (l1 l2:list A) : l1 ~p l2 -> l2 ~p l1.
Proof.
  intros H.
  induction H.
  apply perm_nil.
  apply perm_cons.
  assumption.
  apply perm_swap.
  apply perm_trans with l2.
  apply IHperm2.
  apply IHperm1.
Qed.

Fact incl_right_cons_choose {A:Type}x (l m:list A) : incl m (x::l) -> In x m \/ incl m l.
Proof.
  intros H.
  apply incl_right_cons_split in H.
  destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
  destruct m1 as [ | y m1 ].
  right.
  simpl in H1.
  apply perm_incl in H1.    
  revert H1 H3.
  apply incl_tran.
  apply Forall_forall in H2.
  apply Forall_inv in H2.
  subst.
  apply perm_sym in H1.
  apply perm_incl in H1.
  apply incl_cons_inv in H1.
  destruct H1.
  left.
  apply H.
Qed.

Fact repeat_choice_two {X:Type} (x : X) m : (forall a, In a m -> a = x) -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
Proof.
  intros H.
  destruct m as [ | a [ | b m ] ].
  right; left; auto.
  right; right; rewrite (H a); auto; left; auto.
  left; rewrite (H a), (H b).
  exists m; auto.
  right; left; auto.
  left; auto.
Qed.

Inductive list_has_dup {X:Type} : list X -> Prop :=
| in_lhd_1 : forall x l, In x l -> list_has_dup (x::l)
| in_lhd_2 : forall x l, list_has_dup l -> list_has_dup (x::l).

Notation lhd := list_has_dup.

Fact lhd_cons_inv {A:Type}x (l:list A) : lhd (x::l) -> In x l \/ lhd l.
Proof.
  inversion_clear 1;auto.
Qed.

Fact perm_lhd {A:Type} (l m:list A) : l ~p m -> lhd l -> lhd m.
Proof.
  intros H.
  induction H as [ | x l m H1 IH1 | x y l | ]; auto.
  intros H.
  apply lhd_cons_inv in H; destruct H as [ H | H ].
  left.
  apply perm_incl in H1. 
  apply H1.
  apply H.
  right.
  apply IH1.
  apply H.
  intros H.
  apply lhd_cons_inv in H. simpl in *.
  destruct H as [H | H];subst.
  destruct H as [H | H];subst.
  induction l.
  left.
  left.
  reflexivity.
  left.
  left.
  reflexivity.
  right.
  left.
  apply H.
  apply lhd_cons_inv in H.
  destruct H as [ H | H ].
  left.
  right.
  apply H.
  right.
  right.
  apply H.
Qed.

Fact incl_right_cons_incl_or_lhd_or_perm {A:Type} x (m l:list A) : incl m (x::l) -> incl m l \/ (lhd m) \/ exists m', m ~p x::m' /\ incl m' l.
Proof.
  intros H.
  apply incl_right_cons_split in H.
  destruct H as (m1 & m2 & H1 & H2 & H3).
  destruct (repeat_choice_two _ _ H2) as [ (m3 & H4) | [ H4 | H4 ] ]; 
    subst m1; simpl in H1; clear H2.
  apply perm_sym in H1.
  right; left.
  apply perm_lhd with (1 := H1).
  constructor 1; left; auto.
  left.
  intros u Hu.
  apply H3.
  apply perm_incl with (1 := H1); auto.
  right; right.
  exists m2; auto.
Qed.

Fact In_perm_head {X:Type}(x : X) l : In x l -> exists m, l ~p x::m.
Proof.
  intros H.
  apply in_split in H.
  destruct H as (u & v & ?).
  subst l.
  exists (u++v).
  apply perm_sym, perm_middle.
Qed.

Fact perm_length {A:Type} (l1 l2:list A) : l1 ~p l2 -> length l1 = length l2.
Proof.
  intros H.
  induction H as [ 
                  | x l1 l2 H1 IH1 
                  | x y l 
                  | l1 l2 l3 H1 IH1 H2 IH2 
                  ].
  apply refl_equal. 
  simpl. 
  f_equal.
  apply IH1.
  simpl. 
  apply refl_equal.
  transitivity (length l2).
  apply IH1.
  apply IH2.
Qed.

Fact length_le_and_incl_implies_dup_or_perm {A:Type} (l:list A)  :  
forall m, (length l <= length m)%nat
                      -> incl m l 
                      -> (lhd m) \/ m ~p l.
Proof.
induction l as [ [ | x l ] IHl ] using list_gen_ind.

(* case l -> nil *)
- intros ? ? ?.
  right. 
  apply incl_l_nil in H0.
  subst.
  apply perm_nil.

- intros [ | y m ] H1 H2.
  (* case l -> x::l and m -> nil *)
  + simpl in H1. lia.
  (* case l -> x::l and m -> y :: m *)
  + simpl in H1; apply le_S_n in H1.
    apply incl_cons_inv in H2.
    destruct H2 as [ H3 H4 ].
    simpl in H3.
    destruct H3 as [ H3 | H3 ].
    (* case x = y *)
    ++ subst y.
       apply incl_right_cons_choose in H4.
       destruct H4 as [ H4 | H4 ].

      (* case x = y & In x m *)
      +++ left.
          left.
          apply H4.

      (* case x = y & incl m l *)
      +++ destruct IHl with (3 := H4).
          simpl; lia.
          assumption.
          left. right;auto.
          right. constructor;auto.
      (* case In y l *)
    ++ apply incl_right_cons_incl_or_lhd_or_perm in H4.
       destruct H4 as [ H4 | [ H4 | (m' & H4 & H5) ] ].
       (* case In y l and incl m l *)
      +++ destruct IHl with (3 := H4) as [ H5 | H5 ]; auto.
          left;right;apply H5.
          left.
          left.
          apply perm_sym in H5.
          apply perm_incl in H5.
          apply H5.
          apply H3.
          (* case In y l and lhd m *)
      +++ left.
          right.
          apply H4.
      (* case In y l and m ~p x::m' and incl m' l *)
      +++ apply perm_sym in H4.
          apply In_perm_head in H3.
          destruct H3 as (l' & Hl').
          (* l ~p y::l' for some l' *)
          assert (incl m' (y::l')) as H6.
          {intros ? ?; apply perm_incl with (1 := Hl'), H5; auto. }
          clear H5.
          (* and incl m' (y::l') *)
          apply incl_right_cons_choose in H6.
          destruct H6 as [ H6 | H6 ].
          (* subcase In y m' *)
          ++++ left.
               left.
               apply perm_incl in H4. 
               apply H4.
               right.
               apply H6.
          (* subcase incl m' l' *)
          ++++ apply IHl in H6.
              destruct H6 as [ H6 | H6 ].
              left.
              apply perm_lhd in H4. 
              right.
              apply H4.
              right.
              apply H6.
              right.
              move Hl' after m'.
              apply perm_sym in H4.
              apply perm_cons with(x:=y) in H4.
              apply perm_cons with(x:=x) in H6.
              apply perm_cons with(x:=y) in H6.
              apply perm_cons with(x:=x) in Hl'.
              apply perm_sym in Hl'.
              apply perm_trans with(l2:=x::y::l')(l1:=y::x::l') in Hl' . 
              apply perm_trans with(l1:=y::m) in H6.
              apply perm_trans with(l1:=y::m) in Hl'.
              apply Hl'.
              apply H6.
              apply H4.
              apply perm_swap.
              apply perm_length in Hl'.
              simpl in Hl' |- *.
              rewrite Hl'.
              lia.
              apply perm_length in Hl'.
              apply perm_length in H4.
              simpl in H4, Hl'.
              apply le_S_n.
              rewrite <- Hl', H4; auto.
Qed.

Lemma NoDup_lhd_ff {A:Type}: forall l:list A, NoDup l -> lhd l -> False.
Proof.
  intros l H.
  induction H;try easy;simpl;intros.
  inversion H1;subst;auto.
Qed.

Lemma In_pigeon_hole: forall {A: Type} ( X' X: list A), (*11*)
  NoDup X ->
  (length X > length X')%nat ->
  (forall x, In x X -> In x X') ->
  False.
Proof.
  intros.
  eapply length_le_and_incl_implies_dup_or_perm in H1;try lia.
  destruct H1. 
  - eapply NoDup_lhd_ff;eauto.
  - apply perm_length in H1;lia.
Qed.

End Util.