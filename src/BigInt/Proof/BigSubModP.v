Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators.
From Circom.BigInt.Proof Require Import BigAdd BigLessThan BigSub.
From Circom.BigInt.Definition Require Import BigAdd BigLessThan BigSub.
From Circom.BigInt.Definition Require Import BigSubModP.
(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigSubModP.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.BigAdd.
Module Sub := BigSub.BigSub.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigSubModP.
Context {n k: nat}.


Definition cons (a b p out: F^k) :=
  exists (sub: @Sub.t n k) (add: @Add.t n k) (tmp: F^n),
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    sub.(Sub.a)[i] = a[i] /\
    sub.(Sub.b)[i] = b[i]) k True /\
  let flag := sub.(Sub.underflow) in
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.a)[i] = sub.(Sub.out)[i] /\
    add.(Add.b)[i] = p[i]) k True /\
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    tmp[i] = (1 - flag) * sub.(Sub.out)[i] /\
    out[i] = tmp[i] + flag * add.(Add.out)[i]) k True.

Record t := { a: F^k; b: F^k; p: F^k; out: F^k; _cons: cons a b p out }.
Local Notation "[| xs |]" := (RZ.as_le n xs).

(* Lemma firstn_congruence: forall i *)
Local Notation "xs !! i" := (List.nth i xs _) (at level 10).

Definition scale (m: F) (xs: list F) := List.map (fun x => m * x) xs.
Definition add (xs: list F) (ys: list F) := List.map (fun '(x,y) => x+y) (List.combine xs ys).
Definition ite (m: F) (xs: list F) (ys: list F) :=
  add (scale m xs) (scale (1-m) ys).


Create HintDb DSL discriminated.

#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core.
#[local]Hint Extern 10 (_ = _) => lia : core.

Lemma add_nil_l ys: add nil ys = nil.
Proof. destruct ys; unfold add; reflexivity. Qed.

Lemma add_nil_r xs: add xs nil = nil.
Proof. destruct xs; unfold add; reflexivity. Qed.

Hint Rewrite add_nil_l: DSL.
Hint Rewrite add_nil_r: DSL.

Lemma ite_nil_l: forall m ys,
  ite m nil ys = nil.
Proof.
  induction ys; unfold ite; simpl; intros; autorewrite with DSL; auto.
Qed.

Lemma ite_nil_r: forall m xs,
  ite m xs nil = nil.
Proof.
  induction xs; unfold ite; simpl; intros; autorewrite with DSL; auto.
Qed.

Hint Rewrite ite_nil_l: DSL.
Hint Rewrite ite_nil_r: DSL.

Lemma scale_nil: forall m, scale m nil = nil.
Proof. intros. unfold scale. auto. Qed.

Hint Rewrite scale_nil: DSL.


Lemma scale_nth: forall m xs (i: nat) d,
  i < length xs ->
  List.nth i (scale m xs) d = m * (List.nth i xs d).
Proof. induction xs; intros; simpl in *. lia.
  destruct i. auto.
  simpl. rewrite IHxs. auto. lia.
Qed.

Lemma scale_length: forall m xs,
  length (scale m xs) = length xs.
Proof.
  intros. unfold scale. rewrite map_length. auto.
Qed.

#[local]Hint Extern 10 (_ :: _ = _ :: _) => f_equal : core.

Lemma scale_0: forall xs, scale 0 xs = List.repeat (0:F) (length xs).
Proof. induction xs; simpl; auto. Qed.

Lemma scale_1: forall xs, scale 1 xs = xs.
Proof. induction xs; simpl; simplify; auto. Qed.

Lemma add_0_r: forall (i: nat) xs, i >= length xs ->
  add xs (List.repeat 0 i) = xs.
Proof. 
  induction i; destruct xs; simpl in *; intros; auto.
  unfold add in *. simpl. simplify. rewrite IHi; auto.
Qed.

Lemma add_0_r': forall (i: nat) xs,
  add xs (List.repeat 0 i) = xs[:min (length xs) i].
Proof.
  induction i; destruct xs; simpl in *; intros; auto.
  unfold add in *. simpl. simplify. f_equal. rewrite IHi; auto.
Qed.

Lemma add_0_l: forall (i: nat) xs, i >= length xs ->
  add (List.repeat 0 i) xs = xs.
Proof. 
  induction i; destruct xs; simpl in *; intros; auto.
  unfold add in *. simpl. simplify. rewrite IHi; auto.
Qed.

Lemma add_0_l': forall (i: nat) xs,
  add (List.repeat 0 i) xs = xs[:min (length xs) i].
Proof. 
  induction i; destruct xs; simpl in *; intros; auto.
  unfold add in *. simpl. simplify. rewrite IHi; auto.
Qed.



Lemma ite_true: forall m xs ys,
  m = 1 ->
  length xs = length ys ->
  ite m xs ys = xs.
Proof.
  unwrap_C. intros; subst.
  unfold ite. simpl. simplify. replace (1-1)%F with (0:F) by fqsatz.
  rewrite scale_0, scale_1, add_0_r; auto.
Qed.

Lemma ite_true': forall m xs ys,
  m = 1 ->
  ite m xs ys = xs[:min (length xs) (length ys)].
Proof.
  unwrap_C. intros; subst.
  unfold ite. simpl. simplify. replace (1-1)%F with (0:F) by fqsatz.
  rewrite scale_0, scale_1, add_0_r'; auto.
Qed.

Lemma ite_false: forall m xs ys,
  m = 0 ->
  length xs = length ys ->
  ite m xs ys = ys.
Proof.
  unwrap_C. intros; subst.
  unfold ite. simpl. simplify. replace (1-0)%F with (1:F) by fqsatz.
  rewrite scale_0, scale_1, add_0_l; auto.
Qed.

Lemma ite_false': forall m xs ys,
  m = 0 ->
  ite m xs ys = ys[:min (length xs) (length ys)].
Proof.
  unwrap_C. intros; subst.
  unfold ite. simpl. simplify. replace (1-0)%F with (1:F) by fqsatz.
  rewrite scale_0, scale_1, add_0_l'. f_equal. lia.
Qed.

Lemma add_length: forall xs ys,
  length (add xs ys) = Nat.min (length xs) (length ys).
Proof.
  intros. unfold add. rewrite map_length. apply combine_length.
Qed.

Lemma ite_length: forall m xs ys,
  length (ite m xs ys) = Nat.min (length xs) (length ys).
Proof.
  intros.
  unfold ite. rewrite add_length, scale_length, scale_length. auto.
Qed.

Local Open Scope nat_scope.
Lemma combine_nth2 {X Y}: forall i xs ys (dx:X) (dy:Y),
  i < length xs ->
  i < length ys ->
  List.nth i (combine xs ys) (dx,dy) = (List.nth i xs dx, List.nth i ys dy).
Proof.
  induction i.
  - intros. destruct xs; destruct ys; simpl in *; auto; lia.
  - intros. destruct xs; destruct ys; cbn [length] in *; try lia.
    simpl. apply IHi; lia.
Qed.

Local Close Scope nat_scope.

Lemma add_nth: forall xs ys (i:nat) d,
  i < length xs ->
  i < length ys ->
  List.nth i (add xs ys) d =
  (List.nth i xs d) + (List.nth i ys d).
Proof.
  intros. unfold add.
  remember (fun '(x, y) => x + y) as f.
  pose proof (map_nth f (combine xs ys)).
  erewrite nth_oblivious.
  rewrite map_nth.
  rewrite combine_nth2 by lia. rewrite Heqf. auto.
  rewrite map_length, combine_length. lia.
Qed.

#[local]Hint Extern 10 => match goal with
  | [ |- context[ length (scale _ _) ] ] =>
    rewrite scale_length
  end : core.
#[local]Hint Extern 10 => match goal with
  | [ |- context[ length (add _ _) ] ] =>
    rewrite add_length
  end : core.
#[local]Hint Extern 10 => match goal with
  | [ |- context[ length (ite _ _ _) ] ] =>
    rewrite ite_length
  end : core.

Lemma firstn_mod: forall xs (i: nat),
  i < length xs ->
  xs |: (n) ->
  [| xs[:i] |] = [|xs|] mod 2^(n*i).
Proof.
  intros xs i Hi Hxs.
  replace [|xs|] with [|xs[:i] ++ skipn i xs|].
  rewrite RZ.as_le_app.
  rewrite firstn_length_le by lia.
  rewrite Zplus_mod.
  rewrite Zmult_comm with (n:=(2^(n*i))%Z).
  rewrite Z_mod_mult.
  simplify.
  rewrite Zmod_mod, Zmod_small. reflexivity.
  split. apply RZ.as_le_nonneg.
  assert ([|xs [:i]|] <= 2 ^ (n * i) - 1).
    applys_eq RZU.repr_le_ub'. repeat f_equal.
    symmetry. apply firstn_length_le; lia.
    apply Forall_firstn. auto.
  lia.
  f_equal. rewrite firstn_skipn; auto.
Qed.

#[local]Hint Extern 10 => match goal with
| [ |- context[ ite ?m _ _] ] =>
  try (replace m with (0:F); try rewrite ite_false; try fqsatz)
end : core.

#[local]Hint Extern 10 => match goal with
| [ |- context[ ite ?m _ _] ] =>
  try (replace m with (1:F); try rewrite ite_true; try fqsatz)
end : core.

Lemma ite_as_le: forall m xs ys,
  binary m ->
  length xs = length ys ->
  [| ite m xs ys |] = if dec (m = 1) then [|xs|] else [|ys|].
Proof.
  unwrap_C.
  intros.
  destruct H; subst;
  split_dec; try (exfalso; fqsatz); auto.
Qed.

#[local]Hint Extern 10 => match goal with
  | [ |- context[length (firstn _ _)]] =>
    rewrite firstn_length_le by lia
  end : core.

Lemma scale_firstn: forall i m xs,
  scale m (xs[:i]) = (scale m xs)[:i].
Proof.
  induction i; simpl; intros; destruct xs; auto.
  unfold scale. simpl. f_equal. rewrite firstn_map. auto.
Qed.


Lemma add_firstn: forall (i: nat) xs ys,
  (i <= length xs)%nat ->
  (i <= length ys)%nat ->
  add (xs[:i]) (ys[:i]) = (add xs ys)[:i].
Proof.
  induction i; destruct xs as [ | x xs]; destruct ys as [ | y ys]; simpl in *; auto; intros.
  unfold add. simpl. f_equal.
  rewrite <- combine_firstn, firstn_map. auto.
Qed.

Lemma ite_firstn: forall (i: nat) m xs ys,
  binary m ->
  i <= length xs ->
  i <= length ys ->
  ite m (xs[:i]) (ys[:i]) = ite m xs ys [:i].
Proof.
  intros. unfold ite.
  repeat rewrite scale_firstn.
  rewrite add_firstn; auto;
  rewrite scale_length; lia.
Qed.

Lemma ite_range: forall m xs ys,
  binary m ->
  xs |: (n) ->
  ys |: (n) ->
  ite m xs ys |: (n).
Proof.
  intros.
  destruct H; subst.
  rewrite ite_false'; auto. apply Forall_firstn. auto.
  rewrite ite_true'; auto. apply Forall_firstn. auto.
Qed.

Lemma mod_sub_geq: forall a b c,
  0 <= a < c ->
  0 <= b < c ->
  a >= b ->
  ((a-b) mod c = a-b)%Z.
Proof.
  intros a b c. intros.
  rewrite Zmod_small. auto.
  lia.
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

Ltac pose_as_le_nonneg := repeat match goal with
| [ |- context[RZ.as_le ?n ?xs ] ] =>
  let t := type of (RZ.as_le_nonneg n xs) in
  lazymatch goal with
  (* already posed *)
  | [ _: t |- _] => fail
  | _ => 
    let Hnonneg := fresh "_Hnonneg" in
    pose proof (RZ.as_le_nonneg n xs) as Hnonneg
    ;move Hnonneg at top
  end
| _ => fail
end.

Ltac rewrite_length :=
  repeat match goal with
  | [ H: length ?xs = ?l |- context[length ?xs] ] =>
    rewrite H
  | [ H: length ?xs = ?l, H': context[length ?xs] |- _] =>
    rewrite H in H'
  end.

Ltac lrewrite :=
  repeat match goal with
  | [ H: ?x = _ |- context[?x] ] => rewrite H
  end.
Ltac rrewrite :=
  repeat match goal with
  | [ H: _ = ?x |- context[?x] ] => rewrite H
  end.

Theorem soundness: forall (c: t),
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(a) |: (n) ->
  'c.(b) |: (n) ->
  'c.(p) |: (n) ->
  [|'c.(a)|] <= [|'c.(p)|] - 1 ->
  [|'c.(b)|] <= [|'c.(p)|] - 1->
  [|'c.(out)|] = ([|'c.(a)|] - [|'c.(b)|]) mod [|'c.(p)|] /\ 'c.(out) |: (n).
Proof.
  unwrap_C.
  intros c Hn Hk Hnk Ha Hb Hp Hap Hbp.
  destruct c as [a b p out [sub [add [tmp prog]]]].
  destruct prog as [Psub [Padd Pout]]. 
  simpl in *.
  pose_lengths.
  rem_iter.

  (* sub *)
  pose (Isub := fun (i:nat) _cons => _cons ->
    'sub.(Sub.a)[:i] = 'a[:i] /\
    'sub.(Sub.b)[:i] = 'b[:i]).
  assert (Hsub: Isub k (D.iter f1 k True)) by connection Isub.
  destruct (Hsub Psub) as [sub_a sub_b]. firstn_all.
  destruct (Sub.soundness_ite sub) as [bin_underflow [Hsub_out_range Hsub_out]];
  try (lrewrite; lia || auto).

  (* add *)
  pose (Iadd := fun (i:nat) _cons => _cons ->
    'add.(Add.a)[:i] = 'sub.(Sub.out)[:i] /\
    'add.(Add.b)[:i] = 'p[:i]).
  assert (Hadd: Iadd k (D.iter f0 k True)) by connection Iadd.
  destruct (Hadd Padd) as [add_a add_b]. firstn_all.
  destruct (Add.soundness add) as [Hadd_out Hadd_out_range];
  try (lrewrite; lia || auto).

  (* out *)
  pose (Iout := fun (i:nat) _cons => _cons ->
    'out[:i] = ite sub.(Sub.underflow) ('add.(Add.out)[:i]) ('sub.(Sub.out)[:i])).
  assert (Hout: Iout k (D.iter f k True)). {
    apply D.iter_inv; unfold Iout. easy.
    intros i _cons IH Hi Hstep. subst f. intuition.
    rewrite ite_firstn; auto. applys_eq (@firstn_congruence F).
    rewrite <- ite_firstn; auto.
    auto. lift_to_list. pose_lengths.
    fold_default.
    rewrite H2. rewrite H1. unfold ite.
    unfold_default. rewrite add_nth; auto. repeat rewrite scale_nth; auto.
    fqsatz.
    rewrite ite_length; lia.
  }
  apply Hout in Pout. firstn_all. move Pout at bottom.
  rewrite Pout.
  
  rewrite sub_a, sub_b in *. clear sub_a sub_b.
  rewrite add_a, add_b in *. clear add_a add_b.

  pose_as_le_nonneg.
  pose proof (RZU.repr_le_ub' _ _ Ha).
  pose proof (RZU.repr_le_ub' _ _ Hb).
  pose proof (RZU.repr_le_ub' _ _ Hp).
  rewrite_length.
  
  intuit.
  rewrite ite_as_le; auto.
  split_dec; intuit; try fqsatz.
  (* a < b *)
  rewrite e in *.
  rewrite firstn_mod; auto.
  rewrite Hadd_out, H3.
  rewrite @F.to_Z_1; try lia. simplify.
  replace (2 ^ (n * k) + [|' a|] - [|' b|] + [|' p|])%Z with 
  (2 ^ (n * k) + ([|' a|] - [|' b|] + [|' p|]))%Z by lia.
  rewrite Zplus_mod, Z_mod_same_full.
  simplify.
  rewrite Zmod_mod.
  pose_as_le_nonneg.
  rewrite Zmod_small, mod_sub_lt; lia.
  

  (* case a >= b *)
  firstn_all. rewrite H3.
  rewrite mod_sub_geq; try lia.

  rewrite ite_firstn; auto.
  apply Forall_firstn.
  apply ite_range; auto.

  Unshelve. all:exact F.zero.
Qed.

End _BigSubModP.
End BigSubModP.