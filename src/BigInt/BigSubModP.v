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
From Circom.BigInt Require Import BigAdd BigLessThan BigSub.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigAddModP.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.
Module Sub := BigSub.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigAddModP.
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

Lemma ite_true: forall m xs ys,
  m = 1 ->
  length xs = length ys ->
  ite m xs ys = xs.
Admitted.

Lemma ite_false: forall m xs ys,
  m = 0 ->
  length xs = length ys ->
  ite m xs ys = ys.
Admitted.

Lemma ite_firstn: forall i m xs ys,
  ite m (xs[:i]) (ys[:i]) = ite m xs ys [:i].
Admitted.

Lemma add_length: forall xs ys,
  length (add xs ys) = Nat.min (length xs) (length ys).
Admitted.

Lemma ite_length: forall m xs ys,
  length (ite m xs ys) = Nat.min (length xs) (length ys).
Admitted.

Lemma scale_nth: forall m xs i d,
  List.nth i (scale m xs) d = m * (List.nth i xs d).
Admitted.

Lemma scale_length: forall m xs,
  length (scale m xs) = length xs.
Admitted.

Lemma add_nth: forall xs ys (i:nat) d,
  i < length xs ->
  i < length ys ->
  List.nth i (add xs ys) d =
  (List.nth i xs d) + (List.nth i ys d).
Admitted.

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
#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core.
#[local]Hint Extern 10 (_ = _) => lia : core.

Lemma firstn_mod: forall xs k,
  [| xs[:k] |] = [|xs|] mod (2^(n*k)).
Admitted.

Lemma ite_as_le: forall m xs ys,
  binary m ->
  [| ite m xs ys |] = if dec (m = 1) then [|xs|] else [|ys|].
Admitted.

Lemma ite_range: forall m xs ys,
  xs |: (n) ->
  ys |: (n) ->
  ite m xs ys |: (n).
Admitted.

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

  (* add *)
  pose (Iadd := fun (i:nat) _cons => _cons ->
    'add.(Add.a)[:i] = 'sub.(Sub.out)[:i] /\
    'add.(Add.b)[:i] = 'p[:i]).
  assert (Hadd: Iadd k (D.iter f0 k True)) by connection Iadd.
  destruct (Hadd Padd) as [add_a add_b]. firstn_all.

  (* out *)
  pose (Iout := fun (i:nat) _cons => _cons ->
    'out[:i] = ite sub.(Sub.underflow) ('add.(Add.out)[:i]) ('sub.(Sub.out)[:i])).
  assert (Hout: Iout k (D.iter f k True)). {
    apply D.iter_inv; unfold Iout. easy.
    intros i _cons IH Hi Hstep. subst f. intuition.
    rewrite ite_firstn. applys_eq (@firstn_congruence F). rewrite <- ite_firstn.
    auto. lift_to_list. pose_lengths.
    fold_default.
    rewrite H2. rewrite H1. unfold ite.
    unfold_default. rewrite add_nth. repeat rewrite scale_nth.
    fqsatz.
    repeat rewrite scale_length. lia.
    repeat rewrite scale_length. lia.
    rewrite ite_length. lia.
  }
  apply Hout in Pout. firstn_all. move Pout at bottom.
  rewrite Pout.
  destruct (Add.soundness add) as [Hadd_out Hadd_out_range]. admit. admit. admit. admit. admit. 
  destruct (Sub.soundness_ite sub) as [bin_underflow [Hsub_out_range Hsub_out]]. admit. admit. admit. admit. admit.
  rewrite sub_a, sub_b in *. clear sub_a sub_b.
  rewrite add_a, add_b in *. clear add_a add_b.
  intuition.
  rewrite ite_as_le; auto.
  split_dec; intuition; try fqsatz. 
  rewrite e in *.
  rewrite firstn_mod.
  rewrite Hadd_out, H0.
  rewrite @F.to_Z_1; try lia. simplify.
  replace (2 ^ (n * k) + [|' a|] - [|' b|] + [|' p|])%Z with 
  (2 ^ (n * k) + ([|' a|] - [|' b|] + [|' p|]))%Z by lia.
  rewrite Zplus_mod, Z_mod_same_full.
  simplify.
  rewrite Zmod_mod.
  rewrite Zmod_small.
  admit. (* mod range *)
  admit. (* range: 0 <= [|' a|] - [|' b|] + [|' p|] < 2 ^ (n * k) *)

  (* case a >= b *)
  firstn_all. rewrite H0.
  admit. (* mod range *)

  rewrite ite_firstn.
  apply Forall_firstn.
  apply ite_range; auto.

  Unshelve. all:exact F.zero.
Admitted.