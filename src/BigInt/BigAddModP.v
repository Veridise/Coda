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
Module Lt := BigLessThan.

(* Import BigAdd.  *)
(* Import BigLessThan. *)
(* Import BigSub. *)

Check BigSub.t.

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
  exists (add: @Add.t n k) (lt: @Lt.t n (S k)) (sub: @Sub.t n (S k)),
  D.iter (fun i _cons => _cons /\
    add.(Add.a)[i] = a[i] /\
    add.(Add.b)[i] = b[i]) k True /\
  D.iter (fun i _cons => _cons /\
    lt.(Lt.a)[i] = add.(Add.out)[i] /\
    lt.(Lt.b)[i] = p[i]) k True /\
  lt.(Lt.a)[k] = add.(Add.out)[k] /\
  lt.(Lt.b)[k] = 0 /\
  D.iter (fun i _cons => _cons /\
    sub.(Sub.a)[i] = add.(Add.out)[i] /\
    sub.(Sub.b)[i] = (1 - lt.(Lt.out)) * p[i]) k True /\
  sub.(Sub.a)[k] = add.(Add.out)[k] /\
  sub.(Sub.b)[k] = 0 /\
  sub.(Sub.out)[k] = 0 /\
  D.iter (fun i _cons => _cons /\
    out[i] = sub.(Sub.out)[i]) k True.
  
Record t := { a: F^k; b: F^k; p: F^k; out: F^k; _cons: cons a b p out }.
Local Notation "[| xs |]" := (RZ.as_le n xs).

(* Lemma firstn_congruence: forall i *)
Local Notation "xs !! i" := (List.nth i xs _) (at level 10).

Lemma firstn_congruence {A}: forall i l l' (d: A),
  l[:i] = l'[:i] ->
  List.nth i l d = List.nth i l' d ->
  l[:S i] = l'[:S i].
Admitted.

Lemma list_tail_congruence {A}: forall i l l' (d: A),
  length l = S i ->
  length l' = S i ->
  l[:i] = l'[:i] ->
  List.nth i l d = List.nth i l' d ->
  l = l'.
Proof.
  intros.
  rewrite <- firstn_all with (l:=l).
  rewrite <- firstn_all with (l:=l').
  rewrite H, H0.
  eapply firstn_congruence; auto.
  rewrite H2. auto.
Qed.

Ltac firstn_all := 
  repeat match goal with
  | [ H: context[?l [:?k]],
      Hlen: length ?l = ?k |- _ ] =>
    rewrite firstn_all2 in H by lia
  | [ Hlen: length ?l = ?k |- context[?l [:?k]] ] =>
    rewrite firstn_all2  by lia
  end.

Ltac pose_lengths :=
  repeat match goal with
    | [ _: context[?xs] |- _ ] =>
    lazymatch type of xs with
    | tuple F ?k =>
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
  

(* prove invariant Inv about simple connection circuits *)
Ltac connection Inv :=
  apply D.iter_inv; unfold Inv; easy ||
  ( intros i _cons IH Hi Hstep;
    subst; lift_to_list; intuition;
    eapply firstn_congruence; fold_default; (lia || eauto)).

Lemma Forall_firstn_and_last {A}: forall l (d: A) (P: A -> Prop),
  length l > 0 ->
  Forall P (l[:length l-1]) ->
  P (List.nth (length l - 1)%nat l d) ->
  Forall P l.
Proof.
  intros.
  apply Forall_rev_iff.
  pose proof (rev_length l).
  erewrite <- firstn_split_last with (l:=l) (n:=(length l - 1)%nat).
  rewrite rev_unit.
  constructor. eauto.
  apply Forall_rev.
  auto.
  lia.
Qed.

Ltac rewrite_length :=
  repeat match goal with
  | [ H: length ?xs = ?l |- context[length ?xs] ] =>
    rewrite H
  end; simplify.

Ltac lrewrite :=
  repeat match goal with
  | [ H: ?x = _ |- context[?x] ] => rewrite H
  end.
Ltac rrewrite :=
  repeat match goal with
  | [ H: _ = ?x |- context[?x] ] => rewrite H
  end.

Ltac rewrite_clear H := rewrite H in *; clear H.

Lemma scale_0: forall l, List.map (fun pi => 0 * pi) l = List.repeat (0:F) (length l).
Proof.
  induction l as [ | x l]; simpl; auto.
  simplify. f_equal. auto.
Qed.

Lemma as_le_0: forall i, [| List.repeat (0:F) i|] = 0%Z.
Proof.
  induction i; simpl; auto.
  rewrite IHi. simplify.
Qed.

Lemma forall_repeat {A}: forall (i:nat) P (x: A),
  i > 0 ->
  Forall P (List.repeat x i) <-> P x.
Proof.
  induction i; simpl; intros.
  lia.
  intuit.
  - inversion H0. auto.
  - constructor; auto. destruct i. simpl. auto.
    apply IHi. lia. auto.
Qed.


Lemma as_le_msb_0: forall xs l,
  length xs = S l ->
  xs |: (n) ->
  [| xs |] <= 2^(n*l)-1 ->
  [| xs |] = [| xs[:l] |].
Proof.
  intros.
  unwrap_C.
  pose proof (RZ.repr_trivial n xs H0).
  pose proof (RZ.as_le_split_last n l [|xs|] xs).
  rewrite H in H2.
  apply H3 in H2.
  rewrite H2.
  destruct (dec (xs ! l = 0)).
  rewrite e. simplify.
  remember (RZ.ToZ.to_Z (xs ! l)) as y.
  assert (y <> 0)%Z. subst. apply F.to_Z_nonzero. auto.
  assert (0 <= y). subst. apply F.to_Z_range. lia.
  assert (0 <= [|xs [:l]|]). pose_as_le_nonneg. lia.
  assert ([|xs [:l]|] <= 2 ^ (n * l) - 1).
    eapply RZU.repr_le_ub.
    applys_eq RZ.repr_trivial. rewrite firstn_length_le; lia.
    apply Forall_firstn. auto.
  exfalso. nia.
Qed.

Lemma scale_binary_range: forall s xs,
  xs |: (n) ->
  binary s ->
  List.map (fun x => s * x) xs |: (n).
Proof.
  induction xs; simpl; intros; constructor;
  inversion H; subst; clear H.
  destruct H0; subst; simplify.
  rewrite F.to_Z_0. lia.
  apply IHxs; auto.
Qed.

Lemma scale_binary0: forall (s: F) xs l,
  s = 0 ->
  l = length xs ->
  List.map (fun x => s * x) xs = List.repeat 0 l.
Proof.
  induction xs; intros; subst; simpl in *; simplify.
  reflexivity.
  f_equal. auto.
Qed.

Lemma scale_binary1: forall (s: F) xs l,
  s = 1 ->
  l = length xs ->
  List.map (fun x => s * x) xs = xs.
Proof.
  induction xs; intros; subst; simpl in *; simplify.
  reflexivity.
  f_equal. erewrite IHxs; eauto.
Qed.

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

#[local]Hint Extern 10 => match goal with
  | [ |- context[ length (firstn _ _) ] ] =>
    rewrite firstn_length_le by lia
  end : core.
#[local]Hint Extern 10 (eq (F.F q) _ _) => fqsatz : core.
#[local]Hint Extern 10 F => exact F.zero: core.


Theorem soundness: forall (c: t),
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(a) |: (n) ->
  'c.(b) |: (n) ->
  'c.(p) |: (n) ->
  [|'c.(a)|] <= [|'c.(p)|] - 1 ->
  [|'c.(b)|] <= [|'c.(p)|] - 1->
  [|'c.(out)|] = ([|'c.(a)|] + [|'c.(b)|]) mod [|'c.(p)|] /\ 'c.(out) |: (n).
Proof with (lia || eauto).
  unwrap_C.
  intros c Hn Hk Hnk Ha Hb Hp Hap Hbp. 
  destruct c as [a b p out [add [lt [sub prog]]]].
  destruct prog as [Padd [Plt [Plt_ak [Plt_bk [Psub [Psub_ak [Psub_bk [Psub_outk Pout]]]]]]]].
  simpl in *.
  lift_to_list.
  pose_lengths.
  rem_iter.
  assert (0 < 2^n). { apply Zpow_facts.Zpower_gt_0... }
  assert (0 <= [|' a|] + [|' b|]) by (pose_as_le_nonneg; lia).
  assert ([|'p|] <= 2^(n*k)-1). {
    eapply RZU.repr_le_ub with (xs:='p).
    unfold RZU.RZ.repr_le. intuition.
  }

  (* add *)
  pose (Iadd := fun (i:nat) _cons => _cons ->
    'add.(Add.a)[:i] = 'a[:i] /\
    'add.(Add.b)[:i] = 'b[:i]).
  assert (Hadd: Iadd k (D.iter f2 k True)) by connection Iadd.
  pose proof (Add.soundness add) as Sadd.
  destruct Hadd as [Hadd_a Hadd_b]...
  firstn_all. rewrite Hadd_a, Hadd_b in *. clear Hadd_a Hadd_b.
  destruct Sadd as [Sadd_out Sadd_out_range]...
  subst f2. clear Padd Iadd.
  
  (* less than *)
  pose (Ilt := fun (i:nat) _cons => _cons ->
    'lt.(Lt.a)[:i] = 'add.(Add.out)[:i] /\
    'lt.(Lt.b)[:i] = 'p[:i]).
  assert (Hlt: Ilt k (D.iter f1 k True)) by connection Ilt.
  destruct Hlt as [Hlt_a Hlt_b]... clear Ilt.
  pose proof (Lt.soundness lt) as Slt.
  destruct Slt as [Slt_bin Slt]; try lia;
  try (applys_eq (@Forall_firstn_and_last F);
    rewrite_length;
    fold_default; lrewrite; unfold_default;
    try apply Forall_firstn)...
  apply Forall_nth... rewrite F.to_Z_0...
  assert (Hlt_a': 'lt.(Lt.a) = 'add.(Add.out)). {
    applys_eq (@list_tail_congruence F)...
    fold_default...
  }
  rewrite Hlt_a', Sadd_out in *. clear Hlt_a Hlt_a'.
  assert (Hlt_b': [|' Lt.b lt |] = [|'p|]). {
    erewrite RZ.as_le_split_last with (ws:='Lt.b lt) (i:=k).
    rewrite Hlt_b, Plt_bk.
    firstn_all. simplify.
    applys_eq RZ.repr_trivial...
    eapply Forall_firstn_and_last; rewrite_length;
    fold_default; lrewrite; unfold_default.
    apply Forall_firstn... rewrite F.to_Z_0...
  }
  move Hlt_b' before Hlt_b.
  
  (* sub *)
  (* sub.a = add.out *)
  pose (Isub_a := fun (i: nat) _cons => _cons ->
    'Sub.a sub [:i] = 'Add.out add [:i]).
  assert (Hsub_a: Isub_a k (D.iter f0 k True)) by connection Isub_a.
  specialize (Hsub_a Psub).
  assert (Hsub_a': 'sub.(Sub.a) = 'add.(Add.out)). {
    applys_eq (@list_tail_congruence F)... fold_default...
  }
  clear Hsub_a Isub_a Psub_ak.
  (* [|sub.b|] = [|p|] *)
  pose (Isub_b := fun (i: nat) _cons => _cons ->
    'Sub.b sub [:i] = List.map (fun pi => (1-Lt.out lt) * pi) ('p)[:i]).
  assert (Hsub_b: Isub_b k (D.iter f0 k True)). {
    apply D.iter_inv; unfold Isub_b.
    - easy.
    - intros i _cons IH Hi Hstep. subst f0. lift_to_list. intuition.
      applys_eq (@firstn_congruence F)...
      rewrite map_nth. fold_default...
  }
  specialize (Hsub_b Psub). clear Isub_b.
  rewrite Hlt_b' in *.

  (* out *)
  pose (Iout := fun (i: nat) _cons => _cons ->
    'out [:i] = 'Sub.out sub [:i]).
  assert (Hout: Iout k (D.iter f k True)) by connection Iout.
  specialize (Hout Pout). clear Pout Iout.
  firstn_all.

  destruct (Sub.soundness_ite sub) as [H_sub_out_bin [H_sub_out H_sub]]; try lia.
    rewrite Hsub_a'. auto.
    eapply Forall_firstn_and_last; rewrite_length.
    rewrite Hsub_b. rewrite firstn_map. firstn_all.
    apply scale_binary_range...
    eapply one_minus_binary; eauto. 
    fold_default. rewrite Psub_bk. autorewrite with F_to_Z...
  
  rewrite Hsub_a', Sadd_out in *.
  destruct (dec ([|' a|] + [|' b|] < [|' p|])).
  - rewrite Zmod_small...
    assert (Hsub_b': 'Sub.b sub = List.repeat 0 (S k)). {

      erewrite <- firstn_split_last with (l:=' Sub.b sub) (n:=k)...
      cbn [List.repeat]. rewrite repeat_cons.
      apply app_congruence_iff; intuition.
      rewrite firstn_length_le, repeat_length...
      replace (1 - lt.(Lt.out)) with (0:F) in Hsub_b by fqsatz.
      rewrite Hsub_b, scale_0. rewrite_length. 
      rewrite firstn_all2... rewrite repeat_length...
      fold_default. f_equal...
    }
    rewrite Hsub_b', as_le_0 in *.
    destruct (dec ([|' a|] + [|' b|] >= 0)); try lia.
    intuition;
    rewrite Hout.
    rewrite <- as_le_msb_0...
    apply Forall_firstn...
  - rewrite Zmod_once...
    rewrite Hout.
    assert (Hsub_bk: [|'sub.(Sub.b)|] = [|'sub.(Sub.b)[:k]|]). {
      erewrite RZ.as_le_split_last with (i:=k).
      lrewrite. simplify.
      applys_eq RZ.repr_trivial...
      eapply Forall_firstn_and_last; rewrite_length; lrewrite...
      apply Forall_firstn. apply scale_binary_range... eapply one_minus_binary...
      fold_default. lrewrite. autorewrite with F_to_Z...
    }
    assert (Hsub_outk: [|'sub.(Sub.out)|] = [|'sub.(Sub.out)[:k]|]). {
      erewrite RZ.as_le_split_last with (i:=k).
      lrewrite. simplify.
      applys_eq RZ.repr_trivial...
    }
    destruct (Slt_bin) as [Hlt_out | Hlt_out]; rewrite Hlt_out in *.
    split_dec.
    erewrite scale_binary1 with (l:=k) in Hsub_b; try fqsatz...
    rewrite firstn_all2 with (l:='p) in Hsub_b...
    rewrite Hsub_bk, Hsub_b, <- Hsub_outk in *.
    intuition.
    apply Forall_firstn...
    erewrite scale_binary1 with (l:=k) in Hsub_b; try fqsatz...
    rewrite firstn_all2 with (l:='p) in Hsub_b...
    rewrite Hsub_bk, Hsub_b, <- Hsub_outk in *.
    lia.
    exfalso.
    erewrite scale_binary0 with (l:=k) in Hsub_b; try fqsatz...
    assert ([|' a|] + [|' b|] < [|' p|]). apply Slt...
    lia.
    Unshelve. all:auto.
Qed.

End _BigAddModP.
End BigAddModP.