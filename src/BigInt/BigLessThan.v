Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.


From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators Gates.

(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigLessThan.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.


Section _BigLessThan.
Context {n k: nat}.

Import Cmp Gates.


(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Notation "[\ xs \]" := (RZ.as_be n xs).

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Definition cons (a b: F^k) (out: F) : Prop :=
  exists (lt: (@LessThan.t n) ^ k) (eq: IsEqual.t ^ k),
  D.iter (fun i _cons => _cons /\
    lt[i].(LessThan._in)[0] = a[i] /\
    lt[i].(LessThan._in)[1] = b[i] /\
    eq[i].(IsEqual._in)[0] = a[i] /\
    eq[i].(IsEqual._in)[1] = b[i]) k True /\
  exists (ands: AND.t^k) (eq_ands: AND.t^k) (ors: OR.t^k),
  D.iter (fun j _cons => _cons /\
    let i := (k-2 - j)%nat in
    if ((i = k-2)%nat)? then
      ands[i].(AND.a) = eq[k-1].(IsEqual.out) /\
      ands[i].(AND.b) = lt[k-2].(LessThan.out) /\
      eq_ands[i].(AND.a) = eq[k-1].(IsEqual.out) /\
      eq_ands[i].(AND.b) = eq[k-2].(IsEqual.out) /\
      ors[i].(OR.a) = lt[k-1].(LessThan.out) /\
      ors[i].(OR.b) = ands[i].(AND.out)
    else
      ands[i].(AND.a) = eq_ands[i+1].(AND.out) /\
      ands[i].(AND.b) = lt[i].(LessThan.out) /\
      eq_ands[i].(AND.a) = eq_ands[i+1].(AND.out) /\
      eq_ands[i].(AND.b) = eq[i].(IsEqual.out) /\
      ors[i].(OR.a) = ors[i+1].(OR.out) /\
      ors[i].(OR.b) = ands[i].(AND.out))
    (k-1)%nat True /\
  out = ors[0].(OR.out).

Record t := {a: F^k; b: F^k; out: F; _cons: cons a b out}.

#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core.
#[local]Hint Extern 10 => match goal with
  | [ H: _ :: _ = _ :: _ |- _] => invert H
  end : core.

Fixpoint list_to_nths {A} `{Default A} (l: list A) :=
  match l with
  | nil => nil
  | _::l' => l!0 :: list_to_nths l'
  end.

Lemma unfold_list_to_nths {A: Type} `{Default A}: forall (l: list A),
  l = list_to_nths l.
Proof.
  induction l; simpl. reflexivity.
  unfold_default. simpl. rewrite <- IHl. auto.
Qed.

Lemma forall_split {A} (x:A) (P Q R: A -> Prop):
  (forall x, P x -> Q x /\ R x) ->
  (forall x, P x -> Q x) /\
  (forall x, P x -> R x).
Proof.
  intros. intuition; specialize (H x0); tauto.
Qed.

Ltac split_and := match goal with
  | [ |- _ /\ _] => split
  end.

Theorem soundness: forall (c: t),
  n <= C.k - 1 ->
  2 <= k ->
  'c.(a) |: (n) ->
  'c.(b) |: (n) ->
  binary c.(out) /\
  (c.(out) = 1%F <-> [|' c.(a) |] < [|' c.(b) |]).
Proof with (lia || eauto).
  unwrap_C.
  intros c Hn Hk Ha Hb.
  destruct c as [a b out [lt [eq [lt_eq [ands [eq_ands [ors main]]]]]]]. unfold cons in *. simpl in *.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  remember (rev ('a)) as ra.
  remember (rev ('b)) as rb.
  assert (Hlen_ra: length ra = k). subst. rewrite rev_length. lia.
  assert (Hlen_rb: length rb = k). subst. rewrite rev_length. lia.

  pose (Inv0 := fun (i:nat) _cons => _cons ->
    forall (j:nat), j < i -> 
      binary (lt[j].(LessThan.out)) /\ 
      (lt[j].(LessThan.out) = 1%F <-> 'a!j <q 'b!j) /\
      binary (eq[j].(IsEqual.out)) /\ 
      (eq[j].(IsEqual.out) = 1%F <-> 'a!j = 'b!j)).
  destruct main as [main final].
  rem_iter.
  assert (H_inv0: Inv0 k (D.iter f0 k True)). {
    apply D.iter_inv; unfold Inv0.
    - intros _ j Hj. lia.
    - intros i acc IH Hi Hstep j Hj.
      rewrite Heqf0 in *. 
      destruct (dec (j<i)).
      (* j<i (trivial) *)
      apply IH. intuition. lia.
      (* j=i *)
      assert (e: j=i) by lia. rewrite e in *. clear e.
      destruct Hstep as [Hacc [lt_a [lt_b [eq_a eq_b]]]].
      pose proof (@LessThan.is_binary n (lt[i])) as LT_bin.
      pose proof (@LessThan.is_sound n (lt[i])) as LT_sound.
      pose proof (@LessThan.is_complete n (lt[i])) as LT_complete.
      pose proof (@IsEqual.is_binary (eq[i])) as EQ_bin.
      pose proof (@IsEqual.is_complete (eq[i])) as EQ_complete.
      rewrite lt_a, lt_b, eq_a, eq_b in *.
      lift_to_list.
      assert (Hai: ' a ! i | (n)) by default_apply ltac:(apply Forall_nth; auto).
      assert (Hbi: ' b ! i | (n)) by default_apply ltac:(apply Forall_nth; auto).
      intuition idtac; auto.
      + rewrite H2 in *. destruct (dec (1=1)%F). apply LT_sound... fqsatz.
      + apply LT_complete...
  }

  apply H_inv0 in lt_eq. clear H_inv0 Heqf0 Inv0.

  apply forall_split in lt_eq. destruct lt_eq as [LT_bin lt_eq].
  apply forall_split in lt_eq. destruct lt_eq as [LT_sound lt_eq].
  apply forall_split in lt_eq. destruct lt_eq as [EQ_bin EQ_sound].
  
  pose (Inv := fun (j:nat) _cons => _cons ->
    forall (i j0: nat), j0 < j ->
    i = (k-2-j0)%nat ->
    (ors[i].(OR.out) = 1%F <-> RZU.big_lt (ra[:j0+2]) (rb[:j0+2]) = true) /\
    (eq_ands[i].(AND.out) = 1%F <-> ra[:j0+2] = rb[:j0+2]) /\
    binary (eq_ands[i].(AND.out)) /\
    binary (ors[i].(OR.out))).
  assert (H_inv: Inv (k-1)%nat (D.iter f (k-1)%nat True)). {
    unfold Inv.
    apply D.iter_inv.
    - intuition; lia.
    - intros j acc IH Hj Hstep i j0 Hj0 Hi. rewrite Heqf in *.
      destruct (dec (j0<j)). eapply IH; eauto; intuition.
      assert (e: j0 = j) by lia. rewrite e in *. clear e n0 Hj0 j0.
      rewrite <- Hi in *.
      destruct (dec (i = (k-2)%nat));
      destruct Hstep as [Hacc [Hands_a [Hands_b [Heqands_a [Heqands_b [Hors_a Hors_b]]]]]].
      + 
      assert (ej: j=0%nat) by lia. rewrite ej in *. clear ej.
      autorewrite with natsimplify in *.
      repeat progress first [
        rewrite OR.is_sound
      | apply OR.is_binary
      | rewrite AND.is_sound
      | apply AND.is_binary
      | rewrite Hors_a
      | rewrite Hors_b
      | rewrite Hands_a
      | rewrite Hands_b
      | rewrite Heqands_a
      | rewrite Heqands_b
      | rewrite LT_sound by lia
      | rewrite EQ_sound by lia
      | apply LT_bin;try lia
      | apply EQ_bin;try lia
      ].
      

      (* try apply AND.is_binary;
      try apply OR.is_binary. *)

      repeat default_apply ltac:(rewrite rev_nth' with (l:='a)); try (subst; lia).
      repeat default_apply ltac:(rewrite rev_nth' with (l:='b)); try (subst; lia).
      rewrite <- Heqra, <-Heqrb, Hlen_a, Hlen_b.
      replace (k - S (k - 1))%nat with 0%nat by lia.
      replace (k - S (k - 2))%nat with 1%nat by lia.

      destruct ra as [ | a0 ra]. simpl in *. lia.
      destruct ra as [ | a1 ra]. simpl in *. lia.
      destruct rb as [ | b0 rb]. simpl in *. lia.
      destruct rb as [ | b1 rb]. simpl in *. lia.
      default_apply ltac:(simpl).
      destruct (dec (a0 <q b0));
      destruct (dec (a0 = b0));
      destruct (dec (a1 <q b1));
      destruct (dec (a1 = b1)); 
      intuition;
      (lia || solve [subst; auto] || auto);
      repeat progress first [
        rewrite OR.is_sound
      | apply OR.is_binary
      | rewrite AND.is_sound
      | apply AND.is_binary
      | rewrite Hors_a
      | rewrite Hors_b
      | rewrite Hands_a
      | rewrite Hands_b
      | rewrite Heqands_a
      | rewrite Heqands_b
      | rewrite LT_sound by lia
      | rewrite EQ_sound by lia
      | apply LT_bin;try lia
      | apply EQ_bin;try lia
      ].
    + 
    assert (j > 0) by lia.
    assert (Hai: 'a!i = ra!(j+1)%nat). {
      rewrite Heqra.
      unfold_default. rewrite rev_nth'; try lia. 
      rewrite Hlen_a. f_equal. lia.
    }
    assert (Hbi: 'b!i = rb!(j+1)%nat). {
      rewrite Heqrb.
      unfold_default. rewrite rev_nth'; try lia. 
      rewrite Hlen_b. f_equal. lia.
    }
    specialize (IH Hacc (i+1)%nat (j-1)%nat). clear Hacc.
    destruct IH as [IHors [IHeq_ands [IHeq_ands_bin IHors_bin]]]; try lia.
    repeat split_and;
    repeat progress first [
      rewrite OR.is_sound with (c:=ors [i])
      | apply OR.is_binary with (c:=ors [i])
      | rewrite Hors_a | rewrite Hors_b
      | rewrite AND.is_sound with (c:=eq_ands [i])
      | rewrite AND.is_sound with (c:=ands [i])
      | apply AND.is_binary with (c:=eq_ands [i])
      | apply AND.is_binary with (c:=ands [i])
      | rewrite Hands_a | rewrite Hands_b
      | rewrite Heqands_a | rewrite Heqands_b
      | rewrite IHeq_ands
      | rewrite IHors
      | rewrite EQ_sound
      | rewrite LT_sound
      | rewrite Hai, Hbi
      (* | replace ('a!i) with (ra!(j+1)) *)
      | auto
    ];
    replace (j-1+2)%nat with (j+1)%nat by lia;
    erewrite <- firstn_split_last with (l:=ra[:j+2]) (n:=(j+1)%nat) by (rewrite firstn_length_le; try lia); rewrite firstn_firstn by lia; rewrite firstn_nth by lia; rewrite min_l by lia;
    erewrite <- firstn_split_last with (l:=rb[:j+2]) (n:=(j+1)%nat) by (rewrite firstn_length_le; try lia); rewrite firstn_firstn by lia; rewrite firstn_nth by lia; rewrite min_l by lia;
    assert (length (ra[:j+1]) = (j+1)%nat) by (rewrite firstn_length_le; try lia);
    assert (length (rb[:j+1]) = (j+1)%nat) by (rewrite firstn_length_le; try lia);
    fold_default.
    
    * 
    rewrite <- RZU.big_lt_app'; try (simpl; lia).
    rewrite RZU.big_lt_single. intuition. shelve.
    * rewrite <- app_congruence_iff; try (simpl; lia).
    intuition. f_equal. auto.
  }
  unfold Inv in H_inv.
  repeat rewrite RZ.le__rev_be.
  rewrite <- Heqra, <- Heqrb.
  rewrite final.
  intuition;
  destruct (H 0%nat (k-2)%nat) as [Hors [Hands [Hors_bin Heqands_bin]]]; try lia; auto.
  
  assert (Href: RZU.big_lt (ra) (rb) = true). {
    rewrite <- firstn_all with (l:=ra).
    rewrite <- firstn_all with (l:=rb).
    rewrite Hlen_ra, Hlen_rb.
    replace k with (k-2+2)%nat by lia.
    applys_eq H; try lia.
    replace (k-2-(k-2))%nat with 0%nat by lia.
    auto.
  }
  
  apply RZU.big_lt_dec; try (
    lia || auto ||
    rewrite ?Heqra, ?Heqrb; apply Forall_rev; auto).
  
  rewrite Hors.
  
  replace (k-2+2)%nat with k by lia.
  replace (ra[:k]) with ra by (symmetry; applys_eq firstn_all; f_equal; lia).
  replace (rb[:k]) with rb by (symmetry; applys_eq firstn_all; f_equal; lia).
  applys_eq (RZU.big_lt_dec n); try (
    lia || auto ||
    rewrite ?Heqra, ?Heqrb; apply Forall_rev; auto).
  Unshelve.
  exact 0%nat. exact 0%nat. exact 0%nat.
  exact F.zero. exact F.zero. exact F.zero. exact F.zero.
  exact 0%nat.
Qed.

End _BigLessThan.
End BigLessThan.