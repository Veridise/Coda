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
From Circom.CircomLib Require Import Bitify.

From Circom.BigInt.Definition Require Import BigAdd BigMult BigLessThan.
From Circom.BigInt.Proof Require Import BigAdd BigMult BigLessThan.
From Circom.BigInt.Definition Require Import BigMod.
From Circom.BigInt.Theory Require Import Signed.
(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigMod.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.BigAdd.
Module Mult := BigMult.BigMult.
Module LessThan := BigLessThan.BigLessThan.
Import B.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigMod.
Context {n k: nat}.

(* // leading register of b should be non-zero
template BigMod(n, k) {
    signal input a[2 * k];
    signal input b[k];

    signal output div[k + 1];
    signal output mod[k];

    component range_checks[k + 1];
    for (var i = 0; i <= k; i++) {
        range_checks[i] = Num2Bits(n);
        range_checks[i].in <== div[i];
    }

    component mul = BigMult(n, k + 1);
    for (var i = 0; i < k; i++) {
        mul.a[i] <== div[i];
        mul.b[i] <== b[i];
    }
    mul.a[k] <== div[k];
    mul.b[k] <== 0;

    component add = BigAdd(n, 2 * k + 2);
    for (var i = 0; i < 2 * k; i++) {
        add.a[i] <== mul.out[i];
        if (i < k) {
            add.b[i] <== mod[i];
        } else {
            add.b[i] <== 0;
        }
    }

    add.a[2 * k] <== mul.out[2 * k];
    add.a[2 * k + 1] <== mul.out[2 * k + 1];
    add.b[2 * k] <== 0;
    add.b[2 * k + 1] <== 0;

    for (var i = 0; i < 2 * k; i++) {
        add.out[i] === a[i];
    }
    add.out[2 * k] === 0;
    add.out[2 * k + 1] === 0;

    component lt = BigLessThan(n, k);
    for (var i = 0; i < k; i++) {
        lt.a[i] <== mod[i];
        lt.b[i] <== b[i];
    }
    lt.out === 1;
} *)

Definition cons (a: F^(2 * k)) (b: F^k) (div: F^(k+1)) (_mod: F^k) :=
  exists (range_checks: (@Num2Bits.t n) ^ (k + 1)) 
         (mul: @Mult.t (k+1)%nat) (add: @Add.t n (2 * k + 2)) 
         (lt: @LessThan.t n k),
  (* range check for div *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    range_checks[i].(Num2Bits._in) = div[i]) (k+1) True /\
  (* mul *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    mul.(Mult.a)[i] = div[i] /\
    mul.(Mult.b)[i] = b[i]) k True /\
  mul.(Mult.a)[k] = div[k] /\
  mul.(Mult.b)[k] = 0 /\
  (* add *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.a)[i] = mul.(Mult.out)[i] /\
    if (i < k)? then
      add.(Add.b)[i] = _mod[i]
    else
      add.(Add.b)[i] = 0) (2 * k) True /\
  add.(Add.a)[2 * k] = mul.(Mult.out)[2 * k] /\
  add.(Add.a)[2 * k + 1] = mul.(Mult.out)[2 * k + 1] /\
  add.(Add.b)[2 * k] = 0 /\
  add.(Add.b)[2 * k + 1] = 0 /\
  (* a and add.out *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.out)[i] = a[i]) (2 * k) True /\
  add.(Add.out)[2 * k] = 0 /\
  add.(Add.out)[2 * k + 1] = 0 /\
  add.(Add.out)[2 * k + 2] = 0 /\ (* modified *)
  (* less than *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    lt.(LessThan.a)[i] = _mod[i] /\
    lt.(LessThan.b)[i] = b[i]) k True /\
  lt.(LessThan.out) = 1
.

Record t := { a: F^(2 * k); b: F^k; div: F^(k+1); _mod: F^k; _cons: cons a b div _mod }.
Local Notation "[| xs |]" := (RZ.as_le n xs).

(* Lemma firstn_congruence: forall i *)
Local Notation "xs !! i" := (List.nth i xs _) (at level 10).

Create HintDb DSL discriminated.

#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core.
#[local]Hint Extern 10 (_ = _) => lia : core.

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

Ltac solve_to_Z := repeat (autorewrite with F_to_Z; simplify; try (simpl; lia)).
Ltac solve_to_Z' H := autorewrite with F_to_Z in H; simplify' H; try (simpl in H; lia).
Ltac simplify_all :=
  repeat match goal with [ H: _ |- _] => progress simplify' H end.
Ltac split_dec_f :=
  repeat match goal with
  | [H: context[dec (@eq F ?a ?b)] |- _ ] => destruct (dec (a=b))
  | [ |- context[dec (@eq F ?a ?b)] ] => destruct (dec (a=b))
  end.

Lemma all_zero_repr: forall n,
  [|List.repeat 0 n|] = 0%Z.
Proof.
  induction n0;simpl;auto.
Qed.

Theorem soundness: forall (c: t),
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(a) |: (n) ->
  'c.(b) |: (n) ->
  'c.(div) |: (n) ->
  'c.(_mod) |: (n) ->
  ([|'c.(a)|] = [|'c.(div)|] * [|'c.(b)|] + [|'c.(_mod)|])%Z.
Proof.
  unwrap_C.
  intros c Hn Hk Hnk Ha Hb Hdiv Hmod.
  destruct c as [a b div _mod [range_checks [mul [add [lt prog]]]]].
  simpl in *.
  destruct prog as [Prange [Pmul [Pmul1 [Pmul2 [Padd [Padd1 [Padd2 [Padd3 [Padd4 [Pa [Pa1 [Pa2 [Pa3 [Plt Plt1]]]]]]]]]]]]]].
  pose_lengths.
  rem_iter.
  simplify_all.
  pose (Inv1 := fun (i: nat) (_cons: Prop) => _cons -> 
                '(Mult.a mul)[:i] = 'div[:i] /\
                '(Mult.b mul)[:i] = 'b[:i]).
  assert (HInv1: Inv1 k (D.iter f2 k True)) by connection Inv1.
  pose (Inv2_1 := fun (i: nat) (_cons: Prop) => _cons -> 
                '(Add.a add)[:i] = '(Mult.out mul)[:i]).
  assert (HInv2_1: Inv2_1 (k + k)%nat (D.iter f1 (k + k) True)) by connection Inv2_1.
  pose (Inv2_2 := fun (i: nat) (_cons: Prop) => _cons -> 
                            (if dec (i<k) then '(Add.b add)[:i] = '(_mod)[:i]
                              else '(Add.b add)[:i] = '(_mod)[:k] ++ (List.repeat 0 (i - k)))).
  assert (HInv2_2: Inv2_2 (k + k)%nat (D.iter f1 (k + k) True)).
  { apply DSL.iter_inv; unfold Inv2_2; try easy.
    + intros. destruct dec;try easy.
    + intros i _cons IH Hi Hstep;
      subst; lift_to_list; intuition.
      destruct (dec (S i < k));try easy.
      ++ destruct dec;try lia. 
         eapply firstn_congruence; fold_default; (lia || eauto).
      ++ destruct dec;try lia.
         +++ assert(k = S i)%nat by lia. subst. 
             assert((S i - S i) = 0)%nat by lia. rewrite H3. cbv [List.repeat].
             rewrite app_nil_r. eapply firstn_congruence; fold_default; (lia || eauto).
         +++ assert(List.repeat (@F.zero q) (S i - k) = (List.repeat 0 (i - k)) ++ (0::nil))%F.
             { assert(S i - k = (i - k) + 1)%nat by lia. rewrite H3. rewrite repeat_app;auto. }
             rewrite H3. rewrite app_assoc. rewrite <- H0.
             erewrite firstn_S;try lia. fold_default. rewrite H2. auto.
  }
  pose (Inv3 := fun (i: nat) (_cons: Prop) => _cons -> 
                '( Add.out add)[:i] = 'a[:i]).
  assert (HInv3: Inv3 (k + k)%nat (D.iter f0 (k + k) True)) by connection Inv3.
  pose (Inv4 := fun (i: nat) (_cons: Prop) => _cons -> 
                '(LessThan.a lt)[:i] = '_mod[:i] /\
                '(LessThan.b lt)[:i] = 'b[:i]).
  assert (HInv4: Inv4 k (D.iter f k True)) by connection Inv4.
  (* generate result *)
  pose proof (HInv4 Plt) as HInv4k. clear Plt HInv4.
  pose proof (HInv3 Pa) as HInv3k. clear Pa HInv3.
  pose proof (HInv2_2 Padd) as HInv2_2k. clear HInv2_2.
  pose proof (HInv2_1 Padd) as HInv2_1k. clear HInv2_1.
  pose proof (HInv1 Pmul) as HInv1k. clear HInv1.
  intuition.
  pose (Inv1_n := fun (i: nat) (_cons: Prop) => _cons -> 
                '(Mult.a mul)[:i] |: (n) /\
                '(Mult.b mul)[:i] |: (n)).
  assert (HInv1_n: Inv1_n k (D.iter f2 k True)).
  { apply DSL.iter_inv; unfold Inv1_n; try easy. simpl;easy. 
    intros i _cons IH Hi Hstep;
    subst; lift_to_list; intuition.
    + eapply Forall_firstn_S with (i:=i). rewrite firstn_length. rewrite _Hlen10. lia. 
      rewrite firstn_firstn. replace (Init.Nat.min i (S i)) with i by lia;auto.
      rewrite firstn_nth;try lia. fold_default;try lia. rewrite H5. unfold_default.
      apply Forall_nth;auto. lia.
    + eapply Forall_firstn_S with (i:=i). rewrite firstn_length. rewrite _Hlen9. lia. 
      rewrite firstn_firstn. replace (Init.Nat.min i (S i)) with i by lia;auto.
      rewrite firstn_nth;try lia. fold_default;try lia. rewrite H6. unfold_default.
      apply Forall_nth;auto. lia. }
  pose proof (HInv1_n Pmul) as [HInv1n1 HInv1n2]. clear Pmul HInv1_n.
  (* main proof *)
  assert(mul_a_rng: ' Mult.a mul |: (n)).
  { eapply Forall_firstn_and_last;try lia. rewrite _Hlen10. replace (k + 1 - 1)%nat with k by lia;auto.
    rewrite _Hlen10. replace (k + 1 - 1)%nat with k by lia. fold_default. 
    rewrite nth_Default_List_tuple. rewrite Pmul1.
    rewrite <- nth_Default_List_tuple. unfold_default.
    apply Forall_nth;auto. lia. }
  assert(mul_b_rng: ' Mult.b mul |: (n)).
  { eapply Forall_firstn_and_last;try lia. rewrite _Hlen9. replace (k + 1 - 1)%nat with k by lia;auto.
    rewrite _Hlen9. replace (k + 1 - 1)%nat with k by lia. fold_default. 
    rewrite nth_Default_List_tuple. rewrite Pmul2. solve_to_Z. }
  pose proof (@Mult.soundness n _ mul mul_a_rng mul_b_rng) as [mul_rng mul_sound].
  pose (Inv2_1n := fun (i: nat) (_cons: Prop) => _cons -> 
                '(Add.a add)[:i] |: (n)).
  assert (HInv2_1n: Inv2_1n (k + k)%nat (D.iter f1 (k + k) True)).
  { apply DSL.iter_inv; unfold Inv2_1n; try easy. simpl;easy. 
    intros i _cons IH Hi Hstep;
    subst; lift_to_list; intuition.
    eapply Forall_firstn_S with (i:=i). rewrite firstn_length. rewrite _Hlen7. lia. 
      rewrite firstn_firstn. replace (Init.Nat.min i (S i)) with i by lia;auto.
      rewrite firstn_nth;try lia. fold_default.
      replace ((' Add.a add) ! i) with ((' Mult.out mul) ! i).
      unfold_default. apply Forall_nth;auto;lia. }
  pose proof (HInv2_1n Padd) as HInv2n1. clear HInv2_1n.
  assert(add_a_rng: ' Add.a add |: (n)).
  { eapply Forall_firstn_and_last;try lia. rewrite _Hlen7. replace (k + (k + 0) + 2 - 1)%nat with (k + k + 1)%nat by lia;auto.
    eapply Forall_firstn_and_last;try lia. rewrite firstn_length;lia. 
    rewrite firstn_length. rewrite _Hlen7. rewrite firstn_firstn. 
    replace (Init.Nat.min (Init.Nat.min (k + k + 1) (k + (k + 0) + 2) - 1) (k + k + 1))%nat with (k + k)%nat by lia;auto.
    rewrite firstn_length. rewrite _Hlen7.
    replace (Init.Nat.min (k + k + 1) (k + (k + 0) + 2) - 1)%nat with (k + (k + 0))%nat by lia;auto.
    rewrite firstn_nth;try lia. fold_default.
    replace ((' Add.a add) ! (k + (k + 0))) with ((' Mult.out mul) ! (k + (k + 0))).
    unfold_default. apply Forall_nth;auto. rewrite _Hlen8;lia.
    do 2 rewrite nth_Default_List_tuple;auto. rewrite _Hlen7. fold_default.
    replace (' Add.a add ! (k + (k + 0) + 2 - 1)) with (' Mult.out mul ! (k + (k + 0) + 2 - 1)).
    unfold_default. apply Forall_nth;auto. rewrite _Hlen8;lia. 
    do 2 rewrite nth_Default_List_tuple. replace (k + (k + 0) + 2 - 1)%nat with (k + (k + 0) + 1)%nat by lia;auto. }
  pose (Inv2_2n := fun (i: nat) (_cons: Prop) => _cons -> 
                '(Add.b add)[:i] |: (n)).
  assert (HInv2_2n: Inv2_2n (k + k)%nat (D.iter f1 (k + k) True)).
  { apply DSL.iter_inv; unfold Inv2_2n; try easy. simpl;easy. 
    intros i _cons IH Hi Hstep;
    subst; lift_to_list; intuition.
    eapply Forall_firstn_S with (i:=i). rewrite firstn_length. rewrite _Hlen6. lia. 
    rewrite firstn_firstn. replace (Init.Nat.min i (S i)) with i by lia;auto.
    rewrite firstn_nth;try lia. fold_default.
    destruct dec in H6; rewrite H6.
    + unfold_default. apply Forall_nth;auto;lia.
    + solve_to_Z. }
  pose proof (HInv2_2n Padd) as HInv2n2. clear Padd HInv2_2n.
  assert(add_b_rng: ' Add.b add |: (n)).
  { eapply Forall_firstn_and_last;try lia. rewrite _Hlen6. replace (k + (k + 0) + 2 - 1)%nat with (k + k + 1)%nat by lia;auto.
    eapply Forall_firstn_and_last;try lia. rewrite firstn_length;lia. 
    rewrite firstn_length. rewrite _Hlen6. rewrite firstn_firstn. 
    replace (Init.Nat.min (Init.Nat.min (k + k + 1) (k + (k + 0) + 2) - 1) (k + k + 1))%nat with (k + k)%nat by lia;auto.
    rewrite firstn_length. rewrite _Hlen6.
    replace (Init.Nat.min (k + k + 1) (k + (k + 0) + 2) - 1)%nat with (k + (k + 0))%nat by lia;auto.
    rewrite firstn_nth;try lia. fold_default.
    rewrite nth_Default_List_tuple;auto. rewrite Padd3. solve_to_Z.
    rewrite _Hlen6. fold_default. rewrite nth_Default_List_tuple;auto.
    replace (k + (k + 0) + 2 - 1)%nat with (k + (k + 0) + 1)%nat by lia. rewrite Padd4. solve_to_Z. }
  (* loop 1 *)
  assert(L1: [|' Mult.a mul |] = [|' div |]).
  { replace (' Mult.a mul) with ((' Mult.a mul [:k]) ++  (' Mult.a mul ! k) :: nil).
    replace (' div) with ((' div [:k]) ++  (' div ! k) :: nil).
    do 2 rewrite RZ.as_le_app. do 2 rewrite firstn_length.
    rewrite _Hlen10, _Hlen0. rewrite H1. rewrite nth_Default_List_tuple. rewrite Pmul1. 
    rewrite nth_Default_List_tuple. auto.
    erewrite <- firstn_split_last. fold_default;auto. all:try lia.
    erewrite <- firstn_split_last. fold_default;auto. all:try lia. }
  assert(L2: [|' Mult.b mul |] = [|' b |]).
  { replace (' Mult.b mul) with ((' Mult.b mul [:k]) ++  (' Mult.b mul ! k) :: nil).
    replace (' b) with ((' b [:k])).
    rewrite RZ.as_le_app. rewrite firstn_length.
    rewrite _Hlen9. rewrite H2. rewrite nth_Default_List_tuple. rewrite Pmul2.  
    solve_to_Z. rewrite <- firstn_all. rewrite _Hlen1;auto.
    erewrite <- firstn_split_last. fold_default;auto. all:try lia. }
  (* loop 2 *)
  assert(L3: [|' Add.a add |] = [|' Mult.out mul |]).
  { replace (' Add.a add) with ((' Add.a add [:k + k]) ++  (' Add.a add ! (k + k)) :: (' Add.a add ! (k + k + 1)) :: nil).
    replace (' Mult.out mul) with ((' Mult.out mul [:k + k]) ++ (' Mult.out mul ! (k + k)) :: (' Mult.out mul ! (k + k + 1)) :: nil).
    repeat rewrite RZ.as_le_app. repeat rewrite firstn_length.
    rewrite _Hlen7, _Hlen8. rewrite HInv2_1k. repeat rewrite nth_Default_List_tuple. 
    replace (k + k)%nat with (k + (k + 0))%nat by lia.
    rewrite Padd1, Padd2. auto.
    erewrite <- firstn_split_last with (n:=(k + k + 1)%nat). fold_default;auto. all:try lia.
    rewrite ListUtil.app_cons_app_app. f_equal. 
    erewrite <- firstn_split_last with (n:=(k + k)%nat). rewrite firstn_firstn. rewrite firstn_nth;try lia.
    replace (Init.Nat.min (k + k) (k + k + 1)) with (k+k)%nat by lia;fold_default;auto.
    rewrite firstn_length. rewrite _Hlen8. lia.
    erewrite <- firstn_split_last with (n:=(k + k + 1)%nat). fold_default;auto. all:try lia.
    rewrite ListUtil.app_cons_app_app. f_equal. 
    erewrite <- firstn_split_last with (n:=(k + k)%nat). rewrite firstn_firstn. rewrite firstn_nth;try lia.
    replace (Init.Nat.min (k + k) (k + k + 1)) with (k+k)%nat by lia;fold_default;auto.
    rewrite firstn_length. rewrite _Hlen7. lia. }
  assert(L4: [|' Add.b add |] = [|' _mod |]).
  { destruct dec in HInv2_2k;try lia.
    replace (' Add.b add) with (' _mod [:k] ++ List.repeat 0 (k + k - k + 2)).
    replace (' _mod) with (' _mod [:k]).
    repeat rewrite RZ.as_le_app. repeat rewrite firstn_length. rewrite all_zero_repr. solve_to_Z.
    replace ((' _mod [:k]) [:k]) with ((' _mod [:k]));auto. replace (' _mod [:k]) with (' _mod) at 2;auto.
    rewrite <- firstn_all at 1. rewrite _Hlen;auto. rewrite <- firstn_all. rewrite _Hlen;auto.
    replace (' _mod [:k] ++ List.repeat 0 (k + k - k + 2)) with ((' _mod [:k]) ++ List.repeat 0 (k + k - k) ++ 0 :: 0 :: nil);auto.
    rewrite app_assoc. rewrite <- HInv2_2k.
    rewrite <- firstn_skipn with (n:=k) in HInv2_2k at 1.
    rewrite <- firstn_all. rewrite _Hlen6.
    assert (LEN: (length (' Add.b add [:k + (k + 0) + 2]) = k+k+2)%nat).
    { rewrite firstn_length. rewrite _Hlen6. lia. } 
    erewrite <- firstn_split_last with (n:=(k + (k + 0) + 1)%nat). all:try lia. 
    rewrite firstn_firstn. rewrite firstn_nth;try lia.  fold_default;auto.
    replace (Init.Nat.min (k + (k + 0) + 1) (k + (k + 0) + 2)) with (k + (k + 0) + 1)%nat by lia.
    rewrite nth_Default_List_tuple. rewrite Padd4.
    replace (' Add.b add [:k + (k + 0) + 1]) with (' Add.b add [:k + k] ++ (' Add.b add ! (k + (k + 0))) :: nil).
    rewrite nth_Default_List_tuple. rewrite Padd3. rewrite <- app_assoc. auto.
    assert (LEN1: (length (' Add.b add [:k + (k + 0) + 1]) = k+k+1)%nat).
    { rewrite firstn_length. rewrite _Hlen6. lia. } 
    erewrite <- firstn_split_last with (n:=(k + (k+0))%nat). all:try lia.
    rewrite firstn_firstn. rewrite firstn_nth;try lia.  fold_default;auto.
    replace (Init.Nat.min (k + (k + 0)) (k + (k + 0) + 1)) with (k + (k + 0))%nat by lia.
    replace (k+k)%nat with (k + (k + 0))%nat by lia. auto.
    rewrite repeat_app. simpl;auto. }
  (* loop 3 *)
  assert(L5: [|' Add.out add |] = [|' a |]).
  { replace (' Add.out add) with ((' Add.out add [:k + k]) ++ (' Add.out add ! (k + k)) :: (' Add.out add ! (k + k + 1)) :: (' Add.out add ! (k + k + 2)) :: nil).
    replace (' a) with ((' a [:k + k])).
    repeat rewrite RZ.as_le_app. repeat rewrite firstn_length.
    rewrite _Hlen5. rewrite HInv3k. repeat rewrite nth_Default_List_tuple. 
    replace (k + k)%nat with (k + (k + 0))%nat by lia.
    rewrite Pa1, Pa2, Pa3. solve_to_Z.
    rewrite <- firstn_all. rewrite _Hlen2. replace (k + k)%nat with (k + (k + 0))%nat by lia;auto. 
    erewrite <- firstn_split_last with (n:=(k + k + 2)%nat). fold_default;auto. all:try lia. 
    do 2 rewrite ListUtil.app_cons_app_app. f_equal.
    erewrite <- firstn_split_last with (n:=(k + k + 1)%nat). rewrite firstn_firstn. rewrite firstn_nth;try lia.
    replace (Init.Nat.min (k + k + 1) (k + k + 2)) with (k + k +1)%nat by lia;fold_default;auto. f_equal.
    erewrite <- firstn_split_last with (n:=(k + k)%nat). rewrite firstn_firstn. rewrite firstn_nth;try lia.
    replace (Init.Nat.min (k + k) (k + k + 1)) with (k + k)%nat by lia;fold_default;auto. 
    rewrite firstn_length. rewrite _Hlen5. lia. 
    rewrite firstn_length. rewrite _Hlen5. lia. }
  (* loop 4 *)
  assert(L6: [|' LessThan.a lt |] = [|' _mod |]).
  { replace (' LessThan.a lt) with (' LessThan.a lt [:k]).
    replace (' _mod) with (' _mod [:k]).
    rewrite H;auto.
    rewrite <- firstn_all. rewrite _Hlen;auto.
    rewrite <- firstn_all. rewrite _Hlen3;auto. }
  assert(L7: [|' LessThan.b lt |] = [|' b |]).
  { replace (' LessThan.b lt) with (' LessThan.b lt [:k]).
    replace (' b) with (' b [:k]).
    rewrite H0;auto.
    rewrite <- firstn_all. rewrite _Hlen1;auto.
    rewrite <- firstn_all. rewrite _Hlen4;auto. }
  pose proof (Add.soundness add) as add_sound.
  pose proof (LessThan.soundness lt) as lt_sound.
  try rewrite L1, L2, L3, L4, L5, L6, L7 in *.
  rewrite <- mul_sound in add_sound.
  destruct add_sound;auto;try easy.
Unshelve. all:exact 0.
Qed.

End _BigMod.
End BigMod.