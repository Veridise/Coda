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
From Circom Require Import Repr ReprZ LibOverflow Signed.
From Circom.CircomLib Require Import Bitify Comparators.
From Circom.BigInt.Definition Require Import BigAdd.
(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigAdd.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module RZS := ReprZSigned.
Module RZ2 := RZS.RZ.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.


Module ModSumThreeOpt.
Section ModSumThreeOpt.
Context {n: nat}.
Import B R.

(* Note: this is a simplified version from circom-pairing *)
(* 
template ModSumThreeOpt(n) {
  assert(n + 1 <= 253);
  signal input a;
  signal input b;
  signal input c;
  signal output sum;
  signal output carry;

  component n2b = Num2Bits(n + 1);
  n2b.in <== a + b + c;
  carry <== n2b.out[n];
  sum <== a + b + c - carry * (1 << n);
} 
*)

Definition cons (a b c sum carry: F) :=
  exists (n2b: @Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits.out) [n] /\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

Lemma add_sub: forall (x y: F), x + y - y = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Theorem soundness: forall w,
  (* pre-conditions *)
  ( n <= C.k - 1 )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary w.(c) ->
  (* post-conditions *)
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
  w.(sum) | (n) /\
  binary w.(carry).
Proof.
  unwrap_C.
  intros c Hnk Ha Hb Hc.
  destruct c as [a b c sum carry _cons].
  simpl in *. unfold cons in *.
  destruct _cons as [n2b [H_in [H_carry H_sum] ] ].
  apply R.in_range_binary in Hc.
  intuition.
  - fqsatz.
  - subst.
  remember (Num2Bits.out n2b [n] ) as out_n. pose proof (length_to_list (Num2Bits.out n2b)).
  pose proof (Num2Bits.soundness n2b) as H_n2b. unfold repr_le2 in *.
  rewrite <- H_in.
  pose proof H_n2b as H_n2b'. unfold repr_le in H_n2b. destruct H_n2b as [_ [H_n2b_bin H_as_le] ].
  rewrite H_as_le.
  erewrite as_le_split_last; eauto.

  lift_to_list.
  rewrite <- Heqout_n.
  simplify.
  match goal with
  | [ |- context[?x + ?y - ?z] ] => replace (x+y-z) with x by fqsatz
  end.
  eapply repr_le_ub; try lia.
  eapply repr_le_firstn; eauto.
  rewrite firstn_length_le; lia.
  rewrite H. auto.
  - rewrite H_carry.
  pose proof (Num2Bits.soundness n2b) as H_n2b. 
  unfold repr_le2, repr_le in *.
  intuition.
  lift_to_list. unfold_default.
  apply Forall_nth; try lia.
  apply Forall_in_range.
  auto.
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance Default : Default (ModSumThreeOpt.t) := { 
  default := wgen 
}.

End ModSumThreeOpt.
End ModSumThreeOpt.

Module ModSumThree.
Section ModSumThree.
Context {n: nat}.
Import B R.

(* Note: this is the original version from circom-pairing *)
(* 
template ModSumThree(n) {
  assert(n + 2 <= 253);
  signal input a;
  signal input b;
  signal input c;
  signal output sum;
  signal output carry;

  component n2b = Num2Bits(n + 2);
  n2b.in <== a + b + c;
  carry <== n2b.out[n] + 2 * n2b.out[n + 1];
  sum <== a + b + c - carry * (1 << n);
} 
*)

Definition cons (a b c sum carry: F) :=
  exists (n2b: @Num2Bits.t (S (S n))),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits.out) [n] + 2 * n2b.(Num2Bits.out) [n + 1]/\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

Lemma add_sub: forall (x y: F), x + y - y = x.
Proof. unwrap_C. intros. fqsatz. Qed.

Theorem soundness: forall w,
  (* pre-conditions *)
  ( n <= C.k - 2 )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(a) | (n) -> 
  w.(b) | (n) -> 
  binary w.(c) ->
  (* post-conditions *)
  w.(sum) + 2^n * w.(carry) = w.(a) + w.(b) + w.(c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
  w.(sum) | (n) /\
  binary w.(carry).
Proof.
  unwrap_C.
  intros c Hnk Ha Hb Hc.
  destruct c as [a b c sum carry _cons].
  simpl in *. unfold cons in *.
  destruct _cons as [n2b [H_in [H_carry H_sum] ] ].
  apply R.in_range_binary in Hc.
  intuition.
  - fqsatz.
  - subst.
  remember (Num2Bits.out n2b [n] ) as out_n. pose proof (length_to_list (Num2Bits.out n2b)).
  pose proof (Num2Bits.soundness n2b) as H_n2b. unfold repr_le2 in *.

  assert (Hlast0: Num2Bits.out n2b [n + 1] = 0). {
    lift_to_list.
    unfold R.repr_le in H_n2b. intuit.
    applys_eq R.repr_le_ub_last0.
    fold_default. f_equal. lia. lia.
    auto.
    lia.
    rewrite H_in in *.
    rewrite <- H3.
    rewrite H.
    replace (S (S n) - 1)%nat with (S n) by lia.
    assert (0 <= ^a). apply F.to_Z_range. lia.
    assert (0 <= ^b). apply F.to_Z_range. lia.
    assert (0 <= ^c). apply F.to_Z_range. lia.
    assert (0 <= ^ a + ^ b + ^c < q). {
      assert (^ a + ^ b + ^c < 2 * 2^n). lia.
      eapply Signed.le_sub_r_pow with (x:=2%Z) in Hnk; try lia.
    }
    repeat (autorewrite with F_to_Z; try lia).
    rewrite pow_S_Z. lia.
  }
  rewrite Hlast0 in *.
  simplify.


  rewrite <- H_in.
  pose proof H_n2b as H_n2b'. unfold repr_le in H_n2b. destruct H_n2b as [_ [H_n2b_bin H_as_le] ].
  rewrite H_as_le.
  erewrite as_le_split_last; eauto.
  lift_to_list.
  replace ('Num2Bits.out n2b ! S n) with ('Num2Bits.out n2b ! (n+1)%nat) by (f_equal; lia).
  rewrite Hlast0. simplify.
  rewrite as_le_split_last with (i:=n).
  lift_to_list.
  rewrite firstn_firstn. rewrite Nat.min_l by lia.
  unfold_default. rewrite firstn_nth; try lia. fold_default.
  rewrite <- Heqout_n.
  simplify.
  match goal with
  | [ |- context[?x + ?y - ?z] ] => replace (x+y-z) with x by fqsatz
  end.
  eapply repr_le_ub; try lia.
  eapply repr_le_firstn; eauto.
  rewrite firstn_length_le; lia.
  rewrite H. auto.
  rewrite firstn_length_le; try lia.
  apply Forall_firstn. auto.
  - rewrite H_carry.
  pose proof (Num2Bits.soundness n2b) as H_n2b. 
  unfold repr_le2, repr_le in *.
  intuit.
  assert (Hlast0: Num2Bits.out n2b [n + 1] = 0). {
    lift_to_list.
    (* unfold R.repr_le in H_n2b. intuit. *)
    applys_eq R.repr_le_ub_last0.
    fold_default. f_equal. lia. lia.
    auto.
    lia.
    rewrite H_in in *.
    rewrite <- H2.
    rewrite H.
    replace (S (S n) - 1)%nat with (S n) by lia.
    assert (0 <= ^a). apply F.to_Z_range. lia.
    assert (0 <= ^b). apply F.to_Z_range. lia.
    assert (0 <= ^c). apply F.to_Z_range. lia.
    assert (0 <= ^ a + ^ b + ^c < q). {
      assert (^ a + ^ b + ^c < 2 * 2^n). lia.
      eapply Signed.le_sub_r_pow with (x:=2%Z) in Hnk; try lia.
    }
    repeat (autorewrite with F_to_Z; try lia).
    rewrite pow_S_Z. lia.
  }
  lift_to_list.
  rewrite Hlast0. simplify.
  unfold_default.
  apply Forall_nth; try lia.
  apply Forall_in_range.
  auto.
Qed.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance Default : Default (ModSumThree.t) := { default := wgen }.

End ModSumThree.
End ModSumThree.

Module M := ModSumThreeOpt.

Section _BigAdd.
Context {n k: nat}.

(* template BigAdd(n, k) {
    assert(n <= 252);
    signal input a[k];
    signal input b[k];
    signal output out[k + 1];

    component unit0 = ModSum(n);
    unit0.a <== a[0];
    unit0.b <== b[0];
    out[0] <== unit0.sum;

    component unit[k - 1];
    for (var i = 1; i < k; i++) {
        unit[i - 1] = ModSumThreeOpt(n);
        unit[i - 1].a <== a[i];
        unit[i - 1].b <== b[i];
        if (i == 1) {
            unit[i - 1].c <== unit0.carry;
        } else {
            unit[i - 1].c <== unit[i - 2].carry;
        }
        out[i] <== unit[i - 1].sum;
    }
    out[k] <== unit[k - 2].carry;
} *)

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Local Notation "[|| xs ||]" := (RZ.as_le n ('xs)).

Definition cons (a b: tuple F k) (out: tuple F (S k)) :=
  exists (unit: tuple (@M.t n) k),
  D.iter (fun i _cons =>
    _cons /\
    unit [i].(M.a) = a [i] /\
    unit [i].(M.b) = b [i] /\
    (if (dec (i = 0)%nat) then
    unit [i].(M.c) = 0
    else
    unit [i].(M.c) = unit [i-1].(M.carry)) /\
    out [i] = unit [i].(M.sum)
    ) k True /\ 
  out [k] = unit [k-1].(M.carry).

Record t := {
  a: tuple F k;
  b: tuple F k;
  out: tuple F (S k);
  _cons: cons a b out
}.

Ltac split_as_le xs i := 
  erewrite RZ.as_le_split_last' with (ws:=xs[:S i]) (i:=i);
  try rewrite firstn_firstn; simplify;
  try rewrite firstn_nth by lia.

Lemma nth_0 {T} `{Default T}: forall (x: T), (x :: nil) ! 0 = x.
Proof. intro x. erewrite <- fold_nth with (d:=x); auto. Qed.


Theorem soundness: forall (w: t),
  (* pre-condition *)
  n > 0 ->
  k > 0 ->
  (n + 1 <= C.k)%Z ->
  (* a and b are proper big int *)
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  (* post-condition *)
  ([|| w.(out) ||] = [|| w.(a) ||] + [|| w.(b) ||])%Z /\
  'w.(out) |: (n).
Proof.
  unwrap_C.
  intros. destruct w as [a b out _cons].
  intros. cbn [_BigAdd.out _BigAdd.a _BigAdd.b] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  lift_to_list.
  rem_iter.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_k].
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
    (* carry bits are binary *)
    (forall (j: nat), j < i -> binary (('unit ! j).(M.carry))) /\
    (* out are in range *)
    ('out [:i]) |: (n) /\
    (* addition is ok for prefix *)
    (([| 'out [:i] |] +  2^(n*i)%nat * (if dec (i = 0)%nat then 0 else F.to_Z ('unit ! (i-1)).(M.carry))
      = [| 'a [:i] |] +  [| 'b [:i] |]))%Z).
  assert (HInv: Inv k (D.iter f k True)).
  apply D.iter_inv.
  - unfold Inv. intuition.
    + lia.
    + simpl. constructor.
    + split_dec. simpl. nia. lia.
  - intros i _cons IH H_bound.
    unfold Inv in *. intros Hf.
    rewrite Heqf in *. destruct Hf as [Hcons [Hai [Hbi [Hci Houti] ] ] ].
    symmetry in Houti.
    lift_to_list.
    (* push if-then-else inside equality *)
    assert (Hci': M.c ('unit!i) = if dec (i=0)%nat then 0 else M.carry ('unit!(i-1)))
    by (destruct (dec (i=0)%nat); auto).
    clear Hci.
    destruct IH as [IH_bin IH_eq]. auto.
    pose proof (ModSumThreeOpt.soundness ('unit ! i )) as M0.
    destruct M0 as [M_eq [M_sum M_bin] ]. lia.
    rewrite Hai. unfold_default. apply Forall_nth. auto. lia.
    rewrite Hbi. unfold_default. apply Forall_nth. auto. lia.
    destruct (dec (i=0%nat)). rewrite Hci'. left. fqsatz.
    rewrite Hci'. apply IH_bin. lia.
    destruct (dec (S i = 0%nat)). discriminate.
    split_as_le ('out) i. split_as_le ('a) i. split_as_le ('b) i.
    repeat (apply conj_use; split); intuit.
    (* binary *)
    + destruct (dec (j < i)). auto.
      assert (Hij: j=i) by lia. rewrite Hij in *. intuition.
    (* out[:i] |: (n) *)
    + eapply Forall_firstn_S with (d:=0). rewrite firstn_length_le; eauto. lia.
      rewrite firstn_firstn. autorewrite with natsimplify. auto.
      rewrite firstn_nth by lia.
      fold_default. rewrite <- Houti. auto.
    + rewrite Hai, Hbi, Hci', Houti in *. clear Hai Hbi Hci' Houti.
      remember (M.carry ('unit!i)) as ci.
      remember (M.carry ('unit!(i-1))) as ci'.
      (* prepare ranges *)
      assert (0 <= ^ 'a!i)%Z. apply F.to_Z_range; lia.
      assert (0 <= ^ 'b!i)%Z. apply F.to_Z_range; lia.
      assert (0 <= ^ 'out!i)%Z. apply F.to_Z_range; lia.
      assert (^ 'a ! i  <= 2^n-1)%Z. unfold_default. apply Forall_nth; auto. lia.
      assert (^ 'b ! i  <= 2^n-1)%Z. unfold_default. apply Forall_nth; auto. lia.
      assert (^ 'out ! i  <= 2^n-1)%Z. auto.
      assert (2*2^n <= 2^C.k)%Z. replace (2*2^n)%Z with (2^(n+1))%Z. apply Zpow_facts.Zpower_le_monotone; try lia. rewrite Zpower_exp; try lia.
      assert (Hci_bin: (0 <= ^ci <= 1)%Z). destruct M_bin as [M_bin|M_bin]; rewrite M_bin in *; autorewrite with F_to_Z; lia.
      assert (Hci'_bin: (0 <= ^ci' <= 1)%Z). specialize (H4 (i-1)%nat). destruct H4 as [M_bin'|M_bin']; try lia; rewrite Heqci', M_bin' in *; autorewrite with F_to_Z; lia.
      
      (* push F.to_Z *)
      pose proof M_eq as M_eq'.
      apply f_equal with (f:=Signed.to_Z) in M_eq'.
      (* assert (2 <= n < C.k-2) by admit.
      assert (Z.abs ($ ' a ! i) <= 2^(n-1)) by admit.
      assert (Z.abs ($ ' b ! i) <= 2^(n-1)) by admit.
      assert (Z.abs ($ ' out ! i) <= 2^(n-1)) by admit.
      assert (Z.abs ($ci) <= 2^(1%N)) by admit.
      split_dec.
      simplify' M_eq'.
      autorewrite with F_to_Signed in M_eq'; try lia;
      repeat autorewrite with F_to_Signed; try lia;
      overflow (4%nat). *)
      

      assert (Hl: (^(' out ! i + (1 + 1) ^ n * ci) = ^'out!i + 2^n*^ci)%Z). repeat (autorewrite with F_to_Z; cbn -[to_list F.pow]; try lia; try nia).
      assert (Hr: (^(' a ! i + ' b ! i + (if dec (i = 0)%nat then 0 else ci')) 
        = ^'a!i + ^'b!i + ^(if dec (i = 0)%nat then 0 else ci'))%Z). 
        { destruct (dec (i=0)%nat); simplify; repeat (autorewrite with F_to_Z; try lia; try nia). }
      symmetry in Hl, Hr, M_eq.
      apply f_equal with (f:=F.to_Z) in M_eq.
      destruct (dec (i=0%nat)) as []; simplify' M_eq; simplify' Hl; simplify' Hr.
      * rewrite e in *. simplify. unfold RZ.ToZ.to_Z.
        repeat erewrite firstn_1; try lia.
        repeat (fold_default; rewrite nth_0); lia.
      * simplify.
        default_apply ltac:(repeat (rewrite firstn_nth; try lia)).
        unfold RZ.ToZ.to_Z.
        default_apply ltac:(repeat rewrite firstn_nth; try lia).
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + eapply RZ.repr_le_firstn; eauto. rewrite firstn_length_le; lia.
      eauto using RZ.repr_trivial.
    + unfold RZ.repr_le. intuition. rewrite firstn_length_le; lia.
      
  - unfold Inv in HInv.
    replace ('a) with ('a[:k]) by (applys_eq firstn_all; f_equal; lia).
    replace ('b) with ('b[:k]) by (applys_eq firstn_all; f_equal; lia).
    destruct (dec (k=0)%nat). lia.
    assert (H_out_inrange: 'out |: (n)). {
      intuition.
      apply Forall_firstn_S with (i:=k) (d:=0); try eauto.
      fold_default. apply binary_in_range; try lia. rewrite out_k. apply H5; lia.
    }
    intuition; auto.
    rewrite <- H7. rewrite <- out_k.
    simplify.
    apply RZ.as_le_split_last'.
    lia.
  Unshelve. exact F.zero. exact F.zero. exact F.zero.
Qed.

Local Notation "[| xs |]'" := (RZ2.as_le n xs).
Local Notation "[|| xs ||]'" := (RZ2.as_le n ('xs)).

Theorem soundnessZ: forall (w: t),
  (* pre-condition *)
  n > 0 ->
  k > 0 ->
  (n + 1 <= C.k)%Z ->
  (* a and b are proper big int *)
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  (* post-condition *)
  ([|| w.(out) ||]' = [|| w.(a) ||]' + [|| w.(b) ||]')%Z /\
  'w.(out) |: (n).
Admitted.

Theorem soundness_lemma: forall (w: t) i,
  (* pre-condition *)
  n > 0 ->
  k > 0 ->
  (k = i + 2)%nat ->
  (n + 1 <= C.k)%Z ->
  (* a and b are proper big int *)
  'w.(a) |: (n) ->
  'w.(b) |: (n) ->
  w.(b) [i] = 0 ->
  w.(b) [i+1] = 0 ->
  (* post-condition *)
  w.(out)[i + 2] = 0.
Proof.
  unwrap_C.
  intros. destruct w as [a b out _cons].
  intros. cbn [_BigAdd.out _BigAdd.a _BigAdd.b] in *.
  unfold cons in _cons. destruct _cons as [unit prog].
  rem_iter.
  pose proof (length_to_list a) as Hlen_a.
  pose proof (length_to_list b) as Hlen_b.
  pose proof (length_to_list out) as Hlen_out.
  pose proof (length_to_list unit) as Hlen_unit.

  destruct prog as [p_iter out_k]. rewrite <- H1. rewrite out_k.
  pose (Inv := fun (i: nat) (_cons: Prop) => _cons -> 
        (forall j:nat, j < i -> binary (('unit ! j).(M.c)) /\ binary (('unit ! j).(M.carry)) /\
              M.a (unit [j]) = a [j] /\
              M.b (unit [j]) = b [j]
              )).
  assert (HInv: Inv (k)%nat (D.iter f k True)).
  { apply DSL.iter_inv; unfold Inv; try easy. 
    - intros. lia. 
    - intros i1 _cons IH Hi Hstep.
      subst. intros. 
      destruct (dec (j = i1));subst.
      + lift_to_list. intuition;auto. destruct dec in H10;subst;try easy. rewrite H10;constructor;auto.
        rewrite H10. specialize (H11 (i1-1)%nat). intuition. destruct H11;try lia. intuition;auto.
        admit.  
      + apply IH;intuition;lia. }
  apply HInv in p_iter. subst. 
  specialize (p_iter (i+1)%nat) as hh1. destruct hh1;try lia.
  rewrite H6 in H7. intuition.
  pose proof (ModSumThreeOpt.soundness (unit [i + 1])) as M0.
  destruct M0;try lia. rewrite H7. lift_to_list.
  rewrite Forall_forall in H3. apply H3. admit.
  rewrite Forall_forall in H4. apply H4. admit.
  lift_to_list. auto. lift_to_list. intuition.
  rewrite H7 in *. rewrite H10 in *. admit.
Admitted.

End _BigAdd.
End BigAdd.
