Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Crypto.Algebra.Nsatz.
Require Import Crypto.Util.Decidable.

From Circom Require Import Circom DSL Util ListUtil Simplify.


(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Repr.

Import C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion N.of_nat : nat >-> N.


(* Base 2^n representations *)
Section Base2n.

Variable n: nat.

Lemma to_Z_2: @F.to_Z q 2 = 2%Z.
Proof. unwrap_C. simpl. repeat rewrite Z.mod_small; lia. Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) (i: nat),
  (x ^ (S i) = x * x ^ i)%Z.
Proof.
  unwrap_C. intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.


Lemma binary_Z: forall x, binary x <-> ^x = 0%Z \/ ^x = 1%Z.
Proof.
  unfold binary;split;intros;unwrap_C.
  - destruct H;subst;simpl;auto. right. apply Zmod_1_l. lia. 
  - destruct H;subst;simpl;auto. 
    + left. pose proof (@F.to_Z_0 q). rewrite <- H0 in H. apply F.eq_to_Z_iff in H;auto.
    + right. pose proof (@F.to_Z_1 q). rewrite <- H0 in H;auto. apply F.eq_to_Z_iff in H;auto.
Qed.

Lemma leq_F_z_iff: forall x, (x <= 1 /\ x >= 0 <-> x = 0 \/ x = 1)%Z.
Proof.
  split; intros; lia.
Qed.

Lemma in_range_binary: forall x,  x | (1) <-> binary x.
Proof.
  split; intros.
  - apply binary_Z. apply leq_F_z_iff. pose proof (F.to_Z_range x). lia.
  - apply binary_Z in H. apply leq_F_z_iff; auto.
Qed.

Lemma Forall_in_range: forall xs, xs |: (1) <-> Forall binary xs.
Proof. intuition; eapply Forall_weaken; try apply in_range_binary; auto.
Qed.

(* Little- and big-endian *)
Section Endianness.

(* interpret a list of weights as representing a little-endian base-2 number *)
Fixpoint as_le_acc (i: nat) (ws: list F) : F :=
  match ws with
  | nil => 0
  | w::ws' => w * 2^(n * i) + as_le_acc (S i) ws'
  end.

Lemma as_le_acc_S: forall ws i,
  as_le_acc (S i) ws = 2^n * as_le_acc i ws.
Proof.
  unwrap_C. induction ws as [| w ws]; intros; cbn [as_le_acc].
  - fqsatz.
  - rewrite IHws.
    replace (n * S i)%N with (n * i + n)%N by lia.
    rewrite F.pow_add_r.
    fqsatz.
Qed.

Definition as_le' := as_le_acc 0%nat.

Fixpoint as_le (ws: list F) : F :=
  match ws with
  | nil => 0
  | w::ws' => w + 2^n * (as_le ws')
  end.

Notation "[| xs |]" := (as_le xs).

Lemma as_le_as_le': forall ws,
  [| ws |] = as_le' ws.
Proof.
  unwrap_C. unfold as_le'.
  induction ws; simpl.
  - reflexivity.
  - rewrite as_le_acc_S, IHws, N.mul_0_r, F.pow_0_r.
    fqsatz.
Qed.

(* repr func lemma: multi-step index change *)
(* Lemma as_le'_n: forall ws (i j: nat),
  as_le' (i+j)%nat ws = 2^i * as_le' j ws.
Proof.
  unwrap_C. induction i; intros; simpl.
  - rewrite F.pow_0_r. fqsatz.
  - rewrite as_le'_S. rewrite IHi.
    replace (N.pos (Pos.of_succ_nat i)) with (1 + N.of_nat i)%N.
    rewrite F.pow_add_r.
    rewrite F.pow_1_r.
    fqsatz.
    lia.
Qed. *)

Lemma as_le_app: forall ws1 ws2,
  [| ws1 ++ ws2 |] = [| ws1 |] + 2^(n * length ws1) * [| ws2 |].
Proof.
  unwrap_C. induction ws1; intros.
  - rewrite N.mul_0_r, F.pow_0_r. fqsatz.
  - cbn [as_le length app].
    rewrite IHws1.
    remember (length ws1) as l.
    replace (n * S l)%N with (n * l + n)%N by lia.
    rewrite F.pow_add_r. fqsatz.
Qed.

Fixpoint as_be_acc (i: nat) ws :=
  match ws with
  | nil => 0
  | w::ws' => 2^(n*i) * w + as_be_acc (i-1)%nat ws'
  end.

Definition as_be ws := as_be_acc (length ws - 1) ws.

Lemma be__rev_le: forall l,
  as_be l = as_le (rev l).
Proof.
  unwrap_C. unfold as_be.
  induction l.
  - reflexivity.
  - simpl. rewrite as_le_app. simpl.
    replace (length l - 0)%nat with (length l) by lia.
    rewrite IHl.
    rewrite rev_length.
    fqsatz.
Qed.

Lemma rev_be__le: forall l,
  as_be (rev l) = as_le l.
Proof.
  unwrap_C. intros.
  remember (rev l) as l'.
  replace l with (rev (rev l)). rewrite be__rev_le. subst. reflexivity.
  apply rev_involutive.
Qed.

End Endianness.
    

Notation "[| xs |]" := (as_le xs).

Section Representation.

Definition repr_le x m ws :=
  length ws = m /\
  ws |: (n) /\
  x = [| ws |].

Definition repr_be x m ws :=
  length ws = m /\
  ws |: (n) /\
  x = as_be ws.

Lemma repr_rev: forall x m ws, repr_le x m ws <-> repr_be x m (rev ws).
Proof.
  split; intros; unfold repr_le, repr_be in *.
  - intuition.
    + rewrite rev_length. auto.
    + apply Forall_rev. auto.
    + rewrite rev_be__le. auto.
  - intuition.
    + rewrite <- rev_length. auto. 
    + rewrite <- rev_involutive. apply Forall_rev. auto.
    + rewrite <- rev_be__le. auto.
Qed.

(* repr inv: base case *)
Lemma repr_le_base: repr_le 0 0%nat nil.
Proof. unfold repr_le. intuition. Qed.

(* repr inv: invert weight list *)
Lemma repr_le_invert: forall w ws,
  repr_le (as_le (w::ws)) (S (length ws)) (w::ws) ->
  repr_le (as_le ws) (length ws) ws.
Proof.
  unfold repr_le.
  intros. intuition.
  invert H. auto.
Qed.

Lemma as_be_0: forall ws, as_be (0::ws) = as_be ws.
Proof. 
  unwrap_C. 
  intros. unfold as_be. simpl. autorewrite with natsimplify. fqsatz.
Qed.

Lemma repr_le_last0: forall ws x n,
  repr_le x (S n) (ws ++ 0 :: nil) ->
  repr_le x n ws.
Proof.
  unwrap_C.
  intros. rewrite repr_rev in *. rewrite rev_unit in H.
  destruct H as [H_len [ H_bin H_le] ].
  unfold repr_be. intuition idtac.
  auto.
  invert H_bin. auto.
  rewrite <- as_be_0. auto.
Qed.

Lemma repr_le_last0': forall ws x i,
  List.nth i ws 0 = 0 ->
  repr_le x (S i) ws ->
  repr_le x i (firstn i ws).
Proof.
  intros.
  pose proof H0 as H_repr. unfold repr_le in H0.
  apply repr_le_last0.
  rewrite <- H.
  erewrite firstn_split_last by lia.
  auto.
Qed.

(* repr inv: trivial satisfaction *)
Lemma repr_trivial: forall ws,
  ws |: (n) ->
  repr_le (as_le ws) (length ws) ws.
Proof.
  induction ws; unfold repr_le; intuition idtac.
Qed.

(* repr inv: any prefix of weights also satisfies the inv *)
Lemma repr_le_prefix: forall ws1 ws2 x x1 l l1 ws,
  ws = ws1 ++ ws2 ->
  x = as_le ws ->
  x1 = as_le ws1 ->
  l = length ws ->
  l1 = length ws1 ->
  repr_le x l ws ->
  repr_le x1 l1 ws1.
Proof.
  unwrap_C. unfold repr_le. 
  induction ws1; intros; subst; simpl in *; intuition.
  invert H1.
  constructor; auto.
  apply Forall_app in H5. intuition.
Qed.

Lemma repr_le_firstn: forall x x' l l' ws ws' i,
  x = as_le ws ->
  x' = as_le ws' ->
  l' = length ws' ->
  l = length ws ->
  ws' = firstn i ws ->
  repr_le x l ws ->
  repr_le x' l' ws'.
Proof.
  intros. eapply repr_le_prefix with (ws2:=skipn i ws); subst; eauto.
  rewrite firstn_skipn. auto.
Qed.

Lemma as_le_split_last' : forall i ws,
  length ws = S i ->
  [| ws |] = [| ws[:i] |] + 2^(n*i) * ws ! i.
Proof.
  unwrap_C.
  intros i ws Hlen. 
  assert (exists ws', ws = ws'). exists ws. reflexivity.
  destruct H as [ws' Hws]. pose proof Hws as Hws'.
  erewrite <- firstn_split_last with (l:=ws) (n:=i)(d:=0) in Hws; auto.
  pose proof (as_le_app (ws[:i]) (ws!i::nil)).
  rewrite firstn_length_le in H by lia.
  simpl in H. simplify' H.
  rewrite <- H.
  subst.
  f_equal.
  rewrite fold_nth in Hws' by lia.
  auto.
Qed.


Lemma as_le_split_last : forall i ws,
  length ws = S i ->
  ws |: (n) ->
  [| ws |] = [| ws[:i] |] + 2^(n*i) * ws ! i.
Proof.
  intros. apply as_le_split_last'. lia. Qed.


End Representation.

End Base2n.

(* Base 2^1 representation *)
Section Base2.

Definition repr_le2 := (repr_le 1).
Definition repr_be2 := (repr_be 1).
Definition as_le2 := (as_le 1).
Definition as_be2 := (as_be 1).




Create HintDb F_to_Z discriminated.
Hint Rewrite (@F.to_Z_add q) : F_to_Z.
Hint Rewrite (@F.to_Z_mul q) : F_to_Z.
Hint Rewrite (@F.to_Z_pow q) : F_to_Z.
Hint Rewrite (@F.to_Z_1 q) : F_to_Z.
Hint Rewrite (to_Z_2) : F_to_Z.
Hint Rewrite (@F.pow_1_r q) : F_to_Z.

(* [|ws|] <= 2^n - 1 *)
Theorem repr_le_ub: forall ws x n,
  repr_le2 x n ws ->
  n <= k ->
  x <=z (2^n - 1)%Z.
Proof with (lia || nia || eauto).
  unwrap_C.
  induction ws as [| w ws]; intros x n [] H_k; intuition;
  apply Forall_in_range in H1.
  - subst. discriminate.
  - (* analyze n: is has to be S n for some n *)
    destruct n. subst. discriminate.
    simpl in H. invert H. remember (length ws) as l.
    (* lemma preparation starts here *)

    (* extract consequence of IHws *)
    assert (IH: F.to_Z (as_le 1 ws) <= 2 ^ l - 1). {
      apply IHws...
      unfold repr_le2, repr_le. invert H1. intuition. apply Forall_in_range. auto.
    }
    
    (* introduce lemmas into scope *)
    (* bound |w| *)
    assert (H_w: 0 <= F.to_Z w <= 1). {
      invert H1. destruct H2; subst; simpl; rewrite Z.mod_small...
    }
    (* peel off 1 from 2^(x+1) *)
    
    (* bound 2^l *)
    assert (H_2_len: 0 <= 2 * 2 ^ l <= 2 ^ k). {
      split... replace (2 * 2 ^ l)%Z with (2 ^ (l + 1))%Z.
      apply Zpow_facts.Zpower_le_monotone...
      rewrite Zpower_exp...
    }
    (* F.to_Z x is nonneg *)
    assert (0 <= F.to_Z (as_le 1 ws)). {
      apply F.to_Z_range...
    }
    (* lemma preparation ends here *)
    (* actual proof starts here *)
    cbn [as_le].
    rewrite pow_S_Z.
    repeat (autorewrite with F_to_Z; simplify; try lia).
Qed.

Lemma repr_le_ub': forall xs,
  xs |: (1) ->
  length xs <= k ->
  ^as_le 1 xs <= (2^(length xs) - 1)%Z.
Proof.
  intros.
  eapply repr_le_ub; auto. apply repr_trivial; auto.
Qed.

Definition as_le_ub := repr_le_ub'.

Lemma as_le_ub': forall xs,
Forall (fun x1 : F => x1 = 0 \/ x1 = 1) xs ->
  length xs <= k ->
  ^as_le 1 xs <= (2^(length xs) - 1)%Z.
Proof.
  intros.
  apply as_le_ub. eapply Forall_weaken. apply in_range_binary. apply H. lia.
Qed.

Lemma Z_le_mul_pos: forall a b c,
  c > 0 ->
  a <= b ->
  a * c <= b * c.
Proof. intros. nia. Qed.

Lemma F_mul_add_distr_l:
forall n m p : F, p * (n + m) = (n * p + m * p).
Proof. unwrap_C. intros. fqsatz. Qed.


(* ws[i] = 1 -> [|ws|] >= 2^i *)
Theorem repr_le_lb: forall (n i: nat) ws x,
  n <= k ->
  repr_le2 x n ws ->
  i < n ->
  List.nth i ws 0 = 1 ->
  x >=z 2^i.
Proof with (lia || auto).
  unwrap_C.
  intros.
  pose proof H0 as H_repr.
  unfold repr_le2, repr_le in H0. intuition idtac. subst.
  apply Forall_in_range in H0.
  fold (as_le2 ws).

  assert (Hws: ws = ws) by reflexivity.
  rewrite <- firstn_skipn with (n:=i) in Hws.
  rewrite <- firstn_skipn with (n:=1%nat) (l:=(skipn i ws)) in Hws.
  rewrite firstn_1 with (d:=0) in Hws by (rewrite skipn_length; lia).
  rewrite nth_skipn in Hws by lia.
  autorewrite with natsimplify in Hws.
  rewrite H2 in Hws.
  
  rewrite Hws.
  unfold as_le2.
  repeat rewrite as_le_app.
  rewrite skipn_skipn in *.
  replace (as_le2 (1 :: nil)) with (1:F) by (simpl; fqsatz).
  rewrite firstn_length_le by lia.
  repeat rewrite N.mul_1_l.
  cbn [length as_le].
  fold (as_le2).

  assert (0 <= F.to_Z (as_le2 (ws[:i])) <= (2 ^ i - 1)). {
    split. apply F.to_Z_range...
    eapply repr_le_ub with (firstn i ws).
    remember (firstn i ws) as f.
    replace i with (length (firstn i ws)).
    subst. apply repr_trivial.
    apply Forall_firstn. apply Forall_in_range. auto.
    rewrite firstn_length_le; lia. lia.
  }

  remember (length ws) as l.
  assert (0 <= F.to_Z (as_le2 (skipn (1 + i) ws)) <= 2 ^(length (skipn (1 + i) ws)) - 1). {
    split. apply F.to_Z_range...
    eapply repr_le_ub with (skipn (1 + i) ws).
    apply repr_trivial.
    apply Forall_skipn. apply Forall_in_range. auto.
    rewrite skipn_length. lia.
  }

  assert (H_i_l: 2^i < 2^l) by (apply Zpow_facts.Zpower_lt_monotone; lia).
  assert (H_l_k: 2^l <= 2^k) by (apply Zpow_facts.Zpower_le_monotone; lia).
  
  rewrite skipn_length in H4.
  rewrite <- Heql in H4.


  simplify.
  rewrite F_mul_add_distr_l.
  simplify.

  remember (as_le2 (ws[:i])) as pre.
  remember (as_le2 (ws[1+i:])) as post.

  assert (^pre + 2 ^ i * (1 + 2 * ^post) < q). {
    replace (2 ^ i * (1 + 2 * ^post))%Z with (2^i + 2 ^i * 2 * ^post)%Z by lia.
    assert (2^(i+1) * ^post <= 2^l - 2^(i+1)).
    destruct H4. apply Z_le_mul_pos with (c:=(2^(i+1))%Z) in H5.
    rewrite Z.mul_sub_distr_r in H5.
    autorewrite with zsimplify in H5.
    rewrite <- Zpower_exp in H5 by lia.
    replace ((l - (1 + i))%nat + (i + 1))%Z with (Z.of_nat l) in H5 by lia.
    nia.
    lia.
    replace (2 ^ (i + 1) * ^post)%Z with (2 ^ i * 2 * ^post)%Z in H5 by (rewrite Zpower_exp; lia).
    etransitivity.
    apply Z.add_lt_le_mono with (m:=(2 ^ i)%Z).
    lia.
    apply Z.add_le_mono. reflexivity.
    apply H5.
    rewrite Zpower_exp by lia. rewrite Z.pow_1_r. lia.
  }
  assert (1 + 2 * ^post < q). { assert (2^i > 0) by lia. nia. }
  
  repeat (autorewrite with F_to_Z; simplify; try (simpl; lia ));
  replace (1 + 1)%Z with 2%Z; try lia.
Qed.


Local Open Scope Z_scope.
(* From Circom Require Import LibTactics. *)

Theorem as_le_lb: forall xs (i: nat),
  length xs <= k ->
  xs |: (1) ->
  i < length xs ->
  List.nth i xs 0%F = 1%F ->
  as_le 1 xs >=z 2^i.
Proof.
  intros.
  eapply repr_le_lb.
  eauto.
  apply repr_trivial; intuit.
  lia.
  auto.
Qed.
Theorem as_le_lb': forall xs (i: nat),
length xs <= k ->
Forall (fun x1: F => binary x1) xs ->
i < length xs ->
List.nth i xs 0%F = 1%F ->
as_le 1 xs >=z 2^i.
Proof.
  intros.
  apply as_le_lb; try lia; auto.
  eapply Forall_weaken. apply in_range_binary. auto.
Qed.


End Base2.
End Repr.