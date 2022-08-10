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

Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Circom.Circom Circom.DSL Circom.Util.
(* Require Import VST.zlist.Zlist. *)


(* Circuits:
 * https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
 *)
Module Bitify (C: CIRCOM).

Import C.

Module D := DSL C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Notation "w [ i ]" := (Tuple.nth_default 0 i w).
Local Notation "F ^ n" := (tuple F n) : type_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion N.of_nat : nat >-> N.


(* Base 2^n representations *)
Section Base2n.

Variable n: nat.

Lemma to_Z_2: @F.to_Z q 2 = 2%Z.
Proof. unwrap_C. simpl. repeat rewrite Z.mod_small; lia. Qed.

(* peel off 1 from x^(i+1) in field exp *)
Lemma pow_S_N: forall (x: F) (i: nat),
  x ^ (S i) = x * x ^ i.
Proof.
  unwrap_C. intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) (i: nat),
  (x ^ (S i) = x * x ^ i)%Z.
Proof.
  unwrap_C. intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.


Section Firstn.

Lemma firstn_nth {A: Type}: forall l i j (d: A),
  (i < j)%nat ->
  nth i (firstn j l) d = nth i l d.
Proof.
  induction l; simpl; intros.
  - rewrite firstn_nil. destruct i; reflexivity.
  - destruct j. lia. destruct i.
    + rewrite firstn_cons. reflexivity.
    + simpl. rewrite IHl. auto. lia.
Qed.

Lemma fistn_prev {A: Type}: forall l i j (d: A),
  (i < j)%nat ->
  (j < length l)%nat ->
  nth i (firstn (S j) l) d = nth i (firstn j l) d.
Proof.
  induction l; intros.
  - simpl in *. lia.
  - simpl. destruct i. destruct j. lia. reflexivity.
    destruct j. lia.
    rewrite IHl. simpl. reflexivity.
    lia.
    simpl in H0. lia.
Qed.

Lemma firstn_1 {A: Type}: forall l (d: A),
  (length l > 0)%nat ->
  firstn 1 l = nth 0 l d :: nil.
Proof.
  destruct l; simpl; intros. lia. reflexivity.
Qed.

Lemma firstn_to_list: forall m (x: F^m),
  firstn m (to_list m x) = to_list m x.
Proof.
  intros. apply firstn_all2. rewrite length_to_list; lia.
Qed.

Lemma nth_skipn {A: Type}: forall l i j (d: A),
  (i+j < length l)%nat ->
  nth i (skipn j l) d = nth (i+j) l d.
Proof.
  induction l; simpl; intros.
  - destruct i; destruct j; lia.
  - destruct i; destruct j; simpl; repeat first [
      reflexivity
      | progress rewrite IHl by lia
      | progress rewrite Nat.add_0_r
      | progress rewrite Nat.add_succ_r
    ].
Qed.

Lemma firstn_S {A: Type}: forall i l (d: A),
  (i < length l)%nat ->
  firstn (S i) l = firstn i l ++ (nth i l d :: nil).
Proof.
  intros.
  replace (firstn (S i) l) with (firstn (S i) (firstn i l ++ skipn i l)).
  rewrite firstn_app. rewrite firstn_firstn.
  rewrite firstn_length_le by lia.
  replace (min (S i) i) with i by lia.
  replace (S i - i)%nat with 1%nat by lia.
  erewrite firstn_1.
  erewrite nth_skipn by lia.
  simpl. reflexivity.
  rewrite skipn_length. lia.
  rewrite firstn_skipn. reflexivity.
Qed.
End Firstn.


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

Lemma as_le_as_le': forall ws,
  as_le ws = as_le' ws.
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
  as_le (ws1 ++ ws2) = as_le ws1 + 2^(n * length ws1) * as_le ws2.
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
    
Section Representation.

Definition in_range (x: F) := (x <=z (2^n-1)%Z).

Definition repr_le x m ws :=
  length ws = m /\
  List.Forall in_range ws /\
  x = as_le ws.

Definition repr_be x m ws :=
  length ws = m /\
  List.Forall in_range ws /\
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

Lemma skipn_nth_last: forall {A: Type} i xs (d: A),
  length xs = S i ->
  skipn i xs = nth i xs d :: nil.
Proof.
  intros.
  rewrite <- rev_involutive with (l:=xs).
  rewrite skipn_rev. rewrite rev_length. rewrite H. autorewrite with natsimplify.
  erewrite firstn_1.
  simpl.
  rewrite rev_involutive.
  rewrite rev_nth by lia.
  rewrite H. autorewrite  with natsimplify. reflexivity.
  rewrite rev_length. lia.
Qed.

Lemma firstn_split_last {A: Type}: forall (l: list A) n d,
  length l = S n ->
  firstn n l ++ nth n l d :: nil = l.
Proof.
  intros l m d Hlen.
  assert (l=l) by reflexivity.
  rewrite <- firstn_skipn with (n:=m) in H.
  erewrite skipn_nth_last in H by lia.
  rewrite <- H. reflexivity.
Qed.

Lemma skipn_skipn {A: Type}: forall (j i: nat) (l: list A),
  skipn i (skipn j l) = skipn (i+j)%nat l.
Proof.
  induction j; simpl; intros.
  autorewrite with natsimplify. reflexivity.
  destruct l. repeat rewrite skipn_nil. reflexivity.
  rewrite Nat.add_succ_r. simpl. rewrite IHj. reflexivity.
Qed.

Lemma Forall_firstn {A: Type}: forall (l: list A) i P,
  Forall P l -> Forall P (firstn i l).
Proof.
  induction l; intros.
  - rewrite firstn_nil. constructor.
  - invert H. 
    destruct i. simpl. constructor.
    simpl. constructor; auto.
Qed.

Lemma Forall_skipn {A: Type}: forall (l: list A) i P,
  Forall P l -> Forall P (skipn i l).
Proof.
  induction l; intros.
  - rewrite skipn_nil. auto.
  - invert H.
    destruct i; simpl. auto.
    auto.
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
  nth i ws 0 = 0 ->
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
  Forall in_range ws ->
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

End Representation.

End Base2n.

(* Base 2^1 representation *)
Section Base2.

Definition repr_le2 := (repr_le 1).
Definition repr_be2 := (repr_be 1).
Definition as_le2 := (as_le 1).
Definition as_be2 := (as_be 1).


Lemma in_range_binary: forall x, in_range 1 x <-> binary x.
Admitted.

Lemma Forall_if: forall {A: Type} (P Q: A -> Prop) (l: list A),
  (forall x, P x -> Q x) -> Forall P l -> Forall Q l.
Admitted.

Lemma Forall_in_range: forall xs, Forall (in_range 1) xs <-> Forall binary xs.
Proof. intuition; eapply Forall_if; try apply in_range_binary; auto.
Qed.

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
    autorewrite with F_to_Z...
    autorewrite with zsimplify.
    repeat rewrite Z.mod_small...
Qed.

Lemma app_congruence: forall {A: Type} (l1 l2 l1' l2': list A),
  l1 = l1' ->
  l2 = l2' ->
  l1 ++ l2 = l1' ++ l2'.
Proof.
  intros. rewrite H, H0. easy.
Qed.



Lemma Z_le_mul_pos: forall a b c,
  c > 0 ->
  a <= b ->
  a * c <= b * c.
Proof. intros. nia. Qed.

(* ws[i] = 1 -> [|ws|] >= 2^i *)
Theorem repr_le_lb: forall (n i: nat) ws x,
  n <= k ->
  repr_le2 x n ws ->
  i < n ->
  nth i ws 0 = 1 ->
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

  assert (0 <= F.to_Z (as_le2 (firstn i ws)) <= (2 ^ i - 1)). {
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

  autorewrite with F_to_Z...
  autorewrite with zsimplify.
  replace (2 mod q) with 2%Z by (rewrite Zmod_small; lia).

  remember (F.to_Z (as_le2 (firstn i ws))) as pre.
  remember (F.to_Z (as_le2 (skipn (1 + i) ws))) as post.

  assert (pre + 2 ^ i * (1 + 2 * post) < q). {
    replace (2 ^ i * (1 + 2 * post))%Z with (2^i + 2 ^i * 2 * post)%Z by lia.
    assert (2^(i+1) * post <= 2^l - 2^(i+1)).
    destruct H4. apply Z_le_mul_pos with (c:=(2^(i+1))%Z) in H5.
    rewrite Z.mul_sub_distr_r in H5.
    autorewrite with zsimplify in H5.
    rewrite <- Zpower_exp in H5 by lia.
    replace ((l - (1 + i))%nat + (i + 1))%Z with (Z.of_nat l) in H5 by lia.
    nia.
    lia.
    replace (2 ^ (i + 1) * post)%Z with (2 ^ i * 2 * post)%Z in H5 by (rewrite Zpower_exp; lia).
    etransitivity.
    apply Z.add_lt_le_mono with (m:=(2 ^ i)%Z).
    lia.
    apply Z.add_le_mono. reflexivity.
    apply H5.
    rewrite Zpower_exp by lia. rewrite Z.pow_1_r. lia.
  }
  assert (1 + 2 * post < q). { assert (2^i > 0) by lia. nia. }
  repeat rewrite Zmod_small...
Qed.

End Base2.


Module Num2Bits.

Definition cons (n: nat) (_in: F) (_out: F^n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (D.iter (fun (i: nat) '(lc1, e2, _C) =>
    let out_i := (_out [i] ) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    n
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C.

Theorem cons_imply_binary n _in _out:
  cons n _in _out -> (forall i, (i < n)%nat -> binary (_out[i])).
Proof.
  unwrap_C. unfold cons.
  (* provide loop invariant *)
  pose (Inv := fun i '((lc1, e2, _C): (F * F * Prop)) =>
    (_C -> (forall j, (j < i)%nat -> binary (_out[j])))).
  (* iter initialization *)
  remember (0, 1, True) as a0.
  intros prog i H_i_lt_n.
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?f ?n ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* invariant holds *)
  assert (Hinv: forall i, Inv i (D.iter f i a0)). {
  intros. apply D.iter_inv; unfold Inv.
  - (* base case *) 
    subst. intros _ j impossible. lia.
  - (* inductive case *)
    intros j res Hprev.
    destruct res. destruct p.
    rewrite Heqf.
    intros _ Hstep j0 H_j0_lt.
    destruct Hstep as [Hstep HP].
    specialize  (Hprev HP).
    destruct (dec (j0 < j)%nat).
    + auto.
    + unfold binary. intros.
      replace j0 with j by lia.
      destruct (dec (_out[j] = 0)).
      * auto.
      * right. fqsatz.
   }
  unfold Inv in Hinv.
  specialize (Hinv n).
  destruct (D.iter f n a0).
  destruct p.
  intuition.
Qed.

Lemma nth_oblivious: forall {A: Type} l (i: nat) (d1 d2: A),
  i < length l ->  
  nth i l d1 = nth i l d2.
Proof.
  induction l; intros; destruct i; cbn [nth length] in *; try lia; auto.
  erewrite IHl. reflexivity. lia.
Qed.


Class t (n: nat): Type := mk {
  _in: F; 
  _out: F^n; 
  _cons: cons n _in _out
}.

Definition spec (n: nat) (w: t n) := 
  repr_le2 w.(_in) n (to_list n w.(_out)).

Theorem soundness: forall (n: nat) (w: t n), spec n w.
Proof.
  unwrap_C. intros.
  destruct w as [_in _out _cons]. unfold spec, cons in *. simpl.
  pose (Inv := fun i '((lc1, e2, _C)) => 
    (_C: Prop) ->
      (e2 = (2^N.of_nat i) /\
      let firsti := firstn i (to_list n _out) in
      repr_le2 lc1 i firsti)).
  remember (fun (i : nat) '(y, _C) =>
  let
  '(lc1, e2) := y in
   (lc1 + nth_default 0 i _out * e2, 
   e2 + e2,
   nth_default 0 i _out * (nth_default 0 i _out - 1) = 0 /\
   _C)) as f.
  assert (Hinv: Inv n (D.iter f n (0,1,True))). {
    apply D.iter_inv; unfold Inv.
    - intuition. simpl. rewrite F.pow_0_r. fqsatz.
      simpl. apply repr_le_base.
    - intros j acc. destruct acc as [acc _C]. destruct acc as [lc1 e2].
      intros Hprev Hjn. subst. intuition.
      + rewrite pow_S_N. subst. fqsatz.
      + unfold repr_le2, repr_le in *.
        pose proof (length_to_list _out).
        intuition.
        * rewrite firstn_length_le; lia.
        * apply Forall_in_range in H3. apply Forall_in_range.
          apply Forall_nth. intros. subst.
          destruct (dec (i < j)%nat).
          -- rewrite fistn_prev by lia. pose proof Forall_nth.
            apply Forall_nth. apply H3. lia.
          -- rewrite firstn_length_le in H5. assert (i = j) by lia. subst.
            rewrite firstn_nth by lia.
            rewrite nth_oblivious with (d2:=0) by lia.
            rewrite <- nth_default_eq, nth_default_to_list.
            unfold binary.
            destruct (dec (_out[j] = 0)); (left; fqsatz) || (right; fqsatz).
            rewrite length_to_list. lia.
        * subst. erewrite firstn_S with (d:=0) by lia.
          rewrite as_le_app.
          rewrite <- nth_default_eq, nth_default_to_list.
          cbn [as_le].
          rewrite firstn_length_le.
          rewrite N.mul_1_l.
           fqsatz.
          rewrite length_to_list. lia.
  }
  destruct (D.iter f n (0,1,True)) as [ [lc1 e2] _C].
  unfold Inv in Hinv. intuition.
  subst. rewrite <- firstn_to_list. auto.
Qed.

End Num2Bits.

End Bitify.