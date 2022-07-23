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
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Util.
Require Import Circom.circomlib.bitify.

Require Import Crypto.Spec.ModularArithmetic.
(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)

Section _bigint.

Local Open Scope list_scope.
Local Open Scope F_scope.

Ltac fqsatz := fsatz_safe; autorewrite with core; auto.

Context (q:positive) (k:Z) {prime_q: prime q} {two_lt_q: 2 < q} {k_positive: 1 < k} {q_lb: 2^k < q}.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  apply Pos.ltb_lt. lia.
Qed.

Lemma q_gt_2: 2 < q.
Proof.
  replace 2%Z with (2^1)%Z by lia.
  apply Z.le_lt_trans with (m := (2 ^ k)%Z); try lia.
  eapply Zpow_facts.Zpower_le_monotone; try lia.
Qed.

Hint Rewrite q_gtb_1 : core.

(**************************
 * Overflow Representation
 **************************)
Definition two : F q := 1 + 1.
Notation "2" := two.

Lemma to_Z_2: F.to_Z 2 = 2%Z.
Proof. simpl. repeat rewrite Z.mod_small; lia. Qed.


(* peel off 1 from x^(i+1) in field exp *)
Lemma pow_S_N: forall (x: F q) i,
  x ^ (N.of_nat (S i)) = x * x ^ (N.of_nat i).
Proof.
  intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) i,
  (x ^ (Z.of_nat (S i)) = x * x ^ (Z.of_nat i))%Z.
Proof.
  intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.

(* [repr]esentation [func]tion:
 * interpret a list of weights as representing a little-endian base-2^n number
 *)
Fixpoint repr_to_le' (n: nat) (i: nat) (ws: list (F q)) : F q :=
  match ws with
  | nil => 0
  | w::ws' => w * two^(N.of_nat n * N.of_nat i) + repr_to_le' n (S i) ws'
  end.

Definition repr_to_le n := repr_to_le' n 0%nat.

(* repr func lemma: single-step index change *)
Lemma repr_to_le'_S: forall ws n i,
  repr_to_le' n (S i) ws = 2^(N.of_nat n) * repr_to_le' n i ws.
Proof.
  induction ws as [| w ws]; intros.
  - fqsatz.
  - cbn [repr_to_le'].
    rewrite IHws.
    remember (N.of_nat n) as m.
    replace (2^(m * N.of_nat (S i))) with (2^m * 2 ^ (m * N.of_nat i)).
    fqsatz.
    rewrite <- F.pow_add_r. f_equal. lia.
Qed.

(* Probably not needed
(* repr func lemma: multi-step index change *)
Lemma repr_to_le'_n: forall ws i j,
  repr_to_le' (i+j) ws = 2^(N.of_nat i) * repr_to_le' j ws.
Proof.
  induction i; intros; simpl.
  - rewrite F.pow_0_r. fqsatz.
  - rewrite repr_to_le'_S. rewrite IHi.
    replace (N.pos (Pos.of_succ_nat i)) with (1 + N.of_nat i)%N.
    rewrite F.pow_add_r.
    rewrite F.pow_1_r.
    fqsatz.
    lia.
Qed. *)

(* repr func lemma: decomposing weight list *)
Lemma repr_to_le_app: forall ws2 ws1 ws n i,
  ws = ws1 ++ ws2 ->
  repr_to_le' n i ws = repr_to_le' n i ws1 + repr_to_le' n (i + length ws1) ws2.
Proof.
  induction ws1; simpl; intros.
  - subst. replace (i+0)%nat with i by lia. fqsatz.
  - destruct ws; inversion H; subst.
    simpl.
    assert (repr_to_le' n (S i) (ws1 ++ ws2) = 
      repr_to_le' n (S i) ws1 + repr_to_le' n (i + S (length ws1)) ws2). {
        rewrite <- plus_n_Sm, <- plus_Sn_m.
        eapply IHws1. reflexivity.
      }
    fqsatz.
Qed.

(* 
(* overflow representation *)
(* interpret a list of weights as representing a little-endian base-2^n number *)
Fixpoint repr_to_le_Z' (n: nat) (i: nat) (ws: list (F q)) : Z :=
  match ws with
  | nil => 0
  | w::ws' => (toSZ w) * 2^(N.of_nat n * N.of_nat i) + repr_to_le_Z' n (S i) ws'
  end.

(* overflow representation *)
(* FIXME: repr_to_le' should call toSZ *)
Definition repr_overflow x l n ws :=
  length ws = l /\
  x = repr_to_le_Z' n 0%nat ws. *)


Definition half: Z. exact (Z.div q 2). Defined.
Notation "r//2" := half.

(* To signed integer *)
Definition toSZ (x: F q) := let z := F.to_Z x in
  if z >=? r//2 + 1 then (z-q)%Z else z.

Lemma toSZ_add: forall a b,
  Z.abs (toSZ a) + Z.abs (toSZ b) < r//2 ->
  toSZ (a + b) = (toSZ a + toSZ b)%Z.
Proof. Admitted.

Lemma toSZ_mult: forall a b,
  Z.abs (toSZ a) * Z.abs (toSZ b) < r//2 ->
  toSZ (a * b) = (toSZ a * toSZ b)%Z.
Proof. Admitted.

Definition polynomial := list (F q).

(* polynomial addition *)
Fixpoint pairwise {A: Type} (op: A -> A -> A) (p q: list A) : list A :=
  match p, q with
  | nil, q => q
  | p, nil => p
  | (c :: p), (d :: q) => (op c d) :: pairwise op p q
  end.

Definition padd : polynomial -> polynomial -> polynomial := pairwise F.add.

(* polynomial multiplication *)
Fixpoint pmul (xs ys: polynomial) : polynomial :=
  match xs with
  | nil => nil
  | (x :: xs') => padd (List.map (fun y => x * y) ys) (0 :: (pmul xs' ys))
  end.

(* polynomial evaluation *)
Fixpoint eval' (i: N) (cs: polynomial) (x: F q) : F q :=
  match cs with
  | nil => 0
  | c::cs' => c * x^i + eval' (i+1)%N cs' x
  end.

Definition eval := eval' 0.

Definition toPoly {m} (xs: tuple (F q) m) : polynomial := to_list m xs.

Lemma toPoly_length: forall {m} (xs: tuple (F q) m),
  length (toPoly xs) = m.
Admitted.
  

Definition coeff (i: nat) (cs: polynomial) := nth i cs 0.

Lemma coeff_nth: forall {m} (xs: tuple (F q) m) i,
  coeff i (toPoly xs) = nth_default 0 i xs.
Admitted.

Lemma eval_ppadd: forall c d x, eval (padd c d) x = eval c x + eval d x.
Admitted.

Lemma eval_ppmul: forall c d x, eval (pmul c d) x = eval c x * eval d x.
Admitted.

Lemma firstn_toPoly: forall m (x: tuple (F q) m),
  firstn m (toPoly x) = toPoly x.
Admitted.

Lemma eval_app: forall cs0 cs1 x,
  eval (cs0 ++ cs1) x = eval cs0 x + eval' (N.of_nat (length cs0)) cs1 x.
Admitted.

Notation "x [ i ]" := (Tuple.nth_default 0 i x).

Definition init_poly ka kb (poly: tuple (F q) (ka+ kb -1)) {m} (x: tuple (F q) m) _C := 
  iter (ka+kb-1) (fun i _C => _C /\
        (* inner loop: poly[i] = \sum_{j=0...ka+kb-1} x[j] * i ** j *)
        poly[i] = iter m (fun j poly_i =>
          (poly_i + x[j] * (F.of_nat q i)^(N.of_nat j))) 0)
      _C.

Lemma exists_last': forall {A: Type} (l: list A),
  l <> nil ->
  exists l' a, l = l' ++ a::nil.
Proof.
  intros.
  pose proof exists_last as H_last.
  specialize (H_last _ _ H). destruct H_last as [l' H_last]. destruct H_last as [a H_last].
  eexists. eexists. eauto.
Qed.

Lemma init_poly_correct: forall {ka kb} (poly: tuple (F q) (ka+ kb -1)) {m} (x: tuple (F q) m) _C,
  init_poly ka kb poly x _C ->
  (_C (* output constraint preserves _C *)
  /\ forall i, (i < ka + kb -1)%nat -> poly [i] = eval (toPoly x) (F.of_nat q i)).
Proof.
  unfold init_poly.
  intros ka kb poly m x _C0.
  remember (ka+kb-1)%nat as outer_bound.
  (* invariant for the inner loop *)
  remember (fun (i : nat) (_C : Prop) =>
  _C /\
  poly [i] =
  iter m
    (fun (j : nat) (poly_i : F q) =>
     poly_i + x [j] * F.of_nat q i ^ N.of_nat j) 0)
  as outer.
  
  pose (Inv_outer := fun i _C =>
    _C -> _C0 /\ forall i0, (i0 < i)%nat -> poly [i0] = eval (toPoly x) (F.of_nat q i0)).
  assert (Hinv_outer: Inv_outer outer_bound (iter outer_bound outer _C0)). {
    apply iter_inv; unfold Inv_outer.
    (* outer: base case *)
    - intuition idtac. lia.
    (* outer: inductive case *)
    - intros i0 C_prev Hprev H_i0_i.
      rewrite Heqouter.
      intros H_C_prev.
      intuition idtac.
      destruct (dec (i1 < i0)%nat).
      + apply H3. lia.
      + assert (i1 = i0) by lia. subst.
        pose (Inv_inner := fun j acc => acc = eval (firstn j (toPoly x)) (F.of_nat q i0)).
        remember (fun (j : nat) (poly_i : F q) => poly_i + x [j] * F.of_nat q i0 ^ N.of_nat j)
          as inner.
        assert (Hinv_inner: Inv_inner m (iter m inner 0)). {
          apply iter_inv; unfold Inv_inner.
          - intuition idtac.
          - intros j acc Hacc H_j_m. subst.
            destruct m.
            + lia.
            + assert (H_toPoly_len: length (toPoly x) = S m) by apply toPoly_length.
              assert (H_split: exists cs c ds, toPoly x = cs ++ (c::nil) ++ ds /\ length cs = j). {
                remember (toPoly x) as xs.
                assert (exists cs ds, xs = cs ++ ds /\ length cs = S j). {
                  exists (firstn (S j) xs). exists (skipn (S j) xs).
                  rewrite firstn_skipn. split; auto. apply firstn_length_le. lia.
                }
                destruct H4 as [cs H4]. destruct H4 as [ds H4]. destruct H4.
                assert (H_cs_nonil: cs <> nil). unfold not. intros. subst. simpl in *. lia.
                apply exists_last' in H_cs_nonil.
                destruct H_cs_nonil as [cs' Hcs]. destruct Hcs as [c Hcs].
                exists cs'. exists c. exists ds. rewrite H4. rewrite Hcs. split.
                - rewrite app_assoc. reflexivity.
                - assert (length cs = length (cs' ++ c :: nil)) by (subst; auto).
                  rewrite app_length in H6. simpl in H6. lia.
              }
              destruct H_split as [cs H_split]. destruct H_split as [c H_split]. destruct H_split as [cs' H_split]. destruct H_split as [H_split H_cs_len].
              rewrite H_split.
              rewrite firstn_app. replace (j-length cs)%nat with 0%nat by lia. rewrite firstn_O. rewrite app_nil_r.
              replace (firstn j cs) with (firstn (length cs) cs) by (rewrite <- H_cs_len; reflexivity).
              rewrite firstn_all.
              replace (cs ++ (c :: nil) ++ cs') with ((cs ++ (c :: nil)) ++ cs') by (rewrite app_assoc; reflexivity).
              replace (S j) with (length (cs ++ c :: nil)) by (rewrite app_length; simpl; lia).
              rewrite firstn_app. rewrite firstn_all.
              replace (length (cs ++ c :: nil) - length (cs ++ c :: nil))%nat with 0%nat by lia.
              rewrite firstn_O. rewrite app_nil_r. rewrite eval_app. cbn [eval'].
              replace c with (x [j]). subst. replace (length cs + 0)%nat with (length cs) by lia.
              fqsatz.
              rewrite <- coeff_nth. rewrite H_split.
              replace (cs ++ (c :: nil) ++ cs') with ((cs ++ (c :: nil)) ++ cs') by (rewrite app_assoc; reflexivity).
              unfold coeff. rewrite app_nth1. rewrite app_nth2. subst. replace (length cs - length cs)%nat with 0%nat by lia. reflexivity.
              lia.
              rewrite app_length. simpl. lia.
        }
        unfold Inv_inner in Hinv_inner.
        rewrite firstn_toPoly in *. 
        rewrite H0. rewrite Hinv_inner. reflexivity.
  }
  intros.
  unfold Inv_outer in Hinv_outer.
  intuition idtac.
Admitted.

Definition BigMultNoCarry_cons
  ka kb
  (a: tuple (F q) ka)
  (b: tuple (F q) kb)
  (out: tuple (F q) (ka + kb - 1))
  (a_poly: tuple (F q) (ka+ kb -1))
  (b_poly: tuple (F q) (ka+ kb -1))
  (out_poly: tuple (F q) (ka+ kb -1)) 
  :=
  let _C := True in
  let _C :=
    init_poly ka kb out_poly out _C in
  let _C :=
    init_poly ka kb a_poly a _C in
  let _C :=
    init_poly ka kb b_poly b _C in
  let _C :=
    iter (ka+kb-1) (fun i _C => _C /\ 
      out_poly[i] = a_poly[i] * b_poly[i]) _C in
  _C.

Definition BigMultNoCarry
  ka kb
  (a: tuple (F q) ka)
  (b: tuple (F q) kb)
  (out: tuple (F q) (ka + kb - 1)) :=
  exists a_poly b_poly out_poly, 
    BigMultNoCarry_cons ka kb a b out a_poly b_poly out_poly.

(* Partial spec *)
Definition BigMultNoCarry_spec
  ka kb
  (a: tuple (F q) ka)
  (b: tuple (F q) kb)
  (out: tuple (F q) (ka + kb -1)) :=
  to_list (ka + kb -1) out = pmul (to_list ka a) (to_list kb b).

(* Complete spec *)
(* to_list (ka + kb -1) out = mult (to_list ka (map toSZ a)) (to_list kb (map toSZ b)). *)

Fixpoint range (n: nat) : list nat :=
  match n with
  | O => nil
  | S n' => n' :: range n'
  end.
Lemma range_range: forall n i, In i (range n) -> (i < n)%nat.
Proof.
  induction n; simpl; intros; destruct H.
  - subst. lia.
  - assert (i < n)%nat by auto. lia.
Qed.
Lemma range_nodup: forall n, NoDup (range n).
Proof.
  induction n; simpl; constructor; auto.
  unfold not. intros. apply range_range in H. lia.
Qed.
Lemma range_elem: forall n i, (i < n)%nat -> In i (range n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (dec (i < n)%nat).
    + right. apply IHn. lia.
    + left. lia.
Qed.
Lemma range_P: forall P n,
  (forall i, (i < n)%nat -> P i) ->
  (forall i, In i (range n) -> P i).
Proof.
  intros. apply X. apply range_range. auto.
Qed.
Lemma range_length: forall n, length (range n) = n.
Proof. induction n; simpl; auto. Qed.
Lemma range_map_preimage {A: Type}: forall n (f: nat -> A) x,
  In x (List.map f (range n)) ->
  exists i, (i < n)%nat /\ f i = x.
Proof.
  induction n; simpl; intros; destruct H.
  - subst. exists n. split; (auto || lia).
  - apply IHn in H. inversion H. intuition idtac. exists x0. split; (auto || lia).
Qed.

Require Import FinFun.

Lemma Fof_Z_inj: forall x y, 0 <= x < q -> 0 <= y < q -> F.of_Z q x = F.of_Z q y -> x = y.
Proof.
  intros.
  apply F.eq_of_Z_iff in H1.
  rewrite Zmod_small in H1; rewrite Zmod_small in H1; lia.
Qed.

Lemma Fof_nat_injective: forall x y, Z.of_nat x < q -> Z.of_nat y < q -> F.of_nat q x = F.of_nat q y -> x = y.
Proof.
  intros. apply Nat2Z.inj. unfold F.of_nat in *. apply Fof_Z_inj; (lia || auto).
Qed.

Definition Injective_restrict {A B: Type} (f: A -> B) P :=
  forall x y, P x -> P y -> f x = f y -> x = y.

Lemma Injective_map_NoDup_restrict:
  forall (A B : Type) (f : A -> B) (l : list A) P,
  Injective_restrict f P -> (forall x, In x l -> P x) -> NoDup l -> NoDup (List.map f l).
Proof.
  induction l; simpl; intros; constructor.
  - unfold not. intros. apply in_map_iff in H1. destruct H1. intuition.
    apply H in H2.
    assert (~ (In a l)). replace l with (nil ++ l) by reflexivity. apply NoDup_remove_2. simpl. auto.
    subst. auto. apply X. auto.
    apply X. left. auto.
  - eapply IHl; eauto. inversion H0. auto.
Qed.



Theorem interpolant_unique: forall (a b: polynomial) n (X: list (F q)),
(* FIXME: degree at most n *)
(* degree_leq a n -> *)
(* degree_leq b n -> *)
  (length X > n)%nat ->
  NoDup X ->
  (forall x, In x X -> eval a x = eval b x) ->
  a = b.
Admitted.

Print Injective_map_NoDup.




Theorem BigMultNoCarry_correct ka kb a b out:
  BigMultNoCarry ka kb a b out -> BigMultNoCarry_spec ka kb a b out.
Proof.
  unfold BigMultNoCarry, BigMultNoCarry_spec, BigMultNoCarry_cons.
  intros. destruct H as [a_poly H]. destruct H as [b_poly H]. destruct H as [out_poly H].
  remember (init_poly ka kb out_poly out True) as init_out.
  pose proof (init_poly_correct out_poly out True) as H_out.
  remember (init_poly ka kb a_poly a init_out) as init_a.
  pose proof (init_poly_correct a_poly a init_out) as H_a.
  remember (init_poly ka kb b_poly b init_a) as init_b.
  pose proof (init_poly_correct b_poly b init_a) as H_b.

  remember (fun (i : nat) (_C : Prop) =>
    _C /\ out_poly [i] = a_poly [i] * b_poly [i]) as f.

  pose (Inv := fun (i: nat) _C => _C ->
    init_b /\
    forall i0, (i0 < i)%nat -> out_poly [i0] = a_poly [i0] * b_poly [i0]).

  assert (Hind: forall i, Inv i (iter i f init_b)). {
    intros i. unfold Inv; apply iter_inv.
    - intuition idtac. lia.
    - intros i0. intros.
      rewrite Heqf in H2.
      intuition idtac.
      destruct (dec (i1 < i0)%nat). auto.
      assert (i1 = i0) by lia. subst. auto.
  }
  (* FIXME: range check *)
  assert (H_ka_kb: (ka + kb - 1 < Pos.to_nat q)%nat) by admit.

  unfold Inv in Hind.
  specialize (Hind (ka + kb -1)%nat).
  subst. intuition idtac.
  assert (H_evals: forall i, (i < ka + kb - 1)%nat -> eval (toPoly out) (F.of_nat q i) = eval (toPoly a) (F.of_nat q i) * eval (toPoly b) (F.of_nat q i)). {
    intros.
    rewrite <- H4, <- H6, <- H8, H2 by lia. reflexivity.
  }
  assert (H_poly: toPoly out = pmul (toPoly a) (toPoly b)). {
    erewrite interpolant_unique with (a:=toPoly out) (b:=pmul (toPoly a) (toPoly b)) (n:=(ka+kb-2)%nat) (X:=List.map (F.of_nat _) (range (ka+kb-1))).
    reflexivity.
    rewrite map_length, range_length.
    (* FIXME: range check *)
    assert ((ka+kb>=2)%nat) by admit. lia.
    pose proof Fof_nat_injective.

    eapply Injective_map_NoDup_restrict.
    Focus 2. intros. apply range_range. apply H9.
    unfold Injective_restrict. intros. apply Fof_nat_injective; (lia || auto).
    (* FIXME: range check *)
    assert (Z.of_nat (ka+kb-1)%nat < q) by admit.
    apply range_nodup.
    intros.
    rewrite eval_ppmul.
    assert (H_xi: exists i, x = F.of_nat _ i /\ (i < ka + kb -1)%nat). {
      apply range_map_preimage in H0. destruct H0. exists x0. intuition idtac. subst. reflexivity.
    }
    destruct H_xi as [i H_xi].
    intuition idtac.
    subst.
    apply H_evals. lia.
  }
  apply H_poly.
Admitted.













(* PrimeReduce *)
(* source: https://github.com/yi-sun/circom-pairing/blob/743d761f07254ea6407d29ba05f29886cfd14aec/circuits/bigint.circom#L786 *)

(* source: https://github.com/yi-sun/circom-pairing/blob/743d761f07254ea6407d29ba05f29886cfd14aec/circuits/bigint_func.circom *)

Definition F_mod {m} (a b: F m) :=
  F.of_Z m ((F.to_Z a) mod (F.to_Z b))%Z.

(* // a is a n-bit scalar
// b has k registers
function long_scalar_mult(n, k, a, b) {
    var out[50];
    for (var i = 0; i < 50; i++) {
        out[i] = 0;
    }
    for (var i = 0; i < k; i++) {
        var temp = out[i] + (a * b[i]);
        out[i] = temp % (1 << n);
        out[i + 1] = out[i + 1] + temp \ (1 << n);
    }
    return out;
} *)
Definition long_scalar_mult
n k a (_b : tuple (F q) k) (out : tuple (F q) 50) :=
let _C := True in
let '( _C) :=
  (* loop: construct out[i] *)
  iter 50 (fun i '( _C) => (_C /\ out[i] = 0))
    ( _C) in
let '( _C) :=
  iter k (fun i _C => _C /\ 
              out[i] = F_mod (out[i] + (a * _b[i]))  (2^n) /\
              out[i + 1] = out[i + 1] + F.div (out[i] + (a * _b[i])) (2^n))
    _C in
  _C
.

(* // n bits per register
// a has k registers
// b has k registers
// a >= b
function long_sub(n, k, a, b) {
    var diff[50];
    var borrow[50];
    for (var i = 0; i < k; i++) {
        if (i == 0) {
           if (a[i] >= b[i]) {
               diff[i] = a[i] - b[i];
               borrow[i] = 0;
            } else {
               diff[i] = a[i] - b[i] + (1 << n);
               borrow[i] = 1;
            }
        } else {
            if (a[i] >= b[i] + borrow[i - 1]) {
               diff[i] = a[i] - b[i] - borrow[i - 1];
               borrow[i] = 0;
            } else {
               diff[i] = (1 << n) + a[i] - b[i] - borrow[i - 1];
               borrow[i] = 1;
            }
        }
    }
    return diff;
} *)
Definition long_sub (n : nat) (_k : nat) (a b : tuple (F q) _k) : tuple (F q) 50.
Admitted.

(* // 1 if true, 0 if false
function long_gt(n, k, a, b) {
    for (var i = k - 1; i >= 0; i--) {
        if (a[i] > b[i]) {
            return 1;
        }
        if (a[i] < b[i]) {
            return 0;
        }
    }
    return 0;
} *)
Definition long_gt (n : nat) (_k : nat) (a b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + 1 registers
// b has k registers
// assumes leading digit of b is at least 2^(n - 1)
// 0 <= a < (2**n) * b
function short_div_norm(n, k, a, b) {
   var qhat = (a[k] * (1 << n) + a[k - 1]) \ b[k - 1];
   if (qhat > (1 << n) - 1) {
      qhat = (1 << n) - 1;
   }

   var mult[50] = long_scalar_mult(n, k, qhat, b);
   if (long_gt(n, k + 1, mult, a) == 1) {
      mult = long_sub(n, k + 1, mult, b);
      if (long_gt(n, k + 1, mult, a) == 1) {
         return qhat - 2;
      } else {
         return qhat - 1;
      }
   } else {
       return qhat;
   }
} *)
Definition short_div_norm (n : nat) (_k : nat) (a : tuple (F q) (_k + 1)) (b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + 1 registers
// b has k registers
// assumes leading digit of b is non-zero
// 0 <= a < b * 2^n
function short_div(n, k, a, b) {
    var scale = (1 << n) \ (1 + b[k - 1]);
    // k + 2 registers now
    var norm_a[50] = long_scalar_mult(n, k + 1, scale, a);
    // k + 1 registers now
    var norm_b[50] = long_scalar_mult(n, k, scale, b);
    
    var ret;
    if (norm_b[k] != 0) {
	ret = short_div_norm(n, k + 1, norm_a, norm_b);
    } else {
	ret = short_div_norm(n, k, norm_a, norm_b);
    }
    return ret;
}*)
Definition short_div (n : nat) (_k : nat) (a : tuple (F q) (_k + 1)) (b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + m registers
// b has k registers
// out[0] has length m + 1 -- quotient
// out[1] has length k -- remainder
// implements algorithm of https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf
// b[k-1] must be nonzero! *)
Definition long_div2 (n : nat) (_k m : nat) (a : tuple (F q) (_k + m)) (b : tuple (F q) _k) : tuple (F q) 2.
Admitted.

Definition long_div := long_div2.

(* function SplitThreeFn(in, n, m, k) {
    return [in % (1 << n), (in \ (1 << n)) % (1 << m), (in \ (1 << n + m)) % (1 << k)];
} *)

Definition SplitThreeFn _in n m k (out : tuple (F q) 3):=
  out[0] = F_mod _in (2^n) /\
  out[1] = F_mod (F.div _in (2^n)) (2^m) /\
  out[2] = F_mod (F.div _in (2^n + (F.of_Z q m))) (2^k).
   

(* function SplitFn(in, n, m) {
    return [in % (1 << n), (in \ (1 << n)) % (1 << m)];
} *)
Definition SplitFn _in n m (out : tuple (F q) 2):=
  out[0] = F_mod _in (2^n) /\
  out[1] = F_mod (F.div _in (2^n)) (2^m).

(* // n bits per register
// a and b both have k registers
// out[0] has length 2 * k
// adapted from BigMulShortLong and LongToShortNoEndCarry witness computation *)
Definition prod (n : nat) (_k : nat) (a : tuple (F q) _k) (b : tuple (F q) _k) : tuple (F q) 50.
Admitted.

(* function prod_mod(n, k, a, b, p) {
    var prod[50] = prod(n,k,a,b);
    var temp[2][50] = long_div(n,k,prod,p);
    return temp[1];
} *)
Definition prod_mod (n : nat) (_k : nat) (a : tuple (F q) _k) (b p : tuple (F q) _k) : tuple (F q) 50.
Admitted.

Definition repr_binary n x m ws :=
  length ws = m /\
  (forall i, (i < m)%nat -> binary q (nth i ws 0)) /\
  x = repr_to_le n ws.

Hypothesis prod_mod_correct:
  forall (n: nat) k (a b p: tuple (F q) k),
  repr_binary n (F_mod ((repr_to_le n (to_list k a)) * (repr_to_le n (to_list k b))) (repr_to_le n (to_list k p))) 50
  (to_list 50 (prod_mod n k a b p)).

(* // n bits per register
// a has k registers
// p has k registers
// e has k registers
// k * n <= 500
// p is a prime
// computes a^e mod p *)
Definition mod_exp {_k1 _k2 _k3} (n: nat) (_k: nat) (a : tuple (F q) _k1) (p : tuple (F q) _k2) (e : tuple (F q) _k3) : tuple (F q) 50. Admitted.

Hypothesis mod_exp_correct:
  forall (n: nat) k (a p e : tuple (F q) k),
  repr_binary n (F_mod ((repr_to_le n (to_list k a)) ^ (F.to_N (repr_to_le n (to_list k e))))
                        (repr_to_le n (to_list k p))) 50
  (to_list 50 (mod_exp n k a p e)).

Definition PrimeReduce_cons
  n k m p m_out
  (_in : tuple (F q) (m+k))
  (_out : tuple (F q) k)
  (two : tuple (F q) k)
  (e_1 : tuple (F q) k)
  (e_2 : tuple (F q) k)
  (r : tuple (tuple (F q) 50) m)
   :=
  let _C := two[0] = 2 /\ e_1[0] = (F.of_nat q n) /\ e_2[0] = (F.of_nat q k) in
  let _C :=
    iter' (Nat.sub k 1) k (fun i _C => _C /\ 
      two[i] = 0 /\ e_1[i] = 0 /\ e_2[i] = 0) _C in
  let pow2n := mod_exp n k two p e_1 in
  let pow2nk := mod_exp n k pow2n p e_2 in
  _C
  .