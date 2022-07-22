Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Setoid.
Require Import Coq.Lists.List.
Require Import Lia.
Open Scope signature_scope.

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
Require Import Coq.Lists.ListSet.
Require Import Coq.PArith.BinPosDef.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.


Section Polynomial.

Context {F eq zero one opp add sub mul inv div}
        {fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
        {eq_dec:DecidableRel eq}.

Local Infix "==" := eq. 
(* Local Notation "a <> b" := (not (a = b)). *)
Local Notation "a <> b" := (not (a = b)) : type_scope.
Local Infix "==" := eq : type_scope. 
Local Notation "0" := zero.  Local Notation "1" := one.
Local Infix "+" := add. Local Infix "*" := mul.
Local Infix "-" := sub. Local Infix "/" := div.


(* https://coq-club.inria.narkive.com/cL8AtXMS/how-could-i-do-polynomials-in-coq *)

Definition polynomial := list F.

Inductive empty_poly : polynomial -> Prop :=
| empty_poly_nil : empty_poly nil
| empty_poly_cons : forall p, empty_poly p -> empty_poly (0::p).

Definition p0 : polynomial := nil.

Reserved Notation "a ~ b" (at level 20).
Inductive eq_poly : polynomial -> polynomial -> Prop :=
| eq_poly_empty : forall p1 p2, empty_poly p1 -> empty_poly p2 -> eq_poly p1 p2
| eq_poly_cons : forall n p1 p2, eq_poly p1 p2 -> eq_poly (n::p1) (n::p2).
Notation "a ~ b" := (eq_poly a b) (at level 20).

Hint Constructors eq_poly.
Hint Constructors empty_poly.

Instance eq_poly_equivalence : Equivalence eq_poly.
(* proof that eq_poly is reflexive, symmetric, and transitive *)
Admitted.

Fixpoint peval (x: F) (p: polynomial) :=
  match p with
  | nil => 0
  | (a::b) => a + x * peval x b
  end.

Lemma peval_empty_zero (p: polynomial): 
  empty_poly p -> forall x, peval x p == 0.
Proof.
  intros. induction H; simpl.
  - fsatz.
  - rewrite IHempty_poly; fsatz.
Qed.

(* proof that peval depends only upon the equivalence class of the
* polynomial, not its concrete representation as a list *)
(* Instance peval_Proper: forall x, Proper (eq_poly ==> eq) (peval x).
Proof.
  intros; unfold Proper; unfold respectful; intros.
  induction H.
  rewrite peval_empty_zero; auto.
  rewrite peval_empty_zero; auto. fsatz.
  simpl; rewrite IHeq_poly; fsatz.
Defined. *)

Instance peval_Proper: Proper (eq ==> eq_poly ==> eq) peval.
Proof.
  intros; unfold Proper; unfold respectful; intros.
  induction H0.
  repeat rewrite peval_empty_zero; auto. reflexivity.
  simpl. rewrite IHeq_poly. fsatz.
Defined.

Definition peval_then (op: F -> F -> F) (x: F) (p1 p2: polynomial) : F :=
  op (peval x p1) (peval x p2).

Definition peval_then_add := peval_then add.
Definition peval_then_sub := peval_then sub.
Definition peval_then_mul := peval_then mul.
Definition peval_then_div := peval_then div.

Instance peval_then_add_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_add.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_add, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_sub_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_sub.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_sub, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_mul_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_mul.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_mul, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_div_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_div.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_div, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.


Definition coeff (i: nat) (p: polynomial) : F := nth i p 0.

Notation "p [ i ]" := (coeff i p).

Lemma nth_nil: forall {A: Type} i (d: A), nth i nil d = d.
Proof.
  induction i; simpl; intros; reflexivity.
Qed.

Lemma coeff_empty: forall p, empty_poly p -> forall i, p[i] == 0.
Proof.
  intros p H. unfold coeff. induction H; intros.
  - rewrite nth_nil. fsatz.
  - destruct i.
    + reflexivity.
    + cbn. apply IHempty_poly.
Qed.

Lemma coeff_equal: forall p q, p ~ q -> forall i, p[i] == q[i].
Proof.
  intros p q H. induction H; simpl; intros.
  - repeat rewrite coeff_empty by auto. reflexivity.
  - destruct i.
    + reflexivity.
    + apply IHeq_poly.
Qed.

Definition degree := option nat.
Definition mk_degree (n: nat) := Some n.
Fixpoint deg (p: polynomial) : degree := 
  match p with
  | nil => None
  | a::p' =>
    match deg p' with
    | Some d => Some (S d)
    | None => if (dec (a == 0)) then None else Some O
    end
  end.

Definition degree_leqb d1 d2 :=
  match d1, d2 with
  | Some d1, Some d2 => (d1 <=? d2)%nat
  | None, _ => true
  | _, None => false
  end.
Definition degree_leq d1 d2 : Prop := degree_leqb d1 d2 = true.

Definition degree_max d1 d2 :=
  match d1, d2 with
  | None, _ => d2
  | _, None => d1
  | Some d1, Some d2 => Some (max d1 d2)
  end.

Definition degree_min d1 d2 :=
  match d1, d2 with
  | None, _ => d1
  | _, None => d2
  | Some d1, Some d2 => Some (min d1 d2)
  end.

Definition degree_add d1 d2 :=
  match d1, d2 with
  | None, _ => d2
  | _, None => d1
  | Some d1, Some d2 => Some (d1 + d2)%nat
  end.

Require Import Coq.Lists.List.
Definition uncurry {A B C: Type} (f: A -> B -> C) := fun xy => f (fst xy) (snd xy).
Fixpoint padd (p q: polynomial) : polynomial := 
  match p, q with
  | nil, _ => q
  | _, nil => p
  | a :: p', b :: q' => (a+b) :: padd p' q'
  end.
Notation "p p+ q" := (padd p q) (at level 50).

Definition pscale (k: F) : polynomial -> polynomial := map (fun a => k * a).

Lemma peval_padd: forall (p q: polynomial) (x: F),
  peval x (p p+ q) == peval x p + peval x q.
Proof.
  induction p; simpl; intros.
  - fsatz.
  - destruct q; simpl.
    + fsatz.
    + rewrite IHp. fsatz.
Qed.

Lemma peval_pscale: forall p k x,
  peval x (pscale k p) == k * peval x p.
Proof.
  induction p; simpl; intros.
  - fsatz.
  - rewrite IHp. fsatz.
Qed.

Instance padd_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) padd.
Admitted.

Instance pscale_Proper:
  Proper (eq ==> eq_poly ==> eq_poly) pscale.
Admitted.

Definition psub (p q: polynomial) : polynomial := padd p (pscale (opp 1) q).
Notation "p p- q" := (psub p q) (at level 50).

Lemma peval_psub: forall (p q: polynomial) (x: F),
  peval x (p p- q) = peval x p - peval x q.
Admitted.

Fixpoint pmul (p q: polynomial) : polynomial :=
  match p with
  | nil => nil
  | (a :: p') => padd (List.map (fun b => a * b) q) (0 :: (pmul p' q))
  end.
Notation "p p* q" := (pmul p q) (at level 50).

Lemma peval_pmul: forall (p q: polynomial) (x: F),
  peval x (p p* q) = peval x p * peval x q.
Admitted.

Instance pmul_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) pmul.
Admitted.


Definition root x p := peval x p == 0.

Definition linear a := (opp a :: 1 :: nil).

Lemma deg_padd: forall p q,
  degree_leq (deg (p p+ q)) (degree_max (deg p) (deg q)).
Admitted.

Lemma deg_pmul: forall p q,
  degree_leq (deg (p p* q)) (degree_add (deg p) (deg q)).
Admitted.

Lemma deg_pscale: forall p k,
  degree_leq (deg (pscale k p)) (deg p).
Admitted.

Lemma deg_psub: forall p q,
  degree_leq (deg (p p- q)) (degree_max (deg p) (deg q)).
Admitted.

Lemma psub_0: forall p q,
  (p p- q) ~ p0 <-> p ~ q.
Admitted.

Lemma eq_poly_decidable: forall p q,
  p ~ q \/ ~ (p ~ q).
Admitted.

Lemma psub_0_neg: forall p q,
  ~((p p- q) ~ p0) <-> ~(p ~ q).
Admitted.

Lemma not0_implies_positive_deg: forall p,
  ~ (p ~ p0) -> exists n, deg p = Some n /\ (n > 0)%nat.
Admitted.

Lemma deg_d_has_most_d_roots: forall p d,
  deg p = Some d ->
  (d > 0)%nat ->
  exists X, length X = d /\ forall x, root x p -> In x X.
Admitted.


Lemma pdiv: forall a b,
  ~ (a ~ p0) ->
  exists q r, a ~ ((q p* b) p+ r) /\
  (r ~ p0 \/ degree_leq (deg r) (deg b)).
Admitted.

Lemma factor_root: forall p a, root a p ->
  exists q, p ~ (linear a p* q).
Admitted.

Lemma In_pigeon_hole: forall {A: Type} (X X': list A),
  (length X > length X')%nat ->
  (forall x, In x X -> In x X') ->
  False.
Proof.
Admitted.

Lemma unique_interpolant: forall p q n X,
  deg p = Some n ->
  deg q = Some n ->
  NoDup X ->
  length X = S n ->
  (forall x, In x X -> peval x p == peval x q) ->
  p ~ q.
Proof.
  (* Proof: https://inst.eecs.berkeley.edu/~cs70/fa14/notes/n7.pdf *)
  intros.
  destruct (eq_poly_decidable p q).
  trivial.
  exfalso.
  apply psub_0_neg in H4.
  apply not0_implies_positive_deg in H4.
  destruct H4 as [d [H_deg_r H_x] ].
  pose proof (deg_psub p q) as H_deg_r_leq. rewrite H, H0 in H_deg_r_leq.
  rewrite H_deg_r in H_deg_r_leq. simpl in H_deg_r_leq.
  assert (H_d_n: (d <= n)%nat). apply leb_complete in H_deg_r_leq. lia.
  replace (degree_max (Some n) (Some n)) with (Some n) in H_deg_r_leq by (simpl; f_equal; lia).
  specialize (deg_d_has_most_d_roots _ _ H_deg_r H_x).
  intro HX. destruct HX as [X' [H_len_X H_X] ].
  eapply In_pigeon_hole with (X := X ) (X' := X').
  lia.
  intros. apply H_X. unfold root. rewrite peval_psub.
  apply H3 in H4. fsatz.
Qed.

End Polynomial.