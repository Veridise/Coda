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
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field Crypto.Algebra.Ring.
Require Import Coq.Lists.ListSet.
Require Import Crypto.Util.Decidable Crypto.Util.Notations Crypto.Util.Tuple.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Util DSL.


Module Polynomial.

Section Polynomial.

Context {F eq zero one opp add sub mul inv div}
        `{fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
        `{eq_dec:DecidableRel eq}.

Local Infix "==" := eq. 
Local Notation "a <> b" := (not (a == b)).
Local Infix "==" := eq : type_scope. 
Local Notation "a <> b" := (not (a == b)) : type_scope.
Local Notation "0" := zero.  Local Notation "1" := one.
Local Infix "+" := add. Local Infix "*" := mul.
Local Infix "-" := sub. Local Infix "/" := div.
(* Local Infix "^" := pow. *)

Ltac invert H := inversion H; subst; clear H.


(* Formalization due to 
 * https://coq-club.inria.narkive.com/cL8AtXMS/how-could-i-do-polynomials-in-coq *)

Definition polynomial := list F.

Inductive empty_poly : polynomial -> Prop :=
| empty_poly_nil : empty_poly nil
| empty_poly_cons : forall f x, x == 0 -> empty_poly f -> empty_poly (x::f).

Notation "0p" := (nil : polynomial).

(* A [polynomial] with trailing zeros is equivalent to one without. *)
Reserved Notation "a ~ b" (at level 20).
Inductive eq_poly : polynomial -> polynomial -> Prop :=
| eq_poly_empty : forall f g, empty_poly f -> empty_poly g -> eq_poly f g
| eq_poly_cons : forall x y f g, eq_poly f g -> x == y -> eq_poly (x::f) (y::g).
Notation "a ~ b" := (eq_poly a b) (at level 20).

Hint Constructors empty_poly : core.
Hint Constructors eq_poly : core.

Hint Extern 10 (_ == _) => fsatz : core.
Hint Extern 10 (?A ~ ?A) => reflexivity : core.
Hint Extern 10 (nil ~ ?A) => symmetry : core.

Lemma eq_poly_empty_imp: forall f g, f ~ g -> empty_poly g -> empty_poly f.
Proof.
  intros f g H.
  induction H; intro; auto.
  invert H1. auto.
Qed.

Global Instance eq_poly_equivalence : Equivalence eq_poly.
Proof.
  constructor.
  (* reflexive *)
  - intro. induction x; auto. 
  (* symmetric *)
  - intros x y H. 
    induction H.
    + apply eq_poly_empty;auto.
    + apply eq_poly_cons;auto.
  (* transitive *)
    - intros x y z H1 H2. revert H2. revert z.
      induction H1; intros z H2.
    + apply eq_poly_empty; auto.
      induction H2; auto. invert H0.
      constructor; auto.
    + invert H2; auto.
      apply eq_poly_empty; auto. invert H0.
      constructor. fsatz. eapply eq_poly_empty_imp; eauto.
Qed.

(* Lemma 0p_empty: empty_poly 0p.
Proof. constructor. Qed. *)

Lemma empty_eq_0: forall f, empty_poly f -> f ~ 0p.
Proof. auto. Qed.

Global Instance cons_Proper: forall c, Proper (eq_poly ==> eq_poly) (cons c).
Proof.
  intros. unfold Proper, respectful.
  intros f g H.
  induction H; auto.
Qed.

Lemma eq_cons_invert: forall c d f g,
  (c :: f) ~ (d :: g) -> c == d /\ f ~ g.
Proof.
  intros. invert H.
  + invert H0. invert H1. split; auto.
  + split; auto.
Qed.

Ltac p0_to_empty := repeat match goal with
  | [ H: ?f ~ nil |- _] => apply eq_poly_empty_imp in H; auto
  | [ H: nil ~ _ |- _] => symmetry in H
  | [ _: _ |- nil ~ ?f ] => symmetry
  | [ _: _ |- ?f ~ nil ] => apply empty_eq_0; auto
  end.

Ltac empty_to_0p := repeat match goal with
  | [ H: empty_poly ?f |- _] => apply empty_eq_0 in H; auto 
  | [ _: _ |- empty_poly ?f ] => apply eq_poly_empty_imp with (g:= 0p); auto
  end.

Lemma cons_eq_nil: forall c f, (c == 0 /\ f ~ nil) <-> (c :: f) ~ nil.
Proof.
  intros. split; intros.
  destruct H. p0_to_empty.
  invert H. invert H0. auto.
Qed.

Lemma cons_eq_cons: forall c d f g, (c == d /\ f ~ g) <-> (c::f) ~ (d::g).
Proof.
  intros. split; intros.
  destruct H. apply eq_poly_cons; auto.
  invert H; auto. 
  invert H0; invert H1. auto.
Qed.

Hint Extern 10 ((_::_) ~ nil) => apply cons_eq_nil : core.
Hint Extern 10 => match goal with
  [ H: ((_::_) ~ nil) |- _ ] =>  apply cons_eq_nil in H; destruct H
  end: core.
Hint Extern 10 ((_::_) ~ (_::_)) => apply cons_eq_cons : core.
Hint Extern 10 => match goal with 
  [ H: (_::_) ~ (_::_) |- _ ] => apply cons_eq_cons in H; destruct H
  end : core.


(**************************************
 *            Evaluation              *
 **************************************)
Fixpoint peval x f : F :=
  match f with
  | nil => 0
  | c::f' => c + x * peval x f'
  end.

Notation "f ([ x ]) " := (peval x f) (at level 19).

Lemma peval_empty_zero (f: polynomial): 
  empty_poly f -> forall (x: F),  f([x]) == 0.
Proof.
  intros. induction H; simpl; auto.
Qed.

Lemma peval_nil: forall f x,
  f ~ 0p -> f ([x]) == 0.
Proof.
  intros. p0_to_empty. induction H; simpl; auto.
Qed.

(* 
(* accumulative evaluation *)
Fixpoint aeval' (i: nat) (x: F) (cs: polynomial) : F :=
  match cs with
  | nil => 0
  | c::cs' => c * x^i + eval' (S i) x cs'
  end.

Definition aeval := eval' 0.

Lemma peval *)


(**************************************
 *     Evaluation under context       *
 **************************************)

 (* proof that peval depends only upon the equivalence class of the
* polynomial, not its concrete representation as a list *)
(* Instance peval_r_Proper: forall x, Proper (eq_poly ==> eq) (peval x).
Proof.
  intros; unfold Proper; unfold respectful; intros.
  induction H.
  rewrite peval_empty_zero; auto.
  rewrite peval_empty_zero; auto.
  simpl; rewrite IHeq_poly; fsatz.
Defined. *)

Global Instance peval_Proper: Proper (eq ==> eq_poly ==> eq) peval.
Proof.
  intros x y Hxy f g Hfg.
  induction Hfg.
  - repeat rewrite peval_empty_zero; auto.
  - simpl. rewrite IHHfg. fsatz.
Defined.

(* Definition peval_then (op: F -> F -> F) (x: F) (f g: polynomial) : F :=
  op (f ([x])) (g ([x])).

Definition peval_then_add := peval_then add.
Definition peval_then_sub := peval_then sub.
Definition peval_then_mul := peval_then mul.
Definition peval_then_div := peval_then div. *)

(* Instance peval_then_add_Proper: forall x,
  Proper (eq_poly ==> eq_poly ==> eq) (peval_then_add x).
Proof.
  intros ? ? ? ? ? ? ?.
  unfold peval_then_add, peval_then.
  rewrite H. rewrite H0.
  reflexivity.
Defined.

Instance peval_then_mul_Proper: forall x,
  Proper (eq_poly ==> eq_poly ==> eq) (peval_then_mul x).
Proof.
  intros ? ? ? ? ? ? ?.
  unfold peval_then_mul, peval_then.
  rewrite H. rewrite H0.
  reflexivity.
Defined. *)

(* Instance peval_then_add_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_add.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_add, peval_then.
  rewrite H0. rewrite H1.
  Set Printing All.
  rewrite H.
  reflexivity.
Defined.

Instance peval_then_sub_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_sub.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_sub, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Defined.

Instance peval_then_mul_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_mul.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_mul, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Defined.

Instance peval_then_div_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_div.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_div, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Defined. *)


(**************************************
 *            Coefficient             *
 **************************************)

Definition coeff (i: nat) (f: polynomial) : F := nth i f 0.

Notation "f [ i ]" := (coeff i f).

Lemma nth_nil: forall {A: Type} i (d: A), nth i nil d = d.
Proof.
  intros. destruct i; reflexivity.
Qed.

Lemma coeff_nil: forall i, 0p [i] = 0.
Proof.
  intros. unfold coeff. apply nth_nil.
Qed.

Lemma coeff_empty: forall f, empty_poly f -> forall i, f[i] == 0.
Proof.
  intros f H. unfold coeff. induction H; intros.
  - rewrite nth_nil. fsatz.
  - destruct i.
    + fsatz.
    + cbn. apply IHempty_poly.
Qed.

Lemma eq_coeff_equal: forall f g, f ~ g -> forall i, f[i] == g[i].
Proof.
  intros f g H. induction H; simpl; intros.
  - repeat rewrite coeff_empty by auto. reflexivity.
  - destruct i.
    + fsatz.
    + apply IHeq_poly.
Qed.

Lemma coeff_all_0: forall g, (forall i, g[i] == 0) -> g ~ 0p.
Proof.
  unfold coeff; induction g; intros; auto.
  pose proof (H 0%nat).
  assert (g ~ nil). apply IHg. intros. specialize (H (S i)). auto.
  auto.
Qed.

Lemma coeff_equal_eq: forall f g,
  (forall i, f[i] == g[i] ) -> f ~ g.
Proof.
  induction f; intros g H.
  - symmetry. apply coeff_all_0. intros.
    rewrite <- H, coeff_nil. auto.
  - pose proof (H 0%nat). destruct g as [| d g].
    + assert (f ~ nil).
      { apply IHf. intros. specialize (H (S i)). rewrite coeff_nil in *. auto. }
      auto.
    + assert (f ~ g). 
      { apply IHf. intros. specialize (H (S i)). auto. }
      auto.
Qed.




(**************************************
 *            Reflection              *
 **************************************)

Fixpoint isnil f :=
  match f with
  | nil => true
  | c::f => if eq_dec c 0 then isnil f else false
  end.

Lemma isnil_sound: forall f, isnil f = true -> f ~ nil.
Proof.
  induction f; simpl; intros; auto.
  destruct (eq_dec a 0); auto.
  invert H.
Qed.

Lemma isnil_complete: forall f, f ~ nil -> isnil f = true.
Proof.
  intros f H. p0_to_empty. induction H; simpl; auto.
  destruct (eq_dec x 0); auto.
Qed.

Fixpoint eqb f g :=
  match f, g with
  | nil, _ => isnil g
  | _, nil => isnil f
  | c::f, d::g => if (eq_dec c d) then (eqb f g) else false
  end.

Lemma eqb_sound: forall f g, eqb f g = true -> f ~ g.
Proof.
  induction f as [| c f]; intros g; destruct g as [| d g]; simpl; auto;
  intros;
  repeat match goal with
  | [ H: context[eq_dec ?a ?b] |- _ ] => destruct (eq_dec a b)
  | [ H: isnil ?f = true |- _] => apply isnil_sound in H
  | [ H: false = true |- _] => invert H
  end; (auto || p0_to_empty).
Qed.

Lemma eqb_comm: forall f g, eqb f g = eqb g f.
Proof.
  induction f; intros; destruct g; simpl; auto.
  rewrite IHf. destruct (eq_dec a f0); destruct (eq_dec f0 a); auto; fsatz.
Qed.

Global Instance isnil_Proper: Proper (eq_poly ==> Logic.eq) (isnil).
Proof.
  intros f g H. induction H; simpl.
  - empty_to_0p. repeat rewrite isnil_complete; auto.
  - destruct (eq_dec x 0); destruct (eq_dec y 0); (auto || fsatz).
Defined.

Global Instance eqb_nil_Proper: forall f, f ~ nil -> Proper (eq_poly ==> Logic.eq) (eqb f).
Proof.
  intros f Hf.
  induction Hf; intros g1 g2 Hg.
Admitted.


Global Instance eqb_r_Proper: forall f, Proper (eq_poly ==> Logic.eq) (eqb f).
Proof.
  intros f g1 g2 Hg. generalize dependent f.
  induction Hg as [g1 g2 | c1 c2 g1 g2]; intros.
Admitted.

Global Instance eqb_Proper: Proper (eq_poly ==> eq_poly ==> Logic.eq) eqb.
Proof.
  intros f1 f2 Hf. induction Hf; intros g1 g2 Hg; induction Hg.
  - empty_to_0p.
    rewrite eqb_comm. rewrite H. rewrite eqb_comm.
    rewrite eqb_comm with (f:=g). rewrite H0.
    rewrite eqb_comm with (f:=g0). simpl.
    simpl.
Admitted.

Lemma eqb_complete: forall f g, f ~ g -> eqb f g = true.
Proof.
  intros. induction H.
  - empty_to_0p. rewrite H, H0. auto.
  - simpl. destruct (eq_dec x y); auto.
Qed.

Lemma eq_poly_decidable: forall f g,
  f ~ g \/ ~ (f ~ g).
Proof.
  intros.
  pose proof (eqb_sound f g).
  pose proof (eqb_complete f g).
  destruct (eqb f g); auto.
  right. intuition idtac. discriminate.
Qed.



(**************************************
 *         Tuple Conversion           *
 **************************************)

Definition toPoly {m} (xs: tuple F m) : polynomial := to_list m xs.
Lemma toPoly_length: forall {m} (xs: tuple F m),
  length (toPoly xs) = m.
Proof.
  intros. apply length_to_list.
Qed.


Lemma firstn_toPoly: forall m (x: tuple F m),
  firstn m (toPoly x) = toPoly x.
Proof.
  intros.
  apply firstn_all2. unfold toPoly.
  rewrite length_to_list; lia.
Qed.



(**************************************
 *  Tuple Conversion and Coefficient  *
 **************************************)

 Lemma coeff_nth: forall {m} (xs: tuple F m) i,
  coeff i (toPoly xs) = nth_default 0 i xs.
Proof.
  unfold coeff. unfold toPoly. intros.
  rewrite <- nth_default_eq. apply nth_default_to_list.
Qed.



(**************************************
 *             Arithmetic             *
 **************************************)

Fixpoint padd (f g: polynomial) : polynomial :=
  match f, g with
  | nil, _ => g
  | _, nil => f
  | (a :: f), (b :: g) => a + b :: padd f g
  end.
Notation "f p+ g" := (padd f g) (at level 18).

Definition pscale (k: F) : polynomial -> polynomial := List.map (fun a => k * a).
Notation "k p$ f" := (pscale k f) (at level 17).

Definition psub (f g: polynomial) : polynomial := padd f (pscale (opp 1) g).
Notation "f p- g" := (psub f g) (at level 18).

Fixpoint pmul (f g: polynomial) : polynomial :=
  match f with
  | nil => nil
  | (a :: f') => padd (pscale a g) (0 :: (pmul f' g))
  end.
Notation "f p* g" := (pmul f g) (at level 17).


Lemma padd_0_r: forall f g, g ~ 0p -> f p+ g ~ f.
Proof.
  induction f; intros; auto.
  invert H. invert H0.
  - simpl. auto.
  - simpl. apply eq_poly_cons; auto.
Qed.
  
Lemma padd_comm: forall f g,
  padd f g ~ padd g f.
Proof.
  induction f; simpl; intros.
  - rewrite padd_0_r; auto.
  - destruct g as [|b g]; simpl. auto.
    rewrite IHf. auto. 
Qed.

Local Instance padd_r_Proper: forall f,
  Proper (eq_poly ==> eq_poly) (padd f).
Proof.
  unfold Proper, respectful.
  intros f g1 g2 H. generalize dependent f.
  induction H as [g1 g2 H1 H2 | c d g1 g2 Hcd IH]; intros.
  - repeat rewrite padd_0_r; auto.
  - destruct f as [|a f]; simpl; auto.
Qed.

Global Instance padd_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) padd.
Proof.
  unfold Proper, respectful.
  intros f1 g1 H.
  induction H as [f1 g1 Hf Hg| c d f1 g1]; intros f2 g2 H2.
  - rewrite padd_comm. 
    rewrite padd_comm with (f := g1).
    repeat rewrite padd_0_r; auto.
  - invert H2.
    + repeat rewrite padd_0_r; auto.
    + simpl. rewrite IHeq_poly with (x:=f) (y:=g); auto.
Qed.


Lemma padd_assoc: forall f g h,
  (f p+ g) p+ h ~ f p+ (g p+ h).
Proof.
  induction f; intros.
  - reflexivity.
  - destruct g as [| d g]; destruct h as [|e h]; simpl; try reflexivity.
    rewrite IHf. auto.
Qed.

Lemma pscale_0p: forall f k, f ~ 0p -> (k p$ f) ~ 0p.
Proof.
  induction f; simpl; intros; auto.
Qed.

Global Instance pscale_Proper:
  Proper (eq ==> eq_poly ==> eq_poly) pscale.
Proof.
  intros x y Hxy f g Hfg.
  induction Hfg.
  + repeat rewrite pscale_0p; auto.
  + simpl. apply eq_poly_cons; auto.
Qed.

Global Instance psub_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) psub.
Proof.
  intros f1 g1 H1 f2 g2 H2.
  unfold psub. rewrite H1, H2. auto.
Qed.

Lemma padd_congruence: forall f1 f2 g1 g2,
  f1 ~ f2 -> g1 ~ g2 -> f1 p+ g1 ~ f2 p+ g2.
Proof. intros. rewrite H, H0; auto. Qed.

Lemma pscale_congruence: forall k1 k2 f1 f2,
  k1 == k2 -> f1 ~ f2 -> k1 p$ f1 ~ k2 p$ f2.
Proof. intros. rewrite H, H0; auto. Qed.

Lemma psub_congruence: forall f1 f2 g1 g2,
  f1 ~ f2 -> g1 ~ g2 -> f1 p- g1 ~ f2 p- g2.
Proof. intros. rewrite H, H0; auto. Qed.


Hint Extern 10 (?k1 p$ ?f ~ ?k2 p$ ?g) => apply pscale_congruence : core.
Hint Extern 10 (?c :: ?f ~ ?d :: ?g) => apply eq_poly_cons : core.
Hint Extern 10 (?f1 p+ ?g1 ~ ?f2 p+ ?g2) => apply padd_congruence : core.
Hint Extern 10 (?f1 p- ?g1 ~ ?f2 p- ?g2) => apply padd_congruence : core.

Lemma pmul_0_r: forall f g, g ~ 0p -> f p* g ~ 0p.
Proof.
  induction f; auto.
  intros. simpl. rewrite pscale_0p; auto. rewrite IHf; simpl; auto.
Qed.

Lemma pmul_cons_r: forall f d g,
  f p* (d :: g) ~ d p$ f p+ (0 :: f p* g).
Proof.
  induction f; simpl; intros; auto.
  rewrite IHf.
  apply cons_eq_cons. split; auto.
  (* FIXME: we should really prove polynomials form a ring and do Add Ring *)
  rewrite <- padd_assoc. rewrite padd_comm with (f:=a p$ g). rewrite padd_assoc.
  reflexivity.
Qed.

Lemma pmul_comm: forall f g,
  f p* g ~ g p* f.
Proof.
  induction f; simpl; intros.
  - rewrite pmul_0_r; auto.
  - rewrite pmul_cons_r. rewrite IHf. reflexivity.
Qed.

Lemma pmul_assoc: forall f g h,
  (f p* g) p* h ~ f p* (g p* h).
Proof.
Abort.



Global Instance pmul_r_Proper: forall f,
  Proper (eq_poly ==> eq_poly) (pmul f).
Proof.
  intros f g1. generalize dependent f.
  induction g1 as [| d1 g1]; intros f g2 Hg.
  - repeat rewrite pmul_0_r; auto. symmetry. auto.
  - destruct g2 as [| d2 g2].
    + repeat rewrite pmul_0_r; auto.
    + destruct f as [| c f]; simpl; auto.
      * apply eq_cons_invert in Hg. destruct Hg.
        rewrite pmul_cons_r.
        rewrite pmul_cons_r.
        rewrite IHg1 with (y:=g2); auto.
Qed.

Global Instance pmul_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) pmul.
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  induction Hf.
  - rewrite pmul_comm with (f:=f).
    rewrite pmul_comm with (f:=g).
    repeat rewrite pmul_0_r; auto.
  - simpl. auto.
Qed.

Lemma pmul_congruence: forall f1 f2 g1 g2,
  f1 ~ f2 -> g1 ~ g2 -> f1 p* g1 ~ f2 p* g2.
Proof. intros. rewrite H, H0; auto. Qed.



(**************************************
 *     Arithmetic and Evaluation      *
 **************************************)

Lemma peval_padd: forall f g x,
  (f p+ g) ([x]) == f ([x]) + g ([x]).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - destruct g; simpl.
    + fsatz.
    + rewrite IHf. fsatz.
Qed.

Lemma peval_pscale: forall f k x,
  (k p$ f) ([x]) == k * f ([x]).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - rewrite IHf. fsatz.
Qed.

Lemma peval_popp: forall f x,
  ((opp 1) p$ f) ([x]) == opp (f ([x])).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - rewrite IHf. fsatz.
Qed.

Lemma peval_psub: forall f g x,
  (f p- g) ([x]) == f ([x]) - g ([x]).
Proof.
  unfold psub. intros. rewrite peval_padd, peval_popp. auto.
Qed.

Lemma peval_ppmul: forall f g x, (f p* g)([x]) == f([x]) * g([x]).
Proof.
  induction f; simpl; intros; auto.
  rewrite peval_padd.
  rewrite peval_pscale.
  simpl. rewrite IHf. fsatz.
Qed.


(* 
Lemma eval_repeat_0: forall k x, (List.repeat 0 k)([x]) == 0.
Proof.
  induction k; intros; simpl; auto.
  rewrite IHk. auto.
Qed. *)


(**************************************
 *               Degree               *
 **************************************)

Local Open Scope nat_scope.

Definition degree := option nat.
Definition mk_degree (n: nat) := Some n.
Definition d0 := (mk_degree 0).

Fixpoint deg (f: polynomial) : degree := 
  match f with
  | nil => None
  | c::f' =>
    match deg f' with
    | Some d => Some (S d)
    | None => if eq_dec c zero then None else Some O
    end
  end.

Definition degree_leq d1 d2 :=
  match d1, d2 with
  | Some d1, Some d2 => (d1 <= d2)
  | None, _ => True
  | _, None => False
  end.

Notation "d1 p<= d2" := (degree_leq d1 d2) (at level 20). 
(* Notation "d1 p< d2" := (degree_leq (S d1) d2) (at level 20). *)

(* TODO: probably need a ton of tactics to do case split here *)

Lemma degree_leq_reflexive: forall d, d p<= d.
Admitted.

Lemma degree_leq_transitive: forall d1 d2 d3, d1 p<= d2 -> d2 p<= d3 -> d1 p<= d3.
Admitted.

Lemma degree_leq_total: forall d1 d2, d1 p<= d2 \/ d2 p<= d1.
Admitted.

Lemma degree_leq_bottom: forall d, d0 p<= d.
Admitted.

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
  | Some d1, Some d2 => Some (d1 + d2)
  end.

Lemma degree_max_self: forall d1 d2,
  d1 p<= degree_max d1 d2.
Admitted.

Lemma degree_max_comm: forall d1 d2,
  degree_max d1 d2 = degree_max d2 d1.
Admitted.

Lemma degree_add_le: forall d1 d2 b1 b2,
  d1 p<= Some b1 ->
  d2 p<= Some b2 ->
  degree_add d1 d2 p<= Some (b1 + b2).
Admitted.

Lemma degree_le_length: forall f,
  deg f p<= Some (length f - 1).
Admitted.

Lemma degree_max_congruence: forall d1 d2 b1 b2,
  d1 p<= b1 ->
  d2 p<= b2 ->
  degree_max d1 d2 p<= degree_max b1 b2.
Admitted.

Locate Decidable.


(**************************************
 *         Degree and Others          *
 **************************************)

Lemma degree_padd: forall p q,
  degree_leq (deg (p p+ q)) (degree_max (deg p) (deg q)).
Proof.
Admitted.

Lemma degree_pscale: forall p k,
  degree_leq (deg (k p$ p)) (deg p).
Admitted.

Lemma degree_psub: forall p q, (*11*)
  degree_leq (deg (p p- q)) (degree_max (deg p) (deg q)).
Proof.
  intros. unfold psub.
  eapply degree_leq_transitive.
  apply degree_padd.
  eapply degree_max_congruence. apply degree_leq_reflexive.
  apply degree_pscale.
Qed.

Lemma degree_pmul: forall f g,
  degree_leq (deg (f p* g)) (degree_add (deg f) (deg g)).
Admitted.

Lemma degree_toPoly: forall n (l:tuple F n),
  degree_leq (deg (toPoly l)) (Some (n-1)).
Proof.
  intros. eapply degree_leq_transitive. apply degree_le_length.
  simpl. rewrite toPoly_length. lia.
Qed.

Lemma degree_pmul_from_tuple: forall ka kb (a: tuple F ka) (b: tuple F kb),
  ka > 0 -> kb > 0 ->
  degree_leq (deg (pmul (toPoly a) (toPoly b))) (Some (ka + kb - 2)).
Proof.
  intros. eapply degree_leq_transitive. apply degree_pmul.
  eapply degree_leq_transitive.
  apply degree_add_le; apply degree_toPoly.
  simpl. lia.
Qed.


Lemma deg_coeff: forall f n,
  deg f = Some n ->
  f[n] <> zero /\
  forall i, i > n -> f[i] == zero.
Admitted.

Local Close Scope nat_scope.


(**************************************
 *        Unique Interpolant          *
 **************************************)

Definition root x p := peval x p == 0.

Definition linear a := (opp a :: 1 :: nil).

Lemma pscale_0_invert: forall f k,
  (k p$ f) ~ 0p -> k == 0 \/ f ~ 0p.
Proof.
  induction f; simpl; intros; auto.
  destruct (eq_dec k 0); auto.
  right.
  invert H. invert H0.
  assert (a == 0) by fsatz.
  assert ((k p$ f) ~ 0p) by auto.
  apply IHf in H0. destruct H0. fsatz.
  auto.
Qed.

Lemma psub_cons: forall c d f g,
  (c :: f) p- (d :: g) ~ ((c-d) :: (f p- g)).
Admitted.

Lemma eq_poly_invert: forall c d f g,
  (c :: f) ~ (d :: g) -> c == d /\ f ~ g.
Proof.
  intros. invert H.
  - invert H0. invert H1; auto.
  - auto.
Qed.

Lemma psub_0: forall f g,
  (f p- g) ~ 0p <-> f ~ g.
Proof.
  induction f as [| c f]; intros g; split; intros H.
  - apply pscale_0_invert in H. destruct H. fsatz. symmetry. auto.
  - unfold psub. simpl. rewrite pscale_0p. auto. symmetry. auto.
  - destruct g as [| d g]; auto.
    rewrite psub_cons in H.
    assert (f ~ g). apply IHf. auto.
    auto.
  - destruct g as [| d g]; auto.
    rewrite psub_cons.
    assert (f p- g ~ nil). apply IHf. auto.
    auto.
Qed.

Lemma psub_0_neg: forall f g,
  ~((f p- g) ~ 0p) <-> ~(f ~ g).
Proof.
  split; intros; unfold not; intros.
  - apply psub_0 in H0; auto.
  - apply H. apply psub_0. auto.
Qed.


Lemma not0_implies_positive_deg: forall f,
  ~ (f ~ 0p) -> exists n, deg f = Some n /\ (n >= 0)%nat.
Proof.
  induction f; intros.
  - exfalso. auto.
  - destruct (eq_dec a 0).
    + assert (Hf: ~ (f ~ nil)). intros Hf. apply H. auto.
      apply IHf in Hf.
      destruct Hf. destruct H0.
      eexists. simpl. split. rewrite H0. auto. lia. 
    + simpl. destruct (deg f).
      * exists (S n0). split; auto || lia.
      * destruct (eq_dec a 0); auto.
        exists 0%nat; split; auto || lia.
Qed.

Lemma deg_d_has_most_d_roots: forall p d,
  deg p = Some d ->
  (d > 0)%nat ->
  exists X, NoDup X /\ length X = d /\ forall x, root x p -> In x X.
Admitted.

(* polynomial long division *)
Lemma pdiv: forall a b,
  ~ (a ~ 0p) ->
  exists q r, a ~ ((q p* b) p+ r) /\
  (r ~ 0p \/ degree_leq (deg r) (deg b)).
Admitted.

(* if a polynomial has a root at a, then it is divi *)
Lemma factor_root: forall p a, root a p ->
  exists q, p ~ (linear a p* q).
Admitted.

Lemma In_pigeon_hole: forall {A: Type} (X X': list A), (*11*)
  NoDup X ->
  NoDup X' ->
  (length X > length X')%nat ->
  (forall x, In x X -> In x X') ->
  False.
Proof.
Admitted.

Lemma deg_0_has_no_root: forall f,
  deg f = Some O -> forall x, f([x]) <> 0.
Proof.
  intros. 
  destruct f as [| c fnil]. discriminate.
  apply deg_coeff in H. destruct H.
  unfold coeff in *.
  simpl in H.
  simpl.
  assert (fnil ~ 0p). {
    apply coeff_equal_eq.
    intros. specialize (H0 (S i)). rewrite coeff_nil. apply H0. lia.
  }
  rewrite H1.
  rewrite peval_nil; auto.
Qed.

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
  (* p ~ q *)
  trivial.
  (* not p ~ q *)
  apply psub_0_neg in H4.
  apply not0_implies_positive_deg in H4.
  destruct H4 as [d [H_deg_r H_x] ].
  exfalso.
  destruct d.
  (* d = 0 *)
  assert (Hx: exists x, In x X). destruct X; simpl in *. lia. exists f. auto.
  destruct Hx.
  apply H3 in H4.
  assert (p([x]) - q([x]) == 0) by fsatz.
  rewrite <- peval_psub in H5.
  eapply deg_0_has_no_root in H_deg_r.
  auto.
  (* d > 0 *)
  remember (S d) as d'. assert (Hd': (d' > 0)%nat) by lia.
  assert (H_d'_n: (d' <= n)%nat). {
    pose proof (degree_psub p q) as H_deg_r_leq. rewrite H, H0 in H_deg_r_leq.
    replace (degree_max (Some n) (Some n)) with (Some n) in H_deg_r_leq by (simpl; f_equal; lia).
    rewrite H_deg_r in H_deg_r_leq. simpl in H_deg_r_leq.
    auto.
  }
  specialize (deg_d_has_most_d_roots _ _ H_deg_r Hd').
  intro HX. destruct HX as [X' [H_NoDup [H_len_X H_X] ] ].
  eapply In_pigeon_hole with (X := X ) (X' := X'); auto.
  lia.
  intros. apply H_X. unfold root. rewrite peval_psub.
  apply H3 in H4. fsatz.
Qed.

End Polynomial. (* section *)

End Polynomial. (* polynomial *)
(* 
Module _polynomial_test.
Import Circom.
Import Polynomial.
Definition x : F := 0.
Definition p: polynomial := @nil F.
Compute (peval x p).
End _polynomial_test. *)

Declare Scope P_scope.
Delimit Scope P_scope with P.
(* Bind Scope F_scope with F.F. *)
(* Infix "+" := F.add : F_scope.
Infix "*" := F.mul : F_scope.
Infix "-" := F.sub : F_scope.
Infix "/" := F.div : F_scope.
Infix "^" := F.pow : F_scope. *)
(* Notation "0" := F.zero : F_scope. *)
(* Notation "1" := F.one : F_scope. *)

Notation "0p" := (nil : Polynomial.polynomial) : P_scope.
Notation "a ~ b" := (Polynomial.eq_poly a b) (at level 20) : P_scope.
Notation "f ([ x ]) " := (Polynomial.peval x f) (at level 19) : P_scope.
(* Notation "f [ i ]" := (Polynomial.coeff i f) : P_scope. *)
Notation "f p+ g" := (Polynomial.padd f g) (at level 18) : P_scope.
Notation "k p$ f" := (Polynomial.pscale k f) (at level 17) : P_scope.
Notation "f p- g" := (Polynomial.psub f g) (at level 18) : P_scope.
Notation "f p* g" := (Polynomial.pmul f g) (at level 17) : P_scope.
Notation "d1 p<= d2" := (Polynomial.degree_leq d1 d2) (at level 20) : P_scope. 


(* 
The following requires the pow function.

Lemma eval_app': forall cs0 cs1 n x,
  eval' n (cs0 ++ cs1) x = eval' n cs0 x + eval' (n + N.of_nat (length cs0)) cs1 x.
Proof.
  induction cs0;simpl;intros.
  - assert(n + 0 =n)%N by lia. rewrite H. fqsatz.
  - rewrite IHcs0.
    assert (N.pos (Pos.of_succ_nat (length cs0)) = (1 + N.of_nat (length cs0))%N).
    rewrite Pos.of_nat_succ. lia.
    rewrite H. 
    assert(n + (1 + N.of_nat (length cs0)) = n + 1 + N.of_nat (length cs0))%N. lia.
    rewrite H0. fqsatz.
Qed.

Lemma eval_app: forall cs0 cs1 x,
  eval (cs0 ++ cs1) x = eval cs0 x + eval' (N.of_nat (length cs0)) cs1 x.
Proof.
  intros. apply eval_app'.
Qed. *)



(* Hanzhi's version *)
(* 


Lemma degree_leq_trans: forall a b d n,
  degree_leq a (Some n) ->
  degree_leq b (Some n) ->
  degree_leq (Some d) (degree_max a b) ->
  (d <= n)%nat.
Proof.
Admitted.

Theorem interpolant_unique: forall (a b: polynomial) n (X: list (F q)),
  degree_leq (deg a) (Some n) ->
  degree_leq (deg b) (Some n) ->
  (length X > n)%nat ->
  NoDup X ->
  (forall x, In x X -> eval a x = eval b x) ->
  a = b.
Proof.
  (* Proof: https://inst.eecs.berkeley.edu/~cs70/fa14/notes/n7.pdf *)
  intros.
  destruct (eq_poly_decidable a b).
  trivial.
  exfalso.
  apply psub_0_neg in H4.
  apply not0_implies_positive_deg in H4.
  destruct H4 as [d [H_deg_r H_x] ].
  pose proof (deg_psub a b) as H_deg_r_leq. 
  rewrite H_deg_r in H_deg_r_leq. simpl in H_deg_r_leq.
  assert (H_d_n: (d <= n)%nat).
  { eapply degree_leq_trans. 3: apply H_deg_r_leq. all:auto. }
  specialize (deg_d_has_most_d_roots _ _ H_deg_r H_x).
  intro HX. destruct HX as [X' [H_len_X H_X] ].
  eapply In_pigeon_hole with (X := X ) (X' := X');auto.
  lia.
  intros. apply H_X. unfold root. rewrite eval_psub.
  apply H3 in H4. fqsatz.
Qed. 
*)

