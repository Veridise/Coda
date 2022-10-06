Require Import Nat.
Require Import List.
Import ListNotations.

Require Import BinPosDef.
Require Import Crypto.Spec.ModularArithmetic.

Context {q : positive}.

Definition var := nat.

(* Expressions that can be used in constraints *)
Inductive cexpr : Type :=
| Sig (s : F q)
| Var (v : var)
| Opp (e : cexpr)
| Add (e1 e2 : cexpr)
| Mul (e1 e2 : cexpr).

(* Expressions that can be used in non-constraint assignments *)
Inductive expr : Type :=
| Cexpr (c : cexpr)
| Inv (e : expr)
| Ite (e1 e2 e3 : expr).

Definition var_map := var -> expr.

Definition set_var (m : var_map) (v : var) (e : expr) : var_map :=
  fun v' => if (eqb v' v) then e else m v'.

Definition const_map (v : var) : expr := (Cexpr (Sig 0)).

Inductive stmt : Type :=
| A (v : var) (e : expr)
| C (c1 c2 : cexpr)
| AC (v : var) (c : cexpr).

Definition tmpl := list stmt.

Definition state := (var_map * list Prop * list stmt) % type.

Inductive step : state -> state -> Prop :=
| step_A : forall m c s' v e,
    step (m, c, (A v e) :: s') (set_var m v e, c, s')
| step_C : forall m c s' e1 e2,
    step (m, c, (C e1 e2) :: s') (m, (e1 = e2) :: c, s')
| step_AC : forall m c s' v e,
    step (m, c, (AC v e) :: s') (m, c, (A v (Cexpr e)) :: (C (Var v) e) :: s').

Inductive stepStar : state -> state -> Prop :=
| stepStar_refl: forall m c s, stepStar (m, c, s) (m, c, s)
| stepStar_tran: forall m1 m2 m3 c1 c2 c3 s1 s2 s3,
    step (m1, c1, s1) (m2, c2, s2) -> stepStar (m2, c2, s2) (m3, c3, s3) -> stepStar (m1, c1, s1) (m3, c3, s3).

Fixpoint reduce (m : var_map) (c : list Prop) (s : list stmt) {struct s} : (var_map * list Prop) :=
  match s with
  | [] => (m, c)
  | (A v e) :: s' =>
      reduce (set_var m v e) c s'
  | (C c1 c2) :: s' =>
      reduce m ((c1 = c2) :: c) s'
  | (AC v e) :: s' =>
      let m' := set_var m v (Cexpr e) in
      let c' := ((Var v) = e) :: c in
      reduce m' c' s'
  end.

(* IsZero from circomlib: 0 -> in, 1 -> out, 2 -> inv *)
Definition IsZero := [
    A 2 (Ite (Cexpr (Var 0)) (Inv (Cexpr (Var 0))) (Cexpr (Sig 0))) ;
    AC 1 (Add (Opp (Mul (Var 0) (Var 2))) (Sig 1)) ;
    C (Mul (Var 0) (Var 1)) (Sig 0)
  ].

Definition reduce_is_zero := reduce (const_map) [] IsZero.

Compute reduce_is_zero.
