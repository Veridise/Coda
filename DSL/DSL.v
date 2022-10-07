Require Import List.
Import ListNotations.

Require Import BinPosDef.
Require Import Crypto.Spec.ModularArithmetic.

Context {q : positive}.

Definition var := nat.

(* Expressions that can be used in constraints *)
Inductive expr : Type :=
| Sig (s : F q)
| Var (v : var)
| Opp (e : expr)
| Add (e1 e2 : expr)
| Mul (e1 e2 : expr).

Inductive stmt : Type :=
  (* Constrain *)
| C (e1 e2 : expr).

Definition tmpl := list stmt.

Definition state := (list Prop * list stmt) % type.

Fixpoint reduce' (c : list Prop) (s : list stmt) : list Prop :=
  match s with
  | [] => c
  | (C e1 e2) :: s' =>
      reduce' ((e1 = e2) :: c) s'
  end.

Definition reduce (s : state) : list Prop := reduce' (fst s) (snd s).

(* IsZero from circomlib: 0 -> in, 1 -> out, 2 -> inv *)
Definition IsZero := [
    C (Var 1) (Add (Opp (Mul (Var 0) (Var 2))) (Sig 1)) ;
    C (Mul (Var 0) (Var 1)) (Sig 0)
  ].

Definition reduce_is_zero := reduce ([], IsZero).

Compute reduce_is_zero.
