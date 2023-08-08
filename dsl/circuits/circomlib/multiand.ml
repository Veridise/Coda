(* open Ast *)
open Dsl
open Nice_dsl
open Expr

(* open Qual *)
(* open Typ *)
(* open TypRef *)
open Hoare_circuit

let body_AND (out, a, b) body = elet out F.(var a * var b) @@ body

let circuit_AND =
  Hoare_circuit
    { name= "AND"
    ; inputs= [Presignal "a"; Presignal "b"]
    ; outputs= [Presignal "out"]
    ; preconditions= []
    ; postconditions= []
    ; body= body_AND ("out", "a", "b") (var "out") }

let body_MultiAND (out, in_0, in_1) body =
  elet "var_0" (F.const (Big_int_Z.big_int_of_int 2))
  @@ elet "and1_a" (var in_0)
  @@ elet "and1_b" (var in_1)
  @@ body_AND ("and1_out", "and1_a", "and1_b")
  @@ elet out (var "and1_out")
  @@ body

let circuit_MultiAND =
  Hoare_circuit.to_circuit
  @@ Hoare_circuit
       { name= "MultiAND"
       ; inputs= [Presignal "in_0"; Presignal "in_1"]
       ; outputs= [Presignal "out"]
       ; preconditions= []
       ; postconditions= []
       ; body= body_MultiAND ("out", "in_0", "in_1") (var "out") }
