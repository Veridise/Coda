(* open Ast *)
open Dsl
open Nice_dsl
open Expr

(* open Qual *)
(* open Typ *)
(* open TypRef *)
open Hoare_circuit

let body_XOR (out, a, b) body =
  elet out
    F.(
      F.(var a + var b)
      - F.(F.(F.const (2) * var a) * var b) )
  @@ body

let circuit_XOR =
  Hoare_circuit.to_circuit
  @@ Hoare_circuit
       { name= "XOR"
       ; inputs= [Presignal "a"; Presignal "b"]
       ; outputs= [Presignal "out"]
       ; preconditions= []
       ; postconditions=
           [ Qual.iff_binary_field (var "out")
               (Qual.from_expr Z.Unint.(var "a" ^ var "b")) ]
       ; body= body_XOR ("out", "a", "b") (var "out") }
