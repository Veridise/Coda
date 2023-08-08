open Ast
open Dsl
open Nice_dsl
open Expr
open Qual
open Typ
open TypRef

let a = var "a"

let a_sig = ("a", binary_field)

let b = var "b"

let b_sig = ("b", binary_field)

let in_ = var "in"

let out = v "out"

(*

   (* NOT *)

   let not_circuit =
     let open Hoare_circuit in
     to_circuit
     @@ Hoare_circuit
          { name= "Not"
          ; inputs= BaseTyp.[("in", field)]
          ; outputs= BaseTyp.[("out", field)]
          ; preconditions= []
          ; postconditions=
              [iff_binary_field (var "out") (Qual.to_expr (Z.not in_))]
          ; body= F.(F.(in_ + z1) - F.(f2 * in_)) }

   let not_sig = field |: fun x -> iff_binary_field x (Qual.to_expr (Z.not in_))

   let not_imp =
     circuit "Not"
       [("in", binary_field)]
       [("out", not_sig)]
       F.(Z.(in_ + z1) - F.(f2 * in_))

   let cnot = not_imp
*)

(* NOT *)

let vin = v "in"

let tnot = tfq (ind_dec nu (unint "not" [v "in"]))

let cnot =
  Circuit
    { name= "Not"
    ; inputs= [("in", tf_binary)]
    ; outputs= [("out", tnot)]
    ; dep= None
    ; body= fsub (fadd1 vin) (fmul f2 vin) }

(* XOR *)

let xor_sig =
  field |: fun x -> iff_binary_field x (Qual.to_expr Z.Unint.(a ^ b))

let xor_imp =
  circuit "Xor" [a_sig; b_sig]
    [("out", xor_sig)]
    F.(F.(a + b) - F.product [f2; a; b])

(* let cxor = xor_imp *)
let cxor = xor_imp

(* AND *)

let and_sig =
  field |: fun x -> iff_binary_field x (Qual.to_expr Z.Unint.(a && b))

let and_imp = circuit "And" [a_sig; b_sig] [("out", and_sig)] F.(a * b)

let cand = and_imp

(* NAND *)

let nand_sig =
  field |: fun x -> iff_binary_field x (Qual.to_expr Z.Unint.(a &&! b))

let nand_imp =
  circuit "Nand" [a_sig; b_sig] [("out", nand_sig)] F.(f1 - F.(a * b))

let cnand = nand_imp

(* OR *)

let or_sig =
  field |: fun x -> iff_binary_field x (Qual.to_expr Z.Unint.(a || b))

let or_imp =
  circuit "Or" [a_sig; b_sig] [("out", or_sig)] F.(F.(a + b) - F.(a * b))

let cor = or_imp

(* NOR *)

let nor_sig =
  field |: fun x -> iff_binary_field x (Qual.to_expr Z.Unint.(a ||! b))

let nor_imp =
  circuit "Nor" [a_sig; b_sig] [("out", or_sig)] F.(F.(F.add1 F.(a * b) - a) - b)

let cnor = nor_imp
