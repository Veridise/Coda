(* open Ast *)
open Dsl
open Nice_dsl
open Expr
open Qual
open Typ
open TypRef

let a = var "a"

let b = var "b"

let in_ = var "in"

let out = v "out"

(* NOT *)

let not_sig = field |: fun x -> iff_binary_field x (qual_of_expr (not_int in_))

let not_imp =
  circuit ~name:"Not" ~dep:None
    ~inputs:[("in", binary_field)]
    ~outputs:[("out", not_sig)]
    ~body:F.(Z.(in_ + z1) - F.(f2 * in_))

let cnot = not_imp

(* XOR *)

let xor_sig =
  field |: fun x -> iff_binary_field x (qual_of_expr Z.Unint.(a ^ b))

let xor_imp =
  Circuit.make "Xor"
    [("a", binary_field); ("b", binary_field)]
    [("out", xor_sig)]
    (function [a; b] -> Some F.(Z.(a + b) - F.product [f2; a; b]) | _ -> None)

(* let cxor = xor_imp *)
let cxor = xor_imp

(* AND *)

let and_sig =
  (* field |: fun x -> iff_binary_field x (qual_of_expr (unint "and" [a; b])) *)
  field |: fun x -> iff_binary_field x (qual_of_expr Z.Unint.(a && b))

let and_imp =
  Circuit.make "And"
    [("a", binary_field); ("b", binary_field)]
    [("out", and_sig)]
    (function [a; b] -> Some F.(a * b) | _ -> None)

let cand = and_imp

(* NAND *)

let nand_sig =
  (* field |: fun x -> iff_binary_field x (qual_of_expr (unint "nand" [a; b])) *)
  field |: fun x -> iff_binary_field x (qual_of_expr Z.Unint.(a &&! b))

let nand_imp =
  Circuit.make "Nand"
    [("a", binary_field); ("b", binary_field)]
    [("out", nand_sig)]
    (function [a; b] -> Some F.(f1 - F.(a * b)) | _ -> None)

let cnand = nand_imp

(* OR *)

let or_sig =
  field |: fun x -> iff_binary_field x (qual_of_expr Z.Unint.(a || b))

let or_imp =
  Circuit.make "Or"
    [("a", binary_field); ("b", binary_field)]
    [("out", or_sig)]
    (function [a; b] -> Some F.(F.(a + b) - F.(a * b)) | _ -> None)

let cor = or_imp

(* NOR *)

let nor_sig =
  field |: fun x -> iff_binary_field x (qual_of_expr Z.Unint.(a ||! b))

let nor_imp =
  Circuit.make "Nor"
    [("a", binary_field); ("b", binary_field)]
    [("out", or_sig)]
    (function [a; b] -> Some F.(F.(F.add1 F.(a * b) - a) - b) | _ -> None)

let cnor = nor_imp
