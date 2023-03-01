open Ast
open Dsl
open Typecheck

let a = v "a"

let b = v "b"

let vin = v "in"

let out = v "out"

(* NOT *)
let tnot = tfq (ind_dec nu (unint "not" [v "in"]))

let cnot =
  Circuit
    { name= "Not"
    ; inputs= [("in", tf_binary)]
    ; outputs= [("out", tnot)]
    ; dep= None
    ; body= [assert_eq out (fsub (fadd1 vin) (fmul f2 vin))] }

let check_not = typecheck_circuit d_empty cnot

(* XOR *)
let txor = tfq (ind_dec nu (unint "xor" [v "a"; v "b"]))

let cxor =
  Circuit
    { name= "Xor"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", txor)]
    ; dep= None
    ; body= [assert_eq out (fsub (fadd a b) (fmuls [f2; a; b]))] }

let check_xor = typecheck_circuit d_empty cxor

(* AND *)
let tand = tfq (ind_dec nu (unint "and" [v "a"; v "b"]))

let cand =
  Circuit
    { name= "And"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tand)]
    ; dep= None
    ; body= [assert_eq out (fmul a b)] }

let check_and = typecheck_circuit d_empty cand

(* NAND *)
let tnand = tfq (ind_dec nu (unint "nand" [v "a"; v "b"]))

let cnand =
  Circuit
    { name= "Nand"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tnand)]
    ; dep= None
    ; body= [assert_eq out (fsub f1 (fmul a b))] }

let check_nand = typecheck_circuit d_empty cnand

(* OR *)
let tor = tfq (ind_dec nu (unint "or" [v "a"; v "b"]))

let cor =
  Circuit
    { name= "Or"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tor)]
    ; dep= None
    ; body= [assert_eq out (fsub (fadd a b) (fmul a b))] }

let check_or = typecheck_circuit d_empty cor

(* NOR *)
let tnor = tfq (ind_dec nu (unint "nor" [v "a"; v "b"]))

let cnor =
  Circuit
    { name= "Nor"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tnor)]
    ; dep= None
    ; body= [assert_eq out (fsub (fsub (fadd1 (fmul a b)) a) b)] }

let check_nor = typecheck_circuit d_empty cnor
