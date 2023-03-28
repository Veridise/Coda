open Ast
open Dsl

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
    ; body= fsub (fadd1 vin) (fmul f2 vin) }

(* XOR *)
let txor = tfq (ind_dec nu (unint "xor" [v "a"; v "b"]))

let cxor =
  Circuit
    { name= "Xor"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", txor)]
    ; dep= None
    ; body= fsub (fadd a b) (fmuls [f2; a; b]) }

(* AND *)
let tand = tfq (ind_dec nu (unint "and" [v "a"; v "b"]))

let cand =
  Circuit
    { name= "And"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tand)]
    ; dep= None
    ; body= fmul a b }

(* NAND *)
let tnand = tfq (ind_dec nu (unint "nand" [v "a"; v "b"]))

let cnand =
  Circuit
    { name= "Nand"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tnand)]
    ; dep= None
    ; body= fsub f1 (fmul a b) }

(* OR *)
let tor = tfq (ind_dec nu (unint "or" [v "a"; v "b"]))

let cor =
  Circuit
    { name= "Or"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tor)]
    ; dep= None
    ; body= fsub (fadd a b) (fmul a b) }

(* NOR *)
let tnor = tfq (ind_dec nu (unint "nor" [v "a"; v "b"]))

let cnor =
  Circuit
    { name= "Nor"
    ; inputs= [("a", tf_binary); ("b", tf_binary)]
    ; outputs= [("out", tnor)]
    ; dep= None
    ; body= fsub (fsub (fadd1 (fmul a b)) a) b }
