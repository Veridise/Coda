open Ast
open Dsl
open Notation

let vin = v "in"

let vinv = v "inv"

let vout = v "out"

let x = v "x"

let y = v "y"

let z = v "z"

let n = v "n"

let k = v "k"

let i = v "i"

(* IsZero *)
let t_is_zero = tfq (ind_dec nu (eq vin f0))

let is_zero =
  Circuit
    { name= "IsZero"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_is_zero)]
    ; dep= None
    ; body=
        elets
          [ ("inv", star)
          ; ("out", star)
          ; ("u1", vout === f1 +% (f0 -% (vin *% vinv)))
          ; ("u2", vin *% vout === f0) ]
          vout }

(* IsEqual *)
let t_is_equal = tfq (ind_dec nu (eq x y))

let c_is_equal =
  Circuit
    { name= "IsEqual"
    ; inputs= [("x", tf); ("y", tf)]
    ; outputs= [("out", t_is_equal)]
    ; dep= None
    ; body= call "IsZero" [fsub x y] }

(* LessThan *)
let t_lt = tfq (ind_dec nu (lt (toUZ x) (toUZ y)))

let c_less_than =
  Circuit
    { name= "LessThan"
    ; inputs= [("n", tnat); ("x", tf); ("y", tf)]
    ; outputs= [("out", t_lt)]
    ; dep= None
    ; body=
        elet "z"
          (call "Num2Bits" [nadd1 n; fadd (fsub x y) (fpow f2 n)])
          (elet "b" (fsub1 (get z n)) (assert_eq vout (v "b"))) }

(* GreaterThan *)

let t_gt = tfq (ind_dec nu (lt (toUZ (get vin z1)) (toUZ (get vin z0))))

let c_greater_than =
  Circuit
    { name= "GreaterThan"
    ; inputs= [("n", tnat); ("in", tarr_tf z2)]
    ; outputs= [("out", t_gt)]
    ; dep= None
    ; body= call "LessThan" [n; get vin z1; get vin z0] }

(* LessEqThan *)

let t_leq = tfq (ind_dec nu (leq (toUZ (get vin z0)) (toUZ (get vin z1))))

let c_less_eq_than =
  Circuit
    { name= "LessEqThan"
    ; inputs= [("n", tnat); ("in", tarr_tf z2)]
    ; outputs= [("out", t_leq)]
    ; dep= None
    ; body= call "LessThan" [n; get vin z0; fadd1 (get vin z1)] }
