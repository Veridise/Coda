open Ast
open Dsl

let vin = v "in"

let vout = v "out"

let x = v "x"

let y = v "y"

let z = v "z"

let n = v "n"

let k = v "k"

let i = v "i"

(* IsZero *)
let t_is_zero = tfq (ind_dec nu (eq vin f0))

let c_is_zero =
  Circuit
    { name= "IsZero"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_is_zero)]
    ; dep= None
    ; body=
        elet "inv" star
          (elet "u1"
             (assert_eq vout (fadd1 (fopp (fmul vin (v "inv")))))
             (elet "u2" (assert_eq (fmul vin vout) f0) vout) ) }

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
