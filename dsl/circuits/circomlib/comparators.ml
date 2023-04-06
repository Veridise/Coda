open Ast
open Dsl
open Notation

let vin = v "in"

let vinv = v "inv"

let vout = v "out"

let x = v "x"

let y = v "y"

let a = v "a"

let b = v "b"

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

let is_equal =
  Circuit
    { name= "IsEqual"
    ; inputs= [("x", tf); ("y", tf)]
    ; outputs= [("out", t_is_equal)]
    ; dep= None
    ; body= call "IsZero" [fsub x y] }

(* LessThan *)
let t_lt = tfq (ind_dec nu (lt (toUZ x) (toUZ y)))

let lt_n_t = attach (QExpr (nu <. CPLen -! z1)) tnat

let input_t = attach (QExpr (toUZ nu <. z2 ^! n)) tf

let less_than =
  Circuit
    { name= "LessThan"
    ; inputs=
        [ ("n", attach (lift (nu <=. CPLen -! z1)) tnat)
        ; ("x", input_t)
        ; ("y", input_t) ]
    ; outputs= [("out", t_lt)]
    ; dep= None
    ; body=
        elet "z"
          (call "Num2Bits" [n +. z1; x -% y +% (f2 ^% n)])
          (call1 "Not" (get z n)) }

(* GreaterThan *)

let t_gt = tfq (ind_dec nu (toUZ a >. toUZ b))

let greater_than =
  Circuit
    { name= "GreaterThan"
    ; inputs= [("n", attach (lift (nu <=. CPLen -! z1)) tnat); ("a", input_t); ("b", input_t)]
    ; outputs= [("out", t_gt)]
    ; dep= None
    ; body= call "LessThan" [n; b; a] }

(* LessEqThan *)
let t_leq = tfq (ind_dec nu (toUZ a <=. toUZ b))

let input_t' = attach (QExpr (toUZ nu +! z1 <. z2 ^! n)) tf

let leq =
  Circuit
    { name= "LessEqThan"
    ; inputs= [("n", attach (lift (nu <=. CPLen -! z1)) tnat); ("a", input_t); ("b", input_t')]
    ; outputs= [("out", t_leq)]
    ; dep= None
    ; body= call "LessThan" [n; a; b +% f1] }

let t_geq = tfq (ind_dec nu (toUZ x >=. toUZ y))

let input_t' = attach (QExpr (toUZ nu +! z1 <. z2 ^! n)) tf

let geq =
  Circuit
    { name= "GreaterEqThan"
    ; inputs= [("n", attach (lift (nu <=. CPLen -! z1)) tnat); ("x", input_t'); ("y", input_t)]
    ; outputs= [("out", t_geq)]
    ; dep= None
    ; body= call "LessEqThan" [n; y; x] }
