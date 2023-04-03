open Ast
open Dsl
open Notation

let a = v "a"

let b = v "b"

let i = v "i"

let n = v "n"

let x = v "x"

let y = v "y"

let z = v "z"

let vin = v "in"

let out = v "out"

let key = v "KEY"

let n2b = v "n2b"

let rng = v "rng"

let eqs = v "eqs"

let choices = v "choices"

let index = v "index"

(* CalculateTotal *)

let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", tfq (qeq nu (u_sum vin)))]
    ; dep= None
    ; body= make_sum vin ~len:n }

let sum_equals =
  Circuit
    { name= "SumEquals"
    ; inputs= [("n", tnat); ("nums", tarr_tf n); ("sum", tf)]
    ; outputs= [("out", tf_binary)]
    ; dep= None
    ; body=
        elet "x"
          (call "CalculateTotal" [n; v "nums"])
          (call "IsEqual" [x; v "sum"]) }

let is_not_zero =
  Circuit
    { name= "IsNotZero"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (bnot (vin =. f0))))]
    ; dep= None
    ; body= elet "isz" (call1 "IsZero" vin) (call1 "Not" (v "isz")) }

let is_filtered =
  Circuit
    { name= "IsFiltered"
    ; inputs= [("x", tf); ("y", tf); ("op", tf)]
    ; outputs= [("out", tf)]
    ; dep= None
    ; body=
        elet "a"
          (call "IsEqual" [v "op"; f0])
          (elet "b"
             (call "IsEqual" [v "op"; f1])
             (elet "z"
                (cons (x *% a) (cons (y *% b) cnil))
                (call "CalculateTotal" [z2; z]) ) ) }
