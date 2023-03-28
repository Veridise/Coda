open Ast
open Dsl
open Notation

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

let lam_sum_arr xs = lama "i" tint (lama "x" tf (fadd x (get xs i)))

let rec sum_arr xs =
  iter z0 (len xs) (lam_sum_arr xs) ~init:f0 ~inv:(fun i ->
      tfq (qeq nu (sum_arr (take i xs))) )

let t_ct = tfq (qeq nu (sum_arr vin))

let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", t_ct)]
    ; dep= None
    ; body= sum_arr vin }

let sum_equals =
  Circuit
    { name= "SumEquals"
    ; inputs= [("n", tnat); ("nums", tarr_tf n); ("sum", tf)]
    ; outputs= [("out", tf_binary)]
    ; dep= None
    ; body= call "IsEqual" [call "CalculateTotal" [n; v "nums"]; v "sum"] }

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
        call "CalculateTotal"
          [ z2
          ; x *% call "IsEqual" [v "op"; f0]
          ; y *% call "IsEqual" [v "op"; f1] ] }
