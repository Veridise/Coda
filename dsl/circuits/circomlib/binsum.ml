open Ast
open Dsl
open Notation
open Liblam

let n = v "n"

let x = v "x"

let ops = v "ops"

let vin = v "in"

let u_len_bs n ops = unint "binsum_length" [((z2 ^! n) -! z1) *! ops]

let u_map f xs = unint "map" [f; xs]

(* As a field element, out is the sum of the ins as field elements *)
let t_binsum =
  tarr_t_q_k tf_binary
    (qeq (as_le_f nu)
       (u_sum (u_map (lama "x" (tarr_t_k tf_binary n) (as_le_f x)) vin)) )
    (u_len_bs n ops)

let binsum =
  Circuit
    { name= "BinSum"
    ; inputs=
        [("n", tnat); ("ops", tnat); ("in", tarr_t_k (tarr_t_k tf_binary n) ops)]
    ; outputs= [("out", t_binsum)]
    ; dep= None
    ; body= stars (u_len_bs n ops) }
