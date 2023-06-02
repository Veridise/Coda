open Ast
open Dsl
open Notation

let z254 = zn 254

let i = v "i"

let j = v "j"

let n = v "n"

let x = v "x"

let y = v "y"

let z = v "z"

let r = v "r"

let c = v "c"

let h = v "h"

let vin = v "in"

let out = v "out"

let n2b = v "n2b"

let nRows = v "nRows"

let nCols = v "nCols"

let nChannels = v "nChannels"

(* is_negative (in : F) : { F | binary nu /\ nu = 1 -> (toSZ in < 0) /\ nu = 0 -> ~(toSZ in < 0) } *)
let is_negative =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (toSZ vin <. z0)))]
    ; dep= None
    ; body= elet "n2b" (call2 "Num2Bits" z254 vin) (call1 "Sign" n2b) }

(* is_positive (in : F) : { F | binary nu /\ nu = 1 -> (0 < toSZ in) /\ nu = 0 -> ~(0 < toSZ in) } *)
let is_positive =
  Circuit
    { name= "IsPositive"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (z0 <. toSZ vin)))]
    ; dep= None
    ; body=
        elet "n2b"
          (call2 "Num2Bits" z254 vin)
          (elets
             [("s", call1 "Sign" n2b); ("isz", call1 "IsZero" vin)]
             ((f1 -% v "s") *% (f1 -% v "isz")) ) }

(* relu (in : F) : { F | toSZ nu = max 0 (toSZ in) } *)
let relu =
  Circuit
    { name= "ReLU"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfe (toSZ nu =. zmax z0 (toSZ vin)))]
    ; dep= None
    ; body= elet "isp" (call1 "IsPositive" vin) (vin *% v "isp") }

(* poly (n : F) (in : F) : { F | nu = in * (in + n) } *)
let poly =
  Circuit
    { name= "Poly"
    ; inputs= [("n", tf); ("in", tf)]
    ; outputs= [("out", tfe (nu =. vin *% (vin +% n)))]
    ; dep= None
    ; body= (vin *% vin) +% (n *% vin) }

let vmax = v "max"

let gt = v "gt"

let cmax =
  Circuit
    { name= "Max"
    ; inputs=
        [ ("n", attaches [lift (z1 <=. nu); lift (nu <=. CPLen -! z1)] tnat)
        ; ("in", tarr_t_k (attach (lift (toUZ nu <=. (z2 ^! n) -! z1)) tf) n) ]
    ; outputs= [("out", tfq (nu ==. unint "fmax" [vin]))]
    ; dep= None
    ; body=
        iter z1 n ~init:(get vin z0)
          ~inv:(fun i ->
            attaches
              [ nu ==. unint "fmax" [take vin i]
              ; lift (toUZ nu <=. (z2 ^! n) -! z1) ]
              tf )
          (lama "i" tnat
             (lama "max" tf
                (elet "gt"
                   (call3 "GreaterThan" n (get vin i) vmax)
                   (tfst (call3 "Switcher" gt vmax (get vin i))) ) ) ) }

let q_flatten_2d =
  qforall "r" z0 nRows
    (qforall "c" z0 nCols
       (qforall_e "h" z0 nChannels
          ( get out ((r *! (nCols *! nChannels)) +! (c *! nChannels) +! h)
          =. get (get (get vin r) c) h ) ) )

let inv_col j = tarr_tf (j *! nChannels)

let inv_row i = tarr_tf (i *! nCols *! nChannels)

let iter_row r =
  iter z0 nCols
    (lama "j" tint
       (lama "y" (tarr_tf (j *! nChannels)) (push (concat y (get r j)))) )
    ~init:cnil ~inv:inv_col

let flatten_2d =
  Circuit
    { name= "Flatten2D"
    ; inputs=
        [ ("nRows", tnat)
        ; ("nCols", tnat)
        ; ("nChannels", tnat)
        ; ("in", tarr_t_k (tarr_t_k (tarr_tf nChannels) nCols) nRows) ]
    ; outputs=
        [("out", tarr_t_q_k tf q_flatten_2d (nRows *! nCols *! nChannels))]
    ; dep= None
    ; body=
        iter z0 nRows
          (lama "i" tint
             (lama "x"
                (tarr_tf (i *! nCols *! nChannels))
                (push (concat x (iter_row (get vin i)))) ) )
          ~init:cnil ~inv:inv_row }
