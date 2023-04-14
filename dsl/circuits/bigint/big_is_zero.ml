open Ast
open Dsl
open Notation

let vin = v "in"

let vout = v "out"

let xs = v "xs"

let x = v "x"

let z = v "z"

let n = v "n"

let k = v "k"

let i = v "i"

let total = v "total"

(* BigIsEqual *)
let bie_forall i =
  let j = "bie_j" in
  qforall j z0 i (get xs (v j) ==. f0)

let bie_exists i =
  let j = "bie_j" in
  qexists j z0 i (qnot (get xs (v j) ==. f0))

let t_bie i =
  tfq
    (qand
       (lift (toUZ nu <=. i))
       (ite (toUZ nu ==. i) (bie_forall i) (bie_exists i)) )

let big_is_zero =
  Circuit
    { name= "BigIsZero"
    ; inputs= [("k", attaches [lift (k <=. CPLen)] tnat); ("xs", tarr_tf k)]
    ; outputs=
        [ ( "out"
          , attach (ite (nu ==. f1) (bie_forall k) (bie_exists k)) tf_binary )
        ]
    ; dep= None
    ; body=
        elet "total"
          (iter z0 k ~init:f0 ~inv:t_bie
             (lama "i" tint
                (lama "x" tf
                   (elet "ise" (call "IsZero" [get xs i]) (x +% v "ise")) ) ) )
          (call "IsEqual" [nat2f k; v "total"]) }
