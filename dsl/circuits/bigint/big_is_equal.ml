open Ast
open Dsl
open Notation

let vin = v "in"

let vout = v "out"

let x = v "x"

let y = v "y"

let z = v "z"

let n = v "n"

let k = v "k"

let i = v "i"

let a = v "a"

let b = v "b"

let total = v "total"


(* BigIsEqual *)
let bie_forall i = let j = "bie_j" in qforall j z0 i (get a (v j) ==. get b (v j))
let bie_exists i = let j = "bie_j" in qexists j z0 i (qnot (get a (v j) ==. get b (v j)))

let t_bie i = tfq (qand (lift (toUZ nu <=. i)) (ite (toUZ nu ==. i) (bie_forall i) (bie_exists i)))

let big_is_equal =
  Circuit
    { name= "BigIsEqual"
    ; inputs= [
      ("k", attaches [lift (k <=. CPLen)] tnat);
      ("a", tarr_tf k);
      ("b", tarr_tf k)]
    ; outputs= [("out", attach ((ite (nu ==. f1) (bie_forall k) (bie_exists k))) tf_binary)]
    ; dep= None
    ; body=
      (elet
      "total"
      (iter z0 k ~init:f0 ~inv:t_bie
        (lama "i" tint
          (lama "x" tf
            (elet "ise" (call "IsEqual" [get a i; get b i])
            (x +% v "ise")))))
        (call "IsEqual" [nat2f k; v "total"]))}
