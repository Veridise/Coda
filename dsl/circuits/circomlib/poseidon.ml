open Ast
open Dsl

let nInputs = v "nInputs"

let inputs = v "inputs"

let t_poseidon = tfq (qeq nu (unint "Poseidon" [nInputs; inputs]))

let poseidon =
  Circuit
    { name= "Poseidon"
    ; inputs= [("nInputs", tnat); ("inputs", tarr_tf nInputs)]
    ; outputs= [("out", t_poseidon)]
    ; dep= None
    ; body= star }

let vrfy_eddsa_poseidon =
  Circuit
    { name= "EdDSAPoseidonVerifier"
    ; inputs=
        [ ("enabled", tf)
        ; ("Ax", tf)
        ; ("Ay", tf)
        ; ("S", tf)
        ; ("R8x", tf)
        ; ("R8y", tf)
        ; ("M", tf) ]
    ; outputs= []
    ; dep= None
    ; body= unit_val }
