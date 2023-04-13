open Ast
open Dsl

let nInputs = v "nInputs"

let inputs = v "inputs"

let u_poseidon n xs = unint "Poseidon" [n; xs]

let t_poseidon = tfq (qeq nu (u_poseidon nInputs inputs))

let poseidon =
  Circuit
    { name= "Poseidon"
    ; inputs= [("nInputs", tnat); ("inputs", tarr_tf nInputs)]
    ; outputs= [("out", t_poseidon)]
    ; dep= None
    ; body= star }

let u_eddsa_poseidon xs = unint "EdDSAPoseidonVerifier" xs

let enabled = v "enabled"

let ax = v "Ax"

let ay = v "Ay"

let s = v "S"

let r8x = v "R8x"

let r8y = v "R8y"

let m = v "M"

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
    ; dep=
        Some
          (qimply (qeq enabled f1)
             (lift (u_eddsa_poseidon [ax; ay; s; r8x; r8y; m])) )
    ; body= unit_val }
