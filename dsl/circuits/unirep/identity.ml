open Ast
open Dsl
open Circomlib__Poseidon

let nullifier = v "nullifier"

let trapdoor = v "trapdoor"

let t_identity_secret =
  tfq (qeq nu (u_poseidon z2 (const_array tf [nullifier; trapdoor])))

let identity_secret1 =
  Circuit
    { name= "IdentitySecret"
    ; inputs= [("nullifier", tf); ("trapdoor", tf)]
    ; outputs= [("out", t_identity_secret)]
    ; dep= None
    ; body= call "Poseidon" [z2; const_array tf [nullifier; trapdoor]] }

let t_identity_commitment_out nullifier trapdoor =
  tfq
    (qeq nu
       (u_poseidon z1
          (const_array tf
             [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ) ) )

let t_identity_commitment_secret nullifier trapdoor =
  tfq (qeq nu (u_poseidon z2 (const_array tf [nullifier; trapdoor])))

let identity_commitment =
  Circuit
    { name= "IdentityCommitment"
    ; inputs= [("nullifier", tf); ("trapdoor", tf)]
    ; outputs=
        [ ("secret", t_identity_commitment_secret nullifier trapdoor)
        ; ("out", t_identity_commitment_out nullifier trapdoor) ]
    ; dep= None
    ; body=
        make
          [ call "IdentitySecret" [nullifier; trapdoor]
          ; call "Poseidon"
              [ z1
              ; const_array tf
                  [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ] ] }
