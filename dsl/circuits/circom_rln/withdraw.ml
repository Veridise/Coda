open Ast
open Dsl
open Circomlib__Poseidon

let identity_secret = v "identitySecret"

let address = v "address"

let t_withdraw = tfq (qeq nu (u_poseidon z1 (const_array tf [identity_secret])))

let withdraw =
  Circuit
    { name= "Withdraw"
    ; inputs= [("identitySecret", tf); ("address", tf)]
    ; outputs= [("out", t_withdraw)]
    ; dep= None
    ; body= call "Poseidon" [z1; const_array tf [identity_secret]] }
