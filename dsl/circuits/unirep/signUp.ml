open Ast
open Dsl
open Circomlib__Poseidon

let identity_nullifier = v "identity_nullifier"

let identity_trapdoor = v "identity_trapdoor"

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let data_drop_1 data = drop data z1

let t_state_tree_leaf identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_poseidon z3
          (const_array tf
             [ identity_secret
             ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
             ; u_state_tree_leaf (data_drop_1 data) (get data z0) ] ) ) )

let t_identity_commitment_out nullifier trapdoor =
  tfq
    (qeq nu
       (u_poseidon z1
          (const_array tf
             [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ) ) )

let signup =
  Circuit
    { name= "Signup"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("identity_nullifier", tf)
        ; ("identity_trapdoor", tf) ]
    ; outputs=
        [ ( "identity_commitment"
          , t_identity_commitment_out identity_nullifier identity_trapdoor )
        ; ( "state_tree_leaf"
          , t_state_tree_leaf
              (u_poseidon z2
                 (const_array tf [identity_nullifier; identity_trapdoor]) )
              attester_id epoch (v "all_0") ) ]
    ; dep= None
    ; body=
        elet "all_0"
          (consts_n (v "FIELD_COUNT") f0)
          (match_with' ["ic_secret"; "ic_out"]
             (call "IdentityCommitment" [identity_nullifier; identity_trapdoor])
             (make
                [ v "ic_out"
                ; call "StateTreeLeaf"
                    [ v "FIELD_COUNT"
                    ; v "all_0"
                    ; v "ic_secret"
                    ; v "attester_id"
                    ; v "epoch" ] ] ) ) }
