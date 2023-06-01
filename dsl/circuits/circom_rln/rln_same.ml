open Ast
open Dsl
open Circomlib__Poseidon
open Notation

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let identity_secret = v "identitySecret"

let user_message_limit = v "userMessageLimit"

let message_id = v "messageId"

let path_elements = v "pathElements"

let identity_path_index = v "identityPathIndex"

let external_nullifier = v "externalNullifier"

let x = v "x"

let t_root identity_secret path_elements identity_path_index =
  tfq
    (qeq nu
       (u_hasher
          (u_zip identity_path_index path_elements)
          (u_poseidon z1 (const_array tf [identity_secret])) ) )

let t_y identity_secret message_id x external_nullifier =
  tfq
    (qeq nu
       (fadds
          [ identity_secret
          ; fmul
              (u_poseidon z3
                 (const_array tf
                    [identity_secret; external_nullifier; message_id] ) )
              x ] ) )

let t_nullifier identity_secret message_id external_nullifier =
  tfq
    (qeq nu
       (u_poseidon z1
          (const_array tf
             [ u_poseidon z3
                 (const_array tf
                    [identity_secret; external_nullifier; message_id] ) ] ) ) )

let rln =
  Circuit
    { name= "RLN_same"
    ; inputs=
        [ ("DEPTH", tnat)
        ; ("LIMIT_BIT_SIZE", attaches [lift (nu <. zn 253)] tnat)
        ; ("identitySecret", tf)
        ; ("messageId", tf)
        ; ("pathElements", tarr_t_k tf (v "DEPTH"))
        ; ("identityPathIndex", tarr_t_k tf (v "DEPTH"))
        ; ("x", tf)
        ; ("externalNullifier", tf)
        ; ("messageLimit", tf) ]
    ; outputs=
        [ ("y", t_y identity_secret message_id x external_nullifier)
        ; ("root", t_root identity_secret path_elements identity_path_index)
        ; ( "nullifier"
          , t_nullifier identity_secret message_id external_nullifier ) ]
    ; dep= None
    ; body=
        elet "identityCommitment"
          (call "Poseidon" [z1; const_array tf [identity_secret]])
          (elet "root"
             (call "MerkleTreeInclusionProof"
                [ v "DEPTH"
                ; v "identityCommitment"
                ; v "identityPathIndex"
                ; v "pathElements" ] )
             (elet "rangeCheck"
                (call "RangeCheck"
                   [v "LIMIT_BIT_SIZE"; v "messageId"; v "messageLimit"] )
                (elet "a1"
                   (call "Poseidon"
                      [ z3
                      ; const_array tf
                          [ v "identitySecret"
                          ; v "externalNullifier"
                          ; v "messageId" ] ] )
                   (elet "y"
                      (fadd (v "identitySecret") (fmul (v "a1") (v "x")))
                      (elet "nullifier"
                         (call "Poseidon" [z1; const_array tf [v "a1"]])
                         (make [v "y"; v "root"; v "nullifier"]) ) ) ) ) ) }
