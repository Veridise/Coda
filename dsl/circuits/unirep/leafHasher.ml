open Ast
open Dsl
open Circomlib__Poseidon

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

(* EpochKeyHasher *)

let t_epoch_key_hasher identity_secret attester_id epoch nonce =
  tfq
    (qeq nu
       (u_poseidon z2
          (const_array tf
             [ identity_secret
             ; fadds
                 [ attester_id
                 ; fmul (fpow f2 (zn 160)) epoch
                 ; fmul (fpow f2 (zn 208)) nonce ] ] ) ) )

let epoch_key_hasher =
  Circuit
    { name= "EpochKeyHasher"
    ; inputs=
        [ ("identity_secret", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf) ]
    ; outputs=
        [("out", t_epoch_key_hasher identity_secret attester_id epoch nonce)]
    ; dep= None
    ; body=
        call "Poseidon"
          [ z2
          ; const_array tf
              [ identity_secret
              ; fadds
                  [ attester_id
                  ; fmul (fpow f2 (zn 160)) epoch
                  ; fmul (fpow f2 (zn 208)) nonce ] ] ] }

let field_count = v "FIELD_COUNT"

let lam_eptl =
  lama "i" tint
    (lama "x" tf
       (call "Poseidon" [z2; const_array tf [v "x"; get (v "data") (v "i")]]) )

let u_epoch_tree_leaf a b = unint "u_epoch_tree_leaf" [a; b]

let inv_eptl i =
  tfq (qeq nu (u_epoch_tree_leaf (take (v "data") i) (v "epoch_key")))

let t_epoch_tree_leaf =
  tfq (qeq nu (u_epoch_tree_leaf (v "data") (v "epoch_key")))

let epoch_tree_leaf =
  Circuit
    { name= "EpochTreeLeaf"
    ; inputs=
        [("FIELD_COUNT", tnat); ("epoch_key", tf); ("data", tarr_tf field_count)]
    ; outputs= [("out", t_epoch_tree_leaf)]
    ; dep= None
    ; body= iter z0 field_count lam_eptl ~init:(v "epoch_key") ~inv:inv_eptl }

let data_drop_1 data = drop data z1

let lam_stl =
  lama "i" tint
    (lama "x" tf
       (call "Poseidon"
          [z2; const_array tf [v "x"; get (data_drop_1 (v "data")) (v "i")]] ) )

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let inv_stl i =
  tfq
    (qeq nu
       (u_state_tree_leaf (take (data_drop_1 (v "data")) i) (get (v "data") z0)) )

let t_state_tree_leaf identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_poseidon z3
          (const_array tf
             [ identity_secret
             ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
             ; u_state_tree_leaf (data_drop_1 data) (get data z0) ] ) ) )

let state_tree_leaf =
  Circuit
    { name= "StateTreeLeaf"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ("data", tarr_tf field_count)
        ; ("identity_secret", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf) ]
    ; outputs=
        [("out", t_state_tree_leaf identity_secret attester_id epoch (v "data"))]
    ; dep= None
    ; body=
        elet "out1"
          (iter z0 (nsub field_count z1) lam_stl
             ~init:(get (v "data") z0)
             ~inv:inv_stl )
          (call "Poseidon"
             [ z3
             ; const_array tf
                 [ identity_secret
                 ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
                 ; v "out1" ] ] ) }
