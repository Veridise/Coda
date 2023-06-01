open Ast
open Dsl
open Circomlib__Poseidon
open Notation

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

let t_identity_commitment_out nullifier trapdoor =
  tfq
    (qeq nu
       (u_poseidon z1
          (const_array tf
             [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ) ) )

let t_control reveal_nonce attester_id epoch nonce =
  tfq
    (qeq nu
       (fadds
          [ fmul reveal_nonce (fpow f2 (zn 232))
          ; fmul attester_id (fpow f2 (zn 72))
          ; fmul epoch (fpow f2 (zn 8))
          ; fmul reveal_nonce nonce ] ) )

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let t_n =
  TRef
    ( tint
    , QAnd
        ( lift (leq z0 nu)
        , qand (lift (nu <=. zn 254)) (lift (zn 254 <=. zsub1 CPLen)) ) )

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

let t_epoch_key_hasher_out identity_secret attester_id epoch nonce =
  t_epoch_key_hasher identity_secret attester_id epoch nonce

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let data_drop_1 data = drop data z1

let t_r path_index path_elements identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_hasher
          (u_zip path_index path_elements)
          (u_poseidon z3
             (const_array tf
                [ identity_secret
                ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
                ; u_state_tree_leaf (data_drop_1 data) (get data z0) ] ) ) ) )

let prevent_double_action =
  Circuit
    { name= "PreventDoubleAction"
    ; inputs=
        [ ("STATE_TREE_DEPTH", t_n)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", t_n)
        ; ("FIELD_COUNT", tnat)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf)
        ; ("sig_data", tf)
        ; ("identity_nullifier", tf)
        ; ("external_nullifier", tf)
        ; ("identity_trapdoor", tf)
        ; ("data", tarr_t_k tf (v "FIELD_COUNT")) ]
    ; outputs=
        [ ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce )
        ; ( "state_tree_root"
          , t_r (v "state_tree_indexes") (v "state_tree_elements")
              identity_secret attester_id epoch (v "data") )
        ; ( "nullifier"
          , tfq
              (qeq nu
                 (u_poseidon z2
                    (const_array tf
                       [v "identity_nullifier"; v "external_nullifier"] ) ) ) )
        ; ( "identity_commitment"
          , t_identity_commitment_out (v "identity_nullifier")
              (v "identity_trapdoor") )
        ; ( "control"
          , t_control (v "reveal_nonce") (v "attester_id") (v "epoch")
              (v "nonce") ) ]
    ; dep= None
    ; body=
        elet "nullifier"
          (call "Poseidon"
             [ zn 2
             ; const_array tf [v "identity_nullifier"; v "external_nullifier"]
             ] )
          (match_with' ["identity_secret"; "out"]
             (call "IdentityCommitment"
                [v "identity_nullifier"; v "identity_trapdoor"] )
             (elet "leaf_hasher"
                (call "StateTreeLeaf"
                   [ v "FIELD_COUNT"
                   ; v "data"
                   ; v "identity_secret"
                   ; v "attester_id"
                   ; v "epoch" ] )
                (elet "merkletree"
                   (call "MerkleTreeInclusionProof"
                      [ v "STATE_TREE_DEPTH"
                      ; v "leaf_hasher"
                      ; v "state_tree_indexes"
                      ; v "state_tree_elements" ] )
                   (match_with' ["control"; "epoch_key"]
                      (call "EpochKeyLite"
                         [ v "FIELD_COUNT"
                         ; v "EPOCH_KEY_NONCE_PER_EPOCH"
                         ; v "identity_secret"
                         ; v "reveal_nonce"
                         ; v "attester_id"
                         ; v "epoch"
                         ; v "nonce" ] )
                      (make
                         [ v "epoch_key"
                         ; v "merkletree"
                         ; v "nullifier"
                         ; v "out"
                         ; v "control" ] ) ) ) ) ) }
