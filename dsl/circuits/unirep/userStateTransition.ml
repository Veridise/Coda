open Ast
open Dsl
open Circomlib__Poseidon

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let data_drop_1 data = drop data z1

let t_r' path_index path_elements identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_hasher
          (u_zip path_index path_elements)
          (u_poseidon z2
             (const_array tf
                [ u_hasher
                    (u_zip (v "state_tree_indexes") (v "state_tree_elements"))
                    (u_poseidon z3
                       (const_array tf
                          [ identity_secret
                          ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
                          ; u_state_tree_leaf (data_drop_1 data) (get data z0)
                          ] ) )
                ; v "epoch_tree_root" ] ) ) ) )

let user_state_transition =
  Circuit
    { name= "UserStateTransition"
    ; inputs=
        [ ("STATE_TREE_DEPTH", tnat)
        ; ("EPOCH_TREE_DEPTH", tnat)
        ; ("HISTORY_TREE_DEPTH", tnat)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", tnat)
        ; ("FIELD_COUNT", tnat)
        ; ("SUM_FIELD_COUNT", tnat)
        ; ("REPL_NONCE_BITS", tnat)
        ; ("from_epoch", tf)
        ; ("to_epoch", tf)
        ; ("identity_secret", tf)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("history_tree_indices", tarr_t_k tf (v "HISTORY_TREE_DEPTH"))
        ; ("history_tree_elements", tarr_t_k tf (v "HISTORY_TREE_DEPTH"))
        ; ("attester_id", tf)
        ; ("data", tarr_t_k tf (v "FIELD_COUNT"))
        ; ( "new_data"
          , tarr_t_k
              (tarr_t_k tf (v "FIELD_COUNT"))
              (v "EPOCH_KEY_NONCE_PER_EPOCH") )
        ; ("epoch_tree_root", tf)
        ; ( "epoch_tree_elements"
          , tarr_t_k
              (tarr_t_k tf (v "EPOCH_TREE_DEPTH"))
              (v "EPOCH_KEY_NONCE_PER_EPOCH") )
        ; ( "epoch_tree_indices"
          , tarr_t_k
              (tarr_t_k tf (v "EPOCH_TREE_DEPTH"))
              (v "EPOCH_KEY_NONCE_PER_EPOCH") ) ]
    ; outputs=
        [ ( "history_tree_root"
          , t_r' (v "history_tree_indices")
              (v "history_tree_elements")
              identity_secret attester_id (v "from_epoch") (v "data") )
        ; ("state_tree_leaf", tf)
        ; ("epks", tarr_t_k tf (v "EPOCH_KEY_NONCE_PER_EPOCH")) ]
    ; dep= None
    ; body=
        elet "from_epoch_check"
          (call "Num2Bits" [zn 48; v "from_epoch"])
          (elet "to_epoch_check"
             (call "Num2Bits" [zn 48; v "to_epoch"])
             (elet "epoch_check"
                (call "GreaterThan" [zn 48; v "to_epoch"; v "from_epoch"])
                (elet "u0"
                   (assert_eq (v "epoch_check") f1)
                   (elet "attester_id_check"
                      (call "Num2Bits" [zn 160; v "attester_id"])
                      (elet "leaf_hasher"
                         (call "StateTreeLeaf"
                            [ v "FIELD_COUNT"
                            ; v "data"
                            ; identity_secret
                            ; attester_id
                            ; v "from_epoch" ] )
                         (elet "state_merkletree"
                            (call "MerkleTreeInclusionProof"
                               [ v "STATE_TREE_DEPTH"
                               ; v "leaf_hasher"
                               ; v "state_tree_indexes"
                               ; v "state_tree_elements" ] )
                            (elet "history_leaf_hasher"
                               (call "Poseidon"
                                  [ z2
                                  ; const_array tf
                                      [v "state_merkletree"; v "epoch_tree_root"]
                                  ] )
                               (elet "history_merkletree"
                                  (call "MerkleTreeInclusionProof"
                                     [ v "HISTORY_TREE_DEPTH"
                                     ; v "history_leaf_hasher"
                                     ; v "history_tree_indices"
                                     ; v "history_tree_elements" ] )
                                  (make
                                     [ v "history_merkletree"
                                     ; f0
                                     ; consts_n
                                         (v "EPOCH_KEY_NONCE_PER_EPOCH")
                                         f0 ] ) ) ) ) ) ) ) ) ) }
