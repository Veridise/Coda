open Ast
open Dsl
open Circomlib__Poseidon
open Notation
(* open Typecheck *)

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

let identity_nullifier = v "identity_nullifier"

let identity_trapdoor = v "identity_trapdoor"

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
        elet "all_0" (consts_n field_count f0)
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

let t_epoch_key_hasher_out identity_secret attester_id epoch nonce =
  t_epoch_key_hasher identity_secret attester_id epoch nonce

let t_control reveal_nonce attester_id epoch nonce =
  tfq
    (qeq nu
       (fadds
          [ fmul reveal_nonce (fpow f2 (zn 232))
          ; fmul attester_id (fpow f2 (zn 72))
          ; fmul epoch (fpow f2 (zn 8))
          ; fmul reveal_nonce nonce ] ) )

let epoch_key_lite =
  Circuit
    { name= "EpochKeyLite"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ( "EPOCH_KEY_NONCE_PER_EPOCH"
          , tnat_e (leq nu (zsub (zpow (zn 2) (zn 8)) z1)) )
        ; ("identity_secret", tf)
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf) ]
    ; outputs=
        [ ("control", t_control reveal_nonce attester_id epoch nonce)
        ; ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce ) ]
    ; dep= None
    ; body=
        elet "reveal_nonce_check"
          (assert_eq (fmul reveal_nonce (fsub reveal_nonce f1)) f0)
          (elet "attester_id_check"
             (call "Num2Bits" [zn 160; v "attester_id"])
             (elet "epoch_bits"
                (call "Num2Bits" [zn 48; v "epoch"])
                (elet "nonce_range_check"
                   (call "Num2Bits" [zn 8; v "nonce"])
                   (elet "nonce_lt"
                      (call "LessThan"
                         [zn 8; v "nonce"; nat2f (v "EPOCH_KEY_NONCE_PER_EPOCH")] )
                      (elet "u0"
                         (assert_eq (v "nonce_lt") f1)
                         (elet "ctrl"
                            (fadds
                               [ fmul reveal_nonce (fpow f2 (zn 232))
                               ; fmul attester_id (fpow f2 (zn 72))
                               ; fmul epoch (fpow f2 (zn 8))
                               ; fmul reveal_nonce nonce ] )
                            (make
                               [ v "ctrl"
                               ; call "EpochKeyHasher"
                                   [ v "identity_secret"
                                   ; v "attester_id"
                                   ; v "epoch"
                                   ; v "nonce" ] ] ) ) ) ) ) ) ) }

let t_alias_check = lift (lt (toUZ (as_le_f (v "in"))) CPrime)

let alias_check =
  Circuit
    { name= "AliasCheck"
    ; inputs= [("in", tarr_t_k tf (zn 254))]
    ; outputs= []
    ; dep= Some t_alias_check
    ; body= unit_val }

let t_n =
  TRef
    ( tint
    , QAnd
        ( lift (leq z0 nu)
        , qand (lift (nu <=. zn 254)) (lift (zn 254 <=. zsub1 CPLen)) ) )

let t_upper_less_than_out =
  tfq
    (ind_dec nu
       (lt
          (zdiv (toUZ (get (v "in_") (zn 0))) (zpow z2 (nsub (zn 254) (v "n"))))
          (zdiv (toUZ (get (v "in_") (zn 1))) (zpow z2 (nsub (zn 254) (v "n")))) ) )

let upper_less_than =
  Circuit
    { name= "UpperLessThan"
    ; inputs= [("n", t_n); ("in_", tarr_t_k tf z2)]
    ; outputs= [("out", t_upper_less_than_out)]
    ; dep= None
    ; body=
        elet "bits_0"
          (call "Num2Bits" [zn 254; get (v "in_") (zn 0)])
          (elet "bits_1"
             (call "Num2Bits" [zn 254; get (v "in_") (zn 1)])
             (elet "alias0"
                (call "AliasCheck" [v "bits_0"])
                (elet "alias1"
                   (call "AliasCheck" [v "bits_1"])
                   (elet "upper_bits_0"
                      (call "Bits2Num"
                         [v "n"; drop (v "bits_0") (nsub (zn 254) (v "n"))] )
                      (elet "upper_bits_1"
                         (call "Bits2Num"
                            [v "n"; drop (v "bits_1") (nsub (zn 254) (v "n"))] )
                         (elet "lt"
                            (call "LessThan"
                               [v "n"; v "upper_bits_0"; v "upper_bits_1"] )
                            (v "lt") ) ) ) ) ) ) }

let t_repl_field_equal_out =
  tfq
    (ind_dec nu
       (eq
          (zmod
             (toUZ (get (v "in_") (zn 0)))
             (zpow z2 (nsub (zn 254) (v "REPL_NONCE_BITS"))) )
          (zmod
             (toUZ (get (v "in_") (zn 1)))
             (zpow z2 (nsub (zn 254) (v "REPL_NONCE_BITS"))) ) ) )

let repl_field_equal =
  Circuit
    { name= "ReplFieldEqual"
    ; inputs= [("REPL_NONCE_BITS", t_n); ("in_", tarr_t_k tf z2)]
    ; outputs= [("out", t_repl_field_equal_out)]
    ; dep= None
    ; body=
        elet "bits_0"
          (call "Num2Bits" [zn 254; get (v "in_") (zn 0)])
          (elet "bits_1"
             (call "Num2Bits" [zn 254; get (v "in_") (zn 1)])
             (elet "alias0"
                (call "AliasCheck" [v "bits_0"])
                (elet "alias1"
                   (call "AliasCheck" [v "bits_1"])
                   (elet "repl_bits_0"
                      (call "Bits2Num"
                         [ nsub (zn 254) (v "REPL_NONCE_BITS")
                         ; take (v "bits_0")
                             (nsub (zn 254) (v "REPL_NONCE_BITS")) ] )
                      (elet "repl_bits_1"
                         (call "Bits2Num"
                            [ nsub (zn 254) (v "REPL_NONCE_BITS")
                            ; take (v "bits_1")
                                (nsub (zn 254) (v "REPL_NONCE_BITS")) ] )
                         (elet "eq"
                            (call "IsEqual" [v "repl_bits_0"; v "repl_bits_1"])
                            (v "eq") ) ) ) ) ) ) }

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

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

let epoch_key =
  Circuit
    { name= "EpochKey"
    ; inputs=
        [ ("STATE_TREE_DEPTH", t_n)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", t_n)
        ; ("FIELD_COUNT", tnat)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("identity_secret", tf)
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf)
        ; ("data", tarr_t_k tf (v "FIELD_COUNT"))
        ; ("sig_data", tf) ]
    ; outputs=
        [ ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce )
        ; ( "state_tree_root"
          , t_r (v "state_tree_indexes") (v "state_tree_elements")
              identity_secret attester_id epoch (v "data") )
        ; ("control", t_control reveal_nonce attester_id epoch nonce) ]
    ; dep= None
    ; body=
        elet "leaf_hasher"
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
                (make [v "epoch_key"; v "merkletree"; v "control"]) ) ) }

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

(* (1) binary prove_graffiti /\ binary prove_min_rep /\ binary prove_max_rep /\ binary prove_zero_rep
   (2) min_rep < 2^64 /\ max_rep < 2^64 /\ epoch < 2^48 /\ attester_id < 2^160
   (3) control[1] = prove_graffiti * 2^131 + prove_zero_rep * 2^130 + prove_max_rep * 2^129 + prove_min_rep * 2^128 + max_rep * 2^64 + min_rep
*)
let u_prove_reputation =
  ands
    [ lift (is_binary (v "prove_graffiti"))
    ; lift (is_binary (v "prove_min_rep"))
    ; lift (is_binary (v "prove_max_rep"))
    ; lift (is_binary (v "prove_zero_rep"))
    ; lift ( (toUZ (v "min_rep")) <. (zpow (zn 2) (zn 64)))
    ; lift ( (toUZ (v "max_rep")) <. (zpow (zn 2) (zn 64)))
    ; lift ( (toUZ (v "epoch")) <. (zpow (zn 2) (zn 48)))
    ; lift ( (toUZ (v "attester_id")) <. (zpow (zn 2) (zn 160))) ]

let u_control =
  ands
    [ qeq (get nu z0)
        (fadds
           [ fmul reveal_nonce (fpow f2 (zn 232))
           ; fmul attester_id (fpow f2 (zn 72))
           ; fmul epoch (fpow f2 (zn 8))
           ; fmul reveal_nonce nonce ] )
    ; qeq (get nu z1)
        (fadds
           [ fmuls [v "prove_graffiti"; fpow (fn 2) (zn 131)]
           ; fmuls [v "prove_zero_rep"; fpow (fn 2) (zn 130)]
           ; fmuls [v "prove_max_rep"; fpow (fn 2) (zn 129)]
           ; fmuls [v "prove_min_rep"; fpow (fn 2) (zn 128)]
           ; fmuls [v "max_rep"; fpow (fn 2) (zn 64)]
           ; v "min_rep" ] ) ]

let prove_reputation =
  Circuit
    { name= "ProveReputation"
    ; inputs=
        [ ("STATE_TREE_DEPTH", t_n)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", t_n)
        ; ("SUM_FIELD_COUNT", tnat_e (nu <. v "FIELD_COUNT"))
        ; ("FIELD_COUNT", tnat)
        ; ("REPL_NONCE_BITS", t_n)
        ; ("identity_secret", tf)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("data", tarr_t_k tf (v "FIELD_COUNT"))
        ; ("prove_graffiti", tf)
        ; ("graffiti", tf)
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf)
        ; ("min_rep", tf)
        ; ("max_rep", tf)
        ; ("prove_min_rep", tf)
        ; ("prove_max_rep", tf)
        ; ("prove_zero_rep", tf)
        ; ("sig_data", tf) ]
    ; outputs=
        [ ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce )
        ; ( "state_tree_root"
          , t_r (v "state_tree_indexes") (v "state_tree_elements")
              identity_secret attester_id epoch (v "data") )
        ; ("control", tarr_t_q_k tf u_control z2) ]
    ; dep= Some u_prove_reputation
    ; body=
        elet "min_rep_bits"
          (call "Num2Bits" [zn 64; v "min_rep"])
          (elet "max_rep_bits"
             (call "Num2Bits" [zn 64; v "max_rep"])
             (elet "u0"
                (assert_eq
                   (fmul (v "prove_graffiti") (fsub (v "prove_graffiti") f1))
                   f0 )
                (elet "u1"
                   (assert_eq
                      (fmul (v "prove_min_rep") (fsub (v "prove_min_rep") f1))
                      f0 )
                   (elet "u2"
                      (assert_eq
                         (fmul (v "prove_max_rep")
                            (fsub (v "prove_max_rep") f1) )
                         f0 )
                      (elet "u3"
                         (assert_eq
                            (fmul (v "prove_zero_rep")
                               (fsub (v "prove_zero_rep") f1) )
                            f0 )
                         (elet "control_1"
                            (fadds
                               [ fmuls [v "prove_graffiti"; fpow (fn 2) (zn 131)]
                               ; fmuls [v "prove_zero_rep"; fpow (fn 2) (zn 130)]
                               ; fmuls [v "prove_max_rep"; fpow (fn 2) (zn 129)]
                               ; fmuls [v "prove_min_rep"; fpow (fn 2) (zn 128)]
                               ; fmuls [v "max_rep"; fpow (fn 2) (zn 64)]
                               ; v "min_rep" ] )
                            (elet "epoch_range_check"
                               (call "Num2Bits" [zn 48; v "epoch"])
                               (elet "attester_id_check"
                                  (call "Num2Bits" [zn 160; v "attester_id"])
                                  (elet "epoch_key_gen"
                                     (call "EpochKey"
                                        [ v "STATE_TREE_DEPTH"
                                        ; v "EPOCH_KEY_NONCE_PER_EPOCH"
                                        ; v "FIELD_COUNT"
                                        ; v "state_tree_indexes"
                                        ; v "state_tree_elements"
                                        ; v "identity_secret"
                                        ; v "reveal_nonce"
                                        ; v "attester_id"
                                        ; v "epoch"
                                        ; v "nonce"
                                        ; v "data"
                                        ; v "sig_data" ] )
                                     (elet "epoch_key"
                                        (tget (v "epoch_key_gen") 0)
                                        (elet "state_tree_root"
                                           (tget (v "epoch_key_gen") 1)
                                           (elet "control_0"
                                              (tget (v "epoch_key_gen") 2)
                                              (elet "data_0_check"
                                                 (call "Num2Bits"
                                                    [zn 64; get (v "data") z0] )
                                                 (elet "data_1_check"
                                                    (call "Num2Bits"
                                                       [zn 64; get (v "data") z1] )
                                                    (elet "min_rep_check"
                                                       (call "GreaterEqThan"
                                                          [ zn 66
                                                          ; get (v "data") z0
                                                          ; fadd
                                                              (get (v "data") z1)
                                                              (v "min_rep") ] )
                                                       (elet
                                                          "if_not_prove_min_rep"
                                                          (call "IsZero"
                                                             [v "prove_min_rep"] )
                                                          (elet
                                                             "output_rep_check"
                                                             (call "Or"
                                                                [ v
                                                                    "if_not_prove_min_rep"
                                                                ; v
                                                                    "min_rep_check"
                                                                ] )
                                                             (elet "u4"
                                                                (assert_eq
                                                                   (v
                                                                      "output_rep_check" )
                                                                   f1 )
                                                                (elet
                                                                   "max_rep_check"
                                                                   (call
                                                                      "GreaterEqThan"
                                                                      [ zn 66
                                                                      ; get
                                                                          (v
                                                                             "data" )
                                                                          z1
                                                                      ; fadd
                                                                          (get
                                                                             (v
                                                                                "data" )
                                                                             z0 )
                                                                          (v
                                                                             "max_rep" )
                                                                      ] )
                                                                   (elet
                                                                      "if_not_prove_max_rep"
                                                                      (call
                                                                         "IsZero"
                                                                         [ v
                                                                             "prove_max_rep"
                                                                         ] )
                                                                      (elet
                                                                         "max_rep_check_out"
                                                                         (call
                                                                            "Or"
                                                                            [ v
                                                                                "if_not_prove_max_rep"
                                                                            ; v
                                                                                "max_rep_check"
                                                                            ] )
                                                                         (elet
                                                                            "u5"
                                                                            (assert_eq
                                                                               (v
                                                                                "max_rep_check_out" )
                                                                               f1 )
                                                                            (elet
                                                                               "zero_rep_check"
                                                                               (call
                                                                                "IsEqual"
                                                                                [ 
                                                                                get
                                                                                (
                                                                                v
                                                                                "data" )
                                                                                z0
                                                                                ; 
                                                                                get
                                                                                (
                                                                                v
                                                                                "data" )
                                                                                z1
                                                                                ] )
                                                                               (elet
                                                                                "if_not_prove_zero_rep"
                                                                                (
                                                                                call
                                                                                "IsZero"
                                                                                [ 
                                                                                v
                                                                                "prove_zero_rep"
                                                                                ] )
                                                                                (
                                                                                elet
                                                                                "zero_rep_check_out"
                                                                                (
                                                                                call
                                                                                "Or"
                                                                                [ 
                                                                                v
                                                                                "if_not_prove_zero_rep"
                                                                                ; 
                                                                                v
                                                                                "zero_rep_check"
                                                                                ] )
                                                                                (
                                                                                elet
                                                                                "u6"
                                                                                (
                                                                                assert_eq
                                                                                (
                                                                                v
                                                                                "zero_rep_check_out" )
                                                                                f1 )
                                                                                (
                                                                                elet
                                                                                "if_not_check_graffiti"
                                                                                (
                                                                                call
                                                                                "IsZero"
                                                                                [ 
                                                                                v
                                                                                "prove_graffiti"
                                                                                ] )
                                                                                (
                                                                                elet
                                                                                "repl_field_equal"
                                                                                (
                                                                                call
                                                                                "ReplFieldEqual"
                                                                                [ 
                                                                                v
                                                                                "REPL_NONCE_BITS"
                                                                                ; 
                                                                                cons
                                                                                (
                                                                                v
                                                                                "graffiti" )
                                                                                (
                                                                                cons
                                                                                (
                                                                                get
                                                                                (
                                                                                v
                                                                                "data" )
                                                                                (
                                                                                v
                                                                                "SUM_FIELD_COUNT" ) )
                                                                                cnil )
                                                                                ] )
                                                                                (
                                                                                elet
                                                                                "check_graffiti"
                                                                                (
                                                                                call
                                                                                "Or"
                                                                                [ 
                                                                                v
                                                                                "if_not_check_graffiti"
                                                                                ; 
                                                                                v
                                                                                "repl_field_equal"
                                                                                ] )
                                                                                (
                                                                                elet
                                                                                "u7"
                                                                                (
                                                                                assert_eq
                                                                                (
                                                                                v
                                                                                "check_graffiti" )
                                                                                f1 )
                                                                                (
                                                                                make
                                                                                [ 
                                                                                v
                                                                                "epoch_key"
                                                                                ; 
                                                                                v
                                                                                "state_tree_root"
                                                                                ; 
                                                                                cons
                                                                                (
                                                                                v
                                                                                "control_0" )
                                                                                (
                                                                                cons
                                                                                (
                                                                                v
                                                                                "control_1" )
                                                                                cnil )
                                                                                ] ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
    }
