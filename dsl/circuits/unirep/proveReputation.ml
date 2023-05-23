open Ast
open Dsl
open Circomlib__Poseidon
open Notation

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

let t_n =
  TRef
    ( tint
    , QAnd
        ( lift (leq z0 nu)
        , qand (lift (nu <=. zn 254)) (lift (zn 254 <=. zsub1 CPLen)) ) )

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let data_drop_1 data = drop data z1

let u_prove_reputation =
  ands
    [ lift (is_binary (v "prove_graffiti"))
    ; lift (is_binary (v "prove_min_rep"))
    ; lift (is_binary (v "prove_max_rep"))
    ; lift (is_binary (v "prove_zero_rep"))
    ; lift (toUZ (v "min_rep") <. zpow (zn 2) (zn 64))
    ; lift (toUZ (v "max_rep") <. zpow (zn 2) (zn 64))
    ; lift (toUZ (v "epoch") <. zpow (zn 2) (zn 48))
    ; lift (toUZ (v "attester_id") <. zpow (zn 2) (zn 160)) ]

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

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

let t_epoch_key_hasher_out identity_secret attester_id epoch nonce =
  t_epoch_key_hasher identity_secret attester_id epoch nonce

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
