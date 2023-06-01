open Ast
open Dsl
open Circomlib__Poseidon

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

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
