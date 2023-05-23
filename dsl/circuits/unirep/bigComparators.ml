open Ast
open Dsl
open Notation

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
