open Ast
open Dsl
open Notation

let b0 = v "b0"

let b1 = v "b1"

let c = v "c"

let i = v "i"

let s = v "s"

let vin = v "in"

let base = v "base"

let nBits = v "nBits"

let in0 = v "in0"

let in1 = v "in1"

let out = v "out"

let bit = v "bit"

let bit1 = v "bit1"

let bit2 = v "bit2"

let vval = v "val"

let sum = v "sum"

let carry = v "carry"

let carry_out = v "carry_out"

(* fulladder *)

let fulladder =
  Circuit
    { name= "fulladder"
    ; inputs= [("bit1", tf_binary); ("bit2", tf_binary); ("carry", tf_binary)]
    ; outputs= [("val", tf_binary); ("carry_out", tf_binary)]
    ; dep= Some ((f2 *% carry_out) +% vval ==. bit1 +% bit2 +% carry)
    ; body=
        elet "val" star
          (elet "u0"
             (assert_eq (vval *% (vval -% f1)) f0)
             (elet "u1"
                (assert_eq (toUZ vval) (zmod (toUZ (bit1 +% bit2 +% carry)) z2))
                (elet "carry_out" star
                   (elet "u2"
                      (assert_eq (carry_out *% (carry_out -% f1)) f0)
                      (elet "u3"
                         (assert_eq (toUZ carry_out)
                            (zdiv (toUZ (bit1 +% bit2 +% carry)) z2) )
                         (pair vval carry_out) ) ) ) ) ) }

(* onlycarry *)

let t_val_oc = tfq (toUZ nu ==. zmod (toUZ (bit +% carry)) z2)

let t_carry_out_oc = tfq (toUZ nu ==. zdiv (toUZ (bit +% carry)) z2)

let onlycarry =
  Circuit
    { name= "onlycarry"
    ; inputs= [("bit", tf_binary); ("carry", tf_binary)]
    ; outputs= [("val", t_val_oc); ("carry_out", t_carry_out_oc)]
    ; dep= Some ((f2 *% carry_out) +% vval ==. bit +% carry)
    ; body=
        elet "val" star
          (elet "u0"
             (assert_eq (vval *% (vval -% f1)) f0)
             (elet "u1"
                (assert_eq (toUZ vval) (zmod (toUZ (bit +% carry)) z2))
                (elet "carry_out" star
                   (elet "u2"
                      (assert_eq (carry_out *% (carry_out -% f1)) f0)
                      (elet "u3"
                         (assert_eq (toUZ carry_out)
                            (zdiv (toUZ (bit +% carry)) z2) )
                         (pair vval carry_out) ) ) ) ) ) }

(* BinAdd *)

let inv_bin_add i =
  refine
    (ttuple [tarr_t_k tf_binary i; tf_binary])
    ( as_le_f (concat (tfst nu) (consts [tsnd nu]))
    ==. as_le_f (take in0 i) +% as_le_f (take in1 i) )

let t_bin_add =
  attach
    (as_le_f nu ==. as_le_f in0 +% as_le_f in1)
    (tarr_t_k tf_binary (nBits +. z1))

let bin_add =
  Circuit
    { name= "BinAdd"
    ; inputs=
        [ ("nBits", tnat)
        ; ("in0", tarr_t_k tf_binary nBits)
        ; ("in1", tarr_t_k tf_binary nBits) ]
    ; outputs= [("out", t_bin_add)]
    ; dep= None
    ; body=
        match_with' ["sum"; "carry"]
          (iter z0 nBits
             ~init:(pair (push cnil) f0)
             ~inv:inv_bin_add
             (lama "i" tint
                (lama_match
                   [("s", tarr tf); ("c", tf)]
                   (elets
                      [("b0", get in0 i); ("b1", get in1 i)]
                      (match_with' ["val"; "carry_out"]
                         (call "fulladder" [b0; b1; c])
                         (pair
                            (push (concat s (const_array tf [vval])))
                            carry_out ) ) ) ) ) )
          (push (concat sum (consts [carry]))) }

(* LessThanPower *)

let t_base_ltp =
  TRef
    ( tint
    , qand
        (lift (leq z252 (zsub1 CPLen)))
        (qand
           (lift (leq z0 nu))
           (lift (leq (toUZ (fpow f2 base)) (zsub1 (zpow z2 z252)))) ) )

let t_in_ltp = tfq (lift (leq (toUZ nu) (zsub1 (zpow z2 z252))))

let t_ltp = tfq (ind_dec nu (lt (toUZ vin) (zpow z2 base)))

let less_than_power =
  Circuit
    { name= "LessThanPower"
    ; inputs= [("base", t_base_ltp); ("in", t_in_ltp)]
    ; outputs= [("out", t_ltp)]
    ; dep= None
    ; body= call "LessThan" [z252; vin; fpow f2 base] }

(* LessThanBounded *)

let t_ltb = tfq (ind_dec nu (lt (toUZ in0) (toUZ in1)))

let less_than_bounded =
  Circuit
    { name= "LessThanBounded"
    ; inputs= [("base", t_base_ltp); ("in0", t_in_ltp); ("in1", t_in_ltp)]
    ; outputs= [("out", t_ltb)]
    ; dep= None
    ; body=
        elet "_x"
          (call "LessThanPower" [base; in0])
          (elet "_y"
             (call "LessThanPower" [base; in1])
             (call "LessThan" [z252; in0; in1]) ) }
