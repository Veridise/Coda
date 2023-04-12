open Ast
open Dsl
open Notation
open Circomlib.Poseidon

let z8 = zn 8

let z16 = zn 16

let z40 = zn 40

let z216 = zn 216

let z256 = zn 256

let d = v "d"

let i = v "i"

let j = v "j"

let t = v "t"

let x = v "x"

let z = v "z"

let eq = v "eq"

let l = v "lt"

let gt = v "gt"

let iN = v "in"

let vin = v "in"

let out = v "out"

let n2b = v "n2b"

let count = v "count"

let value = v "value"

let v0 = get value z0

let index = v "index"

let claim = v "claim"

let valueArraySize = v "valueArraySize"

let op = v "operator"

let claimsTreeRoot = v "claimsTreeRoot"

let revTreeRoot = v "revTreeRoot"

let rootsTreeRoot = v "rootsTreeRoot"

(* IN *)

let t_sz =
  TRef
    ( tint
    , qand
        (lift (z2 <. CPrime))
        (qand (lift (z252 <=. zsub1 CPLen)) (lift (z0 <. nu))) )

let q_IN = qexists_e "i" z0 valueArraySize (get value i =. vin)

let t_IN = tfq (q_ind_dec nu q_IN)

let lam_IN =
  lama "i" tint
    (lama "x" tf
       (elet "ise" (call "IsEqual" [vin; get value i]) (fadd x (v "ise"))) )

let inv_IN i = tfq (q_ind_dec nu (qexists_e "j" z0 i (get value j =. vin)))

let c_in =
  Circuit
    { name= "IN"
    ; inputs=
        [("valueArraySize", t_sz); ("in", tf); ("value", tarr_tf valueArraySize)]
    ; outputs= [("out", t_IN)]
    ; dep= None
    ; body=
        elet "count"
          (iter z0 valueArraySize lam_IN ~init:f0 ~inv:inv_IN)
          (call "GreaterThan" [z252; count; f0]) }

(* Query *)

let is_eq x y = call "IsEqual" [x; y]

let is_lt x y = call "LessThan" [z252; x; y]

let is_gt x y = call "GreaterThan" [z252; x; y]

(* [1; e; l; g; i; 1 - i; 0; 0] *)
let mux_query e l g i = const_array tf [f1; e; l; g; i; f1 -% i; f0; f0]

let t_vas =
  TRef
    ( tint
    , qand
        (lift (z2 <. CPrime))
        (qand (lift (z252 <=. zsub1 CPLen)) (lift (z0 <. nu))) )

let t_query =
  tfq
    (ites_expr
       [ (op =. fn 0, nu ==. f1)
       ; (op =. fn 1, ind_dec nu (vin =. v0))
       ; (op =. fn 2, ind_dec nu (vin <.. v0))
       ; (op =. fn 3, ind_dec nu (vin >.. v0))
       ; ( op =. fn 4
         , q_ind_dec nu (qexists_e "j" z0 valueArraySize (get value j =. vin))
         )
       ; ( op =. fn 5
         , q_ind_dec nu
             (qnot (qexists_e "j" z0 valueArraySize (get value j =. vin))) ) ]
       qfalse )

let query =
  Circuit
    { name= "Query"
    ; inputs=
        [ ("valueArraySize", t_vas)
        ; ("in", tf)
        ; ("value", tarr_tf valueArraySize)
        ; ("operator", tf) ]
    ; outputs= [("out", t_query)]
    ; dep= None
    ; body=
        elet "x" (get value z0)
          (elet "eq" (is_eq vin x)
             (elet "lt" (is_lt vin x)
                (elet "gt" (is_gt vin x)
                   (elet "in"
                      (call "IN" [valueArraySize; vin; value])
                      (elet "n2b"
                         (call "Num2Bits" [z3; op])
                         (call "Mux3" [mux_query eq l gt iN; n2b]) ) ) ) ) ) }

(* getValueByIndex *)

let t_get_val_by_idx = tfq (qeq nu (get claim (zmod (toUZ index) z8)))

let get_val_by_idx =
  Circuit
    { name= "getValueByIndex"
    ; inputs= [("claim", tarr_tf z8); ("index", tf)]
    ; outputs= [("value", t_get_val_by_idx)]
    ; dep= None
    ; body=
        elet "n2b"
          (call "Num2Bits" [z8; index])
          (elet "z" (take n2b z3) (call "Mux3" [claim; z])) }

(* getIdenState *)

let t_get_iden_state =
  tfq
    (qeq nu
       (u_poseidon z3
          (const_array tf [claimsTreeRoot; revTreeRoot; rootsTreeRoot]) ) )

let get_iden_state =
  Circuit
    { name= "getIdenState"
    ; inputs=
        [("claimsTreeRoot", tf); ("revTreeRoot", tf); ("rootsTreeRoot", tf)]
    ; outputs= [("idenState", t_get_iden_state)]
    ; dep= None
    ; body=
        elet "z"
          (const_array tf [claimsTreeRoot; revTreeRoot; rootsTreeRoot])
          (call "Poseidon" [z3; z]) }

(* cutId *)

let t_cut_id =
  tfq (qeq nu (as_le_f (u_take z216 (u_drop z16 (to_le_f z256 vin)))))

let cut_id =
  Circuit
    { name= "cutId"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_cut_id)]
    ; dep= None
    ; body=
        elet "n2b"
          (call "Num2Bits" [z256; vin])
          (elet "d" (drop n2b z16)
             (elet "t" (take d z216) (call "Bits2Num" [z216; t])) ) }

(* cutState *)

let t_cut_st = tfq (qeq nu (as_le_f (u_drop z40 (to_le_f z256 vin))))

let cut_st =
  Circuit
    { name= "cutState"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_cut_st)]
    ; dep= None
    ; body=
        elet "n2b"
          (call "Num2Bits" [z256; vin])
          (elet "d" (drop n2b z40) (call "Bits2Num" [z216; d])) }
