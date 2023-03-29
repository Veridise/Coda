open Ast
open Dsl

let z8 = zn 8

let z16 = zn 16

let z40 = zn 40

let z216 = zn 216

let z256 = zn 256

let i = v "i"

let j = v "j"

let x = v "x"

let z = v "z"

let eq = v "eq"

let lt = v "lt"

let gt = v "gt"

let iN = v "in"

let vin = v "in"

let out = v "out"

let n2b = v "n2b"

let count = v "count"

let value = v "value"

let index = v "index"

let claim = v "claim"

let valueArraySize = v "valueArraySize"

let operator = v "operator"

let claimsTreeRoot = v "claimsTreeRoot"

let revTreeRoot = v "revTreeRoot"

let rootsTreeRoot = v "rootsTreeRoot"

(* IN *)

(* ~(forall 0 <= i < len value, value[i] <> in) *)
let q_out = qnot (qforall "i" z0 (len value) (qnot (qeq (get value i) vin)))

let t_out = tfq (q_ind_dec nu q_out)

let lam_in =
  lama "i" tint
    (lama "x" tf
       (fadd x (call "IsEqual" [cons vin (cons (get value i) cnil)])) )

let inv_in i =
  tfq (qimply (qeq nu f0) (qforall "j" z0 i (qnot (qeq (get value j) vin))))

let c_in =
  Circuit
    { name= "IN"
    ; inputs=
        [("valueArraySize", tnat); ("in", tf); ("value", tarr_tf valueArraySize)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        elet "count"
          (iter z0 valueArraySize lam_in ~init:f0 ~inv:inv_in)
          (call "GreaterThan" [z252; cons count (cons f0 cnil)]) }

(* let deltas_in = add_to_deltas d_empty [c_is_equal; c_greater_than] *)

(* let check_c_in = typecheck_circuit deltas_in c_in *)

(* Query *)

let is_eq x y = call "IsEqual" [cons x (cons y cnil)]

let is_lt x y = call "LessThan" [z252; cons x (cons y cnil)]

let is_gt x y = call "GreaterThan" [z252; cons x (cons y cnil)]

(* [1; e; l; g; i; 1 - i; 0; 0] *)
let mux_query e l g i =
  cons f1
    (cons e
       (cons l (cons g (cons i (cons (fsub f1 i) (cons f0 (cons f0 cnil)))))) )

let t_out =
  tfq
    (qeq nu
       (call "Mux3"
          [ mux_query
              (is_eq vin (get value z0))
              (is_lt vin (get value z0))
              (is_gt vin (get value z0))
              (call "IN" [valueArraySize; vin; value])
          ; call "Num2Bits" [z3; operator] ] ) )

let query =
  Circuit
    { name= "Query"
    ; inputs=
        [ ("valueArraySize", tpos)
        ; ("in", tf)
        ; ("value", tarr_tf valueArraySize)
        ; ("operator", tf) ]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        elet "x" (get value z0)
          (elet "eq" (is_eq vin x)
             (elet "lt" (is_lt vin x)
                (elet "gt" (is_gt vin x)
                   (elet "in"
                      (call "IN" [valueArraySize; vin; value])
                      (elet "n2b"
                         (call "Num2Bits" [z3; operator])
                         (call "Mux3" [mux_query eq lt gt iN; n2b]) ) ) ) ) ) }

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
          (call "Mux3" [claim; take z3 n2b]) }

(* getIdenState *)

let t_get_iden_state =
  tfq
    (qeq nu
       (call "Poseidon"
          [z3; cons claimsTreeRoot (cons revTreeRoot (cons rootsTreeRoot cnil))] ) )

let get_iden_state =
  Circuit
    { name= "getIdenState"
    ; inputs=
        [("claimsTreeRoot", tf); ("revTreeRoot", tf); ("rootsTreeRoot", tf)]
    ; outputs= [("idenState", t_get_iden_state)]
    ; dep= None
    ; body=
        call "Poseidon"
          [z3; cons claimsTreeRoot (cons revTreeRoot (cons rootsTreeRoot cnil))]
    }

(* cutId *)

let t_cut_id =
  tfq
    (qeq nu
       (call "Bits2Num"
          [z216; take z216 (drop z16 (call "Num2Bits" [z256; vin]))] ) )

let cut_id =
  Circuit
    { name= "cutId"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_cut_id)]
    ; dep= None
    ; body=
        elet "n2b"
          (call "Num2Bits" [z256; vin])
          (call "Bits2Num" [z216; take z216 (drop z16 n2b)]) }

(* cutState *)

let t_cut_st =
  tfq (qeq nu (call "Bits2Num" [z216; drop z40 (call "Num2Bits" [z256; vin])]))

let cut_st =
  Circuit
    { name= "cutState"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_cut_st)]
    ; dep= None
    ; body=
        elet "n2b"
          (call "Num2Bits" [z256; vin])
          (call "Bits2Num" [z216; drop z40 n2b]) }
