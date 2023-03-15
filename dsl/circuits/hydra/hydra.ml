open Ast
open Dsl
open Typecheck

let s = v "s"

let vin = v "in"

let in0 = v "in0"

let in1 = v "in1"

let out = v "out"

let out0 = v "out0"

let out1 = v "out1"

(* 2 <= length i /\ 2 <= length o /\ o[0] = i[0] /\ o[1] = i[1] *)
let q_same i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z0)) (qeq (get o z1) (get i z1)))

(* 2 <= length i /\ 2 <= length o /\ o[0] = i[1] /\ o[1] = i[0] *)
let q_switch i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z1)) (qeq (get o z1) (get i z0)))

(* binary(s) -> (s = 1 -> q_switch in out) /\ (s = 0 -> q_same in out) *)
let q_out =
  qimply (QExpr (is_binary s)) (q_ind s (q_switch vin nu) (q_same vin nu))

(* { Array<F> | q_out(v) /\ length v = 2 } *)
let t_out = tarr_t_q_k tf q_out z2

let position_switcher =
  Circuit
    { name= "PositionSwitcher"
    ; inputs= [("in", tarr_tf z2); ("s", tf)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        (* s * (1 - s) === 0 *)
        elet "_"
          (assert_eq (fmul s (fsub f1 s)) f0)
          (elet "in0" (get vin z0)
             (elet "in1" (get vin z1)
                (* out[0] === (in[1] - in[0]) * s + in[0] *)
                (elet "out0"
                   (fadd (fmul (fsub in1 in0) s) in0)
                   (* out[1] === (in[0] - in[1]) * s + in[1] *)
                   (elet "out1"
                      (fadd (fmul (fsub in0 in1) s) in1)
                      (cons out0 (cons out1 cnil)) ) ) ) ) }

let check_position_switcher = typecheck_circuit d_empty position_switcher
