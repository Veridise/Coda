open Ast
open Dsl
open Liblam

let z220 = zn 220

let nInputs = v "nInputs"

let nRounds = v "nRounds"

let nOutputs = v "nOutputs"

let ins = v "ins"

let k = v "k"

let outs = v "outs"

let t_mimc_sponge =
  tarr_t_q_k tf
    (qeq nu (unint "MiMCSponge" [nInputs; nRounds; nOutputs; ins; k]))
    nOutputs

let mimc_sponge =
  Circuit
    { name= "MiMCSponge"
    ; inputs=
        [ ("nInputs", tnat)
        ; ("nRounds", tnat)
        ; ("nOutputs", tnat)
        ; ("ins", tarr_tf nInputs)
        ; ("k", tf) ]
    ; outputs= [("outs", t_mimc_sponge)]
    ; dep= None
    ; body= stars nOutputs }
