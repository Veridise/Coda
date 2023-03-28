open Ast
open Dsl
open Notation
open Liblam

let i = v "i"

let j = v "j"

let k = v "k"

let xs = v "xs"

let xi = get xs i

let xj = get xs j

let c_all_binary =
  Circuit
    { name= "all_binary"
    ; inputs= [("k", tnat); ("xs", tarr tf)]
    ; outputs= []
    ; dep= Some (qforall_e "i" z0 k (is_binary xi))
    ; body=
        iter z0 k
          (lama "i" tint (lama "u" tunit (xi *% (xi -% f1) === f0)))
          ~init:unit_val
          ~inv:(fun i -> tunit_dep (qforall_e "j" z0 i (is_binary xj))) }

let stars =
  Circuit
    { name= "Stars"
    ; inputs= [("k", tnat)]
    ; outputs= [("_", tarr_t_k tf (v "k"))]
    ; dep= None
    ; body= stars (v "k") }
