open Ast
open Dsl
open Notation

let sel = v "sel"

let l = v "L"

let r = v "R"

let aux = v "aux"

let switcher =
  Circuit
    { name= "Switcher"
    ; inputs= [("sel", tf_binary); ("L", tf); ("R", tf)]
    ; outputs=
        [ ("outL", tfq (ite (sel ==. f0) (nu ==. l) (nu ==. r)))
        ; ("outR", tfq (ite (sel ==. f0) (nu ==. r) (nu ==. l))) ]
    ; dep= None
    ; body= elet "aux" ((r -% l) *% sel) (pair (aux +% l) (f0 -% aux +% r)) }
