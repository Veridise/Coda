open Ast
open Dsl
open Notation

let a = v "a"

let b = v "b"

let i = v "i"

let n = v "n"

let s = v "s"

let x = v "x"

let y = v "y"

let z = v "z"

let vin = v "in"

let out = v "out"

let key = v "KEY"

let n2b = v "n2b"

let rng = v "rng"

let eqs = v "eqs"

let choices = v "choices"

let index = v "index"

let nops = v "nops"

let word = v "word"

let test = v "test"

let total = v "total"

(* CalculateTotal *)

let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", tfq (qeq nu (u_sum vin)))]
    ; dep= None
    ; body= make_sum vin ~len:n }

let sum_equals =
  Circuit
    { name= "SumEquals"
    ; inputs= [("n", tnat); ("nums", tarr_tf n); ("s", tf)]
    ; outputs= [("out", tf_binary)]
    ; dep= None
    ; body=
        elet "x" (call "CalculateTotal" [n; v "nums"]) (call "IsEqual" [x; s])
    }

let is_not_zero =
  Circuit
    { name= "IsNotZero"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (bnot (vin =. f0))))]
    ; dep= None
    ; body= elet "isz" (call1 "IsZero" vin) (call1 "Not" (v "isz")) }

let is_filtered =
  Circuit
    { name= "IsFiltered"
    ; inputs= [("x", tf); ("y", tf); ("op", tf)]
    ; outputs= [("out", tf)]
    ; dep= None
    ; body=
        elet "a"
          (call "IsEqual" [v "op"; f0])
          (elet "b"
             (call "IsEqual" [v "op"; f1])
             (call "CalculateTotal" [z2; const_array tf [x *% a; y *% b]]) ) }

let t_multisum = tfq (qeq nu (u_sum vin))

let multisum =
  Circuit
    { name= "MultiSum"
    ; inputs= [("n", tnat); ("nops", tnat); ("in", tarr_tf nops)]
    ; outputs= [("out", t_multisum)]
    ; dep= None
    ; body=
        elet "n2bs"
          (map (lama "x" tf (call "Num2Bits" [n; v "x"])) vin)
          (elet "bsum"
             (call "BinSum" [n; nops; v "n2bs"])
             (call "Bits2Num" [n; v "bsum"]) ) }

let t_is_equal_word = tfq (q_ind_dec nu (qeq word test))

let lam_iew = lama "x" (tpair tf tf) (call "IsEqual" [tget x 0; tget x 1])

let is_equal_word =
  Circuit
    { name= "IsEqualWord"
    ; inputs= [("n", tnat); ("word", tarr_tf n); ("test", tarr_tf n)]
    ; outputs= [("out", t_is_equal_word)]
    ; dep= None
    ; body=
        elet "z" (zip word test)
          (elet "eqs" (map lam_iew z)
             (elet "total"
                (call "MultiSum" [zn 32; n; v "eqs"])
                (call "IsEqual" [nat2f n; v "total"]) ) ) }

let t_n = TRef (tint, qand (lift (lt z0 nu)) (lift (lt nu CPrime)))

let t_multi_or = tfq (q_ind_dec nu (qexists_e "i" z0 n (eq (get vin i) f1)))

let multi_or =
  Circuit
    { name= "MultiOR"
    ; inputs= [("n", t_n); ("in", tarr_t_k tf_binary n)]
    ; outputs= [("out", t_multi_or)]
    ; dep= None
    ; body=
        elet "total" (call "CalculateTotal" [n; vin]) (call1 "IsNotZero" total)
    }
