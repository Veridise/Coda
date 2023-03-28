open Ast
open Dsl
open Notation
open Liblam

let i = v "i"

let j = v "j"

let n = v "n"

let vin = v "in"

let ini = get vin i

let inj = get vin j

let vout = v "out"

let outi = get vout i

let outj = get vout j

let lc1 = v "lc1"

let e2 = v "e2"

let n2b_inv i = ttuple [tfe (nu =. as_le_f (take vout i)); tfe (nu =. f2 ^% i)]

let n2b_tout = refine (tarr tf_binary) (QExpr (as_le_f nu =. vin))

let num2bits =
  circuit ~name:"Num2Bits"
    ~inputs:[("n", tnat); ("in", tf)]
    ~outputs:[("out", n2b_tout)]
    ~dep:None
    ~body:
      (elet "out" (stars n)
         (elet_p ["lc1"; "e2"]
            (iter z0 n
               (lama "i" tint
                  (lama_p
                     [("lc1", tf); ("e2", tf)]
                     (pair (lc1 +% (outi *% e2)) (e2 +% e2)) ) )
               ~init:(pair f0 f1) ~inv:n2b_inv )
            (elets
               [ ("u0", vin === lc1)
               ; ( "u"
                 , iter z0 n
                     (lama "i" tint
                        (lama "u" tunit (outi *% (outi -% f1) === f0)) )
                     ~init:unit_val
                     ~inv:(fun i ->
                       tunit_dep (qforall_e "j" z0 i (is_binary outj)) ) ) ]
               (push vout) ) ) )

let b2n_tin = tarr_t_k tf_binary n

let b2n_tout = tfe (eq nu (as_le_f vin))

let b2n_inv i = ttuple [tfe (nu =. as_le_f (take vin i)); tfe (nu =. f2 ^% i)]

let bits2num =
  Circuit
    { name= "Bits2Num"
    ; inputs= [("n", tnat); ("in", b2n_tin)]
    ; outputs= [("out", b2n_tout)]
    ; dep= None
    ; body=
        elet_p ["lc1"; "e2"]
          (iter z0 n ~init:(pair f0 f1) ~inv:b2n_inv
             (lama "i" tint
                (lama_p
                   [("lc1", tf); ("e2", tf)]
                   (pair (lc1 +% (ini *% e2)) (e2 +% e2)) ) ) )
          lc1 }
