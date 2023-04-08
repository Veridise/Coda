open Ast
open Dsl
open Notation
open Monads

type lib = Lib of {name: string; def: expr; typ: typ}

let name (Lib l) = l.name
let def (Lib l) = l.def
let typ (Lib l) = l.typ

let verify_ty ~gamma (Lib l : lib) = Typecheck.run_checking ~gamma l.def l.typ
let verify ~gamma (Lib l : lib) = verify_ty ~gamma (Lib l) |> Coqgen.generate_lemmas l.name |> print_endline

let use (Lib l : lib) = AscribeUnsafe (v l.name, l.typ)

let stars k =
  let i = v "i" in
  let x = v "x" in
  let lam_stars =
    lama "i" tint
      (lama "x" (tarr_t_k tf i) (elet "star" star (cons (v "star") x)))
  in
  let inv_stars i = tarr_t_k tf i in
  iter z0 k lam_stars ~init:cnil ~inv:inv_stars

let gen_rng =
  let f = v "f" in
  let x = v "x" in
  let k = v "k" in
  let j = "rng_j" in
  let t_k = attach (lift (nu <. CPrime)) tnat in
  let t_ks i = tarr_t_q_k tf (qforall j z0 i (toUZ (get nu (v j)) ==. v j)) i in
  Lib
    { name= "gen_rng"
    ; def=
        lama "k" t_k
          (match_with' ["_f"; "ks"]
             (iter z0 k
                (lama "i" tint
                   (lama_match
                      [("f", tf); ("x", tarr tf)]
                      (pair (v "f" +% f1) (concat x (consts [f]))) ) )
                ~init:(pair f0 cnil)
                ~inv:(fun i ->
                  tpair
                    (tfe (toUZ nu =. i))
                    (* forall z0 <= j < i, v[j] = ^j *)
                    (t_ks i) ) )
             (v "ks") )
    ; typ= tfun "k" t_k (t_ks k) }
