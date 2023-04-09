open Ast
open Dsl
open Notation
open Monads

type lib = Lib of {name: string; def: expr; typ: typ option}

let name (Lib l) = l.name

let def (Lib l) = l.def

let typ (Lib l) =
  match l.typ with
  | Some t ->
      t
  | None ->
      Typecheck.run_synthesis ~gamma:[] l.def |> fst

let verify_ty ~gamma (Lib l : lib) =
  Typecheck.run_checking ~gamma l.def (typ (Lib l))

let verify ~gamma (Lib l : lib) =
  verify_ty ~gamma (Lib l) |> Coqgen.generate_lemmas l.name |> print_endline

let use (Lib l : lib) = AscribeUnsafe (v l.name, typ (Lib l))

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
    ; typ= None }

let pairwise_add =
  let k = v "k" in
  let xs = v "xs" in
  let ys = v "ys" in
  let zs = v "zs" in
  let t_xs = tarr_t_k tf k in
  let i = v "i" in
  let j = "add_j" in
  let t_zs i =
    tarr_t_q_k tf
      (qforall j z0 i (get nu (v j) ==. get xs (v j) +% get ys (v j)))
      i
  in
  Lib
    { name= "pairwise_add"
    ; typ= None
    ; def=
        lamas
          [("k", tnat); ("xs", t_xs); ("ys", t_xs)]
          (iter z0 k ~init:cnil
             ~inv:(fun i -> t_zs i)
             (lama "i" tnat
                (lama "zs" (t_zs i)
                   (concat zs (consts [get xs i +% get ys i])) ) ) ) }

let pairwise_mul =
  let k = v "k" in
  let xs = v "xs" in
  let ys = v "ys" in
  let zs = v "zs" in
  let t_xs = tarr_t_k tf k in
  let i = v "i" in
  let j = "mul_j" in
  let t_zs i =
    tarr_t_q_k tf
      (qforall j z0 i (get nu (v j) ==. get xs (v j) +% get ys (v j)))
      i
  in
  Lib
    { name= "pairwise_add"
    ; typ= None
    ; def=
        lamas
          [("k", tnat); ("xs", t_xs); ("ys", t_xs)]
          (iter z0 k ~init:cnil
             ~inv:(fun i -> t_zs i)
             (lama "i" tnat
                (lama "zs" (t_zs i)
                   (concat zs (consts [get xs i +% get ys i])) ) ) ) }

let scale =
  let k = v "k" in
  let x = v "x" in
  let ys = v "ys" in
  let zs = v "zs" in
  let t_ys = tarr_t_k tf k in
  let i = v "i" in
  let j = "scale_j" in
  let t_zs i =
    tarr_t_q_k tf (qforall j z0 i (get nu (v j) ==. x *% get ys (v j))) i
  in
  Lib
    { name= "scale"
    ; typ= None
    ; def=
        lamas
          [("k", tnat); ("x", tf); ("ys", t_ys)]
          (iter z0 k ~init:cnil
             ~inv:(fun i -> t_zs i)
             (lama "i" tnat
                (lama "zs" (t_zs i) (concat zs (consts [x *% get ys i]))) ) ) }
