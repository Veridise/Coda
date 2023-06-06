open Core
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

let use (l : lib) = (name l, typ l)

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
    ; typ= Some (tfun "k" t_k (t_ks k)) }

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
    ; typ= Some (tfun "k" tnat (tfun "xs" t_xs (tfun "ys" t_xs (t_zs k))))
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
      (qforall j z0 i (get nu (v j) ==. get xs (v j) *% get ys (v j)))
      i
  in
  Lib
    { name= "pairwise_mul"
    ; typ= Some (tfun "k" tnat (tfun "xs" t_xs (tfun "ys" t_xs (t_zs k))))
    ; def=
        lamas
          [("k", tnat); ("xs", t_xs); ("ys", t_xs)]
          (iter z0 k ~init:cnil
             ~inv:(fun i -> t_zs i)
             (lama "i" tnat
                (lama "zs" (t_zs i)
                   (concat zs (consts [get xs i *% get ys i])) ) ) ) }

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
    ; typ= Some (tfun "k" tnat (tfun "x" tf (tfun "ys" t_ys (t_zs k))))
    ; def=
        lamas
          [("k", tnat); ("x", tf); ("ys", t_ys)]
          (iter z0 k ~init:cnil
             ~inv:(fun i -> t_zs i)
             (lama "i" tnat
                (lama "zs" (t_zs i) (concat zs (consts [x *% get ys i]))) ) ) }

let ite_array =
  let k = v "k" in
  let c = v "c" in
  let xs = v "us" in
  let ys = v "vs" in
  let t_xs = tarr_t_k tf k in
  let t_zs i = tarr_t_q_k tf (ite_expr (c =. f1) (nu =. xs) (nu =. ys)) i in
  Lib
    { name= "ite_array"
    ; typ=
        Some
          (tfun "k" tnat
             (tfun "c" tf_binary (tfun "us" t_xs (tfun "vs" t_xs (t_zs k)))) )
    ; def=
        lamas
          [("k", tnat); ("c", tf_binary); ("us", t_xs); ("vs", t_xs)]
          (elets
             [ ("c_true", apps (v "scale") [k; c; xs])
             ; ("c_false", apps (v "scale") [k; f1 -% c; ys]) ]
             (apps (v "pairwise_add") [k; v "c_true"; v "c_false"]) ) }

let libs = [gen_rng; pairwise_add; pairwise_mul; scale; ite_array]

let libs_gamma = List.map libs ~f:(fun l -> (name l, typ l))

let libs_gamma_codegen = List.map libs ~f:(fun l -> (name l, def l))
