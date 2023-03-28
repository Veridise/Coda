open Ast
open Dsl
open Notation
open Monads

let _stars k =
  let i = v "i" in
  let x = v "x" in
  let lam_stars =
    lama "i" tint
      (lama "x" (tarr_t_k tf i) (elet "star" star (cons (v "star") x)))
  in
  let inv_stars i = tarr_t_k tf i in
  iter z0 k lam_stars ~init:cnil ~inv:inv_stars

let stars k = _stars k
(* FIXME: can we build a trusted library that the user can assume has been type checked? *)
(* Typecheck.(
   let (t, _) = S.run {empty with gamma=[("k", tnat)]} (synthesize (_stars k)) in
   dummy "stars" t) *)
