open Ast
open Big_int_Z
open Dsl

(* ========================================================================== *)

module Qual = struct
  let to_expr = lift

  let ( #! ) = qnot

  let ( #&& ) = qand

  let ( #==> ) = qimply

  let disjunction = ors

  let conjunction = ands

  let switch = ites

  let contained_in = contained_in

  (* If [a = 1] then [b] else [c] *)
  (* [(a = 0 \/ a = 1) /\ (a = 1 ==> b) /\ (a = 0 ==> c)] *)
  let if_binary_field a b c = q_ind a b c

  (* If [a = 1] then [b] else [not b] *)
  (* [(a = 0 \/ a = 1) /\ (a = 1 ==> b) /\ (a = 0 ==> not b)] *)
  let iff_binary_field a b = q_ind_dec a b

  let forall = qforall

  let exists = qexists

  let def = elet

  let defs = elets

  let def_jumble = elet_p

  let lam_jumble = lama_p
end

open Qual

(* ========================================================================== *)

module Expr = struct
  let make_dependent_product = dmake

  let match_dependent_product_with = match_with

  let match_remembered_dependent_product_with = match_with'

  let var = v

  let const_field = fc

  let const_int = zc

  let const_nil = cnil

  let binary_field = tf_binary

  (* ========================================================================== *)
  (* function [call] *)

  let ( $ ) = call

  (* ========================================================================== *)
  (* built-in function [Fn] *)

  let toSZ e = Fn (ToSZ, [e])

  let toUZ e = Fn (ToUZ, [e])

  let nat2f e = Fn (NatToF, [e])

  (* ========================================================================== *)
  (* [nat] operation *)

  let ( ^. ) = npow

  let ( *. ) = nmul

  let ( +. ) = nadd

  let ( -. ) = nsub

  module N = struct
    let sum = badds BNat

    let product = nmuls

    let ( * ) = npow

    let ( + ) = nadd

    let ( - ) = nsub

    let ( ^ ) = npow
  end

  (* ========================================================================== *)
  (* [int] operation *)

  module Z = struct
    let max = zmax

    let not = znot

    let sum = badds BZ

    let product = zmuls

    let ( * ) = zmul

    let ( + ) = zadd

    let ( - ) = zsub

    let ( ^ ) = zpow

    module Unint = struct
      let xor a b = unint "xor" [a; b]

      let ( ^ ) = xor

      let and_ a b = unint "and" [a; b]

      let ( && ) = and_

      let nand a b = unint "nand" [a; b]

      let ( &&! ) = nand

      let or_ a b = unint "or" [a; b]

      let ( || ) = or_

      let nor a b = unint "nor" [a; b]

      let ( ||! ) = nor
    end
  end

  (* ========================================================================== *)
  (* [field] operation *)

  module F = struct
    let product = fmuls

    let sum = badds BF

    let ( * ) = fmul

    let ( + ) = fadd

    let ( - ) = fsub

    let ( ^ ) = fpow

    let add1 = fadd1
  end

  (* ========================================================================== *)
  (* [bool]-valued operations *)
  let ( @|| ) = bor

  let ( =. ) = eq

  let ( ==. ) = qeq

  let ( <. ) = lt

  let to_q op f1 f2 = op (toUZ f1) (toUZ f2)

  let ( <.. ) = to_q lt

  let ( >. ) a b = b <. a

  let ( >.. ) = to_q ( >. )

  let ( <=. ) = leq

  let ( <=.. ) = to_q ( <=. )

  let ( >=. ) a b = b <=. a

  let ( >=.. ) = to_q ( >=. )

  let ( @! ) = bnot

  let ( @&& ) = band

  let ( @==> ) = imply

  (* misc *)

  let if_ = ite_expr

  (* If [a = 1] then [b] else [c] *)
  (* [(a = 0 \/ a = 1) /\ (a = 1 ==> b) /\ (a = 0 ==> c)] *)
  let if_binary_field a b c = ind a b c

  (* If [a = 1] then [b] else [not b] *)
  (* [(a = 0 \/ a = 1) /\ (a = 1 ==> b) /\ (a = 0 ==> not b)] *)
  let iff_binary_field a b = ind_dec_expr a b

  let tuple = make

  let project = tget

  let project1 = tfst

  let project2 = tsnd

  let pair = pair

  let unit = unit_val
end

open Expr

(* ========================================================================== *)

module BaseTyp = struct
  let field = TF

  let int = TInt

  let bool = TBool

  let to_typ t = TBase t

  let from_typ typ =
    match typ with
    | TBase t ->
        t
    | _ ->
        failwith @@ "Expected " ^ Ast_utils.show_typ typ ^ " to be a base type"
end

module Typ = struct
  let field = tf

  let int = tint

  let bool = tbool

  let func = tfun

  let tuple = ttuple

  let pair = tpair

  let unit = tunit

  let array = tarr

  let field_of_nat = nat2f
end

open Typ

(* ========================================================================== *)

module TypRef = struct
  let such_that t make_q = TRef (t, make_q nu)

  let ( |: ) = such_that

  let as_refined_type = as_tref

  let nat = int |: fun x -> to_expr (z0 <=. x)
end

open TypRef

let circuit name inputs outputs body =
  circuit ~name ~dep:None ~inputs ~outputs ~body
