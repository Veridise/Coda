open Ast
open Dsl
open Notation

let k = v "k"

let n = v "n"

let i = v "i"

let j = v "j"

let xs = v "xs"

let xs' = v "xs'"

let ys = v "ys"

let ys' = v "ys'"

let x = v "x"

let y = v "y"

(* circuit BigLessThan
      (n: nat) (k: nat)
      (xs: F^k) (ys: F^k) : { F | v = ([|a|] <= [|b|])? } {
      fold_left
         \(lt, eq) ->
         \(x,y) ->
         (Or(lt, And(eq, LessThen(a,b))), And(eq, IsEqual(x,y)))
         zip(xs, ys)
   } *)

let as_le xs = as_le n xs

let as_be xs = as_be n xs

let op_le op xs ys = tfq (ind_dec nu (op (as_le xs) (as_le ys)))

let op_be op xs ys = tfq (ind_dec nu (op (as_be xs) (as_be ys)))

let t_out = op_le lt xs ys

let t_in = tarr_t_k (tfe (toUZ nu <=. (z2 ^! n) -! z1)) k

let inv_big_lt i =
  tpair
    (op_be lt (take xs' i) (take ys' i))
    (op_be eq (take xs' i) (take ys' i))

let big_lt =
  Circuit
    { name= "BigLessThan"
    ; inputs=
        [ ("n", tnat_e (nu <=. zsub1 CPLen))
        ; ("k", tnat_e (z2 <=. nu))
        ; ("xs", t_in)
        ; ("ys", t_in) ]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        elets
          [("xs'", rev xs); ("ys'", rev ys)]
          (tfst
             (iter z0 k ~init:(pair f0 f1) ~inv:inv_big_lt
                (lama "i" tnat
                   (lama_match
                      [("lt", tf); ("eq", tf)]
                      (elets
                         [ ("x", get xs' i)
                         ; ("y", get ys' i)
                         ; ("x_lt_y", call "LessThan" [n; x; y])
                         ; ("xs_lt_ys", call "And" [v "eq"; v "x_lt_y"])
                         ; ("x_eq_y", call "IsEqual" [x; y]) ]
                         (pair
                            (call "Or" [v "lt"; v "xs_lt_ys"])
                            (call "And" [v "eq"; v "x_eq_y"]) ) ) ) ) ) ) }
