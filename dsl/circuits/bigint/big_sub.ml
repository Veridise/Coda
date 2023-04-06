(** Benchmark ModSubThree *)

open Ast
open Dsl
open Notation

let a = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let k = v "k"

let n = v "n"

let p = v "p"

let s = v "s"

let x = v "x"

let y = v "y"

let ab = v "ab"

let out = v "out"

let borrow = v "borrow"

let uf = v "underflow"

let b_plus_c = v "b_plus_c"

let add = v "add"

let tmp = v "tmp"

(* { F | ^v <= C.k - 2 } *)
let t_n = attach (lift (nu <=. CPLen -! z2)) tnat

(* { F | ^v <= 2^n - 1 } *)
let tf_n_bit = tfe (toUZ nu <=. (z2 ^! n) -! z1)

let mod_sub_three =
  Circuit
    { name= "ModSubThree"
    ; inputs= [("n", t_n); ("a", tf_n_bit); ("b", tf_n_bit); ("c", tf_binary)]
    ; outputs=
        [("out", tf); ("borrow", tfq (ind_dec nu (toUZ a <. toUZ (b +% c))))]
    ; (* out = borrow * 2 ** n + a - (b + c) *)
      dep= Some (out ==. ((borrow *% f2) ^% n) +% a -% (b +% c))
    ; body=
        elet "borrow"
          (call "LessThan" [n +. z1; a; b +% c])
          (pair
             (* borrow === #LessThan (n + 1) a (b + c) *)
             (((borrow *% f2) ^% n) +% a -% (b +% c))
             (* out === borrow * 2 ** n + a - (b + c) *)
             borrow ) }

(* Proper Big Int of length k *)
let t_big_int k = tarr_t_k tf_n_bit k

(* { F | binary(nu) /\ nu = 1 <-> [| a |] < [| b |] } *)
let t_uf = tfq (q_ind_dec nu (QExpr (lt (toUZ a) (toUZ b))))

(* \i (s, c) => let (si, ci) = #ModSubThree n (ab[i]).0 (ab[i]).1 c in (s ++ si, ci) *)
let lam_big_sub =
  lama "i" tint
    (lama "x"
       (ttuple [tarr_tf i; tf])
       (elet "s" (tget x 0)
          (elet "c" (tget x 1)
             (elet "a"
                (tget (get ab i) 0)
                (elet "b"
                   (tget (get ab i) 1)
                   (elet "y"
                      (call "ModSubThree" [n; a; b; c])
                      (make [concat s (cons (tget y 0) cnil); tget y 1]) ) ) ) ) ) )

let inv_big_sub i = ttuple [t_big_int i; tf_binary]

let big_sub =
  Circuit
    { name= "BigSub"
    ; inputs= [("n", t_n); ("k", tpos); ("a", t_big_int k); ("b", t_big_int k)]
    ; outputs= [("out", t_big_int k); ("underflow", t_uf)]
    ; (* [| out |] = [| a |] - [| b |] + [| underflow |] * 2 ^ (n * k) *)
      dep=
        Some
          (qeq (toUZ out)
             (zadd
                (zsub (toUZ a) (toUZ b))
                (zmul (toUZ uf) (zpow z2 (zmul n k))) ) )
    ; body=
        (* ab = zip a b *)
        elet "ab" (zip a b)
          (* (sub, borrow) = iter 0 k lam_big_sub ([], 0) *)
          (elet "x"
             (iter z0 k lam_big_sub ~init:(make [cnil; f0]) ~inv:inv_big_sub)
             (* out === sub *)
             (make [tget x 0; tget x 1])
             (* underflow === borrow *) ) }

(* BigSubModP *)

(* { F | [| v |] <= [| p |] - 1 } *)
let q_lt_p = QExpr (leq (toUZ nu) (zsub1 (toUZ p)))

(* { F | [| v |] = [| a |] - [| b |] mod [| p |] *)
let q_sub_mod_p = qeq (toUZ nu) (zmod (zsub (toUZ a) (toUZ b)) (toUZ p))

(* Proper BigInts of length k with the q_lt_p property *)
let t_big_int_lt_p k = tarr_t_q_k tf_n_bit q_lt_p k

(* Proper BigInts of length k with the q_sub_mod_p property *)
let t_big_int_sub_mod_p k = tarr_t_q_k tf_n_bit q_sub_mod_p k

let lam_bsmp =
  lama "x"
    (ttuple [tf; tf])
    (fadd (fmul (fsub f1 uf) (tget x 0)) (fmul uf (tget x 1)))

let big_sub_mod_p =
  Circuit
    { name= "BigSubModP"
    ; inputs=
        [ ("n", t_n)
        ; ("k", tpos)
        ; ("a", t_big_int_lt_p k)
        ; ("b", t_big_int_lt_p k)
        ; ("p", t_big_int k) ]
    ; outputs= [("out", t_big_int_sub_mod_p k)]
    ; dep= None
    ; body=
        (* (sub, underflow) = #BigSub n k a b *)
        elet "x"
          (call "BigSub" [n; k; a; b])
          (* add = #BigAdd n k sub p *)
          (elet "add"
             (take k (call "BigAdd" [n; k; tget x 0; p]))
             (* tmp = zip sub add *)
             (elet "tmp"
                (zip (tget x 0) add)
                (* out === map (\(s, a) => (1 - underflow) * s + underflow * a) tmp *)
                (elet "uf" (tget x 1) (map lam_bsmp tmp)) ) ) }
