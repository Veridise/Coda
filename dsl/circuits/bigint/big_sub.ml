(** Benchmark ModSubThree *)

open Ast
open Dsl
open Notation

let a = v "a"

let ai = v "ai"

let b = v "b"

let bi = v "bi"

let c = v "c"

let i = v "i"

let k = v "k"

let n = v "n"

let p = v "p"

let s = v "s"

let s' = v "s'"

let x = v "x"

let y = v "y"

let ab = v "ab"

let out = v "out"

let borrow = v "borrow"

let borrow' = v "borrow'"

let br = v "br"

let br' = v "br'"

let uf = v "uf"

let no_uf = v "no_uf"

let has_uf = v "has_uf"

let add = v "add"

let sub = v "sub"

let tmp = v "tmp"

(* { F | v <= C.k - 2 } *)
let t_n = attaches [lift (nu <=. CPLen -! z2); lift (z1 <=. nu)] tnat

(* { F | ^v <= 2^n - 1 } *)
let tf_n_bit = tfe (toUZ nu <=. (z2 ^! n) -! z1)

let mod_sub_three =
  Circuit
    { name= "ModSubThree"
    ; inputs= [("n", t_n); ("a", tf_n_bit); ("b", tf_n_bit); ("c", tf_binary)]
    ; outputs=
        [("out", tf); ("borrow", tfq (ind_dec nu (toUZ a <. toUZ (b +% c))))]
    ; (* out = borrow * 2 ** n + a - (b + c) *)
      dep= Some (out ==. (borrow *% (f2 ^% n)) +% a -% (b +% c))
    ; body=
        elet "borrow"
          (call "LessThan" [n +. z1; a; b +% c])
          (pair
             (* borrow === #LessThan (n + 1) a (b + c) *)
             ((borrow *% (f2 ^% n)) +% a -% (b +% c))
             (* out === borrow * 2 ** n + a - (b + c) *)
             borrow ) }

(* Proper big Ints of length k *)
let t_big_int k = tarr_t_k tf_n_bit k

let inv_big_sub i =
  refine
    (ttuple
       [t_big_int i; tfq (ind_dec nu (as_le n (take a i) <. as_le n (take b i)))] )
    ( as_le n (tfst nu)
    ==. as_le n (take a i)
        -! as_le n (take b i)
        +! ((z2 ^! (n *! i)) *! toUZ (tsnd nu)) )

let big_sub =
  Circuit
    { name= "BigSub"
    ; inputs=
        [ ("n", t_n)
        ; ("k", attach (lift (z1 <=. nu)) tnat)
        ; ("a", t_big_int k)
        ; ("b", t_big_int k) ]
    ; outputs=
        [("out", t_big_int k); ("uf", tfq (ind_dec nu (as_le n a <. as_le n b)))]
    ; dep=
        Some
          ( as_le n out
          ==. as_le n a -! as_le n b +! ((z2 ^! (n *! k)) *! toUZ uf) )
    ; body=
        match_with' ["s"; "br"]
          (iter z0 k
             ~init:(pair (push cnil) f0)
             ~inv:inv_big_sub
             (lama "i" tint
                (lama_match
                   [("s'", tarr tf); ("br'", tf)]
                   (elets
                      [("ai", get a i); ("bi", get b i)]
                      (match_with' ["s"; "br"]
                         (call "ModSubThree" [n; ai; bi; br'])
                         (pair (push (concat s' (const_array tf [v "s"]))) br) ) ) ) ) )
          (pair (push s) br) }

(* BigSubModP *)

let t_big_int_lt_p k =
  tarr_t_q_k tf_n_bit (lift (as_le n nu <=. as_le n p -! z1)) k

let t_out k =
  tarr_t_q_k tf_n_bit
    (as_le n nu ==. zmod (as_le n a -! as_le n b) (as_le n p))
    k

let t_n' = attaches [lift (nu <=. CPLen -! z2); lift (z1 <=. nu)] tnat

let big_sub_mod_p =
  Circuit
    { name= "BigSubModP"
    ; inputs=
        [ ("n", t_n')
        ; ("k", attach (lift (z1 <=. nu)) tnat)
        ; ("a", t_big_int_lt_p k)
        ; ("b", t_big_int_lt_p k)
        ; ("p", t_big_int k) ]
    ; outputs= [("out", t_out k)]
    ; dep= None
    ; body=
        match_with' ["sub"; "uf"]
          (call "BigSub" [n; k; a; b])
          (elets
             [(* add = #BigAdd n k a b *) ("add", call "BigAdd" [n; k; sub; p])]
             (push (apps (v "ite_array") [k; uf; take add k; sub])) ) }
