(** Benchmarks ModSumThree, BigAdd, BigAddModP *)

open Ast
open Dsl
open Notation

let n = v "n"

let k = v "k"

let p = v "p"

let p' = v "p'"

let a = v "a"

let ai = v "ai"

let b = v "b"

let bi = v "bi"

let c = v "c"

let c' = v "c'"

let i = v "i"

let s = v "s"

let s' = v "s'"

let x = v "x"

let y = v "y"

let n2b = v "n2b"

let sum = v "sum"

let sub = v "sub"

let carry = v "carry"

let add = v "add"

let lt = v "lt"

let out = v "out"

(* { F | ^v <= C.k - 1 } *)
let t_n = attaches [lift (nu <=. CPLen -! z1); lift (z1 <=. nu)] tnat

(* { F | ^v <= 2^n - 1 } *)
let tf_n_bit = tfe (toUZ nu <=. (z2 ^! n) -! z1)

let mod_sum_three =
  Circuit
    { name= "ModSumThree"
    ; inputs= [("n", t_n); ("a", tf_n_bit); ("b", tf_n_bit); ("c", tf_binary)]
    ; outputs= [("sum", tf_n_bit); ("carry", tf_binary)]
    ; dep= Some (sum +% ((f2 ^% n) *% carry) ==. a +% b +% c)
    ; body=
        (* n2b = #Num2Bits (n + 1) (a + b + c) *)
        elet "n2b"
          (call2 "Num2Bits" (n +. z1) (a +% b +% c))
          (elets
             [ (* carry = N2B.out[n] *)
               ("carry", get n2b n)
             ; (* sum === a + b + c - carry * 2^n *)
               ("sum", a +% b +% c -% (carry *% (f2 ^% n))) ]
             (pair sum carry) ) }

(* Proper big Ints of length k *)
let t_big_int k = tarr_t_k tf_n_bit k

let inv_big_add i =
  refine
    (ttuple [t_big_int i; tf_binary])
    ( as_le n (concat (tfst nu) (consts [tsnd nu]))
    ==. as_le n (take a i) +! as_le n (take b i) )

let big_add =
  Circuit
    { name= "BigAdd"
    ; inputs=
        [ ("n", t_n)
        ; ("k", refine_expr tnat (z1 <=. nu))
        ; ("a", t_big_int k)
        ; ("b", t_big_int k) ]
    ; outputs=
        [ ( "out"
          , attach (as_le n nu ==. as_le n a +! as_le n b) (t_big_int (k +. z1))
          ) ]
    ; dep= None
    ; body=
        match_with' ["sum"; "carry"]
          (iter z0 k
             ~init:(pair (push cnil) f0)
             ~inv:inv_big_add
             (lama "i" tint
                (lama_match
                   [("s'", tarr tf); ("c'", tf)]
                   (elets
                      [("ai", get a i); ("bi", get b i)]
                      (match_with' ["sum"; "carry"]
                         (call "ModSumThree" [n; ai; bi; c'])
                         (pair
                            (push (concat s' (const_array tf [v "sum"])))
                            (v "carry") ) ) ) ) ) )
          (* out === sum ++ [carry] *)
          (push (concat (v "sum") (consts [v "carry"]))) }

(* BigAddModP *)

let t_big_int_lt_p k =
  tarr_t_q_k tf_n_bit (lift (as_le n nu <=. as_le n p -! z1)) k

let t_big_int_add_mod_p k =
  tarr_t_q_k tf_n_bit
    (as_le n nu ==. zmod (as_le n a +! as_le n b) (as_le n p))
    k

let t_n' = attaches [lift (nu <=. CPLen -! z2); lift (z1 <=. nu)] tnat

let big_add_mod_p =
  Circuit
    { name= "BigAddModP"
    ; inputs=
        [ ("n", t_n')
        ; ("k", attach (lift (z1 <=. nu)) tnat)
        ; ("a", t_big_int_lt_p k)
        ; ("b", t_big_int_lt_p k)
        ; ("p", t_big_int k) ]
    ; outputs= [("out", t_big_int_add_mod_p k)]
    ; dep= None
    ; body=
        elets
          [ (* add = #BigAdd n k a b *)
            ("add", call "BigAdd" [n; k; a; b])
          ; (* lt = #BigLessThan n (k + 1) add (p ++ [0]) *)
            ("lt", call "BigLessThan" [n; k +. z1; add; concat p (consts [f0])])
          ; (* p' = scale (k+1) (1 - lt) (p ++ [0]) *)
            ("p'", apps (v "scale") [k +. z1; f1 -% lt; concat p (consts [f0])])
          ; (* sub = #BigSub n (k + 1) add p' *)
            ("sub", tfst (call "BigSub" [n; k +. z1; add; p']))
            (* ("u0", assert_eq (get sub k) f0)  *) ]
          (take sub k) }
