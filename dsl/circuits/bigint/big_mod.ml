(** Benchmark BigMod *)

open Ast
open Dsl
open Notation
open Liblam

let n = v "n"

(* { F | ^v <= 2^n - 1 } *)

let tf_n_bit = tfe (toUZ nu <=. (z2 ^! n) -! z1)

(* { F | ^v <= C.k - 1 } *)
let t_n = attaches [lift (nu <=. CPLen -! z1); lift (z1 <=. nu)] tnat

(* Proper big Ints of length k *)
let t_big_int k = tarr_t_k tf_n_bit k

let k = v "k"

let a = v "a"

let b = v "b"

let div = v "div"

let mod_ = v "mod"

let mul = v "mul"

let x = v "x"

let add = v "add"

let lt = v "lt"

let big_mod =
  Circuit
    { name= "BigMod"
    ; inputs=
        [("n", t_n); ("k", t_n); ("a", t_big_int (z2 *. k)); ("b", t_big_int k)]
    ; outputs= [("div", t_big_int (k +. z1)); ("mod", t_big_int k)]
    ; dep= Some (as_le n a ==. as_le n b *! as_le n div +! as_le n mod_)
    ; body= 
    elets 
      [ ("div", stars (k +. z1));
        ("mod", stars k);
        ("u1", map (lama "x" tf_n_bit (call "Num2Bits" [n; x])) div );
        ("u2", map (lama "x" tf_n_bit (call "Num2Bits" [n; x])) mod_ );
        ("mul", ascribe (call "BigMult" [n; k +. z1; div; concat b (consts [f0])] ) (t_big_int (z2 *. k +. z2)));
        ("add", call "BigAdd" [n; z2 *. k +. z2; mul; concat mod_ (consts_n (k +. z3) f0)] );
        ("u3", assert_eq add (concat a (consts_n z2 f0)));
        ("lt", call "BigLessThan" [n; k; mod_; b] );
        ("u4", assert_eq lt f1)
    ]
        (pair div mod_)

     }
