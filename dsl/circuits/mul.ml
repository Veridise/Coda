open Ast
open Dsl
open Typecheck
open Bitify

let n = v "n"

let a = v "a"

let b = v "b"

let n2b = v "n2b"

let prod = v "prod"

let carry = v "carry"

(* { Z | 0 <= v /\ 2 * v <= C.k } *)
let t_n = TRef (TInt, qand (QExpr (leq z0 nu)) (QExpr (leq (zmul z2 nu) CPLen)))

let mod_prod =
  Circuit
    { name= "ModProd"
    ; inputs= [("n", t_n); ("a", tf); ("b", tf)]
    ; outputs= [("prod", tf); ("carry", tf)]
    ; (* carry * 2 ^ n + prod = a * b *)
      dep= Some (qeq (fadd (fmul carry (fpow f2 n)) prod) (fmul a b))
    ; body=
        [ (* n2b = #Num2Bits (2 * n) (a * b) *)
          slet "n2b" (call "Num2Bits" [zmul z2 n; fmul a b])
        ; (* prod === #Bits2Num n (take n n2b) *)
          assert_eq prod (call "Bits2Num" [n; take n n2b])
        ; (* carry === #Bits2Num n (drop n n2b) *)
          assert_eq carry (call "Bits2Num" [n; drop n n2b]) ] }

let deltas_mp = add_to_deltas d_empty [num2bits; bits2num]

let check_mod_prod = typecheck_circuit deltas_mp mod_prod
