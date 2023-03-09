open Dsl

let ( ** ) = star

let ( === ) = assert_eq

let ( *% ) = fmul

let ( +% ) = fadd

let ( -% ) = fsub

let ( ^% ) = fpow

let ( *! ) = zmul

let ( +! ) = zadd

let ( -! ) = zsub

let ( ^! ) = zpow

let ( ^. ) = npow

let ( *. ) = nmul

let ( +. ) = nadd

let ( -. ) = nsub

let ( =. ) = eq

let ( <. ) = lt

let ( <=. ) = leq

let ( @! ) = bnot

let ( @&& ) = band

let ( @|| ) = bor

let ( @==> ) = imply

let ( #! ) = qnot

let ( #&& ) = qand

(* let (@||) = bor *)

let ( #==> ) = qimply
