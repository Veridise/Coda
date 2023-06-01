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

let ( ==. ) = qeq

let to_q op f1 f2 = op (toUZ f1) (toUZ f2)

let ( <. ) = lt

let ( <.. ) = to_q ( <. )

let ( >. ) a b = b <. a

let ( >.. ) = to_q ( >. )

let ( <=. ) = leq

let ( <=.. ) = to_q ( <=. )

let ( >=. ) a b = b <=. a

let ( >=.. ) = to_q ( >=. )

let ( @! ) = bnot

let ( @&& ) = band

let ( @|| ) = bor

let ( @==> ) = imply

let ( #! ) = qnot

let ( #&& ) = qand

(* let (@||) = bor *)

let ( #==> ) = qimply
