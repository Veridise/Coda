open Ast
(* common basic types *)
let triv tb = TRef (tb, QTrue)
let tf = triv TF
let tfq q = TRef (TF, q)
let tfe e = TRef (TF, QExpr e)
let tint = triv TInt
let tbool = triv TBool
let tboole e = TRef (TBool, QExpr e)

(* lambda *)
let lam x e = Lam (x, e)
(* lambda with type-annotated input *)
let lama x t e = LamA (x, t, e)
(* type annotation *)
let ascribe e t = Ascribe (e, t)
(* dummy term with type t *)
let dummy x t = AscribeUnsafe (Var x, t)
(* application *)
let app f x = App (f, x)
(* curried application *)
let rec apps f = function [] -> f | x::xs -> apps (app f x) xs
(* curried application of a dummy function *)
let dummy_apps s f es = apps (dummy s f) es

(* function type *)
let tfun x t1 t2 = TFun (x, t1, t2)
(* dependent product type *)
let tdprod ts xs q = TDProd (ts, xs, q)
(* tuple type *)
let ttuple ts = TTuple ts
let tpair t1 t2 = ttuple [t1; t2]
(* refinement type with base tb refined by expression e *)

(* expressions *)
let re tb e = TRef (tb, QExpr e)
let opp e = Opp e

let badd b e1 e2 = Binop (b, Add, e1, e2)
let nadd = badd BNat
let zadd = badd BZ
let fadd = badd BF
let rec badds b es = match es with [e] -> e | e::es -> badd b e (badds b es)
let nadds = badds BNat
let zadds = badds BZ
let fadds = badds BF

let bsub b e1 e2 = Binop (b, Sub, e1, e2)
let nsub = bsub BNat
let zsub = bsub BZ
let fsub = bsub BF
let rec bsubs b es = match es with [e] -> e | e::es -> bsub b e (bsubs b es)
let nsubs = bsubs BNat
let zsubs = bsubs BZ
let fsubs = bsubs BF

let bmul b e1 e2 = Binop (b, Mul, e1, e2)
let nmul = bmul BNat
let zmul = bmul BZ
let fmul = bmul BF
let rec bmuls b es = match es with [e] -> e | e::es -> bmul b e (bmuls b es)
let nmuls = bmuls BNat
let zmuls = bmuls BZ
let fmuls = bmuls BF

let bpow b e1 e2 = Binop (b, Pow, e1, e2)
let npow = bpow BNat
let zpow = bpow BZ
let fpow = bpow BF

let eq e1 e2 = Comp (Eq, e1, e2)
let qeq e1 e2 = QExpr (eq e1 e2)
let leq e1 e2 = Comp (Leq, e1, e2)
let lt e1 e2 = Comp (Lt, e1, e2)

let unint s es = Fn (Unint s, es)
let call f es = Call (f, es)
let star = NonDet

let bnot e = Not e
let bor e1 e2 = Boolop (Or, e1, e2)
let imply e1 e2 = Boolop (Imply, e1, e2)
let band e1 e2 = Boolop (And, e1, e2)
let qand q1 q2 = QAnd (q1, q2)
let qimply q1 q2 = QImply (q1, q2)

let match_with e1 xs e2 = DPDestr (e1, xs, e2)
let dpcons es xs q = DPCons (es, xs, q)
let dpunit q = dpcons [] [] q
let tdunit q = tdprod [] [] q
let ttunit = ttuple []

let v x = Var x
let nu = Var "ν"
let fc n = Const (CF n)
let zc n = Const (CInt n)
let cnil = Const CNil
let f0 = fc 0
let f1 = fc 1
let f2 = fc 2
let z0 = zc 0
let z1 = zc 1
let z2 = zc 2
let zadd1 e = zadd e z1
let nadd1 e = nadd e z1
let fadd1 e = fadd e f1
let zsub1 e = zsub e z1
let nsub1 e = nsub e f1
let fsub1 e = fsub e f1

let btrue = Const (CBool true)
let bfalse = Const (CBool false)
let is_binary e = bor (eq e f0) (eq e f1)
let tf_binary = tfe (is_binary nu)
let binary_eq e = eq (fmul e (zsub1 e)) f0
let ite e1 e2 e3 = band (imply e1 e2) (imply (bnot e1) e3)
let ind e1 e2 e3 = qand (QExpr (is_binary e1)) (QExpr (band (imply (eq e1 f1) e2) (imply (eq e1 f0) e3)))
let ind_dec e1 e2 = ind e1 e2 (bnot e2)
let tnat = TRef (TInt, QExpr (leq z0 nu))
let tnat_e e = TRef (TInt, QAnd (QExpr (leq z0 nu), QExpr e))

let tmake es = TMake es
let tget e n = TGet (e, n)
let fst_pair e = tget e 0
let snd_pair e = tget e 0
let make_pair e1 e2 = tmake [e1; e2]
let qforall i q = QForall (i, q)
let assert_eq e1 e2 = SAssert (e1, e2)
let slet x e = SLet (x, e)
let elet x e1 e2 = LetIn (x, e1, e2)
let tarr t q e = TArr (t, q, e)
let sum es ee eb = Sum {s=es;e=ee;body=eb}
let rsum s e t = RSum (s, e, t)
let get xs i = ArrayOp (Get, xs, i)
let cons x xs = ArrayOp (Cons, x, xs)
let concat xs1 xs2 = ArrayOp (Concat, xs1, xs2)
let take n xs = ArrayOp (Take, n, xs)
let drop n xs = ArrayOp (Drop, n, xs)
let to_big_int (tb: tyBase) (n: expr) (k: expr) (xs: expr): expr = 
  let sub1 = match tb with TF -> fsub1 | TInt -> nsub1 in
  let mul = match tb with TF -> fmul | TInt -> zmul in
  let pow = match tb with TF -> fpow | TInt -> zpow in
  rsum z0 (sub1 k) (tfun "i" tint (TRef (tb, QExpr (eq nu (mul (get xs (v "i")) (pow f2 (mul n (v "i"))))))))
let z_range l r = TRef (TInt, qand (QExpr (leq l nu)) (QExpr (leq nu r)))
let z_range_co l r = TRef (TInt, qand (QExpr (leq l nu)) (QExpr (lt nu r)))
let toSZ e = Fn (ToSZ, [e])
let toUZ e = Fn (ToUZ, [e])
