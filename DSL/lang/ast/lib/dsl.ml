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
let tprod ts xs q = TDProd (ts, xs, q)
(* tuple type *)
let ttuple ts = TTuple ts
let tpair t1 t2 = ttuple [t1; t2]
(* refinement type with base tb refined by expression e *)

(* expressions *)
let re tb e = TRef (tb, QExpr e)
let opp e = Opp e
let add e1 e2 = Binop (Add, e1, e2)
let rec adds es = match es with [e] -> e | e::es -> add e (adds es)
let sub e1 e2 = Binop (Sub, e1, e2)
let mul e1 e2 = Binop (Mul, e1, e2)
let rec muls es = match es with [e] -> e | e::es -> mul e (muls es)
let pow e1 e2 = Binop (Pow, e1, e2)
let eq e1 e2 = Comp (Eq, e1, e2)
let qeq e1 e2 = QExpr (eq e1 e2)
let leq e1 e2 = Comp (Leq, e1, e2)
let lt e1 e2 = Comp (Lt, e1, e2)
let unint s es = Fn (Unint s, es)
let call f es = Call (f, es)
let star = NonDet

let bnot e = Not e
let bor e1 e2 = Boolop (Or, e1, e2)
let band e1 e2 = Boolop (And, e1, e2)
let qand q1 q2 = QAnd (q1, q2)
let imply e1 e2 = Boolop (Imply, e1, e2)

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
let add1z e = add e z1
let add1f e = add e f1
let sub1z e = sub e z1
let sub1f e = sub e f1
let btrue = Const (CBool true)
let bfalse = Const (CBool false)
let is_binary e = bor (eq e f0) (eq e f1)
let tf_binary = tfe (is_binary nu)
let binary_eq e = eq (mul e (sub e f1)) f0
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
let assert_eq e1 e2 = SAssert (qeq e1 e2)
let slet x e = SLet (x, e)
let assert_forall i q = SAssert (qforall [i] q)
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
  let sub1 = match tb with TF -> sub1f | TInt -> sub1z in
  rsum z0 (sub1 k) (tfun "i" tint (TRef (tb, QExpr (eq nu (mul (get xs (v "i")) (pow f2 (mul n (v "i"))))))))
let z_range l r = TRef (TInt, qand (QExpr (leq l nu)) (QExpr (leq nu r)))
let z_range_co l r = TRef (TInt, qand (QExpr (leq l nu)) (QExpr (lt nu r)))
let toSZ e = Fn (ToSZ, [e])
let toUZ e = Fn (ToUZ, [e])
