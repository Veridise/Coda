open Ast
open Core

(* common basic types *)
let base tb = TBase tb

let tf = base TF

let tfq q = TRef (tf, q)

let tfe e = TRef (tf, QExpr e)

let tint = base TInt

let tbool = base TBool

let tboole e = TRef (tbool, QExpr e)

(* lambda *)
let lam x e = Lam (x, e)

(* lambda with type-annotated input *)
let lama x t e = LamA (x, t, e)

let lamas x_t e = List.fold_right ~f:(Utils.uncurry lama) x_t ~init:e

(* type annotation *)
let ascribe e t = Ascribe (e, t)

(* dummy term with type t *)
let dummy x t = AscribeUnsafe (Var x, t)

(* application *)
let app f x = App (f, x)

(* curried application *)
let rec apps f = function [] -> f | x :: xs -> apps (app f x) xs

(* curried application of a dummy function *)
let dummy_apps s f es = apps (dummy s f) es

(* function type *)
let tfun x t1 t2 = TFun (x, t1, t2)

(* tuple type *)
let ttuple ts = TTuple ts

let tpair t1 t2 = ttuple [t1; t2]
(* refinement type with base tb refined by expression e *)

(* expressions *)
let refine t q = TRef (t, q)

let triv t = refine t QTrue

let refine_expr t e = TRef (t, QExpr e)

let attach q = function
  | TRef (t, q') ->
      TRef (t, QAnd (q', q))
  | t ->
      TRef (t, q)

let get_tq t = match t with TRef (t, q) -> (t, q) | _ -> (t, QTrue)

let as_tref t =
  let t', q = get_tq t in
  TRef (t', q)

let attaches qs t = List.fold_right qs ~f:attach ~init:t

let badd b e1 e2 = Binop (b, Add, e1, e2)

let nadd = badd BNat

let zadd = badd BZ

let fadd = badd BF

let rec badds b es =
  match es with
  | [e] ->
      e
  | e :: es ->
      badd b e (badds b es)
  | [] ->
      failwith "badds: []"

let nadds = badds BNat

let zadds = badds BZ

let fadds = badds BF

let bsub b e1 e2 = Binop (b, Sub, e1, e2)

let nsub = bsub BNat

let zsub = bsub BZ

let fsub = bsub BF

let rec bsubs b es =
  match es with
  | [e] ->
      e
  | e :: es ->
      bsub b e (bsubs b es)
  | [] ->
      failwith "bsubs: []"

let nsubs = bsubs BNat

let zsubs = bsubs BZ

let fsubs = bsubs BF

let bmul b e1 e2 = Binop (b, Mul, e1, e2)

let nmul = bmul BNat

let zmul = bmul BZ

let fmul = bmul BF

let rec bmuls b es =
  match es with
  | [e] ->
      e
  | e :: es ->
      bmul b e (bmuls b es)
  | [] ->
      failwith "bmuls: []"

let nmuls = bmuls BNat

let zmuls = bmuls BZ

let fmuls = bmuls BF

let bpow b e1 e2 = Binop (b, Pow, e1, e2)

let npow = bpow BNat

let zpow = bpow BZ

let fpow = bpow BF

let bmod b e1 e2 = Binop (b, Mod, e1, e2)

let nmod = bmod BNat

let zmod = bmod BZ

let eq e1 e2 = Comp (Eq, e1, e2)

let leq e1 e2 = Comp (Leq, e1, e2)

let lt e1 e2 = Comp (Lt, e1, e2)

let qeq e1 e2 = QExpr (eq e1 e2)

let qleq e1 e2 = QExpr (leq e1 e2)

let qlt e1 e2 = QExpr (lt e1 e2)

let unint s es = Fn (Unint s, es)

let call f es = Call (f, es)

let star = NonDet

let bnot e = Not e

let bor e1 e2 = Boolop (Or, e1, e2)

let imply e1 e2 = Boolop (Imply, e1, e2)

let band e1 e2 = Boolop (And, e1, e2)

let qnot q = QNot q

let qand q1 q2 = QAnd (q1, q2)

let qimply q1 q2 = QImply (q1, q2)

let match_with e1 xs e2 = DMatch (e1, xs, e2)

let dmake es q = DMake (es, q)

let tunit = ttuple []

let tunit_dep q = refine tunit q

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

let zsub2 e = zsub e z2

let fopp e = fsub f0 e

let zopp e = zsub z0 e

let btrue = Const (CBool true)

let bfalse = Const (CBool false)

let is_binary e = bor (eq e f0) (eq e f1)

let tf_binary = tfe (is_binary nu)

let binary_eq e = eq (fmul e (zsub1 e)) f0

let ite e1 e2 e3 = band (imply e1 e2) (imply (bnot e1) e3)

let ind e1 e2 e3 =
  qand
    (QExpr (is_binary e1))
    (QExpr (band (imply (eq e1 f1) e2) (imply (eq e1 f0) e3)))

let q_ind e q1 q2 =
  qand
    (QExpr (is_binary e))
    (qand (qimply (qeq e f1) q1) (qimply (qeq e f0) q2))

let ind_dec e1 e2 = ind e1 e2 (bnot e2)

let q_ind_dec e q = q_ind e q (qnot q)

let tnat = TRef (tint, QExpr (leq z0 nu))

let tnat_e e = TRef (tint, QAnd (QExpr (leq z0 nu), QExpr e))

let tpos = TRef (tint, QExpr (lt z0 nu))

let make es = TMake es

let unit_val = make []

let tget e n = TGet (e, n)

let fst_pair e = tget e 0

let snd_pair e = tget e 1

let pair e1 e2 = make [e1; e2]

let qforall i i0 i1 q = QForall ((i, i0, i1), q)

let qforall_e i i0 i1 e = QForall ((i, i0, i1), QExpr e)

let assert_eq e1 e2 = Assert (e1, e2)

let elet x e1 e2 = LetIn (x, e1, e2)

let elets x_r e = List.fold_right x_r ~f:(Utils.uncurry elet) ~init:e

let elet_p xs e1 e2 =
  let jumble = String.concat ~sep:"_" xs in
  elet jumble e1
    (elets (List.mapi xs ~f:(fun i x -> (x, tget (v jumble) i))) e2)

let lama_p x_t e =
  let xs, ts = List.unzip x_t in
  let jumble = String.concat ~sep:"_" xs in
  lama jumble (ttuple ts)
    (elets (List.mapi xs ~f:(fun i x -> (x, tget (v jumble) i))) e)

let tarr t = TArr t

let sum es ee eb = Sum {s= es; e= ee; body= eb}

let rsum s e t = RSum (s, e, t)

let get xs i = ArrayOp (Get, [xs; i])

let len xs = ArrayOp (Length, [xs])

let cons x xs = ArrayOp (Cons, [x; xs])

let concat xs1 xs2 = ArrayOp (Concat, [xs1; xs2])

let take n xs = ArrayOp (Take, [n; xs])

let drop n xs = ArrayOp (Drop, [n; xs])

let zip e1 e2 = ArrayOp (Zip, [e1; e2])

let iter s e body ~init ~inv = Iter {s; e; body; init; inv}

let map e1 e2 = Map (e1, e2)

(* { Array<t> | length v = k } *)
let tarr_t_k t k = TRef (tarr t, qeq (len nu) k)

(* { Array<t> | length v = k /\ q } *)
let tarr_t_q_k t q k = TRef (tarr t, qand q (qeq (len nu) k))

let tarr_tf = tarr_t_k tf

let to_big_int (tb : base) (n : expr) (k : expr) (xs : expr) : expr =
  let sub1 = match tb with TF -> fsub1 | TInt -> nsub1 in
  let mul = match tb with TF -> fmul | TInt -> zmul in
  let pow = match tb with TF -> fpow | TInt -> zpow in
  rsum z0 (sub1 k)
    (tfun "i" tint
       (TRef
          ( base tb
          , QExpr (eq nu (mul (get xs (v "i")) (pow f2 (mul n (v "i"))))) ) ) )

let z_range l r = TRef (tint, qand (QExpr (leq l nu)) (QExpr (leq nu r)))

let z_range_co l r = TRef (tint, qand (QExpr (leq l nu)) (QExpr (lt nu r)))

let toSZ e = Fn (ToSZ, [e])

let toUZ e = Fn (ToUZ, [e])

let push e = Push e

let pull e = Pull e

let circuit ?(dep = None) ~name ~inputs ~outputs ~body =
  Circuit {name; inputs; outputs; dep; body}

let stars k =
  let i = v "i" in
  let x = v "x" in
  let lam_stars = lama "i" tint (lama "x" (tarr_t_k tf i) (cons star x)) in
  let inv_stars i = tarr_t_k tf i in
  iter z0 k lam_stars cnil inv_stars