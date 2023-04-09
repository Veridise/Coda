open Ast
open Core
open Big_int_Z

(* common basic types *)
let base tb = TBase tb

let tf = base TF

let tfq q = TRef (tf, q)

let lift e = QExpr e

let lower q = EQual q

let tfe e = TRef (tf, lift e)

let tint = base TInt

let tbool = base TBool

let tboole e = TRef (tbool, lift e)

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

let refine_expr t e = TRef (t, lift e)

let attach q = function
  | TRef (t, QTrue) ->
      TRef (t, q)
  | TRef (t, q') ->
      TRef (t, QAnd (q', q))
  | t ->
      TRef (t, q)

let get_tq t = match t with TRef (t, q) -> (t, q) | _ -> (t, QTrue)

let as_tref t =
  let t', q = get_tq t in
  TRef (t', q)

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

let qeq e1 e2 = lift (eq e1 e2)

let qleq e1 e2 = lift (leq e1 e2)

let qlt e1 e2 = lift (lt e1 e2)

let unint s es = Fn (Unint s, es)

let zmax e1 e2 = unint "Z.max" [e1; e2]

let call f es = Call (f, es)

let call1 f e = call f [e]

let call2 f e1 e2 = call f [e1; e2]

let call3 f e1 e2 e3 = call f [e1; e2; e3]

let star = NonDet

let bnot e = Not e

let bor e1 e2 = Boolop (Or, e1, e2)

let imply e1 e2 = Boolop (Imply, e1, e2)

let band e1 e2 = Boolop (And, e1, e2)

let qnot q = QNot q

let qand q1 q2 = QAnd (q1, q2)

let qor q1 q2 = QOr (q1, q2)

let qimply q1 q2 = QImply (q1, q2)

let ors qs = List.fold_right qs ~f:(fun q q' -> qor q q') ~init:QTrue

let ands qs = List.fold_right qs ~f:(fun q q' -> qand q q') ~init:QTrue

let attaches qs t = attach (ands qs) t

let dmake es q = DMake (es, q)

let tunit = ttuple []

let tunit_dep q = refine tunit q

let v x = Var x

let nu = Var "ν"

let fc n = Const (CF n)

let zc n = Const (CInt n)

let cnil = Const CNil

let fn n = fc (big_int_of_int n)

let f0 = fn 0

let f1 = fn 1

let f2 = fn 2

let zn n = zc (big_int_of_int n)

let z0 = zn 0

let z1 = zn 1

let z2 = zn 2

let z3 = zn 3

let z252 = zn 252

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

let qtrue = QTrue

let qfalse = lift bfalse

let is_binary e = bor (eq e f0) (eq e f1)

let tf_binary = tfe (is_binary nu)

let binary_eq e = eq (fmul e (zsub1 e)) f0

let ite q1 q2 q3 = qand (qimply q1 q2) (qimply (qnot q1) q3)

let ite_expr e1 e2 e3 = ite (lift e1) (lift e2) (lift e3)

let ites qqs q =
  List.fold_right qqs ~f:(fun (qif, qthen) q -> ite qif qthen q) ~init:q

let ites_expr eqs q = ites (List.map eqs ~f:(fun (e, q) -> (lift e, q))) q

let contained_in e es = ors @@ List.map es ~f:(fun e' -> qeq e e')

let ind e1 e2 e3 =
  band (is_binary e1) (band (imply (eq e1 f1) e2) (imply (eq e1 f0) e3))

let q_ind e q1 q2 =
  qand (lift (is_binary e)) (qand (qimply (qeq e f1) q1) (qimply (qeq e f0) q2))

let ind_dec_expr e1 e2 = ind e1 e2 (bnot e2)

let ind_dec e1 e2 = lift (ind e1 e2 (bnot e2))

let q_ind_dec e q = q_ind e q (qnot q)

let tnat = TRef (tint, lift (leq z0 nu))

let tnat_e e = TRef (tint, QAnd (lift (leq z0 nu), lift e))

let tpos = TRef (tint, lift (lt z0 nu))

let make es = TMake es

let unit_val = make []

let tget e n = TGet (e, n)

let tfst e = tget e 0

let tsnd e = tget e 1

let pair e1 e2 = make [e1; e2]

let qquant quant i i0 i1 q = QQuant (quant, (i, i0, i1), q)

let qforall = qquant Forall

let qexists = qquant Exists

let qforall_e i i0 i1 e = qforall i i0 i1 (lift e)

let qexists_e i i0 i1 e = qexists i i0 i1 (lift e)

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

let u_sum xs = unint "sum" [xs]

let get xs i = ArrayOp (Get, [xs; i])

let len xs = ArrayOp (Length, [xs])

let cons x xs = ArrayOp (Cons, [x; xs])

let concat xs1 xs2 = ArrayOp (Concat, [xs1; xs2])

let take n xs = ArrayOp (Take, [n; xs])

let u_take n xs = unint "take" [n; xs]

let drop n xs = ArrayOp (Drop, [n; xs])

let u_drop n xs = unint "drop" [n; xs]

let zip e1 e2 = ArrayOp (Zip, [e1; e2])

let iter s e body ~init ~inv = Iter {s; e; body; init; inv}

let map e1 e2 = Map (e1, e2)

let match_with e1 xs e2 = DMatch (e1, xs, e2)

let lama_match x_t e =
  let xs, ts = List.unzip x_t in
  let jumble = String.concat ~sep:"_" xs in
  lama jumble (ttuple ts) (match_with (v jumble) xs e)

let match_with' xs e1 e2 =
  let x = String.concat ~sep:"_" xs in
  elet x e1 (match_with (v x) xs e2)

let pairwise_mul xs ys e' =
  elet "xy_s" (zip xs ys)
    (elet "xmy_s"
       (map
          (lama "x_y" (tpair tf tf)
             (fmul (tget (v "x_y") 0) (tget (v "x_y") 1)) )
          (v "xy_s") )
       (e' "xmy_s") )

let make_sum xs ~len =
  iter z0 len
    (lama "i" tint (lama "x" tf (fadd (v "x") (get xs (v "i")))))
    ~init:f0
    ~inv:(fun i -> tfq (qeq nu (u_sum (u_take i xs))))

(* { Array<t> | q v } *)
let tarr_t_q t q = TRef (tarr t, q)

(* { Array<t> | length v = k } *)
let tarr_t_k t k = refine_expr (tarr t) (eq (len nu) k)

(* { Array<t> | length v = k /\ q } *)
let tarr_t_q_k t q k = TRef (tarr t, qand q (qeq (len nu) k))

let tarr_tf = tarr_t_k tf

let as_le (base : expr) (xs : expr) : expr = unint "as_le" [base; xs]

let as_be (base : expr) (xs : expr) : expr = unint "as_be" [base; xs]

let as_le_signed (base : expr) (xs : expr) : expr =
  unint "as_le_signed" [base; xs]

let as_be_signed (base : expr) (xs : expr) : expr =
  unint "as_be_signed" [base; xs]

let as_le_f (xs : expr) : expr = unint "as_le_f" [xs]

let as_be_f (xs : expr) : expr = unint "as_be_f" [xs]
(* let sub1 = match tb with TF -> fsub1 | TInt -> nsub1 in
   let mul = match tb with TF -> fmul | TInt -> zmul in
   let pow = match tb with TF -> fpow | TInt -> zpow in
   rsum z0 (sub1 k)
     (tfun "i" tint
        (TRef
           ( base tb
           , lift (eq nu (mul (get xs (v "i")) (pow f2 (mul n (v "i"))))) ) ) ) *)

let to_le_f (n : expr) (f : expr) : expr = unint "to_le_f" [n; f]

let z_range l r = TRef (tint, qand (lift (leq l nu)) (lift (leq nu r)))

let z_range_co l r = TRef (tint, qand (lift (leq l nu)) (lift (lt nu r)))

let toSZ e = Fn (ToSZ, [e])

let toUZ e = Fn (ToUZ, [e])

let f_range l r =
  TRef (tf, qand (lift (leq l (toUZ nu))) (lift (leq (toUZ nu) r)))

let f_range_co l r =
  TRef (tf, qand (lift (leq l (toUZ nu))) (lift (lt (toUZ nu) r)))

let push e = Push e

let pull e = Pull e

let const_array t es =
  AscribeUnsafe
    ( List.fold_right es ~f:cons ~init:cnil
    , tarr_t_q_k t
        (List.foldi es ~init:QTrue ~f:(fun i q e ->
             qand q (lift (eq (get nu (zn i)) e)) ) )
        (zn @@ List.length es) )

let consts es = List.fold_right es ~f:cons ~init:cnil

let circuit ?(dep = None) ~name ~inputs ~outputs ~body =
  Circuit {name; inputs; outputs; dep; body}
