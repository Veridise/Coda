open Ast
open Core
open Utils

let show_tyBase = function
  | TF -> "F"
  | TInt -> "Z"
  | TBool -> "Bool"

let show_binop = function
  | Add ->  "+"
  | Sub -> "-"
  | Mul ->  "*"
  | Pow -> "^"

let show_boolop = function
  | And -> "/\\"
  | Or -> "\\/"
  | Imply -> "->"

let show_comp = function
  | Eq -> "="
  | Leq -> "<="
  | Lt -> "<"

let show_func = function
| Id -> "id"
| Unint f -> "$"^f
| ToUZ -> "toUZ"
| ToSZ -> "toSZ"
| ToBigUZ -> "toBigUZ"
| ToBigSZ -> "toBigSZ"

let show_aop = function
| Cons -> "cons"
| Get -> "get"
| Concat -> "@"
| Scale -> "scale"
| Take -> "take"
| Drop -> "drop"
| Zip -> "zip"

let ppf_tyBase ppf tb = Fmt.string ppf (show_tyBase tb)
let ppf_binop ppf op = Fmt.string ppf (show_binop op)
let ppf_boolop ppf op = Fmt.string ppf (show_boolop op)
let ppf_comp ppf op = Fmt.string ppf (show_comp op)
let ppf_func ppf f = Fmt.string ppf (show_func f)
let ppf_aop ppf op = Fmt.string ppf (show_aop op)

let ppf_const ppf = Fmt.(function
  | CNil -> string ppf "[]"
  | CUnit -> string ppf "()"
  | CInt n -> int ppf n
  | CF n -> int ppf n
  | CBool b -> bool ppf b
)

let rec ppf_typ ppf  =  Fmt.(
  let times = Fmt.any " ×@ " in
  function
  | TRef (tb, q) -> 
    (match q with
    | QTrue -> ppf_tyBase ppf tb
    | _ -> pf ppf "{%a | %a}" ppf_tyBase tb ppf_qual q)
  | TFun (x,t1,t2) ->
    (match t1 with 
        | TFun _ -> pf ppf "%s: (%a) -> %a" x ppf_typ t1 ppf_typ t2
        | _ -> pf ppf "%s: %a -> %a" x ppf_typ t1 ppf_typ t2)

  | TArr (t, q, l) ->
    pf ppf "Array<%a>[%a](%a)" ppf_typ t ppf_qual q ppf_expr l
    
    | TTuple ts ->
      if List.length ts = 0 then
        pf ppf "unit"
      else
        pf ppf "%a" (list ~sep:(any " ×@ ") ppf_typ) ts
    
  | TDProd (ts, xs, q) -> 
      pf ppf "(%a)_(λ%a. %a)"
        (list ~sep:times ppf_typ) ts
        (list ~sep:times string) xs
        ppf_qual q
      | _ -> pf ppf "TODO: ppf_typ")
  
and ppf_qual ppf  = Fmt.(function
| QTrue -> pf ppf "⊤"
| QExpr e -> ppf_expr ppf e
| QNot q -> pf ppf "(not %a)" ppf_qual q
| QAnd (q1,q2) -> pf ppf "(qand %a %a)" ppf_qual q1 ppf_qual q2
| QImply (q1,q2) -> pf ppf "(qimply %a %a)" ppf_qual q1 ppf_qual q2
| QForall ((x,s,e),q) -> pf ppf "∀%a<=%s<%a. %a"
  ppf_expr s
  x
  ppf_expr e
  ppf_qual q)

and ppf_expr ppf : expr -> unit = Fmt.(function
| NonDet -> string ppf "✧"
| Const c -> ppf_const ppf c
| CPrime -> string ppf "C.q"
| CPLen -> string ppf "C.k"
| Var x -> string ppf x
| Ascribe (e,t) -> pf ppf "(%a :: %a)" ppf_expr e ppf_typ t
| AscribeUnsafe (e,t) -> pf ppf "(%a ! <%a>)" ppf_expr e ppf_typ t
| LamA (x,t,e) -> pf ppf "λ%s: %a. %a" x ppf_typ t ppf_expr e
| Lam (x,e) -> pf ppf "λ%s. %a" x ppf_expr e
| LamP _ -> string ppf "TODO: ppf_expr: LamP"
(* | LamP (p, e) -> pf ppf "λ%a. %a" ppf_pattern p ppf_expr e *)
| App (e1,e2) -> pf ppf "%a %a" ppf_expr e1 ppf_expr e2
| Binop (_,op,e1,e2) -> pf ppf "(%a %a %a)" ppf_binop op ppf_expr e1 ppf_expr e2
| Not e -> pf ppf "(not %a)" ppf_expr e
| Boolop (op,e1,e2) -> pf ppf "(%a %a %a)" ppf_boolop op ppf_expr e1 ppf_expr e2
| Comp (op,e1,e2) -> pf ppf "(%a %a %a)" ppf_comp op ppf_expr e1 ppf_expr e2
| Call (c,args) -> pf ppf "#%s(%a)" c (list ~sep:(Fmt.any ", ") ppf_expr) args
| LetIn (x,e1,e2) -> pf ppf "let %s = %a in %a" x ppf_expr e1 ppf_expr e2
| ArrayOp (op, es) -> pf ppf "(%a %a)" ppf_aop op (list ppf_expr) es
| RSum (s,e,t) -> pf ppf "\\sum_{%a, %a}(%a)" ppf_expr s ppf_expr e ppf_typ t
| Sum {s;e;body} -> pf ppf "\\sum_{%a, %a}(%a)" ppf_expr s ppf_expr e ppf_expr body
| TMake (es) -> pf ppf "%a" (parens (list ~sep:comma ppf_expr)) es
| TGet (e,n) -> pf ppf "%a.%d" ppf_expr e n
| DPCons _ -> string ppf "TODO: ppf_expr: DPCons"
| DPDestr _ -> string ppf "TODO: ppf_expr: DPDestr"
| DPDestrP _ -> string ppf "TODO: ppf_expr: DPDestrP"
| Map _ -> string ppf "TODO: ppf_expr: Map"
| Foldl _ -> string ppf "TODO: ppf_expr: Foldl"
| Iter _ -> string ppf "TODO: ppf_expr: Iter"
| Fn (f,es) -> pf ppf "(%a %a)" ppf_func f (list ppf_expr) es)



let show_typ (t: typ) = Fmt.str "%a" ppf_typ t
let show_qual (q: qual) = Fmt.str "%a" ppf_qual q
let show_expr (e: expr) = Fmt.str "%a" ppf_expr e
let show_const (c: const) = Fmt.str "%a" ppf_const c



module SS = StringSet

let unions ss = List.fold_left ~f:SS.union ~init:SS.empty ss
let except s x = SS.diff s (SS.singleton x)
let excepts s xs = SS.diff s (SS.of_list xs)
let count = ref 0
let fresh x = let c = !count in count := c+1; x ^ Int.to_string c

let rec vars_typ : typ -> SS.t = function
  | TRef (_, q) -> except (vars_qual q) nu_str
  | TFun (x, t1, t2) -> SS.union (vars_typ t1) (except (vars_typ t2) x)
  | TTuple _ -> todo ()
  | TDProd _ -> todo ()
  | TArr (t, q, e) -> unions [vars_typ t; except (vars_qual q) nu_str; vars_expr e]

and vars_qual : qual -> SS.t = function
  | QExpr e -> vars_expr e
  | QForall ((x,s,e), q) -> unions [except (vars_qual q) x; (vars_expr s); (vars_expr e)]
  | _ -> SS.empty

and vars_expr : expr -> SS.t = function
  | Const _ -> SS.empty
  | Var x -> SS.singleton x
  | Lam (x, e) -> except (vars_expr e) x
  | LamP (p, e) -> SS.diff (vars_expr e) (vars_pattern p) 
  | App (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Binop (_, _, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Not e -> vars_expr e
  | Boolop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Comp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Call (_, es) -> unions (List.map ~f:vars_expr es)
  | ArrayOp (_, es) -> unions (List.map ~f:vars_expr es)
  | Sum {s=s;e=e';body=body} -> unions [vars_expr s; vars_expr e'; vars_expr body]
  | DPCons (es, xs, q) -> todos "vars_expr: DPCons"
  | TMake es -> unions (List.map ~f:vars_expr es)
  | DPDestr (e1, xs, e2) -> SS.union (vars_expr e1) (excepts (vars_expr e2) xs)
  | DPDestrP (e1, p, e2) -> SS.union (vars_expr e1) (SS.diff (vars_expr e2) (vars_pattern p))
  | Map (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Foldl {f; acc; xs} -> unions (List.map ~f:vars_expr [f; acc; xs])
  | Iter {s; e; body; init; inv} ->
    let vars_e = unions (List.map ~f:vars_expr [s;e;body;init]) in
    let (x1, x2) = (fresh "_var", fresh "_var") in
    let vars_inv = excepts (vars_typ (inv (Var x1) (Var x2))) [x1; x2] in
    unions [vars_e; vars_inv]
  | Fn (_, es) -> unions (List.map ~f:vars_expr es)
  
and vars_pattern : pattern -> SS.t = function
  | PStr x -> SS.singleton x
  | PProd pp -> unions (List.map ~f:vars_pattern pp)

let rec subst_typ (x: string) (e: expr) (t: typ) : typ =
  let f = subst_typ x e in
  match t with
  | TRef (tb, q) -> TRef (tb, subst_qual x e q)
  | TFun (y, t1, t2) ->
    if String.(x = y) then
      t
    else
      (* TODO: alpha-rename *)
      TFun (y, subst_typ x e t1, subst_typ x e t2) 
  | TArr (t, q, e') -> TArr (f t, subst_qual x e q, subst_expr x e e')
  | TTuple ts -> TTuple (List.map ~f ts)
  | TDProd (ts, ys, q) ->
    let ts' = List.map ~f ts in
    if List.exists ~f:(String.(=)x) ys then
      TDProd (ts', ys, q)
    else
      TDProd (ts', ys, subst_qual x e q)

and subst_qual (x: string) (e: expr) (q: qual) : qual =
  match q with
  | QTrue -> q
  | QNot q' -> QNot (subst_qual x e q')
  | QAnd (q1, q2) -> QAnd (subst_qual x e q1, subst_qual x e q2)
  | QExpr e' -> QExpr (subst_expr x e e')
  | QForall ((y,es,ee), q') ->
      QForall ((y, subst_expr x e es, subst_expr x e ee), if String.(x = y) then q' else subst_qual x e q')

and subst_expr (x: string) (ef: expr) (e: expr) : expr =
  let f = subst_expr x ef in
  match e with
  | Const _ -> e
  | CPrime -> e
  | CPLen -> e
  | Var y -> if String.(x = y) then ef else e
  | LamA (y, t, body) ->
    if String.(x = y) then e else LamA (y, subst_typ x ef t, f body)
  | App (e1, e2) -> App (f e1, f e2)
  | Not e' -> Not (f e')
  | Binop (t, op, e1, e2) -> Binop (t, op, f e1, f e2)
  | Boolop (op, e1, e2) -> Boolop (op, f e1, f e2)
  | Comp (op, e1, e2) -> Comp (op, f e1, f e2) 
  | Call (c, es) -> Call (c, List.map ~f es)
  | ArrayOp (op, es) -> ArrayOp (op, List.map ~f es)
  | TMake es -> TMake (List.map ~f es)
  | TGet (e, n) -> TGet (f e, n)
  | Fn (fn, es) -> Fn (fn, List.map ~f es)
  | Iter {s; e; body; init; inv} ->
    Iter {
      s = f s; 
      e = f e; 
      body = f body; 
      init = f init; 
      inv = (fun ei -> fun ex -> (subst_typ x ef (inv ei ex)))
    }
  | Sum {s=s;e=e';body=body} -> Sum {s=f s; e=f e'; body=f body}
  | RSum (s,e,t) -> RSum (f s, f e, subst_typ x ef t)
  | DPCons (es, ys, q) ->
    let es' = List.map ~f es in
    if List.exists ~f:(String.(=)x) ys then
      DPCons (es', ys, q)
    else
      DPCons (es', ys, subst_qual x ef q)
  | DPDestr (e1, ys, e2) -> 
    if List.exists ~f:(String.(=)x) ys then
      DPDestr (f e1, ys, e2)
    else
      DPDestr (f e1, ys, f e2)
  | DPDestrP (e1, p, e2) -> todos "subst_expr: DPDestrP"
  | Map (e1, e2) -> todos "subst_expr: Map"
  | Foldl {f; acc; xs} -> todos "subst_expr: Foldl"
  | _ -> todos "subst_expr"
  