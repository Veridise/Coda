open Ast
open Core
open Utils
open Big_int_Z

let show_base = function TF -> "F" | TInt -> "Z" | TBool -> "Bool"

let show_binop = function
  | Add ->
      "+"
  | Sub ->
      "-"
  | Mul ->
      "*"
  | Pow ->
      "^"
  | Mod ->
      "mod"

let show_boolop = function And -> "/\\" | Or -> "\\/" | Imply -> "->"

let show_comp = function Eq -> "=" | Leq -> "<=" | Lt -> "<"

let show_func = function
  | Id ->
      "id"
  | Unint f ->
      "$" ^ f
  | ToUZ ->
      "toUZ"
  | ToSZ ->
      "toSZ"
  | ToBigUZ ->
      "toBigUZ"
  | ToBigSZ ->
      "toBigSZ"

let show_aop = function
  | Length ->
      "length"
  | Cons ->
      "cons"
  | Get ->
      "get"
  | Concat ->
      "@"
  | Scale ->
      "scale"
  | Take ->
      "take"
  | Drop ->
      "drop"
  | Zip ->
      "zip"

let ppf_base ppf tb = Fmt.string ppf (show_base tb)

let ppf_binop ppf op = Fmt.string ppf (show_binop op)

let ppf_boolop ppf op = Fmt.string ppf (show_boolop op)

let ppf_comp ppf op = Fmt.string ppf (show_comp op)

let ppf_func ppf f = Fmt.string ppf (show_func f)

let ppf_aop ppf op = Fmt.string ppf (show_aop op)

let ppf_const ppf =
  Fmt.(
    function
    | CNil ->
        string ppf "[]"
    | CUnit ->
        string ppf "()"
    | CInt n ->
        Z.to_string n |> string ppf
    | CF n ->
        Z.to_string n |> string ppf
    | CBool b ->
        bool ppf b )

let rec ppf_typ ppf =
  Fmt.(
    let times = Fmt.any " × " in
    function
    | TBase tb ->
        ppf_base ppf tb (* pf ppf "Base<%a>" ppf_base tb *)
    | TFun (x, t1, t2) -> (
      match t1 with
      | TFun _ ->
          pf ppf "%s: (%a) -> %a" x ppf_typ t1 ppf_typ t2
      | _ ->
          pf ppf "%s: %a -> %a" x ppf_typ t1 ppf_typ t2 )
    | TArr t ->
        pf ppf "Array<%a>" ppf_typ t
    | TTuple ts ->
        if List.length ts = 0 then pf ppf "unit"
        else pf ppf "[%a]" (list ~sep:(any " × ") ppf_typ) ts
    | TRef (t, q) ->
        (* match q with
           | QTrue ->
               ppf_typ ppf t
           | _ -> *)
        pf ppf "{%a | %a}" ppf_typ t ppf_qual q )

and ppf_qual ppf =
  Fmt.(
    function
    | QTrue ->
        pf ppf "⊤"
    | QExpr e ->
        ppf_expr ppf e
    | QNot q ->
        pf ppf "(not %a)" ppf_qual q
    | QAnd (q1, q2) ->
        pf ppf "(qand %a %a)" ppf_qual q1 ppf_qual q2
    | QImply (q1, q2) ->
        pf ppf "(qimply %a %a)" ppf_qual q1 ppf_qual q2
    | QForall ((x, s, e), q) ->
        pf ppf "(∀%a<=%s<%a. %a)" ppf_expr s x ppf_expr e ppf_qual q )

and ppf_expr ppf : expr -> unit =
  Fmt.(
    function
    | NonDet ->
        string ppf "✧"
    | Assert (e1, e2) ->
        pf ppf "(assert (%a = %a))" ppf_expr e1 ppf_expr e2
    | Const c ->
        ppf_const ppf c
    | CPrime ->
        string ppf "C.q"
    | CPLen ->
        string ppf "C.k"
    | Var x ->
        string ppf x
    | Ascribe (e, t) ->
        pf ppf "(%a :: %a)" ppf_expr e ppf_typ t
    | AscribeUnsafe (e, t) ->
        pf ppf "(%a ! <%a>)" ppf_expr e ppf_typ t
    | LamA (x, t, e) ->
        pf ppf "λ%s: %a. %a" x ppf_typ t ppf_expr e
    | Lam (x, e) ->
        pf ppf "λ%s. %a" x ppf_expr e
    | App (e1, e2) ->
        pf ppf "%a %a" ppf_expr e1 ppf_expr e2
    | Binop (_, op, e1, e2) ->
        pf ppf "(%a %a %a)" ppf_binop op ppf_expr e1 ppf_expr e2
    | Not e ->
        pf ppf "(not %a)" ppf_expr e
    | Boolop (op, e1, e2) ->
        pf ppf "(%a %a %a)" ppf_boolop op ppf_expr e1 ppf_expr e2
    | Comp (op, e1, e2) ->
        pf ppf "(%a %a %a)" ppf_comp op ppf_expr e1 ppf_expr e2
    | Call (c, args) ->
        pf ppf "#%s(%a)" c (list ~sep:(Fmt.any ", ") ppf_expr) args
    | LetIn (x, e1, e2) ->
        pf ppf "let %s = %a in %a" x ppf_expr e1 ppf_expr e2
    | ArrayOp (op, es) ->
        pf ppf "(%a %a)" ppf_aop op (list ~sep:(Fmt.any " ") ppf_expr) es
    | RSum (s, e, t) ->
        pf ppf "\\sum_{%a, %a}(%a)" ppf_expr s ppf_expr e ppf_typ t
    | Sum {s; e; body} ->
        pf ppf "\\sum_{%a, %a}(%a)" ppf_expr s ppf_expr e ppf_expr body
    | TMake es ->
        pf ppf "%a" (parens (list ~sep:comma ppf_expr)) es
    | TGet (e, i) ->
        pf ppf "%a.%d" ppf_expr e i
    | DMake _ ->
        string ppf "TODO: ppf_expr: DPCons"
    | DMatch _ ->
        string ppf "TODO: ppf_expr: DPDestr"
    | Map _ ->
        string ppf "TODO: ppf_expr: Map"
    | Foldl _ ->
        string ppf "TODO: ppf_expr: Foldl"
    | Iter _ ->
        string ppf "TODO: ppf_expr: Iter"
    | Fn (f, es) ->
        pf ppf "(%a %a)" ppf_func f (list ppf_expr) es
    | Push e ->
        pf ppf "(push %a)" ppf_expr e
    | Pull e ->
        pf ppf "(push %a)" ppf_expr e )

let show_typ (t : typ) = Fmt.str "%a" ppf_typ t

let show_qual (q : qual) = Fmt.str "%a" ppf_qual q

let show_expr (e : expr) = Fmt.str "%a" ppf_expr e

let show_const (c : const) = Fmt.str "%a" ppf_const c

module SS = StringSet

let unions ss = List.fold_left ~f:SS.union ~init:SS.empty ss

let except s x = SS.diff s (SS.singleton x)

let excepts s xs = SS.diff s (SS.of_list xs)

let count = ref 0

let fresh x =
  let c = !count in
  count := c + 1 ;
  x ^ Int.to_string c

let rec vars_typ : typ -> SS.t = function
  | TBase _ ->
      SS.empty
  | TRef (_, q) ->
      except (vars_qual q) nu_str
  | TFun (x, t1, t2) ->
      SS.union (vars_typ t1) (except (vars_typ t2) x)
  | TTuple ts ->
      unions (List.map ts ~f:vars_typ)
  | TArr t ->
      vars_typ t

and vars_qual : qual -> SS.t = function
  | QExpr e ->
      vars_expr e
  | QForall ((x, s, e), q) ->
      unions [except (vars_qual q) x; vars_expr s; vars_expr e]
  | _ ->
      SS.empty

and vars_expr : expr -> SS.t = function
  | Const _ ->
      SS.empty
  | NonDet ->
      SS.empty
  | CPLen | CPrime ->
      SS.empty
  | Ascribe (e, t) ->
      SS.union (vars_expr e) (vars_typ t)
  | AscribeUnsafe (e, t) ->
      SS.union (vars_expr e) (vars_typ t)
  | LetIn (x, e1, e2) ->
      SS.union (vars_expr e1) (except (vars_expr e2) x)
  | Assert (e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Var x ->
      SS.singleton x
  | Lam (x, e) ->
      except (vars_expr e) x
  | LamA (x, t, e) ->
      except (vars_expr e) x
  | App (e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Binop (_, _, e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Not e ->
      vars_expr e
  | Boolop (_, e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Comp (_, e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Call (_, es) ->
      unions (List.map ~f:vars_expr es)
  | ArrayOp (_, es) ->
      unions (List.map ~f:vars_expr es)
  | Sum {s; e= e'; body} ->
      unions [vars_expr s; vars_expr e'; vars_expr body]
  | TMake es ->
      unions (List.map ~f:vars_expr es)
  | TGet (e, i) ->
      vars_expr e
  | DMake (es, q) ->
      SS.union (unions (List.map es ~f:vars_expr)) (vars_qual q)
  | DMatch (e1, xs, e2) ->
      SS.union (vars_expr e1) (excepts (vars_expr e2) xs)
  | Map (e1, e2) ->
      SS.union (vars_expr e1) (vars_expr e2)
  | Foldl {f; acc; xs} ->
      unions (List.map ~f:vars_expr [f; acc; xs])
  | Iter {s; e; body; init; inv} ->
      let vars_e = unions (List.map ~f:vars_expr [s; e; body; init]) in
      let x1 = fresh "_var" in
      let vars_inv = except (vars_typ (inv (Var x1))) x1 in
      unions [vars_e; vars_inv]
  | Fn (_, es) ->
      unions (List.map ~f:vars_expr es)
  | RSum (s, e, f) ->
      SS.union (unions (List.map ~f:vars_expr [s; e])) (vars_typ f)
  | Push e ->
      vars_expr e
  | Pull e ->
      vars_expr e

let rec subst_typ (x : string) (e : expr) (t : typ) : typ =
  let f = subst_typ x e in
  match t with
  | TBase _ ->
      t
  | TRef (t, q) ->
      TRef (t, subst_qual x e q)
  | TFun (y, t1, t2) ->
      if String.(x = y) then t
      else (* TODO: alpha-rename *)
        TFun (y, subst_typ x e t1, subst_typ x e t2)
  | TArr t ->
      TArr (f t)
  | TTuple ts ->
      TTuple (List.map ~f ts)

and subst_qual (x : string) (e : expr) (q : qual) : qual =
  match q with
  | QTrue ->
      q
  | QNot q' ->
      QNot (subst_qual x e q')
  | QAnd (q1, q2) ->
      QAnd (subst_qual x e q1, subst_qual x e q2)
  | QImply (q1, q2) ->
      QImply (subst_qual x e q1, subst_qual x e q2)
  | QExpr e' ->
      QExpr (subst_expr x e e')
  | QForall ((y, es, ee), q') ->
      QForall
        ( (y, subst_expr x e es, subst_expr x e ee)
        , if String.(x = y) then q' else subst_qual x e q' )

and subst_expr (x : string) (ef : expr) (e : expr) : expr =
  let f = subst_expr x ef in
  match e with
  | Const _ ->
      e
  | CPrime ->
      e
  | CPLen ->
      e
  | Var y ->
      if String.(x = y) then ef else e
  | LamA (y, t, body) ->
      if String.(x = y) then e else LamA (y, subst_typ x ef t, f body)
  | App (e1, e2) ->
      App (f e1, f e2)
  | Not e' ->
      Not (f e')
  | Binop (t, op, e1, e2) ->
      Binop (t, op, f e1, f e2)
  | Boolop (op, e1, e2) ->
      Boolop (op, f e1, f e2)
  | Comp (op, e1, e2) ->
      Comp (op, f e1, f e2)
  | Call (c, es) ->
      Call (c, List.map ~f es)
  | ArrayOp (op, es) ->
      ArrayOp (op, List.map ~f es)
  | TMake es ->
      TMake (List.map ~f es)
  | TGet (e, n) ->
      TGet (f e, n)
  | Fn (fn, es) ->
      Fn (fn, List.map ~f es)
  | Iter {s; e; body; init; inv} ->
      Iter
        { s= f s
        ; e= f e
        ; body= f body
        ; init= f init
        ; inv= (fun ei -> subst_typ x ef (inv ei)) }
  | Sum {s; e= e'; body} ->
      Sum {s= f s; e= f e'; body= f body}
  | RSum (s, e, t) ->
      RSum (f s, f e, subst_typ x ef t)
  | DMake (es, q) ->
      DMake (List.map ~f es, subst_qual x ef q)
  | DMatch (e1, ys, e2) ->
      if List.exists ~f:(String.( = ) x) ys then DMatch (f e1, ys, e2)
      else DMatch (f e1, ys, f e2)
  | Map (e1, e2) ->
      todos "subst_expr: Map"
  | Foldl {f; acc; xs} ->
      todos "subst_expr: Foldl"
  | Push e ->
      Push (f e)
  | Pull e ->
      Pull (f e)
  | _ ->
      todos "subst_expr"

let rec subst_typ' (e : expr) (e' : expr) (t : typ) : typ =
  let f = subst_typ' e e' in
  match t with
  | TBase _ ->
      t
  | TRef (t, q) ->
      TRef (t, subst_qual' e e' q)
  | TFun (y, t1, t2) ->
      TFun (y, subst_typ' e e' t1, subst_typ' e e' t2)
  | TArr t ->
      TArr (f t)
  | TTuple ts ->
      TTuple (List.map ~f ts)

and subst_qual' (e : expr) (e' : expr) (q : qual) : qual =
  let f = subst_qual' e e' in
  match q with
  | QTrue ->
      q
  | QNot q' ->
      QNot (f q')
  | QAnd (q1, q2) ->
      QAnd (f q1, f q2)
  | QImply (q1, q2) ->
      QImply (f q1, f q2)
  | QExpr e0 ->
      QExpr (subst_expr' e e' e0)
  | QForall ((y, es, ee), q') ->
      QForall ((y, subst_expr' e e' es, subst_expr' e e' ee), f q')

and subst_expr' (eo : expr) (en : expr) (e : expr) : expr =
  let f = subst_expr' eo en in
  if Poly.(eo = e) then en
  else
    match e with
    | Const _ ->
        e
    | CPrime ->
        e
    | CPLen ->
        e
    | Var y ->
        e
    | LamA (y, t, body) ->
        LamA (y, subst_typ' eo en t, f body)
    | App (e1, e2) ->
        App (f e1, f e2)
    | Not e' ->
        Not (f e')
    | Binop (t, op, e1, e2) ->
        Binop (t, op, f e1, f e2)
    | Boolop (op, e1, e2) ->
        Boolop (op, f e1, f e2)
    | Comp (op, e1, e2) ->
        Comp (op, f e1, f e2)
    | Call (c, es) ->
        Call (c, List.map ~f es)
    | ArrayOp (op, es) ->
        ArrayOp (op, List.map ~f es)
    | TMake es ->
        TMake (List.map ~f es)
    | TGet (e, n) ->
        TGet (f e, n)
    | Fn (fn, es) ->
        Fn (fn, List.map ~f es)
    | Iter {s; e; body; init; inv} ->
        Iter
          { s= f s
          ; e= f e
          ; body= f body
          ; init= f init
          ; inv= (fun ei -> subst_typ' eo en (inv ei)) }
    | Sum {s; e= e'; body} ->
        Sum {s= f s; e= f e'; body= f body}
    | RSum (s, e, t) ->
        RSum (f s, f e, subst_typ' eo en t)
    | DMake (es, q) ->
        DMake (List.map ~f es, subst_qual' eo en q)
    | DMatch (e1, ys, e2) ->
        DMatch (f e1, ys, f e2)
    | Map (e1, e2) ->
        todos "subst_expr: Map"
    | Foldl {f; acc; xs} ->
        todos "subst_expr: Foldl"
    | Push e ->
        Push (f e)
    | Pull e ->
        Pull (f e)
    | _ ->
        todos "subst_expr"

let rec skeleton = function
  | TBase tb ->
      TBase tb
  | TFun (x, tx, tr) ->
      TFun (x, skeleton tx, skeleton tr)
  | TArr t ->
      TArr (skeleton t)
  | TTuple ts ->
      TTuple (List.map ts ~f:skeleton)
  | TRef (t, _) ->
      skeleton t

let rec descale = function TRef (t, _) -> descale t | t -> t

let rec normalize (t : typ) =
  match t with
  | TBase tb ->
      TRef (TBase tb, QTrue)
  | TFun _ ->
      t
  | TArr t ->
      TRef (TArr (normalize t), QTrue)
  | TTuple ts ->
      TRef (TTuple (List.map ts ~f:normalize), QTrue)
  | TRef (t, q) -> (
    match normalize t with
    | TRef (t, QTrue) ->
        TRef (t, q)
    | TRef (t, q') ->
        TRef (t, QAnd (q', q))
    | t' ->
        TRef (t', q) )
