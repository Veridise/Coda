open Core
open Ast
open Ast_utils
open Dsl
open Notation
open Utils

let spf = Format.sprintf

(* circuit declarations *)
type delta = (string * circuit) list

(* typing environment *)
type gamma = (string * typ) list

let show_gamma g =
  String.concat ~sep:"\n"
    (List.map g ~f:(fun (x, t) -> spf "%s : %s" x (show_typ t)))

(* assertion store *)
type alpha = qual list

let show_alpha a = String.concat ~sep:"\n" (List.map a ~f:show_qual)

let d_empty = []

let g_empty = []

let a_empty = []

let add_to_delta (d : delta) (c : circuit) : delta =
  match c with Circuit {name; _} -> (name, c) :: d

let add_to_deltas (d : delta) (c : circuit list) =
  List.fold_left ~f:add_to_delta ~init:d c

type cons =
  | CheckCons of gamma * alpha * qual
      [@printer
        fun fmt (g, a, q) ->
          fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Constrain---\n%s"
            (show_gamma g) (show_alpha a) (show_qual q)]
[@@deriving show]

let is_non_trivial = function
  | CheckCons (_, _, QTrue) ->
      false
  | CheckCons (_, _, QImply (_, QTrue)) ->
      false
  | _ ->
      true

let filter_trivial cs = List.filter cs ~f:is_non_trivial

let pc (cs : cons list) ?(filter = false) : unit =
  cs
  |> (if filter then filter_trivial else Fn.id)
  |> List.map ~f:show_cons |> String.concat ~sep:"\n\n" |> print_endline

let substs_qual (q : qual) (xe : (string * expr) list) : qual =
  List.fold_left ~f:(fun q (x, e) -> subst_qual x e q) ~init:q xe

let functionalize_circ_output (Circuit {outputs; dep; _}) : typ =
  let out_tuple = ttuple @@ List.map outputs ~f:snd in
  let out_typ =
    match dep with
    | None ->
        out_tuple
    | Some q ->
        let q' =
          substs_qual q
            ( outputs |> to_numbered
            |> List.map ~f:(fun (i, (x, _)) -> (x, tget nu i)) )
        in
        refine out_tuple q'
  in
  out_typ

let functionalize_circ (Circuit {inputs; _} as c) : typ =
  List.fold_right ~f:(uncurry tfun) inputs ~init:(functionalize_circ_output c)

(* type checking states: delta, gamma, and alpha are read-only, while cs is write-only *)
type state = {delta: delta; gamma: gamma; alpha: alpha; cs: cons list}

module S = Monads.State (struct
  type t = state
end)

let get_delta = S.(get >>| fun st -> st.delta)

let get_gamma = S.(get >>| fun st -> st.gamma)

let get_cs = S.(get >>| fun st -> st.cs)

let with_bindings (g : gamma) f =
  S.(
    get
    >>= fun st ->
    put {st with gamma= g @ st.gamma}
    >> f
    >>= fun r -> get >>= fun st' -> put {st' with gamma= st.gamma} >> return r )

let with_binding (x, t) f = with_bindings [(x, t)] f

let get_alpha = S.(get >>| fun st -> st.alpha)

let add_cons cons =
  if is_non_trivial cons then
    print_endline (spf "New constraint\n%s\n" (show_cons cons))
  else () ;
  S.(modify (fun st -> {st with cs= st.cs @ [cons]}))

let add_assertion q = S.(modify (fun st -> {st with alpha= st.alpha @ q}))

let rec subtype (t1 : typ) (t2 : typ) : unit S.t =
  print_endline (spf "[subtype] Checking %s <: %s" (show_typ t1) (show_typ t2)) ;
  let incomp =
    spf "[subtype] incompatible types: t1 = %s   t2 = %s" (show_typ t1)
      (show_typ t2)
  in
  S.(
    Let_syntax.(
      let%bind g = get_gamma and a = get_alpha in
      match (t1, t2) with
      | TBase tb1, TBase tb2 ->
          if equal_base tb1 tb2 then return ()
          else
            failwith
              (spf "[subtype] unequal base types: t1 = %s   t2 = %s"
                 (show_base tb1) (show_base tb2) )
      | TRef (t1', q1), TRef (t2', q2) ->
          let cons = CheckCons ((nu_str, t1') :: g, a, qimply q1 q2) in
          add_cons cons >> subtype t1' t2'
      | _, TRef _ ->
          subtype (refine t1 QTrue) t2
      | TRef _, _ ->
          subtype t1 (refine t2 QTrue)
      | TFun (x, t1, t2), TFun (y, t1', t2') ->
          subtype t1' t1
          >> with_binding (x, t1') (subtype t2 (subst_typ y (v x) t2'))
      | TTuple ts1, TTuple ts2 ->
          if List.length ts1 = List.length ts2 then
            iterM ~f:(uncurry subtype) (List.zip_exn ts1 ts2)
          else failwith "[subtype] tuples of unequal lengths"
      | TArr t1', TArr t2' ->
          subtype t1' t2'
      | TTuple [t1'], _ -> (
        try subtype t1' t2 with _ -> failwith incomp )
      | _, TTuple [t2'] -> (
        try subtype t1 t2' with _ -> failwith incomp )
      | _, _ ->
          failwith incomp ) )

let rec synthesize (e : expr) : typ S.t =
  S.(
    Let_syntax.(
      print_endline (spf "[synthesize] Synthesizing type for %s" (show_expr e)) ;
      let f = function
        | NonDet ->
            return tf
        | Assert (e1, e2) ->
            let%bind t1 = synthesize e1 and t2 = synthesize e2 in
            (* check t1 & t2 have the same skeleton *)
            subtype (skeleton t1) (skeleton t2)
            >> subtype (skeleton t2) (skeleton t1)
            >> return (tunit_dep (QExpr (e1 =. e2)))
        | CPrime ->
            return (refine_expr tint (nu =. CPrime))
        | CPLen ->
            return (refine_expr tint (nu =. CPLen))
        | Const c ->
            let r tb = refine_expr tb (nu =. e) in
            let t =
              match c with
              | CF _ ->
                  r tf
              | CInt _ ->
                  r tint
              | CBool _ ->
                  r tbool
              | _ ->
                  failwith
                    (spf "[synthesize] invalid constant %s" (show_expr e))
            in
            return t
        | Var x -> (
            if String.(x = "_") then
              failwith
                "[synthesize] cannot synthesize type for ignored variable _"
            else
              let%bind g = get_gamma in
              match List.Assoc.find g x ~equal:String.equal with
              | Some t ->
                  let ws =
                    List.filter g ~f:(fun (_, t) ->
                        match t with
                        | TRef (_, q) ->
                            SS.mem (vars_qual q) x
                        | _ ->
                            false )
                  in
                  print_endline (spf "[synthesize] Var: witnesses for %s:" x) ;
                  print_endline
                    (String.concat ~sep:"\n"
                       (List.map ws ~f:(fun (y, t) ->
                            spf "%s : %s" y (show_typ t) ) ) ) ;
                  let qs =
                    List.map ws ~f:(fun (y, t) ->
                        match t with
                        | TRef (_, q) ->
                            substs_qual q [(x, nu); (nu_str, v y)]
                        | _ ->
                            failwith "impossible" )
                  in
                  return (attaches qs t)
              | None ->
                  failwith ("[synthesize] No such variable: " ^ x) )
        | Ascribe (e, t) ->
            check e t >>| fun () -> t
        | AscribeUnsafe (_, t) ->
            return t
        | LamA (x, t1, e) ->
            let%bind t2 = with_binding (x, t1) (synthesize e) in
            return (tfun x t1 t2)
        | App (e1, e2) -> (
            match%bind synthesize e1 with
            | TFun (x, tx, tr) ->
                check e2 tx >> return (subst_typ x e2 tr)
            | t1 ->
                failwith
                  (spf "[synthesize] App: not a function: %s" (show_typ t1)) )
        | Binop (BF, _, e1, e2) ->
            check e1 tf >> check e2 tf >> return (refine_expr tf (nu =. e))
        | Binop (BZ, _, e1, e2) ->
            check e1 tint >> check e2 tint >> return (refine_expr tf (nu =. e))
        | Boolop (_, e1, e2) ->
            check e1 tbool >> check e2 tbool
            >> return (refine_expr tbool (nu =. e))
        | Comp (op, e1, e2) -> (
            let res = refine_expr tbool (nu =. e) in
            match op with
            | Leq | Lt ->
                check e1 tint >> check e2 tint >> return res
            | Eq -> (
                let%bind t1 = synthesize e1 and t2 = synthesize e2 in
                match (skeleton t1, skeleton t2) with
                | TBase tb1, TBase tb2 when equal_base tb1 tb2 ->
                    return res
                | s1, s2 ->
                    failwith
                      ( "[synthesize] Comp: Unequal types " ^ show_typ s1
                      ^ show_typ s2 ) ) )
        | Not e' ->
            check e' tbool >> return (refine_expr tbool (nu =. e))
        | Call (c_name, args) -> (
            let%bind d = get_delta in
            match List.Assoc.find d c_name ~equal:String.equal with
            | Some c ->
                let ctype = functionalize_circ c in
                synthesize (dummy_apps c_name ctype args)
            | None ->
                failwith ("[synthesize] No such circuit: " ^ c_name) )
        | Sum {s; e= e'; body= b} ->
            ignore s ;
            ignore e' ;
            ignore b ;
            failwith "TODO: [synthesize] Sum"
            (* check s tint >>
                 check e' tint >>
                 let b' =
                   match b with
                   | Lam (x, b') ->
                       LamA (x, z_range s e', b')
                   | _ ->
                       failwith "Sum's body  be Lam"
                 in
                 let t_body, cs3 = f b' in
                 match t_body with
                 | TFun (i, TRef (TInt, _), TRef (tb', _)) -> (
                   match tb' with
                   | TInt | TF ->
                       (TRef (tb', QExpr (eq nu (rsum s e' t_body))), cs1 @ cs2 @ cs3)
                   | _ ->
                       failwith
                         (spf "Sum: %s is not summable" (show_base tb')) )
                 | _ ->
                     failwith (spf "Sum: body has type %s" (show_typ t_body))
                 ) *)
        | Iter {s; e; body; init; inv} ->
            (* s is int *)
            let t_iter =
              (* TODO: ensure var freshness *)
              tfun "s" tint
                (tfun "e" tint
                   (tfun "body"
                      ((* assume s <= i < e *)
                       tfun "i" (z_range_co s e)
                         (* assume inv(i,x) holds *)
                         (tfun "x"
                            (inv (v "i"))
                            (* prove inv(i+1,output) holds *)
                            (inv (v "i" +. z1)) ) )
                      (* prove inv(s,init) holds *)
                      (tfun "init"
                         (inv (v "s"))
                         (* conclude inv(e,output) holds *)
                         (inv (v "e")) ) ) )
            in
            synthesize (dummy_apps "iter" t_iter [s; e; body; init])
        | TMake es ->
            S.mapM es ~f:synthesize >>| fun ts -> ttuple ts
        | TGet (e, n) -> (
            let%bind t = synthesize e in
            match descale t with
            | TTuple ts ->
                if 0 <= n && n < List.length ts then return (List.nth_exn ts n)
                else failwith "[synthesize] Tuple access out of bounds"
            | t ->
                failwith
                  (spf "[synthesize] TGet: expect a tuple, but got: %s"
                     (show_typ t) ) )
        | ArrayOp (Get, [e1; e2]) -> (
            let%bind t1 = synthesize e1 in
            match skeleton t1 with
            | TArr t ->
                (* FIXME: check index in range *)
                ignore e2 ;
                return (refine t (QExpr (nu =. e)))
            | _ ->
                failwith "[synthesize] get: not an array" )
        | ArrayOp (Cons, [e1; e2]) -> (
            let%bind t1 = synthesize e1 and t2 = synthesize e2 in
            match descale t2 with
            | TArr t2' ->
                subtype t1 t2 >> return (tarr t2')
            | t2' ->
                failwith
                  (spf "[synthesize] Cons: expect an array, but got: %s"
                     (show_typ t2') ) )
        | ArrayOp (Take, [e1; e2]) ->
            ignore e1 ;
            ignore e2 ;
            failwith (spf "TODO [synthesize] ArrayOp (%s)" (show_aop Take))
            (* let t1, cs1 = f e1 in
                 match t1 with
                 | TArr (t, q, el) ->
                     (* check index in range *)
                     let cs2 = check d g a e2 (z_range z0 el) in
                     (TArr (t, QExpr (nu =. e), e2), cs1 @ cs2)
                 | _ ->
                     failwith "[synthesize] take: not an array" ) *)
        | ArrayOp (Drop, [e1; e2]) ->
            ignore e1 ;
            ignore e2 ;
            failwith (spf "TODO [synthesize] ArrayOp (%s)" (show_aop Drop))
            (* let t1, cs1 = f e1 in
                 match t1 with
                 | TArr (t, q, el) ->
                     (* check index in range *)
                     let cs2 = check d g a e2 (z_range z0 el) in
                     (TArr (t, QExpr (nu =. e), zsub el e2), cs1 @ cs2)
                 | _ ->
                     failwith "[synthesize] drop: not an array" ) *)
        | ArrayOp (Zip, [e1; e2]) ->
            ignore e1 ;
            ignore e2 ;
            failwith (spf "TODO [synthesize] ArrayOp (%s)" (show_aop Zip))
            (* let t1, cs1 = f e1 in
                 let t2, cs2 = f e2 in
                 match (t1, t2) with
                 | TArr (t1', q1, l1), TArr (t2', q2, l2) ->
                     (* FIXME: q1 and q2 are erased *)
                     ( tarr (ttuple [t1'; t2']) QTrue l1
                     , cs1 @ cs2 @ [CheckCons (g, a, QExpr (eq l1 l2))] )
                 | TArr _, _ | _, TArr _ ->
                     failwith "zip: not an array" ) *)
        | ArrayOp (op, _) ->
            failwith
              (spf "[synthesize] ArrayOp: %s not implemented" (show_aop op))
            (*
    | Map (e1, e2) -> (
        let t1, cs1 = f e1 in
        let t2, cs2 = f e2 in
        match (t1, t2) with
        | TFun (x, tx, TRef (tr, q)), TArr (t2', q2, el) ->
            (* todo: factor out non-dependent part of q *)
            (* FIXME: q is erased *)
            let i = "i" in
            let q2' =
              q
              |> subst_qual x (get e2 (v i))
              |> subst_qual nu_str (get nu (v i))
            in
            ( TArr
                ( TRef (tr, QTrue)
                , qand (qforall i z0 el q2') (QExpr (eq nu (Map (e1, e2))))
                , el )
            , cs1 @ cs2 @ subtype g a t2' tx )
        | _, TArr _ ->
            failwith "map: not a valid function"
        | TFun _, _ ->
            failwith "map: not a valid array" ) *)
        | DMake (es, q) ->
            let%bind ts = S.mapM es ~f:synthesize
            and g = get_gamma
            and a = get_alpha in
            add_cons (CheckCons ((nu_str, ttuple ts) :: g, a, q))
            >> return (refine (ttuple ts) q)
        | _ ->
            failwith
              (spf "Synthesis unavailable for expression %s" (show_expr e))
      in
      f e
      >>| fun t ->
      print_endline
        (spf "[synthesize] type for %s >>> %s\n" (show_expr e) (show_typ t)) ;
      t ) )

and synthesize_app (t : typ) (es : expr list) : typ S.t =
  S.(
    match es with
    | [] ->
        return t
    | e :: es' -> (
      match t with
      | TFun (x, t1, t2) ->
          with_binding (x, t1) (check e t1 >> synthesize_app t2 es')
      | _ ->
          failwith "Not a function" ) )

and check (e : expr) (t : typ) : unit S.t =
  S.(
    Let_syntax.(
      print_endline
        (spf "[check] Checking %s has type %s" (show_expr e) (show_typ t)) ;
      let rec f e t =
        match (e, t) with
        | Const CNil, _ -> (
          match skeleton t with
          | TArr _ as t' ->
              subtype t t'
          | _ ->
              failwith (spf "Expect CNil <= %s to be an array" (show_typ t)) )
        | Lam (x, body), TFun (y, t1, t2) ->
            with_binding (x, t1) (check body (subst_typ y (v x) t2))
        | LamA (x, t, body), TFun (y, t1, t2) ->
            subtype t1 t
            >> with_binding (x, t1) (check body (subst_typ y (v x) t2))
        | LetIn (x, e1, e2), t2 ->
            let%bind t1 = synthesize e1 in
            with_binding (x, t1) (check e2 t2)
            (* | DPDestr (e1, xs, e2), t2 -> *)
            (* synthesize e1 >>= fun t1 ->
               let ts, a' =
                 match t1 with
                 | TDProd (ts, ys, q) ->
                     let q' =
                       List.fold_right
                         (fun (x, y) q -> subst_qual x (v y) q)
                         (List.combine xs ys) q
                     in
                     print_endline
                       (spf "[check] DPDestr: subst'ed q: %s" (show_qual q')) ;
                     (ts, [q'])
                 | TTuple ts ->
                     (ts, [])
                 | _ ->
                     failwith "not a product"
               in
               if List.length ts = List.length xs then
               with_bindings (List.combine xs ts) (
                 check d (List.combine xs ts) (a @ a') e2 t2 in
                 cs1 @ cs2
               else
                 failwith (spf "DPDestr: xs and ts have different lengths") *)
        | Push e, _ -> (
            let t', q = get_tq t in
            match t' with
            | TArr te ->
                (* push e <== Array<{ te | qe(v) }> if *)
                (* e <== {Array<te> | forall 0<= i0 < length nu. qe(v[i]) *)
                let te', qe = get_tq te in
                check e
                  (refine (tarr te')
                     (qand q
                        (qforall "i0" z0 (len nu)
                           (subst_qual nu_str (Dsl.get nu (v "i0")) qe) ) ) )
            | _ ->
                failwith "[check] Push: expect array type" )
        | _ ->
            let%bind t' = synthesize e in
            subtype t' t
      in
      match t with
      | TTuple [t'] -> (
        try check e t' with _ -> f e t )
      | _ ->
          f e t ) )

let init_gamma (c : circuit) : gamma =
  let to_base_types = List.map ~f:(fun (x, t) -> (x, skeleton t)) in
  match c with
  | Circuit {inputs; outputs; _} ->
      List.rev (to_base_types outputs) @ List.rev inputs

let typecheck_circuit (d : delta) (c : circuit) : cons list =
  match c with
  | Circuit {body; _} ->
      S.(
        Let_syntax.(
          let init = {delta= d; gamma= init_gamma c; alpha= []; cs= []} in
          let _, st = S.run init (check body (functionalize_circ_output c)) in
          st.cs ) )
