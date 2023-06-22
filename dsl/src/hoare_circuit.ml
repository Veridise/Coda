open Core
open Ast
open Dsl
open Nice_dsl

type presignal = string * base

(* If [qual] refers to ONLY vars from [presignals]. *)
let restricted_domain (presignals : presignal list) (qual : qual) : bool =
  let presignal_names = List.map presignals ~f:(fun (name, _) -> name) in
  let mem_presignals x = List.mem presignal_names x ~equal:String.equal in
  Set.for_all (Ast_utils.vars_qual qual) ~f:mem_presignals

let extract_signal (prev_presignals : presignal list) (presignal : presignal)
    (quals : qual list) : signal * qual list =
  let name, typ = presignal in
  let presignals = prev_presignals @ [presignal] in
  let quals', quals'' =
    List.partition_tf quals ~f:(restricted_domain presignals)
  in
  ( ( name
    , TypRef.such_that (TBase typ) (fun x ->
          Ast_utils.subst_qual name x (Qual.conjunction quals') ) )
  , quals'' )

let extract_signals ?(prev_presignals' = []) (presignals : presignal list)
    (quals : qual list) (err_msg : string) =
  let _, signals, quals =
    List.fold presignals ~init:([], [], quals)
      ~f:(fun (prev_presignals, signals, quals) presignal ->
        let signal, quals' =
          extract_signal (prev_presignals' @ prev_presignals) presignal quals
        in
        (prev_presignals @ [presignal], signals @ [signal], quals') )
  in
  if List.is_empty quals then signals
  else failwith (err_msg ^ List.to_string quals ~f:Ast_utils.show_qual)

(* Preconditions can only refer to inputs. *)
(* Postconditions can refer to inputs or outputs *)
let circuit name (preinputs : presignal list) (preoutputs : presignal list)
    ?(preconditions : qual list = []) ?(postconditions : qual list = [])
    (body : expr) : circuit =
  let inputs =
    extract_signals preinputs preconditions
      "In circuit specification, some preconditions used no inputs: "
  in
  let outputs =
    extract_signals ?prev_presignals':(Some preinputs) preoutputs postconditions
      "In circuit specification, some postconditions used no outputs: "
  in
  circuit name inputs outputs body

let test () =
  let open Expr in
  let open BaseTyp in
  let _ =
    print_endline @@ Ast_utils.show_circuit
    @@ circuit "C1" [("in1", field)] [("out1", field)] btrue
  in
  let _ =
    print_endline @@ Ast_utils.show_circuit
    @@ circuit "C2"
         [("in1", field); ("in2", field)]
         [("out1", field)]
         ?preconditions:(Some [qeq (var "in1") (var "in2")])
         ?postconditions:(Some []) btrue
  in
  let _ =
    print_endline @@ Ast_utils.show_circuit
    @@ circuit "C2"
         [("in1", field); ("in2", field)]
         [("out1", field); ("out2", field)]
         ?preconditions:
           (Some [qeq (var "in1") (var "in2"); qeq (var "in1") (var "in1")])
         ?postconditions:
           (Some [qeq (var "in1") (var "out1"); qeq (var "in2") (var "out2")])
         btrue
  in
  ()
