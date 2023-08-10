open Core
open Ast
open Dsl
open Nice_dsl

(* type presignal = string * base *)

type presignal = Presignal of string

(* If [qual] refers to ONLY vars from [presignals]. *)
let restricted_domain (presignals : presignal list) (qual : qual) : bool =
  let presignal_names = List.map presignals ~f:(fun (Presignal name) -> name) in
  let mem_presignals x = List.mem presignal_names x ~equal:String.equal in
  Set.for_all (Ast_utils.vars_qual qual) ~f:mem_presignals

let extract_signal (prev_presignals : presignal list) (presignal : presignal)
    (quals : qual list) : signal * qual list =
  let (Presignal name) = presignal in
  let presignals = prev_presignals @ [presignal] in
  let quals', quals'' =
    List.partition_tf quals ~f:(restricted_domain presignals)
  in
  ( ( name
    , TypRef.such_that (TBase BaseTyp.field) (fun x ->
          Ast_utils.subst_qual name x (Qual.conjunction quals') ) )
  , quals'' )

(* If [qual] refers to ONLY vars from [presignals]. *)

let extract_signals ?(prev_presignals' = []) (presignals : presignal list)
    (quals : qual list) (err_msg : string) =
  let _ =
    print_endline ("quals: " ^ List.to_string quals ~f:Ast_utils.show_qual)
  in
  let _, signals, quals =
    List.fold presignals ~init:([], [], quals)
      ~f:(fun (prev_presignals, signals, quals) presignal ->
        let signal, quals' =
          extract_signal (prev_presignals' @ prev_presignals) presignal quals
        in
        (prev_presignals @ [presignal], signals @ [signal], quals') )
  in
  if List.is_empty quals then signals
  else (
    print_endline
      (err_msg ^ "\nquals: " ^ List.to_string quals ~f:Ast_utils.show_qual) ;
    failwith "extract_signals" )

type hoare_circuit =
  | Hoare_circuit of
      { name: string
      ; inputs: presignal list
      ; outputs: presignal list
      ; preconditions: qual list
      ; postconditions: qual list
      ; body: expr }

let to_circuit
    (Hoare_circuit {name; inputs; outputs; preconditions; postconditions; body} :
      hoare_circuit ) : circuit =
  print_endline "BEGIN to_circuit";
  print_endline @@ "name: " ^ name;
  print_endline "[extract inputs]";
  print_endline @@ "inputs:" ^ List.to_string ~f:(fun (Presignal x) -> x) inputs;
  let inputs' =
    extract_signals inputs preconditions
      "In circuit specification, some preconditions used no inputs: "
  in
  print_endline "[extract outputs]";
  print_endline @@ "outputs:" ^ List.to_string ~f:(fun (Presignal x) -> x) outputs;
  let outputs' =
    extract_signals ?prev_presignals':(Some inputs) outputs postconditions
      "In circuit specification, some postconditions used no outputs: "
  in
  let c = circuit name inputs' outputs' body in
  (* print_endline ("to_circuit ==> " ^ Ast_utils.show_circuit c) ; *)
  print_endline "END to_circuit";
  c

let test () =
  let open Expr in
  let open BaseTyp in
  let _ =
    print_endline @@ Ast_utils.show_circuit @@ to_circuit
    @@ Hoare_circuit
         { name= "C1"
         ; inputs= [Presignal "in1"]
         ; outputs= [Presignal "out1"]
         ; preconditions= []
         ; postconditions= []
         ; body= btrue }
  in
  let _ =
    print_endline @@ Ast_utils.show_circuit @@ to_circuit
    @@ Hoare_circuit
         { name= "C2"
         ; inputs= [Presignal "in1"; Presignal "in2"]
         ; outputs= [Presignal "out1"]
         ; preconditions= [qeq (var "in1") (var "in2")]
         ; postconditions= []
         ; body= btrue }
  in
  let _ =
    print_endline @@ Ast_utils.show_circuit @@ to_circuit
    @@ Hoare_circuit
         { name= "C2"
         ; inputs= [Presignal "in1"; Presignal "in2"]
         ; outputs= [Presignal "out1"]
         ; preconditions=
             [qeq (var "in1") (var "in2"); qeq (var "in1") (var "in1")]
         ; postconditions=
             [qeq (var "in1") (var "out1"); qeq (var "in2") (var "out2")]
         ; body= btrue }
  in
  ()
