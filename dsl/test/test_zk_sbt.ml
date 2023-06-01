open Core
open Typecheck
open Coqgen
open Zk_sbt
module U = Test_utils.Utils

let _ = U.test c_in Circomlib.Comparators.[greater_than; is_equal]

let _ =
  U.test query
    Circomlib.(
      Comparators.[greater_than; less_than; is_equal]
      @ Bitify.[num2bits]
      @ [Mux3.mux3] @ [c_in] )

let _ = U.test get_val_by_idx Circomlib.(Bitify.[num2bits] @ Mux3.[mux3])

let _ = U.test get_iden_state Circomlib.Poseidon.[poseidon]

let _ = U.test cut_id Circomlib.Bitify.[bits2num; num2bits]

let _ = U.test cut_st Circomlib.Bitify.[bits2num; num2bits]

(* let t = Dsl.(const_array tf [f0; f1]) |> Ast_utils.show_expr |> print_endline *)
