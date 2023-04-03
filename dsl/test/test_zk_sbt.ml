open Core
open Typecheck
open Coqgen
open Zk_sbt
module U = Test_utils.Utils

(* let _ = U.test c_in Circomlib.Comparators.([greater_than; is_equal]) *)
let _ =
  U.test query
    Circomlib.(
      Comparators.[greater_than; less_than; is_equal]
      @ Bitify.[num2bits]
      @ [Mux3.mux3] @ [c_in] )

(* let t = Dsl.(const_array tf [f0; f1]) |> Ast_utils.show_expr |> print_endline *)
