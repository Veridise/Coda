open Lib__Ast
open Lib__Dsl
open Lib__Typecheck
open Lib__Codegen

let x = v "x"
let y = v "y"
let tx = tf
let ty = re TF (eq nu x)
let c1 = Circuit {
  name = "c1";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  dep = None;
  body = []
}

let d = add_to_delta [] c1

let ty = re TF (eq nu x)

let c2 = Circuit {
  name = "c2";
  inputs = [("x", tf)];
  outputs = [("y", ty)];
  dep = None;
  body = [
    slet "y'" (Call ("c1", [x]));
    assert_eq y (v "y'")
  ]
}

let cs2 = typecheck_circuit d c2


let (tloop, check_loop) = synthesize [] [] [] (Iter {
  s = z0; 
  e = zc 5; 
  body = lama "i" tint (lama "x" tf (fadd1 x));
  init = f0;
  inv = fun i -> fun x -> tfq (QExpr (eq (toUZ x) i))
})

let c_dep = Circuit {
  name = "c_dep";
  inputs = [("x", tf); ("y", tf)];
  outputs = [];
  dep = Some (qeq x y);
  body = [
    assert_eq x y
  ]
}

let check_c_dep = typecheck_circuit [] c_dep

let c_dep_caller = Circuit {
  name = "c_dep_caller";
  inputs = [("x", tf)];
  outputs = [("y", tfe (eq nu x))];
  dep = None;
  body = [
    slet "u" (
      ascribe 
        (match_with
          (call "c_dep" [x; y])
          []
          (dpunit (qeq x y)))
        (tdunit (qeq x y))
    )
  ]
}

let d = add_to_delta d_empty c_dep
let check_c_dep_caller = typecheck_circuit d c_dep_caller

let codegen_c_dep_caller = codegen d c_dep_caller