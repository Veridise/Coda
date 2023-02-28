open Dsl
open Ast
open Typecheck

let x = v "x"
let y = v "y"

let c_assert_equal = Circuit {
  name = "AssertEqual";
  inputs = [("x", tf); ("y", tf)];
  outputs = [];
  dep = Some (qeq x y);
  body = [
    assert_eq x y
  ]
}

let check_c_assert_equal = typecheck_circuit [] c_assert_equal
let d = add_to_delta d_empty c_assert_equal


let eassert_equal x y = ascribe 
  (match_with
    (call "AssertEqual" [x; y])
    []
    (dpunit (qeq x y)))
  (tdunit (qeq x y))

let c_assert_equal_test = Circuit {
  name = "AssertEqualTest";
  inputs = [("x", tf); ("y", tf)];
  outputs = [];
  dep = None;
  body = [
    slet "u" (eassert_equal x y)
  ]
}
let check_c_assert_equal_test = typecheck_circuit d c_assert_equal_test



let eassert_binary x =
  ascribe 
    (match_with
      (call "AssertEqual" [fmul x (fsub f1 x); f0])
      []
      (dpunit (q_is_binary x)))
    (tdunit (q_is_binary x))

let c_assert_binary = Circuit {
  name = "AssertBinary";
  inputs = [("x", tf)];
  outputs = [];
  dep = Some (q_is_binary x);
  body = [
    slet "u" (eassert_binary x)
  ]
}

let check_c_assert_binary = typecheck_circuit d c_assert_binary

let assert_binary x =
  ascribe 
    (match_with
      (call "AssertBinary" [x])
      []
      (dpunit (q_is_binary x)))
    (tdunit (q_is_binary x))


let d = add_to_delta d c_assert_binary