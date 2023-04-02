open Core
open Typecheck
open Coqgen
open Circomlib.Gates

module U = Test_utils.Utils

let _ = U.test cnot []
let _ = U.test cand []
let _ = U.test cor []
let _ = U.test cnor []
let _ = U.test cnand []
let _ = U.test cxor []