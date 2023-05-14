open Ast
open Dsl
open Circomlib__Poseidon


(* template UpperLessThan(n) {
    assert(n < 254);
    signal input in[2];
    signal output out;

    component bits[2];
    for (var x = 0; x < 2; x++) {
        bits[x] = Num2Bits_strict();
        bits[x].in <== in[x];
    }

    component upper_bits[2];
    upper_bits[0] = Bits2Num(n);
    upper_bits[1] = Bits2Num(n);

    for (var x = 0; x < n; x++) {
        upper_bits[0].in[x] <== bits[0].out[x+(254-n)];
        upper_bits[1].in[x] <== bits[1].out[x+(254-n)];
    }

    component lt = LessThan(n);
    lt.in[0] <== upper_bits[0].out;
    lt.in[1] <== upper_bits[1].out;

    out <== lt.out;
}
input: in[2]
output: out
precondition: n < 254
postcondition: out == 1 iff in[0]/2^(254-n) < in[1]/2^(254-n) *)

let 