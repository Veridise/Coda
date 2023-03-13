open Core
open Fmt

type bigint = Big_int.big_int
type symbol = string

(* note: integer in this representation is not necessary a field element, it can be any integer 
         you need to do modular arithmetic on it when generating the constraints *)
type arithmetic_expression =
  | Number of bigint
  | Signal of symbol
  | Linear of (symbol * bigint) list
  (* // Represents the expression: c1*s1 + .. + cn*sn + C
        // where c1..cn are integers modulo a prime and
        // s1..sn are signals. C is a constant value *)
  | Quadratic of (symbol * bigint) list * (symbol * bigint) list * (symbol * bigint) list
  (* // Is a quadratic expression of the form:
        //              a*b + c
        // Where a,b and c are linear expression *)
  | NonQuadratic

let rec show_arithmetic_expression (expr: arithmetic_expression) : string =
    match expr with
    | Number value -> Big_int.string_of_big_int value
    | Signal symbol -> symbol
    | NonQuadratic -> "NonQuadratic"
    | Linear coefficients -> show_linear_expression coefficients
    | Quadratic (a,b,c) -> show_quadratic_expression a b c
  and show_coefficient (symbol: symbol) (value: bigint) : string =
    let value' = Big_int.string_of_big_int value in
    if Big_int.eq_big_int value Big_int.unit_big_int then
        symbol
    else
        "(" ^ value' ^ ")" ^ "*" ^ symbol
  and show_coefficients (coefficients: (symbol * bigint) list) : string =
      match coefficients with
      | [] -> ""
      | [ (symbol, value) ] -> show_coefficient symbol value
      | (symbol, value) :: tail ->
        show_coefficient symbol value ^ " + " ^ show_coefficients tail
  and show_linear_expression (coefficients: (symbol * bigint) list) : string =
    show_coefficients coefficients
  and show_quadratic_expression (a: (symbol * bigint) list) (b: (symbol * bigint) list)
      (c: (symbol * bigint) list) : string =
    let a = show_coefficients a in
    let b = show_coefficients b in
    let c = show_coefficients c in
    "(" ^ a ^ ") * (" ^ b ^ ") + (" ^ c ^ ")"

let default_arithmetic_expression : arithmetic_expression =
  NonQuadratic

let constant_coefficient : symbol =
    "1"
    
let add_symbol_to_coefficients (coefficients: (symbol * bigint) list) (coefficient: bigint) (symbol: symbol) :
    (symbol * bigint) list =
    let c = constant_coefficient in
    let coefficients' = List.filter coefficients ~f:(fun (symbol, _) -> not (String.(=) symbol c)) in
    let coefficients'' = List.filter coefficients ~f:(fun (symbol, _) -> String.(=) symbol c) in
    let coefficients''' = match coefficients'' with
        | [] -> [ (symbol, coefficient) ]
        | [ (c, value') ] -> [ (c, Big_int.add_big_int value' coefficient) ]
        | _ -> failwith "add_symbol_to_coefficients: impossible" in (* unique key *)
    coefficients' @ coefficients'''

let add_constant_to_coefficients (coefficients: (symbol * bigint) list) (value: bigint) :
    (symbol * bigint) list =
    let c = constant_coefficient in
    add_symbol_to_coefficients coefficients value c

let remove_zero_value_coefficients (coefficients: (symbol * bigint) list) :
    (symbol * bigint) list =
    List.filter coefficients ~f:(fun (_, value) -> not (Big_int.eq_big_int value Big_int.zero_big_int))

let add_coefficients_to_coefficients (coefficients_0: (symbol * bigint) list) (coefficients_1: (symbol * bigint) list) :
    (symbol * bigint) list =
    let coefficients_0' = remove_zero_value_coefficients coefficients_0 in
    let coefficients_1' = remove_zero_value_coefficients coefficients_1 in
    List.fold_left coefficients_0' ~init:coefficients_1' ~f:(fun coefficients (symbol, value) ->
        add_symbol_to_coefficients coefficients value symbol)

let multiply_coefficients_by_constant (coefficients: (symbol * bigint) list) (value: bigint) :
    (symbol * bigint) list =
    List.map coefficients ~f:(fun (symbol, value') -> (symbol, Big_int.mult_big_int value value'))

let divide_coefficients_by_constant (coefficients: (symbol * bigint) list) (value: bigint) :
    (symbol * bigint) list =
    List.map coefficients ~f:(fun (symbol, value') -> (symbol, Big_int.div_big_int value' value))

let add (expr_0: arithmetic_expression) (expr_1: arithmetic_expression) : arithmetic_expression =
    match expr_0, expr_1 with
    | Number value_0, Number value_1 -> Number (Big_int.add_big_int value_0 value_1)
    | Number value_0, Signal symbol_1 -> Linear [ (symbol_1, value_0) ]
    | Signal symbol_0, Number value_1 -> Linear [ (symbol_0, value_1) ]
    | Signal symbol_0, Signal symbol_1 -> Linear [ (symbol_0, Big_int.unit_big_int); (symbol_1, Big_int.unit_big_int) ]
    | Number value_0, Linear coefficients_1 -> Linear (add_constant_to_coefficients coefficients_1 value_0)
    | Linear coefficients_0, Number value_1 -> Linear (add_constant_to_coefficients coefficients_0 value_1)
    | Signal symbol_0, Linear coefficients_1 -> Linear (add_symbol_to_coefficients coefficients_1 Big_int.unit_big_int symbol_0)
    | Linear coefficients_0, Signal symbol_1 -> Linear (add_symbol_to_coefficients coefficients_0 Big_int.unit_big_int symbol_1)
    | Linear coefficients_0, Linear coefficients_1 -> Linear (add_coefficients_to_coefficients coefficients_0 coefficients_1)
    | Number value_0, Quadratic (a_1, b_1, c_1) -> Quadratic (a_1, b_1, add_constant_to_coefficients c_1 value_0)
    | Quadratic (a_0, b_0, c_0), Number value_1 -> Quadratic (a_0, b_0, add_constant_to_coefficients c_0 value_1)
    | Signal symbol_0, Quadratic (a_1, b_1, c_1) -> Quadratic (a_1, b_1, add_symbol_to_coefficients c_1 Big_int.unit_big_int symbol_0)
    | Quadratic (a_0, b_0, c_0), Signal symbol_1 -> Quadratic (a_0, b_0, add_symbol_to_coefficients c_0 Big_int.unit_big_int symbol_1)
    | Linear coefficients_0, Quadratic (a_1, b_1, c_1) -> Quadratic
        (a_1, b_1, add_coefficients_to_coefficients c_1 coefficients_0)
    | Quadratic (a_0, b_0, c_0), Linear coefficients_1 -> Quadratic
        (a_0, b_0, add_coefficients_to_coefficients c_0 coefficients_1)
    | _ -> NonQuadratic

let mul (expr_0: arithmetic_expression) (expr_1: arithmetic_expression) : arithmetic_expression =
    match expr_0, expr_1 with
    | Number value_0, Number value_1 -> Number (Big_int.mult_big_int value_0 value_1)
    | Number value_0, Signal symbol_1 -> Linear [ (symbol_1, value_0) ]
    | Signal symbol_0, Number value_1 -> Linear [ (symbol_0, value_1) ]
    | Signal symbol_0, Signal symbol_1 -> Quadratic ([(symbol_0, Big_int.unit_big_int)], [(symbol_1, Big_int.unit_big_int)], [])
    | Number value_0, Linear coefficients_1 -> Linear (multiply_coefficients_by_constant coefficients_1 value_0)
    | Linear coefficients_0, Number value_1 -> Linear (multiply_coefficients_by_constant coefficients_0 value_1)
    | Signal symbol_0, Linear coefficients_1 -> Quadratic (coefficients_1, [ (symbol_0, Big_int.unit_big_int) ], [])
    | Linear coefficients_0, Signal symbol_1 -> Quadratic (coefficients_0, [ (symbol_1, Big_int.unit_big_int) ], [])
    | Linear coefficients_0, Linear coefficients_1 -> Quadratic (coefficients_0, coefficients_1, [])
    | Number value_0, Quadratic (a_1, b_1, c_1) -> Quadratic
        (multiply_coefficients_by_constant a_1 value_0, multiply_coefficients_by_constant b_1 value_0, multiply_coefficients_by_constant c_1 value_0)
    | Quadratic (a_0, b_0, c_0), Number value_1 -> Quadratic
        (multiply_coefficients_by_constant a_0 value_1, multiply_coefficients_by_constant b_0 value_1, multiply_coefficients_by_constant c_0 value_1)
    | _ -> NonQuadratic

let sub (expr_0: arithmetic_expression) (expr_1: arithmetic_expression) : arithmetic_expression =
    add expr_0 (mul expr_1 (Number (Big_int.minus_big_int Big_int.unit_big_int)))

let opp (expr: arithmetic_expression) : arithmetic_expression =
    mul (Number (Big_int.minus_big_int Big_int.unit_big_int)) expr

let div (expr_0: arithmetic_expression) (expr_1: arithmetic_expression) : arithmetic_expression =
    match expr_0, expr_1 with
    | Number value_0, Number value_1 -> Number (Big_int.div_big_int value_0 value_1)
    | Signal symbol_0, Number value_1 -> Linear [ (symbol_0, Big_int.div_big_int Big_int.unit_big_int value_1) ]
    | Linear coefficients_0, Number value_1 -> Linear (divide_coefficients_by_constant coefficients_0 value_1)
    | Quadratic (a_0, b_0, c_0), Number value_1 -> Quadratic
        (divide_coefficients_by_constant a_0 value_1, divide_coefficients_by_constant b_0 value_1, divide_coefficients_by_constant c_0 value_1)
    | _ -> NonQuadratic

let simplify (expr: arithmetic_expression) : arithmetic_expression =
    match expr with
    | Number value -> Number value
    | Signal symbol -> Signal symbol
    | Linear coefficients -> Linear (List.filter coefficients ~f:(fun (_, value) -> not (Big_int.eq_big_int value Big_int.zero_big_int)))
    | Quadratic (a, b, c) -> Quadratic
        (List.filter a ~f:(fun (_, value) -> not (Big_int.eq_big_int value Big_int.zero_big_int)),
        List.filter b ~f:(fun (_, value) -> not (Big_int.eq_big_int value Big_int.zero_big_int)),
        List.filter c ~f:(fun (_, value) -> not (Big_int.eq_big_int value Big_int.zero_big_int)))
    | NonQuadratic -> NonQuadratic
