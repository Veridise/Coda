open Core
open Fmt
open Big_int_Z

type bigint = big_int

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
  | Quadratic of
      (symbol * bigint) list * (symbol * bigint) list * (symbol * bigint) list
  (* // Is a quadratic expression of the form:
        //              a*b + c
        // Where a,b and c are linear expression *)
  | NonQuadratic

let rec show_arithmetic_expression (expr : arithmetic_expression) : string =
  match expr with
  | Number value ->
      Z.to_string value
  | Signal symbol ->
      symbol
  | NonQuadratic ->
      "NonQuadratic"
  | Linear coefficients ->
      show_linear_expression coefficients
  | Quadratic (a, b, c) ->
      show_quadratic_expression a b c

and show_coefficient (symbol : symbol) (value : bigint) : string =
  let value' = Z.to_string value in
  if Z.equal value Z.one then symbol else "(" ^ value' ^ ")" ^ "*" ^ symbol

and show_coefficients (coefficients : (symbol * bigint) list) : string =
  match coefficients with
  | [] ->
      ""
  | [(symbol, value)] ->
      show_coefficient symbol value
  | (symbol, value) :: tail ->
      show_coefficient symbol value ^ " + " ^ show_coefficients tail

and show_linear_expression (coefficients : (symbol * bigint) list) : string =
  show_coefficients coefficients

and show_quadratic_expression (a : (symbol * bigint) list)
    (b : (symbol * bigint) list) (c : (symbol * bigint) list) : string =
  let a = show_coefficients a in
  let b = show_coefficients b in
  let c = show_coefficients c in
  "(" ^ a ^ ")    *    (" ^ b ^ ")    +    (" ^ c ^ ")"

let default_arithmetic_expression : arithmetic_expression = NonQuadratic

let constant_coefficient : symbol = "1"

let add_symbol_to_coefficients (coefficients : (symbol * bigint) list)
    (coefficient : bigint) (symbol : symbol) : (symbol * bigint) list =
  let coefficients' =
    List.filter coefficients ~f:(fun (symbol', _) ->
        not (String.( = ) symbol' symbol) )
  in
  let coefficients'' =
    List.filter coefficients ~f:(fun (symbol', _) ->
        String.( = ) symbol' symbol )
  in
  let coefficients''' =
    match coefficients'' with
    | [] ->
        [(symbol, coefficient)]
    | [(c, value')] ->
        [(c, Z.add value' coefficient)]
    | _ ->
        failwith "add_symbol_to_coefficients: impossible"
  in
  (* unique key *)
  coefficients' @ coefficients'''

let add_constant_to_coefficients (coefficients : (symbol * bigint) list)
    (value : bigint) : (symbol * bigint) list =
  let c = constant_coefficient in
  add_symbol_to_coefficients coefficients value c

let remove_zero_value_coefficients (coefficients : (symbol * bigint) list) :
    (symbol * bigint) list =
  List.filter coefficients ~f:(fun (_, value) ->
      not (eq_big_int value zero_big_int) )

let add_coefficients_to_coefficients (coefficients_0 : (symbol * bigint) list)
    (coefficients_1 : (symbol * bigint) list) : (symbol * bigint) list =
  let coefficients_0' = remove_zero_value_coefficients coefficients_0 in
  let coefficients_1' = remove_zero_value_coefficients coefficients_1 in
  List.fold_left coefficients_0' ~init:coefficients_1'
    ~f:(fun coefficients (symbol, value) ->
      add_symbol_to_coefficients coefficients value symbol )

let multiply_coefficients_by_constant (coefficients : (symbol * bigint) list)
    (value : bigint) : (symbol * bigint) list =
  List.map coefficients ~f:(fun (symbol, value') ->
      (symbol, mult_big_int value value') )

let divide_coefficients_by_constant (coefficients : (symbol * bigint) list)
    (value : bigint) : (symbol * bigint) list =
  List.map coefficients ~f:(fun (symbol, value') ->
      (symbol, div_big_int value' value) )

let add (expr_0 : arithmetic_expression) (expr_1 : arithmetic_expression) :
    arithmetic_expression =
  match (expr_0, expr_1) with
  | Number value_0, Number value_1 ->
      Number (add_big_int value_0 value_1)
  | Number value_0, Signal symbol_1 ->
      Linear [(symbol_1, unit_big_int); (constant_coefficient, value_0)]
  | Signal symbol_0, Number value_1 ->
      Linear [(symbol_0, unit_big_int); (constant_coefficient, value_1)]
  | Signal symbol_0, Signal symbol_1 ->
      Linear [(symbol_0, unit_big_int); (symbol_1, unit_big_int)]
  | Number value_0, Linear coefficients_1 ->
      Linear (add_constant_to_coefficients coefficients_1 value_0)
  | Linear coefficients_0, Number value_1 ->
      Linear (add_constant_to_coefficients coefficients_0 value_1)
  | Signal symbol_0, Linear coefficients_1 ->
      Linear (add_symbol_to_coefficients coefficients_1 unit_big_int symbol_0)
  | Linear coefficients_0, Signal symbol_1 ->
      Linear (add_symbol_to_coefficients coefficients_0 unit_big_int symbol_1)
  | Linear coefficients_0, Linear coefficients_1 ->
      Linear (add_coefficients_to_coefficients coefficients_0 coefficients_1)
  | Number value_0, Quadratic (a_1, b_1, c_1) ->
      Quadratic (a_1, b_1, add_constant_to_coefficients c_1 value_0)
  | Quadratic (a_0, b_0, c_0), Number value_1 ->
      Quadratic (a_0, b_0, add_constant_to_coefficients c_0 value_1)
  | Signal symbol_0, Quadratic (a_1, b_1, c_1) ->
      Quadratic (a_1, b_1, add_symbol_to_coefficients c_1 unit_big_int symbol_0)
  | Quadratic (a_0, b_0, c_0), Signal symbol_1 ->
      Quadratic (a_0, b_0, add_symbol_to_coefficients c_0 unit_big_int symbol_1)
  | Linear coefficients_0, Quadratic (a_1, b_1, c_1) ->
      Quadratic (a_1, b_1, add_coefficients_to_coefficients c_1 coefficients_0)
  | Quadratic (a_0, b_0, c_0), Linear coefficients_1 ->
      Quadratic (a_0, b_0, add_coefficients_to_coefficients c_0 coefficients_1)
  | _ ->
      print_endline
        ("add: non-quadratic expression" ^ show_arithmetic_expression expr_0) ;
      print_endline
        ("add: non-quadratic expression" ^ show_arithmetic_expression expr_1) ;
      NonQuadratic

let mul (expr_0 : arithmetic_expression) (expr_1 : arithmetic_expression) :
    arithmetic_expression =
  match (expr_0, expr_1) with
  | Number value_0, Number value_1 ->
      Number (mult_big_int value_0 value_1)
  | Number value_0, Signal symbol_1 ->
      Linear [(symbol_1, value_0)]
  | Signal symbol_0, Number value_1 ->
      Linear [(symbol_0, value_1)]
  | Signal symbol_0, Signal symbol_1 ->
      Quadratic ([(symbol_0, unit_big_int)], [(symbol_1, unit_big_int)], [])
  | Number value_0, Linear coefficients_1 ->
      Linear (multiply_coefficients_by_constant coefficients_1 value_0)
  | Linear coefficients_0, Number value_1 ->
      Linear (multiply_coefficients_by_constant coefficients_0 value_1)
  | Signal symbol_0, Linear coefficients_1 ->
      Quadratic (coefficients_1, [(symbol_0, unit_big_int)], [])
  | Linear coefficients_0, Signal symbol_1 ->
      Quadratic (coefficients_0, [(symbol_1, unit_big_int)], [])
  | Linear coefficients_0, Linear coefficients_1 ->
      Quadratic (coefficients_0, coefficients_1, [])
  | Number value_0, Quadratic (a_1, b_1, c_1) ->
      Quadratic
        ( multiply_coefficients_by_constant a_1 value_0
        , b_1
        , multiply_coefficients_by_constant c_1 value_0 )
  | Quadratic (a_0, b_0, c_0), Number value_1 ->
      Quadratic
        ( multiply_coefficients_by_constant a_0 value_1
        , b_0
        , multiply_coefficients_by_constant c_0 value_1 )
  | _ ->
      print_endline
        ("mul: non-quadratic expression" ^ show_arithmetic_expression expr_0) ;
      print_endline
        ("mul: non-quadratic expression" ^ show_arithmetic_expression expr_1) ;
      NonQuadratic

let sub (expr_0 : arithmetic_expression) (expr_1 : arithmetic_expression) :
    arithmetic_expression =
  add expr_0 (mul expr_1 (Number (minus_big_int unit_big_int)))

let opp (expr : arithmetic_expression) : arithmetic_expression =
  mul (Number (minus_big_int unit_big_int)) expr

let div (expr_0 : arithmetic_expression) (expr_1 : arithmetic_expression) :
    arithmetic_expression =
  match (expr_0, expr_1) with
  | Number value_0, Number value_1 ->
      Number (div_big_int value_0 value_1)
  | Signal symbol_0, Number value_1 ->
      Linear [(symbol_0, div_big_int unit_big_int value_1)]
  | Linear coefficients_0, Number value_1 ->
      Linear (divide_coefficients_by_constant coefficients_0 value_1)
  | Quadratic (a_0, b_0, c_0), Number value_1 ->
      Quadratic
        ( divide_coefficients_by_constant a_0 value_1
        , b_0
        , divide_coefficients_by_constant c_0 value_1 )
  | _ ->
      print_endline
        ("div: non-quadratic expression" ^ show_arithmetic_expression expr_0) ;
      print_endline
        ("div: non-quadratic expression" ^ show_arithmetic_expression expr_1) ;
      NonQuadratic

let simplify (expr : arithmetic_expression) : arithmetic_expression =
  match expr with
  | Number value ->
      Number value
  | Signal symbol ->
      Signal symbol
  | Linear coefficients ->
      Linear
        (List.filter coefficients ~f:(fun (_, value) ->
             not (eq_big_int value zero_big_int) ) )
  | Quadratic (a, b, c) ->
      Quadratic
        ( List.filter a ~f:(fun (_, value) ->
              not (eq_big_int value zero_big_int) )
        , List.filter b ~f:(fun (_, value) ->
              not (eq_big_int value zero_big_int) )
        , List.filter c ~f:(fun (_, value) ->
              not (eq_big_int value zero_big_int) ) )
  | NonQuadratic ->
      NonQuadratic

let subst_var (e : arithmetic_expression) (x : string) (v : string) :
    arithmetic_expression =
  match e with
  | Number _ ->
      e
  | Signal y ->
      if String.equal x y then Signal v else e
  | Linear coefficients ->
      Linear
        (List.map coefficients ~f:(fun (y, value) ->
             if String.equal x y then (v, value) else (y, value) ) )
  | Quadratic (a, b, c) ->
      Quadratic
        ( List.map a ~f:(fun (y, value) ->
              if String.equal x y then (v, value) else (y, value) )
        , List.map b ~f:(fun (y, value) ->
              if String.equal x y then (v, value) else (y, value) )
        , List.map c ~f:(fun (y, value) ->
              if String.equal x y then (v, value) else (y, value) ) )
  | NonQuadratic ->
      NonQuadratic

let rec simplify_coefficients (coefficients : (symbol * bigint) list) :
    (symbol * bigint) list =
  match coefficients with
  | [] ->
      []
  | (symbol, value) :: rest ->
      let rest' = simplify_coefficients rest in
      let rest'' =
        List.filter rest' ~f:(fun (symbol', _) ->
            not (String.equal symbol symbol') )
      in
      let rest''' =
        List.fold rest' ~init:zero_big_int ~f:(fun acc (key, value') ->
            if String.equal symbol key then add_big_int acc value' else acc )
      in
      let value' = add_big_int value rest''' in
      if eq_big_int value' zero_big_int then rest''
      else (symbol, value') :: rest''

let rec removable_arithmetic_expression (e : arithmetic_expression) : bool =
  match e with
  | Number _ ->
      failwith "removable_arithmetic_expression: Number"
  | Signal _ ->
      false
  | Linear coefficients ->
      List.for_all coefficients ~f:(fun (_, value) ->
          eq_big_int value zero_big_int )
  | Quadratic (a, b, c) ->
      removable_arithmetic_expression (Linear a)
      && removable_arithmetic_expression (Linear b)
      && removable_arithmetic_expression (Linear c)
  | NonQuadratic ->
      false

(* Represents a constraint of the form: A*B - C = 0
   where A,B and C are linear expression. *)
type r1cs =
  (symbol * bigint) list * (symbol * bigint) list * (symbol * bigint) list

let r1cs_of_arithmetic_expression (expr : arithmetic_expression) : r1cs =
  match expr with
  | Number n ->
      ([], [], [("1", n)])
  | Signal x ->
      ([], [], [(x, unit_big_int)])
  | Linear l ->
      ([], [], simplify_coefficients l)
  | Quadratic (a, b, c) ->
      ( simplify_coefficients a
      , simplify_coefficients b
      , simplify_coefficients
          (multiply_coefficients_by_constant c (minus_big_int unit_big_int)) )
  | NonQuadratic ->
      failwith "NonQuadratic expression cannot be converted to R1CS"

let removable_r1cs (e : r1cs) : bool =
  let a, b, c = e in
  List.for_all a ~f:(fun (_, value) -> eq_big_int value zero_big_int)
  && List.for_all b ~f:(fun (_, value) -> eq_big_int value zero_big_int)
  && List.for_all c ~f:(fun (_, value) -> eq_big_int value zero_big_int)

let prime : bigint =
  big_int_of_string
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"

let cast_bigint_to_field (n : bigint) : bigint = mod_big_int n prime

let show_r1cs (r1cs : r1cs) : string =
  let a, b, c = r1cs in
  let show_coefficients (coefficients : (symbol * bigint) list) : string =
    List.map coefficients ~f:(fun (x, n) ->
        Printf.sprintf "%s * %s" (string_of_big_int (cast_bigint_to_field n)) x )
    |> String.concat ~sep:" + "
  in
  Printf.sprintf "( %s )    *    ( %s )    -    ( %s ) = 0"
    (show_coefficients a) (show_coefficients b) (show_coefficients c)

let var_id_map = ref [("1", 0)]

let count = ref 1 (* 0 maps to the const number 1 *)

let coeff_to_json (coeff : symbol * bigint) : string =
  let x, n = coeff in
  match List.Assoc.find !var_id_map x ~equal:String.equal with
  | Some id ->
      Printf.sprintf "{\"var\": \"%d\", \"value\": \"%s\"}" id
        (string_of_big_int (cast_bigint_to_field n))
  | None ->
      var_id_map := (x, !count) :: !var_id_map ;
      count := !count + 1 ;
      Printf.sprintf "{\"var\": \"%d\", \"value\": \"%s\"}" (!count - 1)
        (string_of_big_int (cast_bigint_to_field n))

let r1cs_to_json (r1cs : r1cs) : string =
  let a, b, c = r1cs in
  Printf.sprintf "{\"a\": [%s], \"b\": [%s], \"c\": [%s]}"
    (List.map a ~f:coeff_to_json |> String.concat ~sep:", ")
    (List.map b ~f:coeff_to_json |> String.concat ~sep:", ")
    (List.map c ~f:coeff_to_json |> String.concat ~sep:", ")

let r1cs_list_to_json (r1cs_list : r1cs list) : string =
  var_id_map := [("1", 0)] ;
  count := 1 ;
  Printf.sprintf "{\"constraints\": [%s]}"
    (List.map r1cs_list ~f:r1cs_to_json |> String.concat ~sep:", ")
