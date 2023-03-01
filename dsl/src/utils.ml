let todo () = failwith "not implemented"

let todos s = failwith (s ^ ": not implemented")

module StringSet = Set.Make (String)

let curry f a b = f (a, b)

let uncurry f (a, b) = f a b
