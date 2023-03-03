(*
   module W = Writer(MonoidList(struct type t = string end))

   let inc x : int W.t = (x+1, [Int.to_string (x+1)])
   let dec x : int W.t = (x-1, [Int.to_string (x-1)])
   let run x = W.(
   inc x >>= fun x ->
   inc x >>= fun x ->
     dec x >>= fun x ->
       return x)

   let (x, s) = run 10;;
   print_int x;;
   print_endline "";;
   print_endline (String.concat " " s);; *)

module S = Monad.State (struct
  type t = int
end)

let s =
  S.(
    get
    >>= fun n ->
    Printf.printf "before shadow: %d\n" n ;
    shadow 100 (fun () ->
        S.get
        >>= fun n ->
        Printf.printf "in shadow: %d\n" n ;
        return () )
    >>= fun () ->
    S.get
    >>= fun n ->
    Printf.printf "after shadow: %d\n" n ;
    return () )

let _ = S.run 0 s
