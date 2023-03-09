module type STATE0 = sig
  type st

  type 'a t = st -> 'a * st

  include Base.Monad.Basic with type 'a t := 'a t
end

module State0 (T : sig
  type t
end) : STATE0 with type st := T.t = struct
  type st = T.t

  type 'a t = st -> 'a * st

  let return (a : 'a) : 'a t = fun st -> (a, st)

  let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
   fun st ->
    let a, st' = m st in
    f a st'

  let map = `Define_using_bind
end

module type STATE = sig
  type st

  type 'a t = st -> 'a * st

  include STATE0 with type st := st and type 'a t := 'a t

  include Base.Monad.S with type 'a t := 'a t

  val get : st t

  val put : st -> unit t

  val run : st -> 'a t -> 'a * st

  val modify : (st -> st) -> unit t

  val shadow : st -> (unit -> 'a t) -> 'a t

  val mapM : 'a list -> f:('a -> 'b t) -> 'b list t

  val iterM : 'a list -> f:('a -> unit t) -> unit t

  val ( >> ) : 'a t -> 'b t -> 'b t

  val ( *> ) : 'a t -> 'b t -> 'b t
end

module State (T : sig
  type t
end) : STATE with type st := T.t = struct
  module S0 = State0 (T)
  module M0 = Base.Monad.Make (S0)

  (* include S0 *)
  include S0
  include M0

  type st = T.t

  let get : st t = fun st -> (st, st)

  let put (st : st) : unit t = fun _ -> ((), st)

  let run (st : st) (m : 'a t) : 'a * st = m st

  let modify (f : st -> st) : unit t = get >>= fun st -> put (f st)

  let shadow (st : T.t) (f : unit -> 'a t) =
    get >>= fun st0 -> put st >>= f >>= fun x -> put st0 >>= fun () -> return x

  let rec mapM (xs : 'a list) ~(f : 'a -> 'b t) : 'b list t =
    match xs with
    | [] ->
        return []
    | x :: xs' ->
        f x >>= fun y -> mapM xs' ~f >>| fun ys -> y :: ys

  (* monadic sequencing *)
  let ( >> ) m f = m >>= fun _ -> f

  let ( *> ) = ( >> )

  let iterM xs ~f = mapM xs ~f >> return ()
end

(*
   module type MONOID = sig
     type t

     val mempty : t

     val mappend : t -> t -> t
   end

   module MonoidList (T : sig
     type t
   end) : MONOID with type t = T.t list = struct
     type t = T.t list

     let mempty = []

     let mappend = ( @ )
   end

   module Writer (M : MONOID) : MONAD with type 'a t = 'a * M.t = struct
     type 'a t = 'a * M.t

     let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
       let a, w = m in
       let b, w' = f a in
       (b, M.mappend w w')

     let return (a : 'a) : 'a t = (a, M.mempty)

     let ( >>= ) = bind
   end *)
