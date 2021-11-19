
module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val sub : int -> int -> int **)

  let rec sub = (-)

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)

  (** val modulo : int -> int -> int **)

  let modulo = (mod)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> Pervasives.succ 0
  | false -> 0
 end
