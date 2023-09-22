open Datatypes

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val sub : int -> int -> int **)

  let rec sub = (-)

  (** val eqb : int -> int -> bool **)

  let rec eqb = (=)

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)

  (** val modulo : int -> int -> int **)

  let modulo = (mod)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> succ 0
  | false -> 0
 end
