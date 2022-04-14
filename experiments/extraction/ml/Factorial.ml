
(** val fact : int -> int **)

let rec fact n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> succ 0)
    (fun n0 -> ( * ) (succ n0) (fact n0))
    n
