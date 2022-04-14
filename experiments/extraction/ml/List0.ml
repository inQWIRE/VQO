
(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> [])
    (fun len0 -> start :: (seq (succ start) len0))
    len
