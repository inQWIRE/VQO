
type t =
| F1 of int
| FS of int * t

(** val of_nat : int -> int -> t option **)

let rec of_nat p n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> None)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> Some (F1 n'))
      (fun p' ->
      match of_nat p' n' with
      | Some f -> Some (FS (n', f))
      | None -> None)
      p)
    n
