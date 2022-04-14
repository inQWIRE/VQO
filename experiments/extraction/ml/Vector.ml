open Fin
open VectorDef

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * int * 'a t

(** val caseS : ('a1 -> int -> 'a1 t -> 'a2) -> int -> 'a1 t -> 'a2 **)

let caseS h _ = function
| Coq_nil -> Obj.magic __
| Coq_cons (h0, n0, t0) -> h h0 n0 t0

(** val const : 'a1 -> int -> 'a1 t **)

let rec const a n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> Coq_nil)
    (fun n0 -> Coq_cons (a, n0, (const a n0)))
    n

(** val nth : int -> 'a1 t -> Fin.t -> 'a1 **)

let rec nth _ v' = function
| F1 n -> caseS (fun h _ _ -> h) n v'
| FS (n, p') -> caseS (fun _ -> nth) n v' p'
