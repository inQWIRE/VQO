open PeanoNat

type var = int

type posi = var * int

(** val posi_eq : posi -> posi -> bool **)

let posi_eq r1 r2 =
  let (x1, y1) = r1 in
  let (x2, y2) = r2 in (&&) (Nat.eqb x1 x2) (Nat.eqb y1 y2)

type rz_val = int -> bool

type coq_val =
| Coq_nval of bool * rz_val
| Coq_qval of rz_val * rz_val

(** val eupdate : (posi -> 'a1) -> posi -> 'a1 -> posi -> 'a1 **)

let eupdate f i x j =
  if posi_eq j i then x else f j
