open BasicUtility

type exp =
| SKIP of posi
| X of posi
| CU of posi * exp
| RZ of int * posi
| RRZ of int * posi
| SR of int * var
| SRR of int * var
| Lshift of var
| Rshift of var
| Rev of var
| QFT of var * int
| RQFT of var * int
| Seq of exp * exp

(** val inv_exp : exp -> exp **)

let rec inv_exp = function
| CU (n, p0) -> CU (n, (inv_exp p0))
| RZ (q, p1) -> RRZ (q, p1)
| RRZ (q, p1) -> RZ (q, p1)
| SR (n, x) -> SRR (n, x)
| SRR (n, x) -> SR (n, x)
| Lshift x -> Rshift x
| Rshift x -> Lshift x
| QFT (x, b) -> RQFT (x, b)
| RQFT (x, b) -> QFT (x, b)
| Seq (p1, p2) -> Seq ((inv_exp p2), (inv_exp p1))
| x -> x

(** val init_v : int -> var -> (int -> bool) -> exp **)

let rec init_v n x m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 ->
    if m m0 then Seq ((init_v m0 x m), (X (x, m0))) else init_v m0 x m)
    n
