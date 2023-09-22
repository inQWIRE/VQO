open BasicUtility
open Datatypes
open MathSpec
open PeanoNat

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

(** val get_cua : coq_val -> bool **)

let get_cua = function
| Coq_nval (x, _) -> x
| Coq_qval (_, _) -> false

(** val get_cus : int -> (posi -> coq_val) -> var -> int -> bool **)

let get_cus n f x i =
  if Nat.ltb i n
  then (match f (x, i) with
        | Coq_nval (b, _) -> b
        | Coq_qval (_, _) -> false)
  else allfalse i

(** val rotate : rz_val -> int -> int -> bool **)

let rotate =
  addto

(** val times_rotate : coq_val -> int -> coq_val **)

let times_rotate v q =
  match v with
  | Coq_nval (b, r) ->
    if b then Coq_nval (b, (rotate r q)) else Coq_nval (b, r)
  | Coq_qval (rc, r) -> Coq_qval (rc, (rotate r q))

(** val sr_rotate' :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let rec sr_rotate' st x n size =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> st)
    (fun m ->
    eupdate (sr_rotate' st x m size) (x, m)
      (times_rotate (st (x, m)) ((fun x y -> max 0 (x-y)) size m)))
    n

(** val sr_rotate : (posi -> coq_val) -> var -> int -> posi -> coq_val **)

let sr_rotate st x n =
  sr_rotate' st x (succ n) (succ n)

(** val r_rotate : rz_val -> int -> int -> bool **)

let r_rotate =
  addto_n

(** val times_r_rotate : coq_val -> int -> coq_val **)

let times_r_rotate v q =
  match v with
  | Coq_nval (b, r) ->
    if b then Coq_nval (b, (r_rotate r q)) else Coq_nval (b, r)
  | Coq_qval (rc, r) -> Coq_qval (rc, (r_rotate r q))

(** val srr_rotate' :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let rec srr_rotate' st x n size =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> st)
    (fun m ->
    eupdate (srr_rotate' st x m size) (x, m)
      (times_r_rotate (st (x, m)) ((fun x y -> max 0 (x-y)) size m)))
    n

(** val srr_rotate : (posi -> coq_val) -> var -> int -> posi -> coq_val **)

let srr_rotate st x n =
  srr_rotate' st x (succ n) (succ n)

(** val exchange : coq_val -> coq_val **)

let exchange v = match v with
| Coq_nval (b, r) -> Coq_nval ((negb b), r)
| Coq_qval (_, _) -> v

(** val lshift' :
    int -> int -> (posi -> coq_val) -> var -> posi -> coq_val **)

let rec lshift' n size f x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> eupdate f (x, 0) (f (x, size)))
    (fun m -> eupdate (lshift' m size f x) (x, n) (f (x, m)))
    n

(** val lshift : (posi -> coq_val) -> var -> int -> posi -> coq_val **)

let lshift f x n =
  lshift' ((fun x y -> max 0 (x-y)) n (succ 0))
    ((fun x y -> max 0 (x-y)) n (succ 0)) f x

(** val rshift' :
    int -> int -> (posi -> coq_val) -> var -> posi -> coq_val **)

let rec rshift' n size f x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> eupdate f (x, size) (f (x, 0)))
    (fun m -> eupdate (rshift' m size f x) (x, m) (f (x, n)))
    n

(** val rshift : (posi -> coq_val) -> var -> int -> posi -> coq_val **)

let rshift f x n =
  rshift' ((fun x y -> max 0 (x-y)) n (succ 0))
    ((fun x y -> max 0 (x-y)) n (succ 0)) f x

(** val reverse :
    (posi -> coq_val) -> var -> int -> (var * int) -> coq_val **)

let reverse f x n a =
  if (&&) (Nat.eqb (fst a) x) (Nat.ltb (snd a) n)
  then f (x,
         ((fun x y -> max 0 (x-y)) ((fun x y -> max 0 (x-y)) n (succ 0))
           (snd a)))
  else f a

(** val up_qft : coq_val -> (int -> bool) -> coq_val **)

let up_qft v f =
  match v with
  | Coq_nval (_, r) -> Coq_qval (r, f)
  | Coq_qval (_, _) -> v

(** val lshift_fun : (int -> bool) -> int -> int -> bool **)

let lshift_fun f n i =
  f ((+) i n)

(** val get_r : coq_val -> rz_val **)

let get_r = function
| Coq_nval (_, r) -> r
| Coq_qval (rc, _) -> rc

(** val assign_r :
    (posi -> coq_val) -> var -> (int -> bool) -> int -> posi -> coq_val **)

let rec assign_r f x r n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    eupdate (assign_r f x r m) (x, m) (up_qft (f (x, m)) (lshift_fun r m)))
    n

(** val up_h : coq_val -> coq_val **)

let up_h = function
| Coq_nval (b, r) ->
  if b
  then Coq_qval (r, (rotate allfalse (succ 0)))
  else Coq_qval (r, allfalse)
| Coq_qval (r, f) -> Coq_nval ((f 0), r)

(** val assign_h :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let rec assign_h f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    eupdate (assign_h f x n m) (x, ((+) n m)) (up_h (f (x, ((+) n m)))))
    i

(** val turn_qft :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let turn_qft st x b rmax =
  assign_h (assign_r st x (get_cus b st x) b) x b
    ((fun x y -> max 0 (x-y)) rmax b)

(** val assign_seq :
    (posi -> coq_val) -> var -> (int -> bool) -> int -> posi -> coq_val **)

let rec assign_seq f x vals n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    eupdate (assign_seq f x vals m) (x, m) (Coq_nval ((vals m),
      (get_r (f (x, m))))))
    n

(** val assign_h_r :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let rec assign_h_r f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    eupdate (assign_h_r f x n m) (x, ((+) n m)) (up_h (f (x, ((+) n m)))))
    i

(** val get_r_qft : (posi -> coq_val) -> var -> int -> bool **)

let get_r_qft f x =
  match f (x, 0) with
  | Coq_nval (_, _) -> allfalse
  | Coq_qval (_, g) -> g

(** val turn_rqft :
    (posi -> coq_val) -> var -> int -> int -> posi -> coq_val **)

let turn_rqft st x b rmax =
  assign_h_r (assign_seq st x (get_r_qft st x) b) x b
    ((fun x y -> max 0 (x-y)) rmax b)

(** val exp_sem :
    (var -> int) -> exp -> (posi -> coq_val) -> posi -> coq_val **)

let rec exp_sem env e st =
  match e with
  | SKIP _ -> st
  | X p -> eupdate st p (exchange (st p))
  | CU (p, e') -> if get_cua (st p) then exp_sem env e' st else st
  | RZ (q, p) -> eupdate st p (times_rotate (st p) q)
  | RRZ (q, p) -> eupdate st p (times_r_rotate (st p) q)
  | SR (n, x) -> sr_rotate st x n
  | SRR (n, x) -> srr_rotate st x n
  | Lshift x -> lshift st x (env x)
  | Rshift x -> rshift st x (env x)
  | Rev x -> reverse st x (env x)
  | QFT (x, b) -> turn_qft st x b (env x)
  | RQFT (x, b) -> turn_rqft st x b (env x)
  | Seq (e1, e2) -> exp_sem env e2 (exp_sem env e1 st)

(** val init_v : int -> var -> (int -> bool) -> exp **)

let rec init_v n x m =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> SKIP (x, 0))
    (fun m0 ->
    if m m0 then Seq ((init_v m0 x m), (X (x, m0))) else init_v m0 x m)
    n
