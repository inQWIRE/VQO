open BasicUtility
open Datatypes
open FMapAVL
open MathSpec
open OQASM
open OrderedTypeEx
open PeanoNat

type __ = Obj.t

module Posi_as_OT = PairOrderedType(Nat_as_OT)(Nat_as_OT)

module M = Make(Posi_as_OT)

type rz_val = int

type coq_val =
| Coq_nval of bool * rz_val
| Coq_qval of rz_val * rz_val

(** val addto : rz_val -> int -> int -> rz_val **)

let addto r n rmax =
  Nat.modulo
    ((+) r (Nat.pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) rmax n)))
    (Nat.pow (succ (succ 0)) rmax)

(** val addto_n : rz_val -> int -> int -> int **)

let addto_n r n rmax =
  Nat.modulo
    ((fun x y -> max 0 (x-y)) ((+) r (Nat.pow (succ (succ 0)) rmax))
      (Nat.pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) rmax n)))
    (Nat.pow (succ (succ 0)) rmax)

type state = coq_val M.t

(** val get_state : posi -> state -> coq_val **)

let get_state p f =
  match M.find p f with
  | Some v -> v
  | None -> Coq_nval (false, 0)

(** val exchange : coq_val -> coq_val **)

let exchange v = match v with
| Coq_nval (b, r) -> Coq_nval ((negb b), r)
| Coq_qval (_, _) -> v

(** val get_cua : coq_val -> bool **)

let get_cua = function
| Coq_nval (x, _) -> x
| Coq_qval (_, _) -> false

(** val get_cus : int -> state -> var -> int -> bool **)

let get_cus n f x i =
  if Nat.ltb i n
  then (match get_state (x, i) f with
        | Coq_nval (b, _) -> b
        | Coq_qval (_, _) -> false)
  else allfalse i

(** val get_r : coq_val -> rz_val **)

let get_r = function
| Coq_nval (_, r) -> r
| Coq_qval (rc, _) -> rc

(** val rotate : rz_val -> int -> int -> rz_val **)

let rotate =
  addto

(** val times_rotate : coq_val -> int -> int -> coq_val **)

let times_rotate v q rmax =
  match v with
  | Coq_nval (b, r) ->
    if b then Coq_nval (b, (rotate r q rmax)) else Coq_nval (b, r)
  | Coq_qval (rc, r) -> Coq_qval (rc, (rotate r q rmax))

(** val r_rotate : rz_val -> int -> int -> int **)

let r_rotate =
  addto_n

(** val times_r_rotate : coq_val -> int -> int -> coq_val **)

let times_r_rotate v q rmax =
  match v with
  | Coq_nval (b, r) ->
    if b then Coq_nval (b, (r_rotate r q rmax)) else Coq_nval (b, r)
  | Coq_qval (rc, r) -> Coq_qval (rc, (r_rotate r q rmax))

(** val sr_rotate' : state -> var -> int -> int -> int -> state **)

let rec sr_rotate' st x n size rmax =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> st)
    (fun m ->
    sr_rotate'
      (M.add (x, m)
        (times_rotate (get_state (x, m) st) ((fun x y -> max 0 (x-y)) size m)
          rmax) st) x m size rmax)
    n

(** val sr_rotate : state -> var -> int -> int -> state **)

let sr_rotate st x n rmax =
  sr_rotate' st x (succ n) (succ n) rmax

(** val srr_rotate' : state -> var -> int -> int -> int -> state **)

let rec srr_rotate' st x n size rmax =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> st)
    (fun m ->
    srr_rotate'
      (M.add (x, m)
        (times_r_rotate (get_state (x, m) st)
          ((fun x y -> max 0 (x-y)) size m) rmax) st) x m size rmax)
    n

(** val srr_rotate : state -> var -> int -> int -> state **)

let srr_rotate st x n rmax =
  srr_rotate' st x (succ n) (succ n) rmax

(** val lshift' : int -> int -> state -> var -> coq_val M.t **)

let rec lshift' n size f x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> M.add (x, 0) (get_state (x, size) f) f)
    (fun m -> M.add (x, n) (get_state (x, m) f) (lshift' m size f x))
    n

(** val lshift : state -> var -> int -> coq_val M.t **)

let lshift f x n =
  lshift' ((fun x y -> max 0 (x-y)) n (succ 0))
    ((fun x y -> max 0 (x-y)) n (succ 0)) f x

(** val rshift' : int -> int -> state -> var -> coq_val M.t **)

let rec rshift' n size f x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> M.add (x, size) (get_state (x, 0) f) f)
    (fun m -> M.add (x, m) (get_state (x, n) f) (rshift' m size f x))
    n

(** val rshift : state -> var -> int -> coq_val M.t **)

let rshift f x n =
  rshift' ((fun x y -> max 0 (x-y)) n (succ 0))
    ((fun x y -> max 0 (x-y)) n (succ 0)) f x

(** val reverse' : state -> var -> int -> int -> state -> state **)

let rec reverse' f x n i f' =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f')
    (fun i' ->
    reverse' f x n i'
      (M.add (x, i') (get_state (x, ((fun x y -> max 0 (x-y)) n i)) f) f'))
    i

(** val reverse : state -> var -> int -> state **)

let reverse f x n =
  reverse' f x n n f

(** val up_h : coq_val -> int -> coq_val **)

let up_h v rmax =
  match v with
  | Coq_nval (b, r) ->
    if b then Coq_qval (r, (rotate 0 (succ 0) rmax)) else Coq_qval (r, 0)
  | Coq_qval (r, f) ->
    Coq_nval
      (((<=)
         (Nat.pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) rmax (succ 0))) f),
      r)

(** val assign_h : state -> var -> int -> int -> int -> state **)

let rec assign_h f x n i rmax =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    assign_h
      (M.add (x, ((+) n m)) (up_h (get_state (x, ((+) n m)) f) rmax) f) x n m
      rmax)
    i

(** val up_qft : coq_val -> rz_val -> coq_val **)

let up_qft v f =
  match v with
  | Coq_nval (_, r) -> Coq_qval (r, f)
  | Coq_qval (_, _) -> v

(** val a_nat2fb' : (int -> bool) -> int -> int -> int **)

let rec a_nat2fb' f n acc =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> acc)
    (fun m ->
    a_nat2fb' f m
      ((+) acc (( * ) (Nat.b2n (f m)) (Nat.pow (succ (succ 0)) m))))
    n

(** val a_nat2fb : (int -> bool) -> int -> int **)

let a_nat2fb f n =
  a_nat2fb' f n 0

(** val assign_r : state -> var -> int -> int -> int -> int -> state **)

let rec assign_r f x r n size rmax =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    assign_r
      (M.add (x, ((fun x y -> max 0 (x-y)) size n))
        (up_qft (get_state (x, ((fun x y -> max 0 (x-y)) size n)) f) r) f) x
      (Nat.modulo (( * ) r (succ (succ 0))) (Nat.pow (succ (succ 0)) rmax)) m
      size rmax)
    n

(** val turn_qft : state -> var -> int -> int -> state **)

let turn_qft f x n rmax =
  assign_h
    (assign_r f x
      (( * ) (Nat.pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) rmax n))
        (a_nat2fb (fbrev n (get_cus n f x)) n)) n n rmax) x n
    ((fun x y -> max 0 (x-y)) rmax n) rmax

(** val assign_seq : state -> var -> (int -> bool) -> int -> int -> state **)

let rec assign_seq f x vals size n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> f)
    (fun m ->
    assign_seq
      (M.add (x, ((fun x y -> max 0 (x-y)) size n)) (Coq_nval
        ((vals ((fun x y -> max 0 (x-y)) size n)),
        (get_r (get_state (x, ((fun x y -> max 0 (x-y)) size n)) f)))) f) x
      vals size m)
    n

(** val get_r_qft : state -> var -> int -> int -> int -> bool **)

let get_r_qft f x n rmax =
  match get_state (x, 0) f with
  | Coq_nval (_, _) -> allfalse
  | Coq_qval (_, g) ->
    fbrev n
      (nat2fb
        (Nat.div g
          (Nat.pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) rmax n))))

(** val turn_rqft : state -> var -> int -> int -> state **)

let turn_rqft st x n rmax =
  assign_h (assign_seq st x (get_r_qft st x n rmax) n rmax) x n
    ((fun x y -> max 0 (x-y)) rmax n) rmax

(** val exp_sem : (var -> int) -> int -> exp -> state -> state **)

let rec exp_sem env rmax e st =
  match e with
  | SKIP _ -> st
  | X p -> M.add p (exchange (get_state p st)) st
  | CU (p, e') ->
    if get_cua (get_state p st) then exp_sem env rmax e' st else st
  | RZ (q, p) -> M.add p (times_rotate (get_state p st) q rmax) st
  | RRZ (q, p) -> M.add p (times_r_rotate (get_state p st) q rmax) st
  | SR (n, x) -> sr_rotate st x n rmax
  | SRR (n, x) -> srr_rotate st x n rmax
  | Lshift x -> lshift st x (env x)
  | Rshift x -> rshift st x (env x)
  | Rev x -> reverse st x (env x)
  | QFT (x, _) -> turn_qft st x (env x) rmax
  | RQFT (x, _) -> turn_rqft st x (env x) rmax
  | Seq (e1, e2) -> exp_sem env rmax e2 (exp_sem env rmax e1 st)
