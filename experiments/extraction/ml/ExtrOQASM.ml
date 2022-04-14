open AltGateSet
open BasicUtility
open CLArith
open Datatypes
open MathSpec
open OQASM
open OQASMProof
open OQIMP
open OracleExample
open RZArith

(** val rz_ang : int -> float **)

let rz_ang n =
  ( /. ) (( *. ) 2.0 Float.pi) ((fun r n -> r ** (float_of_int n)) 2.0 n)

(** val rrz_ang : int -> float **)

let rrz_ang n =
  ( -. ) (( *. ) 2.0 Float.pi)
    (( /. ) (( *. ) 2.0 Float.pi) ((fun r n -> r ** (float_of_int n)) 2.0 n))

(** val coq_ID : int -> coq_U ucom **)

let coq_ID q =
  coq_U1 0.0 q

(** val gen_sr_gate' : vars -> var -> int -> int -> coq_U ucom **)

let rec gen_sr_gate' f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((gen_sr_gate' f x m size),
    (coq_U1 (rz_ang ((fun x y -> max 0 (x-y)) size m)) (find_pos f (x, m)))))
    n

(** val gen_sr_gate : vars -> var -> int -> coq_U ucom **)

let gen_sr_gate f x n =
  gen_sr_gate' f x (succ n) (succ n)

(** val gen_srr_gate' : vars -> var -> int -> int -> coq_U ucom **)

let rec gen_srr_gate' f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((gen_srr_gate' f x m size),
    (coq_U1 (rrz_ang ((fun x y -> max 0 (x-y)) size m)) (find_pos f (x, m)))))
    n

(** val gen_srr_gate : vars -> var -> int -> coq_U ucom **)

let gen_srr_gate f x n =
  gen_srr_gate' f x (succ n) (succ n)

(** val controlled_rotations_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec controlled_rotations_gen f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> coq_ID (find_pos f (x, i)))
    (fun m ->
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> coq_ID (find_pos f (x, i)))
      (fun _ -> Coq_useq ((controlled_rotations_gen f x m i),
      (control (find_pos f (x, ((+) m i)))
        (coq_U1 (rz_ang n) (find_pos f (x, i))))))
      m)
    n

(** val coq_QFT_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec coq_QFT_gen f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((coq_QFT_gen f x m size), (Coq_useq
    ((coq_H (find_pos f (x, m))),
    (controlled_rotations_gen f x ((fun x y -> max 0 (x-y)) size m) m)))))
    n

(** val nH : vars -> var -> int -> int -> coq_U ucom **)

let rec nH f x n b =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((nH f x m b), (coq_H (find_pos f (x, ((+) b m))))))
    n

(** val trans_qft : vars -> var -> int -> coq_U ucom **)

let trans_qft f x b =
  Coq_useq ((coq_QFT_gen f x b b),
    (nH f x ((fun x y -> max 0 (x-y)) (vsize f x) b) b))

(** val trans_rqft : vars -> var -> int -> coq_U ucom **)

let trans_rqft f x b =
  invert (Coq_useq ((coq_QFT_gen f x b b),
    (nH f x ((fun x y -> max 0 (x-y)) (vsize f x) b) b)))

(** val trans_exp' :
    vars -> int -> exp -> (int -> posi) -> (coq_U ucom * vars) * (int -> posi) **)

let rec trans_exp' f dim exp0 avs =
  match exp0 with
  | SKIP p -> (((coq_ID (find_pos f p)), f), avs)
  | X p -> (((coq_X (find_pos f p)), f), avs)
  | CU (p, e1) ->
    let (p0, _) = trans_exp' f dim e1 avs in
    let (e1', _) = p0 in (((control (find_pos f p) e1'), f), avs)
  | RZ (q, p) -> (((coq_U1 (rz_ang q) (find_pos f p)), f), avs)
  | RRZ (q, p) -> (((coq_U1 (rrz_ang q) (find_pos f p)), f), avs)
  | SR (n, x) -> (((gen_sr_gate f x n), f), avs)
  | SRR (n, x) -> (((gen_srr_gate f x n), f), avs)
  | Lshift x ->
    (((coq_ID (find_pos f (x, 0))), (trans_lshift f x)),
      (lshift_avs dim f avs x))
  | Rshift x ->
    (((coq_ID (find_pos f (x, 0))), (trans_rshift f x)),
      (rshift_avs dim f avs x))
  | Rev x ->
    (((coq_ID (find_pos f (x, 0))), (trans_rev f x)), (rev_avs dim f avs x))
  | QFT (x, b) -> (((trans_qft f x b), f), avs)
  | RQFT (x, b) -> (((trans_rqft f x b), f), avs)
  | Seq (e1, e2) ->
    let (p, avs') = trans_exp' f dim e1 avs in
    let (e1', f') = p in
    let (p0, avs'') = trans_exp' f' dim e2 avs' in
    let (e2', f'') = p0 in (((Coq_useq (e1', e2')), f''), avs'')

(** val trans_exp : vars -> int -> exp -> (int -> posi) -> coq_U ucom **)

let trans_exp f dim exp0 avs =
  fst (fst (trans_exp' f dim exp0 avs))

(** val trans_cl_adder : int -> coq_U ucom **)

let trans_cl_adder size =
  trans_exp (vars_for_adder01 size)
    ((+) (( * ) (succ (succ 0)) size) (succ 0)) (adder01_out size)
    (avs_for_arith size)

(** val trans_cl_const_mul : int -> int -> coq_U ucom **)

let trans_cl_const_mul size m =
  trans_exp (vars_for_cl_nat_m size)
    ((+) (( * ) (succ (succ 0)) size) (succ 0))
    (cl_nat_mult_out size (nat2fb m)) (avs_for_arith size)

(** val trans_cl_mul : int -> coq_U ucom **)

let trans_cl_mul size =
  trans_exp (vars_for_cl_nat_full_m size)
    ((+) (( * ) (succ (succ (succ 0))) size) (succ 0))
    (cl_full_mult_out size) (avs_for_arith size)

(** val trans_cl_mul_out_place : int -> coq_U ucom **)

let trans_cl_mul_out_place size =
  trans_exp (vars_for_cl_nat_full_out_place_m size)
    ((+) (( * ) (succ (succ (succ (succ 0)))) size) (succ 0))
    (cl_full_mult_out_place_out size) (avs_for_arith size)

(** val trans_rz_const_adder : int -> int -> coq_U ucom **)

let trans_rz_const_adder size m =
  trans_exp (vars_for_rz_adder size) size (rz_adder_out size (nat2fb m))
    (avs_for_arith size)

(** val trans_rz_adder : int -> coq_U ucom **)

let trans_rz_adder size =
  trans_exp (vars_for_rz_full_add size) (( * ) (succ (succ 0)) size)
    (rz_full_adder_out size) (avs_for_arith size)

(** val trans_rz_const_mul : int -> int -> coq_U ucom **)

let trans_rz_const_mul size m =
  trans_exp (vars_for_rz_nat_m size) (( * ) (succ (succ 0)) size)
    (nat_mult_out size (nat2fb m)) (avs_for_arith size)

(** val trans_rz_mul : int -> coq_U ucom **)

let trans_rz_mul size =
  trans_exp (vars_for_rz_nat_full_m size) (( * ) (succ (succ (succ 0))) size)
    (nat_full_mult_out size) (avs_for_arith size)

(** val trans_cl_div_mod : int -> int -> coq_U ucom **)

let trans_cl_div_mod size m =
  trans_exp (vars_for_cl_div_mod size)
    ((+) (( * ) (succ (succ (succ 0))) size) (succ 0))
    (cl_div_mod_out size m) (avs_for_arith size)

(** val trans_rz_div_mod : int -> int -> coq_U ucom **)

let trans_rz_div_mod size m =
  trans_exp (vars_for_rz_div_mod size) (( * ) (succ (succ 0)) (succ size))
    (rz_div_mod_out size m) (avs_for_rz_div_mod size)

(** val trans_rz_div_mod_app_shift : int -> int -> coq_U ucom **)

let trans_rz_div_mod_app_shift size m =
  trans_exp (vars_for_app_div_mod size) (( * ) (succ (succ 0)) (succ size))
    (app_div_mod_out size m) (avs_for_app_div_mod size)

(** val trans_rz_div_mod_app_swaps : int -> int -> coq_U ucom **)

let trans_rz_div_mod_app_swaps size m =
  trans_exp (vars_for_app_div_mod size) (( * ) (succ (succ 0)) (succ size))
    (app_div_mod_aout size m) (avs_for_app_div_mod size)

(** val trans_appx_adder : int -> int -> coq_U ucom **)

let trans_appx_adder size b =
  trans_exp (vars_for_rz_full_add size) (( * ) (succ (succ 0)) size)
    (appx_full_adder_out size b) (avs_for_arith size)

(** val trans_appx_const_adder : int -> int -> int -> coq_U ucom **)

let trans_appx_const_adder size b m =
  trans_exp (vars_for_rz_adder size) (( * ) (succ (succ 0)) size)
    (appx_adder_out size b (nat2fb m)) (avs_for_arith size)

(** val trans_appx_const_sub : int -> int -> int -> coq_U ucom **)

let trans_appx_const_sub size b m =
  trans_exp (vars_for_rz_adder size) (( * ) (succ (succ 0)) size)
    (appx_sub_out size b (nat2fb m)) (avs_for_arith size)

(** val trans_rz_modmult_rev : int -> int -> int -> int -> coq_U ucom **)

let trans_rz_modmult_rev m c cinv size =
  trans_exp (vars_for_rz size) ((+) (( * ) (succ (succ 0)) size) (succ 0))
    (real_rz_modmult_rev m c cinv size) (avs_for_arith size)

(** val trans_rz_modmult_rev_alt : int -> int -> int -> int -> coq_U ucom **)

let trans_rz_modmult_rev_alt m c cinv size =
  trans_exp (vars_for_rz size) ((+) (( * ) (succ (succ 0)) size) (succ 0))
    (real_rz_modmult_rev_alt m c cinv size) (avs_for_arith size)

(** val trans_modmult_rev : int -> int -> int -> int -> coq_U ucom **)

let trans_modmult_rev m c cinv size =
  trans_exp (vars_for_cl (succ size))
    ((+) (( * ) (succ (succ (succ (succ 0)))) (succ size)) (succ 0))
    (real_modmult_rev m c cinv (succ size)) (avs_for_arith (succ size))

(** val trans_dmc_qft : int -> coq_U ucom option **)

let trans_dmc_qft size =
  match compile_dm_qft size with
  | Some v ->
    (match v with
     | Value x ->
       let (p0, _) = x in
       let (p1, _) = p0 in
       let (o, _) = p1 in
       (match o with
        | Some p ->
          Some
            (trans_exp (vars_for_dm_c size)
              ((+) (( * ) (succ (succ 0)) size) (succ 0)) p
              (avs_for_arith size))
        | None -> None)
     | Error -> None)
  | None -> None

(** val trans_dmc_cl : int -> coq_U ucom option **)

let trans_dmc_cl size =
  match compile_dm_classic size with
  | Some v ->
    (match v with
     | Value x ->
       let (p0, _) = x in
       let (p1, _) = p0 in
       let (o, _) = p1 in
       (match o with
        | Some p ->
          Some
            (trans_exp (vars_for_dm_c size)
              ((+) (( * ) (succ (succ 0)) size) (succ 0)) p
              (avs_for_arith size))
        | None -> None)
     | Error -> None)
  | None -> None

(** val trans_dmq_qft : int -> coq_U ucom option **)

let trans_dmq_qft size =
  match compile_dmq_qft size with
  | Some v ->
    (match v with
     | Value x ->
       let (p0, _) = x in
       let (p1, _) = p0 in
       let (o, _) = p1 in
       (match o with
        | Some p ->
          Some
            (trans_exp (vars_for_dm_c size)
              ((+) (( * ) (succ (succ (succ (succ (succ (succ 0)))))) size)
                (succ 0)) p (avs_for_arith size))
        | None -> None)
     | Error -> None)
  | None -> None

(** val trans_dmq_cl : int -> coq_U ucom option **)

let trans_dmq_cl size =
  match compile_dmq_classic size with
  | Some v ->
    (match v with
     | Value x ->
       let (p0, _) = x in
       let (p1, _) = p0 in
       let (o, _) = p1 in
       (match o with
        | Some p ->
          Some
            (trans_exp (vars_for_dm_c size)
              ((+) (( * ) (succ (succ (succ (succ (succ (succ 0)))))) size)
                (succ 0)) p (avs_for_arith size))
        | None -> None)
     | Error -> None)
  | None -> None

(** val compile_collision_sqir : coq_U ucom option **)

let compile_collision_sqir =
  match compile_collision with
  | Some v ->
    (match v with
     | Value a ->
       let (p, _) = a in
       let (p0, _) = p in
       let (o, sn) = p0 in
       (match o with
        | Some e ->
          Some
            (trans_exp (vars_for_collision sn)
              ((+)
                (( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ
                  0))))))))))))))))))) (succ (succ (succ sn)))) e
              avs_for_collision)
        | None -> None)
     | Error -> None)
  | None -> None
