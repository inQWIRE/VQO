open BasicUtility
open CLArith
open List0
open MathSpec
open OQASM
open OQASMProof
open OQIMP

(** val rotate_left_n : qvar -> int -> qexp **)

let rec rotate_left_n x n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> Coq_skip)
    (fun n' -> Coq_qseq ((Coq_slrot (Nor (Var x))), (rotate_left_n x n')))
    n

(** val qr_qexp : qvar -> qvar -> qvar -> qvar -> qexp **)

let qr_qexp a b c d =
  Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq
    ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_unary ((Nor (Var a)),
    Coq_nadd, (Nor (Var b)))), (Coq_unary ((Nor (Var d)), Coq_qxor, (Nor (Var
    a)))))),
    (rotate_left_n d
      ((fun x y -> max 0 (x-y)) (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ 0)))))))))))))))))))), (Coq_unary ((Nor (Var c)),
    Coq_nadd, (Nor (Var d)))))), (Coq_unary ((Nor (Var b)), Coq_qxor, (Nor
    (Var c)))))),
    (rotate_left_n b
      ((fun x y -> max 0 (x-y)) (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))),
    (Coq_unary ((Nor (Var a)), Coq_nadd, (Nor (Var b)))))), (Coq_unary ((Nor
    (Var d)), Coq_qxor, (Nor (Var a)))))),
    (rotate_left_n d
      ((fun x y -> max 0 (x-y)) (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ (succ (succ
        (succ (succ (succ (succ (succ 0)))))))))))), (Coq_unary ((Nor (Var
    c)), Coq_nadd, (Nor (Var d)))))), (Coq_unary ((Nor (Var b)), Coq_qxor,
    (Nor (Var c)))))),
    (rotate_left_n b
      ((fun x y -> max 0 (x-y)) (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ (succ (succ
        (succ (succ (succ (succ 0))))))))))

(** val qr_estore : estore **)

let qr_estore =
  init_estore_g
    (List.map (fun x -> ((TNor (Q, Nat)), x))
      (seq 0 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0))))))))))))))))))

(** val dr_qexp :
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar ->
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qexp **)

let dr_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq
    ((qr_qexp x0 x4 x8 x12), (qr_qexp x1 x5 x9 x13))),
    (qr_qexp x2 x6 x10 x14))), (qr_qexp x3 x7 x11 x15))),
    (qr_qexp x0 x5 x10 x15))), (qr_qexp x1 x6 x11 x12))),
    (qr_qexp x2 x7 x8 x13))), (qr_qexp x3 x4 x9 x14))

(** val chacha_qexp' :
    int -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar ->
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qexp **)

let rec chacha_qexp' n x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> Coq_skip)
    (fun n' -> Coq_qseq
    ((dr_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15),
    (chacha_qexp' n' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)))
    n

(** val chacha_qexp :
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar ->
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qexp **)

let chacha_qexp =
  chacha_qexp' (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))

(** val chacha_vmap : (qvar * int) -> var **)

let chacha_vmap = function
| (x, _) -> (match x with
             | G x' -> x'
             | L x' -> x')

(** val xa : qvar **)

let xa =
  G 0

(** val xb : qvar **)

let xb =
  G (succ 0)

(** val xc : qvar **)

let xc =
  G (succ (succ 0))

(** val xd : qvar **)

let xd =
  G (succ (succ (succ 0)))

(** val xe : qvar **)

let xe =
  G (succ (succ (succ (succ 0))))

(** val xf : qvar **)

let xf =
  G (succ (succ (succ (succ (succ 0)))))

(** val xg : qvar **)

let xg =
  G (succ (succ (succ (succ (succ (succ 0))))))

(** val xh : qvar **)

let xh =
  G (succ (succ (succ (succ (succ (succ (succ 0)))))))

(** val xi : qvar **)

let xi =
  G (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val xj : qvar **)

let xj =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))

(** val xk : qvar **)

let xk =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))

(** val xl : qvar **)

let xl =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))

(** val xm : qvar **)

let xm =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))

(** val xn : qvar **)

let xn =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ 0)))))))))))))

(** val xo : qvar **)

let xo =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ 0))))))))))))))

(** val xp : qvar **)

let xp =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ 0)))))))))))))))

(** val tempVar : var **)

let tempVar =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ 0)))))))))))))))

(** val tempVar1 : var **)

let tempVar1 =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ 0))))))))))))))))

(** val stacka : var **)

let stacka =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ 0)))))))))))))))))

(** val chacha_benv : benv **)

let chacha_benv =
  match gen_genv
          (List.map (fun x -> ((TNor (Q, Nat)), x))
            (seq 0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))) with
  | Some bv -> bv
  | None -> empty_benv

(** val compile_chacha :
    unit -> (((exp option * int) * cstore) * estore) value option **)

let compile_chacha _ =
  trans_qexp (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))) (fun _ -> succ 0) chacha_vmap
    chacha_benv QFTA empty_cstore tempVar tempVar1 stacka 0 [] qr_estore
    qr_estore (chacha_qexp xa xb xc xd xe xf xg xh xi xj xk xl xm xn xo xp)

(** val gen_chacha_vars' : int -> var list -> var list **)

let rec gen_chacha_vars' n acc =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> acc)
    (fun m -> gen_chacha_vars' m (m :: acc))
    n

(** val gen_chacha_vars : var list **)

let gen_chacha_vars =
  gen_chacha_vars' (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))
    []

(** val vars_for_chacha' :
    int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_chacha' =
  gen_vars (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))) gen_chacha_vars

(** val vars_for_chacha :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_chacha sn x =
  if (=) x (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
       (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))
  then ((((( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            0)))))))))))))))))))))))))))))))) (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ 0))))))))))))))))))), (succ (succ sn))), id_nat),
         id_nat)
  else vars_for_chacha' x

(** val avs_for_chacha : int -> int * int **)

let avs_for_chacha n =
  if (<) n
       (( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         0)))))))))))))))))))))))))))))))))
  then avs_for_arith (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ 0)))))))))))))))))))))))))))))))) n
  else ((succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))),
         ((fun x y -> max 0 (x-y)) n
           (( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ
             0)))))))))))))))))) (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ 0)))))))))))))))))))))))))))))))))))

(** val test_fun : qexp **)

let test_fun =
  Coq_qseq ((Coq_binapp ((Nor (Var (L x_var))), Coq_ndiv, (Nor (Var (L
    y_var))), (Nor (Var (L z_var))))), (Coq_binapp ((Nor (Var (L s_var))),
    Coq_nmul, (Nor (Var (L x_var))), (Nor (Var (L c_var))))))

(** val temp_var : int **)

let temp_var =
  succ (succ (succ (succ (succ 0))))

(** val temp1_var : int **)

let temp1_var =
  succ (succ (succ (succ (succ (succ 0)))))

(** val stack_var : int **)

let stack_var =
  succ (succ (succ (succ (succ (succ (succ 0))))))

(** val var_list : (typ * int) list **)

let var_list =
  ((TNor (C, Nat)), x_var) :: (((TNor (C, Nat)), y_var) :: (((TNor (C, Nat)),
    z_var) :: (((TNor (Q, Nat)), s_var) :: (((TNor (Q, Nat)), c_var) :: []))))

(** val dmc_benv : benv **)

let dmc_benv =
  match gen_env var_list empty_benv with
  | Some bv -> bv
  | None -> empty_benv

(** val dmc_vmap' : (typ * var) list -> int -> (qvar * int) -> int **)

let rec dmc_vmap' l n =
  match l with
  | [] ->
    (fun _ -> succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | p :: xl0 ->
    let (t0, x) = p in
    if is_q t0
    then (fun i ->
           if qdty_eq i ((L x), 0) then n else dmc_vmap' xl0 (succ n) i)
    else dmc_vmap' xl0 (succ n)

(** val dmc_vmap : (qvar * int) -> int **)

let dmc_vmap =
  dmc_vmap' var_list 0

(** val dmc_estore : estore **)

let dmc_estore =
  init_estore empty_estore var_list

(** val dmc_cstore : (int -> bool) Store.t **)

let dmc_cstore =
  Store.add ((L z_var), 0) (nat2fb (succ (succ (succ (succ (succ 0))))))
    (Store.add ((L y_var), 0)
      (nat2fb (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0))))))))))) (init_cstore empty_cstore var_list))

(** val compile_dm_qft :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dm_qft size =
  trans_qexp size (fun _ -> succ 0) dmc_vmap dmc_benv QFTA dmc_cstore
    temp_var temp1_var stack_var 0 [] dmc_estore dmc_estore test_fun

(** val compile_dm_classic :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dm_classic size =
  trans_qexp size (fun _ -> succ 0) dmc_vmap dmc_benv Classic dmc_cstore
    temp_var temp1_var stack_var 0 [] dmc_estore dmc_estore test_fun

(** val vars_for_dm_c' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_dm_c' size =
  gen_vars size (0 :: ((succ 0) :: []))

(** val vars_for_dm_c :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_dm_c size x =
  if (=) x stack_var
  then ((((( * ) size (succ (succ 0))), (succ 0)), id_nat), id_nat)
  else vars_for_dm_c' size x

(** val var_list_q : (typ * int) list **)

let var_list_q =
  ((TNor (Q, Nat)), x_var) :: (((TNor (Q, Nat)), y_var) :: (((TNor (C, Nat)),
    z_var) :: (((TNor (Q, Nat)), s_var) :: (((TNor (Q, Nat)), c_var) :: []))))

(** val dmq_benv : benv **)

let dmq_benv =
  match gen_env var_list_q empty_benv with
  | Some bv -> bv
  | None -> empty_benv

(** val dmq_vmap : (qvar * int) -> int **)

let dmq_vmap =
  dmc_vmap' var_list_q 0

(** val dmq_estore : estore **)

let dmq_estore =
  init_estore empty_estore var_list_q

(** val dmq_cstore : (int -> bool) Store.t **)

let dmq_cstore =
  Store.add ((L z_var), 0) (nat2fb (succ (succ (succ (succ (succ 0))))))
    (init_cstore empty_cstore var_list_q)

(** val compile_dmq_qft :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dmq_qft size =
  trans_qexp size (fun _ -> succ 0) dmq_vmap dmq_benv QFTA dmq_cstore
    temp_var temp1_var stack_var 0 [] dmq_estore dmq_estore test_fun

(** val compile_dmq_classic :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dmq_classic size =
  trans_qexp size (fun _ -> succ 0) dmq_vmap dmq_benv Classic dmq_cstore
    temp_var temp1_var stack_var 0 [] dmq_estore dmq_estore test_fun
