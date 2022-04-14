open BasicUtility
open Bvector
open CLArith
open Fin
open List0
open MathSpec
open OQASM
open OQASMProof
open OQIMP
open Vector

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

type word = coq_Bvector

(** val qr_estore : estore **)

let qr_estore =
  init_estore_g
    (List.map (fun x -> ((TNor (Q, Nat)), x))
      (seq 0 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0))))))))))))))))))

(** val dr_qexp :
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar ->
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qexp **)

let dr_qexp x2 x3 x4 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 =
  Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq
    ((qr_qexp x2 x17 x21 x25), (qr_qexp x3 x18 x22 x26))),
    (qr_qexp x4 x19 x23 x27))), (qr_qexp x16 x20 x24 x28))),
    (qr_qexp x2 x18 x23 x28))), (qr_qexp x3 x19 x24 x25))),
    (qr_qexp x4 x20 x21 x26))), (qr_qexp x16 x17 x22 x27))

(** val chacha_qexp' :
    int -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar ->
    qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qvar -> qexp **)

let rec chacha_qexp' n x2 x3 x4 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> Coq_skip)
    (fun n' -> Coq_qseq
    ((dr_qexp x2 x3 x4 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28),
    (chacha_qexp' n' x2 x3 x4 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28)))
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

(** val chacha_benv : benv **)

let chacha_benv =
  match gen_genv
          (List.map (fun x -> ((TNor (Q, Nat)), x))
            (seq 0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))) with
  | Some bv -> bv
  | None -> empty_benv

(** val x0 : qvar **)

let x0 =
  L 0

(** val x1 : qvar **)

let x1 =
  L (succ 0)

(** val x2' : qvar **)

let x2' =
  L (succ (succ 0))

(** val x3' : qvar **)

let x3' =
  L (succ (succ (succ 0)))

(** val x4' : qvar **)

let x4' =
  L (succ (succ (succ (succ 0))))

(** val x5 : qvar **)

let x5 =
  L (succ (succ (succ (succ (succ 0)))))

(** val x6 : qvar **)

let x6 =
  L (succ (succ (succ (succ (succ (succ 0))))))

(** val x7 : qvar **)

let x7 =
  L (succ (succ (succ (succ (succ (succ (succ 0)))))))

(** val x8 : qvar **)

let x8 =
  L (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val x9 : qvar **)

let x9 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))

(** val x10 : qvar **)

let x10 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))

(** val x11 : qvar **)

let x11 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))

(** val x12 : qvar **)

let x12 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))

(** val x13 : qvar **)

let x13 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ 0)))))))))))))

(** val x14 : qvar **)

let x14 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ 0))))))))))))))

(** val x15 : qvar **)

let x15 =
  L (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ 0)))))))))))))))

(** val out : qvar **)

let out =
  G (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ 0))))))))))))))))))

(** val getBit : word -> int -> bool **)

let getBit v k =
  match of_nat k (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          0)))))))))))))))))))))))))))))))) with
  | Some f ->
    nth (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ
      0)))))))))))))))))))))))))))))))) v f
  | None -> false

(** val collision_qexp :
    word -> word -> word -> word -> word -> word -> word -> word -> word ->
    word -> word -> word -> word -> word -> word -> word -> qexp **)

let collision_qexp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  Coq_qseq
    ((chacha_qexp x0 x1 x2' x3' x4' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15),
    (Coq_qif ((Coq_ceq ((Nor (Var x0)), (Nor (Num (Nat, (getBit v0)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x1)), (Nor (Num (Nat, (getBit v1)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x2')), (Nor (Num (Nat, (getBit v2)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x3')), (Nor (Num (Nat, (getBit v3)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x4')), (Nor (Num (Nat, (getBit v4)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x5)), (Nor (Num (Nat, (getBit v5)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x6)), (Nor (Num (Nat, (getBit v6)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x7)), (Nor (Num (Nat, (getBit v7)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x8)), (Nor (Num (Nat, (getBit v8)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x9)), (Nor (Num (Nat, (getBit v9)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x10)), (Nor (Num (Nat, (getBit v10)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x11)), (Nor (Num (Nat, (getBit v11)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x12)), (Nor (Num (Nat, (getBit v12)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x13)), (Nor (Num (Nat, (getBit v13)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x14)), (Nor (Num (Nat, (getBit v14)))))),
    (Coq_qif ((Coq_ceq ((Nor (Var x15)), (Nor (Num (Nat, (getBit v15)))))),
    (Coq_init ((Nor (Var out)), (Nor (Num (Nat, (fun _ -> true)))))),
    Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)),
    Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)),
    Coq_skip)), Coq_skip)), Coq_skip)), Coq_skip)))

(** val zero_word : bool t **)

let zero_word =
  coq_Bvect_false (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))

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
    (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))

(** val compile_collision :
    (((exp option * int) * cstore) * estore) value option **)

let compile_collision =
  trans_qexp (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))) (fun _ -> succ 0) chacha_vmap
    chacha_benv QFTA empty_cstore tempVar tempVar1 stacka 0 [] qr_estore
    qr_estore
    (collision_qexp zero_word zero_word zero_word zero_word zero_word
      zero_word zero_word zero_word zero_word zero_word zero_word zero_word
      zero_word zero_word zero_word zero_word)

(** val gen_collision_vars' : int -> var list -> var list **)

let rec gen_collision_vars' n acc =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> acc)
    (fun m -> gen_collision_vars' m (m :: acc))
    n

(** val gen_collision_vars : var list **)

let gen_collision_vars =
  gen_collision_vars' (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))
    []

(** val vars_for_collision' :
    int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_collision' =
  gen_vars (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))) gen_collision_vars

(** val vars_for_collision :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_collision sn x =
  if (=) x (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
       (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))))
  then ((((succ
         (( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
           (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
           (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
           0)))))))))))))))))))))))))))))))) (succ (succ (succ (succ (succ
           (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
           (succ (succ 0)))))))))))))))))))), (succ (succ sn))), id_nat),
         id_nat)
  else if (=) x (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ
            0))))))))))))))))))
       then ((((( * ) (succ (succ (succ (succ (succ (succ (succ (succ (succ
                 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                 (succ (succ (succ 0)))))))))))))))))))))))))))))))) (succ
                 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                 (succ (succ (succ (succ (succ (succ (succ
                 0))))))))))))))))))), (succ 0)), id_nat), id_nat)
       else vars_for_collision' x

(** val avs_for_collision : int -> int * int **)

let avs_for_collision n =
  if (<=) n
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
         (succ (succ (succ (succ (succ (succ (succ (succ
         0))))))))))))))))))),
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
  | p :: xl ->
    let (t0, x) = p in
    if is_q t0
    then (fun i ->
           if qdty_eq i ((L x), 0) then n else dmc_vmap' xl (succ n) i)
    else dmc_vmap' xl (succ n)

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
