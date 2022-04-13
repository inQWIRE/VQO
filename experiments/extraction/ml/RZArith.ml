open BasicUtility
open CLArith
open MathSpec
open Nat0
open OQASM
open OQASMProof
open PeanoNat

(** val rz_adder' : var -> int -> int -> (int -> bool) -> exp **)

let rec rz_adder' x n size m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((rz_adder' x m0 size m),
    (if m m0 then SR (((-) size n), x) else SKIP (x, m0))))
    n

(** val rz_adder : var -> int -> (int -> bool) -> exp **)

let rz_adder x n m =
  rz_adder' x n n m

(** val rz_sub' : var -> int -> int -> (int -> bool) -> exp **)

let rec rz_sub' x n size m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((rz_sub' x m0 size m),
    (if m m0 then SRR (((-) size n), x) else SKIP (x, m0))))
    n

(** val rz_sub : var -> int -> (int -> bool) -> exp **)

let rz_sub x n m =
  rz_sub' x n n m

(** val qft_cu : var -> posi -> int -> exp **)

let qft_cu x c n =
  Seq ((Seq ((RQFT (x, n)), (coq_CNOT (x, 0) c))), (QFT (x, n)))

(** val qft_acu : var -> posi -> int -> exp **)

let qft_acu x c n =
  Seq ((Seq ((RQFT (x, n)), (Seq ((Seq ((X (x, 0)), (coq_CNOT (x, 0) c))), (X
    (x, 0)))))), (QFT (x, n)))

(** val one_cu_adder : var -> int -> posi -> (int -> bool) -> exp **)

let one_cu_adder x n c m =
  CU (c, (rz_adder x n m))

(** val mod_adder_half :
    var -> int -> posi -> (int -> bool) -> (int -> bool) -> exp **)

let mod_adder_half x n c a m =
  Seq ((Seq ((Seq ((rz_adder x n a), (rz_sub x n m))), (qft_cu x c n))),
    (one_cu_adder x n c m))

(** val clean_hbit : var -> int -> posi -> (int -> bool) -> exp **)

let clean_hbit x n c m =
  Seq ((Seq ((rz_sub x n m), (qft_acu x c n))), (inv_exp (rz_sub x n m)))

(** val mod_adder :
    var -> int -> posi -> (int -> bool) -> (int -> bool) -> exp **)

let mod_adder x n c a m =
  Seq ((mod_adder_half x n c a m), (clean_hbit x n c a))

(** val rz_modmult' :
    var -> var -> int -> int -> posi -> int -> int -> exp **)

let rec rz_modmult' y x n size c a m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (y, 0))
    (fun m0 -> Seq ((rz_modmult' y x m0 size c a m), (CU ((x, ((-) size n)),
    (mod_adder y size c
      (nat2fb
        (Nat.modulo
          (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) m0) a) m))
      (nat2fb m))))))
    n

(** val rz_modmult_half : var -> var -> int -> posi -> int -> int -> exp **)

let rz_modmult_half y x size c a m =
  Seq ((Seq ((QFT (y, size)), (rz_modmult' y x size size c a m))), (RQFT (y,
    size)))

(** val rz_modmult_full :
    var -> var -> int -> posi -> int -> int -> int -> exp **)

let rz_modmult_full y x n c a ainv n0 =
  Seq ((rz_modmult_half y x n c a n0),
    (inv_exp (rz_modmult_half x y n c ainv n0)))

(** val vars_for_rz' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz' size =
  gen_vars size (x_var :: (y_var :: []))

(** val vars_for_rz :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz size x =
  if (=) x z_var
  then ((((mul size (Pervasives.succ (Pervasives.succ 0))), (Pervasives.succ
         0)), id_nat), id_nat)
  else vars_for_rz' size x

(** val real_rz_modmult_rev : int -> int -> int -> int -> exp **)

let real_rz_modmult_rev m c cinv size =
  rz_modmult_full y_var x_var size (z_var, 0) c cinv m

(** val one_cu_sub : var -> int -> posi -> (int -> bool) -> exp **)

let one_cu_sub x n c m =
  CU (c, (rz_sub x n m))

(** val rz_modadder_alt :
    posi -> var -> int -> posi -> (int -> bool) -> (int -> bool) -> exp **)

let rz_modadder_alt c1 x n c a m =
  Seq ((Seq ((Seq ((Seq ((Seq ((one_cu_adder x n c1 a), (rz_sub x n m))),
    (qft_cu x c n))), (Seq ((one_cu_adder x n c m),
    (one_cu_sub x n c1 a))))), (qft_acu x c n))), (one_cu_adder x n c1 a))

(** val rz_modmult_alt' :
    var -> var -> int -> int -> posi -> int -> int -> exp **)

let rec rz_modmult_alt' y x n size c a m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (y, 0))
    (fun m0 -> Seq ((rz_modmult_alt' y x m0 size c a m),
    (rz_modadder_alt (x, ((-) size n)) y size c
      (nat2fb
        (Nat.modulo
          (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) m0) a) m))
      (nat2fb m))))
    n

(** val rz_modmult_half_alt :
    var -> var -> int -> posi -> int -> int -> exp **)

let rz_modmult_half_alt y x size c a m =
  Seq ((Seq ((QFT (y, size)), (rz_modmult_alt' y x size size c a m))), (RQFT
    (y, size)))

(** val rz_modmult_full_alt :
    var -> var -> int -> posi -> int -> int -> int -> exp **)

let rz_modmult_full_alt y x n c a ainv n0 =
  Seq ((rz_modmult_half_alt y x n c a n0),
    (inv_exp (rz_modmult_half_alt x y n c ainv n0)))

(** val real_rz_modmult_rev_alt : int -> int -> int -> int -> exp **)

let real_rz_modmult_rev_alt m c cinv size =
  rz_modmult_full_alt y_var x_var size (z_var, 0) c cinv m

(** val nat_mult' : int -> int -> var -> var -> (int -> bool) -> exp **)

let rec nat_mult' n size x ex m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((one_cu_adder ex size (x, m0) m),
    (nat_mult' m0 size x ex (cut_n (times_two_spec m) size))))
    n

(** val nat_mult : int -> var -> var -> (int -> bool) -> exp **)

let nat_mult size x re m =
  Seq ((Seq ((Seq ((Seq ((Seq ((Rev x), (Rev re))), (QFT (re, size)))),
    (nat_mult' size size x re m))), (RQFT (re, size)))),
    (inv_exp (Seq ((Rev x), (Rev re)))))

(** val vars_for_rz_nat_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_nat_m size =
  gen_vars size (x_var :: (y_var :: []))

(** val nat_mult_out : int -> (int -> bool) -> exp **)

let nat_mult_out size m =
  nat_mult size x_var y_var m

(** val flt_mult' : int -> int -> var -> var -> (int -> bool) -> exp **)

let rec flt_mult' n size x ex m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((one_cu_adder ex size (x, ((-) size n)) m),
    (flt_mult' m0 size x ex (cut_n (div_two_spec m) size))))
    n

(** val flt_mult : int -> var -> var -> (int -> bool) -> exp **)

let flt_mult size x re m =
  Seq ((Seq ((Seq ((Rev x), (Rev re))), (flt_mult' size size x re m))),
    (inv_exp (Seq ((Rev x), (Rev re)))))

(** val rz_full_adder_i : int -> var -> var -> int -> int -> exp **)

let rec rz_full_adder_i size re y n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (re, 0))
    (fun m -> Seq ((rz_full_adder_i size re y m i), (CU ((y, m), (SR
    (((-) ((-) size n) i), re))))))
    n

(** val one_cu_full_adder_i :
    posi -> var -> var -> int -> int -> int -> exp **)

let one_cu_full_adder_i c re y size n i =
  CU (c, (rz_full_adder_i size re y n i))

(** val nat_full_mult' : int -> int -> var -> var -> var -> exp **)

let rec nat_full_mult' n size x y re =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (re, 0))
    (fun m -> Seq ((nat_full_mult' m size x y re),
    (one_cu_full_adder_i (x, ((-) size n)) re y size ((-) size m) m)))
    n

(** val nat_full_mult : int -> var -> var -> var -> exp **)

let nat_full_mult size x y re =
  Seq ((Seq ((Seq ((Seq ((Seq ((Rev re), (Rev x))), (QFT (re, size)))),
    (nat_full_mult' size size x y re))), (RQFT (re, size)))), (Seq ((Rev re),
    (Rev x))))

(** val vars_for_rz_nat_full_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_nat_full_m size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val nat_full_mult_out : int -> exp **)

let nat_full_mult_out size =
  nat_full_mult size x_var y_var z_var

(** val rz_full_adder' : var -> int -> int -> var -> exp **)

let rec rz_full_adder' x n size y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((CU ((y, m), (SR (((-) size n), x)))),
    (rz_full_adder' x m size y)))
    n

(** val rz_full_adder : var -> int -> var -> exp **)

let rz_full_adder x n y =
  rz_full_adder' x n n y

(** val one_cu_full_adder : posi -> var -> int -> var -> exp **)

let one_cu_full_adder c x n y =
  CU (c, (rz_full_adder x n y))

(** val flt_full_mult' : int -> int -> var -> var -> var -> var -> exp **)

let rec flt_full_mult' n size x y re ex =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((Seq ((Seq ((one_cu_full_adder (x, m) re size y),
    (coq_SWAP (y, ((-) size (Pervasives.succ 0))) (ex, m)))), (Lshift y))),
    (flt_full_mult' m size x y re ex)))
    n

(** val flt_full_mult_quar : int -> var -> var -> var -> var -> exp **)

let flt_full_mult_quar size x y re ex =
  flt_full_mult' size size x y re ex

(** val clean_high_flt : int -> int -> var -> var -> exp **)

let rec clean_high_flt n size y ex =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (y, 0))
    (fun m -> Seq ((Seq ((clean_high_flt m size y ex),
    (coq_SWAP (y, ((-) size (Pervasives.succ 0))) (ex, m)))), (Lshift y)))
    n

(** val flt_full_mult : int -> var -> var -> var -> var -> exp **)

let flt_full_mult size x y re ex =
  Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Rev re), (Rev x))), (Rev y))), (QFT
    (re, size)))), (Seq ((flt_full_mult_quar size x y re ex),
    (inv_exp (clean_high_flt size size y ex)))))), (RQFT (re, size)))), (Seq
    ((Seq ((Rev re), (Rev x))), (Rev y))))

(** val rz_full_adder_form : var -> int -> var -> exp **)

let rz_full_adder_form x n y =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))), (rz_full_adder x n y))),
    (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val rz_adder_form : var -> int -> (int -> bool) -> exp **)

let rz_adder_form x n m =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))), (rz_adder x n m))),
    (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val vars_for_rz_adder :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_adder size =
  gen_vars size (x_var :: [])

(** val rz_adder_out : int -> (int -> bool) -> exp **)

let rz_adder_out size m =
  rz_adder_form x_var size m

(** val vars_for_rz_full_add :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_full_add size =
  gen_vars size (x_var :: (y_var :: []))

(** val rz_full_adder_out : int -> exp **)

let rz_full_adder_out size =
  rz_full_adder_form x_var size y_var

(** val rz_full_sub' : var -> int -> int -> var -> exp **)

let rec rz_full_sub' x n size y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((CU ((y, m), (SRR (((-) size n), x)))),
    (rz_full_sub' x m size y)))
    n

(** val rz_full_sub : var -> int -> var -> exp **)

let rz_full_sub x n y =
  rz_full_sub' x n n y

(** val rz_full_sub_form : var -> int -> var -> exp **)

let rz_full_sub_form x n y =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))), (rz_full_sub x n y))),
    (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val rz_sub_right : var -> int -> (int -> bool) -> exp **)

let rz_sub_right x n m =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))), (rz_sub x n m))),
    (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val rz_compare_half3 : var -> int -> posi -> (int -> bool) -> exp **)

let rz_compare_half3 x n c m =
  Seq ((Seq ((rz_sub x n m), (RQFT (x, n)))), (coq_CNOT (x, 0) c))

(** val rz_moder' : int -> int -> var -> var -> (int -> bool) -> exp **)

let rec rz_moder' i n x ex m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun j -> Seq ((Seq ((Seq ((Seq ((rz_compare_half3 x n (ex, j) m), (QFT
    (x, n)))), (CU ((ex, j), (rz_adder x n m))))), (X (ex, j)))),
    (rz_moder' j n x ex (cut_n (div_two_spec m) n))))
    i

(** val rz_moder : int -> var -> var -> var -> int -> exp **)

let rz_moder n x re ex m =
  let i = findnum m n in
  Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Rev x), (Rev re))), (QFT (x, n)))),
  (rz_moder' (Pervasives.succ i) n x ex
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))))),
  (copyto x re n))),
  (inv_exp
    (rz_moder' (Pervasives.succ i) n x ex
      (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m)))))),
  (inv_exp (Seq ((Seq ((Rev x), (Rev re))), (QFT (x, n))))))

(** val vars_for_rz_moder :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_moder size =
  gen_vars (Pervasives.succ size) (x_var :: (y_var :: (z_var :: [])))

(** val avs_for_rz_moder : int -> int -> int * int **)

let avs_for_rz_moder size x =
  ((Nat.div x (Pervasives.succ size)), (Nat.modulo x (Pervasives.succ size)))

(** val rz_moder_out : int -> int -> exp **)

let rz_moder_out size =
  rz_moder (Pervasives.succ size) x_var y_var z_var

(** val rz_div : int -> var -> var -> var -> int -> exp **)

let rz_div n x re ex m =
  let i = findnum m n in
  Seq ((Seq ((Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))),
  (rz_moder' (Pervasives.succ i) n x ex
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))))),
  (copyto ex re n))),
  (inv_exp
    (rz_moder' (Pervasives.succ i) n x ex
      (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m)))))),
  (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val vars_for_rz_div :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_div size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val avs_for_rz_div : int -> int -> int * int **)

let avs_for_rz_div size x =
  ((Nat.div x (Pervasives.succ size)), (Nat.modulo x (Pervasives.succ size)))

(** val rz_div_out : int -> int -> exp **)

let rz_div_out size =
  rz_div (Pervasives.succ size) x_var y_var z_var

(** val rz_div_mod : int -> var -> var -> int -> exp **)

let rz_div_mod n x ex m =
  let i = findnum m ((-) n (Pervasives.succ 0)) in
  Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))),
  (rz_moder' (Pervasives.succ i) n x ex
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))))),
  (inv_exp (Seq ((Rev x), (QFT (x, n))))))

(** val vars_for_rz_div_mod :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_rz_div_mod size =
  gen_vars (Pervasives.succ size) (x_var :: (y_var :: []))

(** val avs_for_rz_div_mod : int -> int -> int * int **)

let avs_for_rz_div_mod size x =
  ((Nat.div x (Pervasives.succ size)), (Nat.modulo x (Pervasives.succ size)))

(** val rz_div_mod_out : int -> int -> exp **)

let rz_div_mod_out size =
  rz_div_mod (Pervasives.succ size) x_var y_var

(** val nat_con_add_mult : int -> var -> var -> var -> exp **)

let nat_con_add_mult n x y re =
  Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq
    ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq
    ((Seq ((Seq ((Rev re), (QFT (re, n)))), (rz_full_adder re n x))), (Rev
    x))), (nat_full_mult' n n x y re))), (Rev x))), (rz_full_adder re n y))),
    (Rev y))), (nat_full_mult' n n y x re))), (Rev y))),
    (rz_full_adder re n x))), (Rev x))), (nat_full_mult' n n x y re))), (Rev
    x))), (rz_full_adder re n y))), (Rev y))), (nat_full_mult' n n y x re))),
    (Rev y))), (rz_full_adder re n x))), (Rev x))),
    (nat_full_mult' n n x y re))), (Rev x))), (rz_full_adder re n y))), (Rev
    y))), (nat_full_mult' n n y x re))), (Rev y))), (RQFT (re, n)))), (Rev
    re))

(** val vars_for_nat_con_add_mult_out :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_nat_con_add_mult_out size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val nat_con_add_mult_out : int -> exp **)

let nat_con_add_mult_out size =
  nat_con_add_mult size x_var y_var z_var

(** val nat_old_con_add_mult : int -> var -> var -> var -> exp **)

let nat_old_con_add_mult n x y re =
  Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq ((Seq
    ((rz_full_adder_form re n x), (nat_full_mult n x y re))),
    (rz_full_adder_form re n y))), (nat_full_mult n y x re))),
    (rz_full_adder_form re n x))), (nat_full_mult n x y re))),
    (rz_full_adder_form re n y))), (nat_full_mult n y x re))),
    (rz_full_adder_form re n x))), (nat_full_mult n x y re))),
    (rz_full_adder_form re n y))), (nat_full_mult n y x re))

(** val vars_for_nat_old_con_add_mult_out :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_nat_old_con_add_mult_out size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val nat_old_con_add_mult_out : int -> exp **)

let nat_old_con_add_mult_out size =
  nat_old_con_add_mult size x_var y_var z_var

(** val appx_full_adder' : var -> int -> int -> int -> var -> exp **)

let rec appx_full_adder' x n b size y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq
    ((if (<=) n b
      then CU ((y, (add ((-) size b) m)), (SR (((-) b n), x)))
      else SKIP (x, m)), (appx_full_adder' x m b size y)))
    n

(** val appx_full_adder : var -> int -> int -> var -> exp **)

let appx_full_adder x n b y =
  appx_full_adder' x n b n y

(** val appx_full_adder_form : var -> int -> int -> var -> exp **)

let appx_full_adder_form x n b y =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, b)))), (appx_full_adder x n b y))),
    (inv_exp (Seq ((Rev x), (QFT (x, b))))))

(** val appx_full_adder_out : int -> int -> exp **)

let appx_full_adder_out size b =
  appx_full_adder_form x_var size b y_var

(** val appx_adder' : var -> int -> int -> (int -> bool) -> exp -> exp **)

let rec appx_adder' x n b m acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun m0 ->
    appx_adder' x m0 b m (Seq
      ((if (&&) ((<=) n b) (m m0) then SR (((-) b n), x) else SKIP (x, m0)),
      acc)))
    n

(** val appx_adder : var -> int -> int -> (int -> bool) -> exp **)

let appx_adder x n b m =
  appx_adder' x n b m (SKIP (x, 0))

(** val appx_adder_form : var -> int -> int -> (int -> bool) -> exp **)

let appx_adder_form x n b m =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, b)))), (appx_adder x n b m))),
    (inv_exp (Seq ((Rev x), (QFT (x, b))))))

(** val appx_adder_out : int -> int -> (int -> bool) -> exp **)

let appx_adder_out size b m =
  appx_adder_form x_var size b m

(** val appx_sub' : var -> int -> int -> (int -> bool) -> exp -> exp **)

let rec appx_sub' x n b m acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun m0 ->
    appx_sub' x m0 b m (Seq
      ((if (&&) ((<=) n b) (m m0) then SRR (((-) b n), x) else SKIP (x, m0)),
      acc)))
    n

(** val appx_sub : var -> int -> int -> (int -> bool) -> exp **)

let appx_sub x n b m =
  appx_sub' x n b m (SKIP (x, 0))

(** val appx_sub_form : var -> int -> int -> (int -> bool) -> exp **)

let appx_sub_form x n b m =
  Seq ((Seq ((Seq ((Rev x), (QFT (x, b)))), (appx_sub x n b m))),
    (inv_exp (Seq ((Rev x), (QFT (x, b))))))

(** val appx_sub_out : int -> int -> (int -> bool) -> exp **)

let appx_sub_out size b m =
  appx_sub_form x_var size b m

(** val appx_compare_half3 :
    var -> int -> int -> posi -> (int -> bool) -> exp **)

let appx_compare_half3 x n b c m =
  Seq ((Seq ((appx_sub x n b m), (RQFT (x, b)))), (coq_SWAP (x, 0) c))

(** val appx_moder' :
    int -> int -> int -> var -> var -> (int -> bool) -> exp **)

let rec appx_moder' i n b x ex m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun j -> Seq ((Seq ((Seq ((Seq ((Seq
    ((appx_compare_half3 x n b (ex, j) m), (Rshift x))), (QFT (x,
    ((-) b (Pervasives.succ 0)))))), (CU ((ex, j),
    (appx_adder x n ((-) b (Pervasives.succ 0)) m))))), (X (ex, j)))),
    (appx_moder' j n ((-) b (Pervasives.succ 0)) x ex
      (cut_n (div_two_spec m) n))))
    i

(** val nLshift : var -> int -> exp **)

let rec nLshift x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((Lshift x), (nLshift x m)))
    n

(** val appx_div_mod : int -> var -> var -> int -> exp **)

let appx_div_mod n x ex m =
  let i = findnum m ((-) n (Pervasives.succ 0)) in
  Seq ((Seq ((Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))),
  (appx_moder' (Pervasives.succ i) n n x ex
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))))),
  (RQFT (x, ((-) n (Pervasives.succ i)))))),
  (nLshift x (Pervasives.succ i)))), (Rev x))

(** val rshift_by_swap : int -> var -> exp **)

let rec rshift_by_swap n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((rshift_by_swap m x), (coq_SWAP (x, m) (x, n))))
    n

(** val lshift_by_swap : int -> var -> exp **)

let rec lshift_by_swap n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((coq_SWAP (x, m) (x, n)), (lshift_by_swap m x)))
    n

(** val nLshift_a : var -> int -> int -> exp **)

let rec nLshift_a x n step =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((lshift_by_swap n x), (nLshift_a x n m)))
    step

(** val appx_moder'_a :
    int -> int -> int -> var -> var -> (int -> bool) -> exp **)

let rec appx_moder'_a i n b x ex m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun j -> Seq ((Seq ((Seq ((Seq ((Seq
    ((appx_compare_half3 x n b (ex, j) m), (rshift_by_swap n x))), (QFT (x,
    ((-) b (Pervasives.succ 0)))))), (CU ((ex, j),
    (appx_adder x n ((-) b (Pervasives.succ 0)) m))))), (X (ex, j)))),
    (appx_moder'_a j n ((-) b (Pervasives.succ 0)) x ex
      (cut_n (div_two_spec m) n))))
    i

(** val appx_div_mod_a : int -> var -> var -> int -> exp **)

let appx_div_mod_a n x ex m =
  let i = findnum m ((-) n (Pervasives.succ 0)) in
  Seq ((Seq ((Seq ((Seq ((Seq ((Rev x), (QFT (x, n)))),
  (appx_moder'_a (Pervasives.succ i) n n x ex
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))))),
  (RQFT (x, ((-) n (Pervasives.succ i)))))),
  (nLshift_a x n (Pervasives.succ i)))), (Rev x))

(** val app_div_mod_out : int -> int -> exp **)

let app_div_mod_out size =
  appx_div_mod (Pervasives.succ size) x_var y_var

(** val vars_for_app_div_mod :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_app_div_mod size =
  gen_vars (Pervasives.succ size) (x_var :: (y_var :: []))

(** val avs_for_app_div_mod : int -> int -> int * int **)

let avs_for_app_div_mod size x =
  ((Nat.div x (Pervasives.succ size)), (Nat.modulo x (Pervasives.succ size)))

(** val app_div_mod_aout : int -> int -> exp **)

let app_div_mod_aout size =
  appx_div_mod_a (Pervasives.succ size) x_var y_var
