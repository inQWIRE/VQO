From Coq Require Import Arith NArith Vector Bvector ZArith List.
From QuickChick Require Import QuickChick.
Require Import BasicUtility OQASM OQASMProof Testing RZArith CLArith.

Extract Inductive positive => int
[ "(fun p->1+2*p)" "(fun p->2*p)" "1" ]
"(fun f2p1 f2p f1 p -> if p=1 then f1 () else if p mod 2 = 0 then f2p (p lsr 1) else f2p1 (p lsr 1))".
Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.sub => "(-)".
Extract Constant Nat.modulo => "(mod)".
Extract Constant Nat.div => "(/)".
Extract Constant N.of_nat => "(fun x -> x)".

Open Scope exp_scope.

Fixpoint exp2 n :=
  match n with
  | 0 => 1%N
  | S n' => N.double (exp2 n')
  end.

Lemma exp2_spec :
  forall n, exp2 n = (2 ^ N.of_nat n)%N.
Proof.
  intros n. induction n as [| n IH].
  - reflexivity.
  - rewrite Nat2N.inj_succ, N.pow_succ_r'. cbn - [ N.mul ].
    rewrite IH. apply N.double_spec.
Qed.

Instance genPosSized : GenSized positive :=
  {| arbitrarySized x := fmap N.succ_pos (arbitrarySized x) |}.

Instance shrinkPos : Shrink positive :=
  {| shrink x := List.map N.succ_pos (shrink (Pos.pred_N x)) |}.

Instance showPos : Show positive := {| show p := show_N (Npos p) |}.

Infix "[+]" := add_bvector (at level 50).

Definition mul_bvector {n} (v v' : Bvector n) :=
  n2bvector n (bvector2n v * bvector2n v')%N.

Infix "[*]" := mul_bvector (at level 40).

Definition div_bvector {n} (v : Bvector n) (m : nat) :=
  n2bvector n (bvector2n v / N.of_nat m).

Infix "[/]" := div_bvector (at level 40).

Definition mod_bvector {n} (v : Bvector n) (m : nat) :=
  n2bvector n (bvector2n v mod N.of_nat m).

Infix "[%]" := mod_bvector (at level 40).

Definition nth_or_false {n} (v : Bvector n) (i : nat) :=
  match lt_dec i n with
  | left P => nth_order v P
  | in_right => false
  end.

Module TofAdd.

  Definition tof_add_env n : f_env := fun _ => n.

  Definition tof_add_prec n : nat := get_prec (tof_add_env n) (adder01_out n).

  Conjecture tof_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equivb (get_vars (adder01_out n)) (tof_add_env n)
      (exp_sem (fun _ => n) n (adder01_out n) (x_var |=> vx, y_var |=> vy))
          (x_var |=> vx, y_var |=> vx [+] vy) = true.

End TofAdd.

(*
QuickChick (TofAdd.tof_add_spec 60).
 *)

Module RzAdd.

  Definition rz_add_env n : f_env := fun _ => n.

  Definition rz_add_prec n : nat := get_prec (rz_add_env n) (rz_full_adder_out n).

  Conjecture rz_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equivb (get_vars (rz_full_adder_out n)) (rz_add_env n)
      (exp_sem (fun _ => n) n (rz_full_adder_out n) (x_var |=> vx, y_var |=> vy))
          (x_var |=> vx [+] vy, y_var |=> vy) = true.

End RzAdd.

(*
QuickChick (RzAdd.rz_add_spec 60).
 *)

Module AddParam.

  Definition add_param_vars n := get_vars (rz_adder_out n (fun _ => false)).

  Definition add_param_env n : f_env := fun _ => n.

  Definition add_param_prec n : nat :=
    get_prec (add_param_env n) (rz_adder_out n (fun _ => false)).

  Conjecture add_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (add_param_vars n) (add_param_env n)
      (exp_sem (add_param_env n) n (rz_adder_out n (nth_or_false vm))
        (x_var |=> vx))
      (x_var |=> vx [+] vm) = true.

End AddParam.

(*
QuickChick (AddParam.add_param_spec 60).
 *)

Module RzMul.

  Definition rz_mul_vars n := get_vars (nat_full_mult_out n).

  Definition rz_mul_env n : f_env := fun _ => n.

  Definition rz_mul_prec n : nat := get_prec (rz_mul_env n) (nat_full_mult_out n).

  Conjecture rz_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (rz_mul_vars n) (rz_mul_env n)
      (exp_sem (rz_mul_env n) n (nat_full_mult_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> vre [+] vx [*] vy) = true.

End RzMul.

(*
QuickChick (RzMul.rz_mul_spec 60).
 *)

Module MulParam.

  Definition mul_param_vars n := get_vars (nat_mult_out n (fun _ => false)).

  Definition mul_param_env n : f_env := fun _ => n.

  Definition mul_param_prec n : nat :=
    get_prec (mul_param_env n) (nat_mult_out n (fun _ => false)).

  Conjecture mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (mul_param_vars n) (mul_param_env n)
      (exp_sem (mul_param_env n) n (nat_mult_out n (nth_or_false vm))
        (x_var |=> vx, y_var |=> vre))
      (x_var |=> vx, y_var |=> vre [+] vx [*] vm) = true.

End MulParam.

(*
QuickChick (MulParam.mul_param_spec 60).
 *)

Module TofMul.

  Definition tof_mul_vars n := get_vars (cl_full_mult_out n).

  Definition tof_mul_env n : f_env := fun _ => n.

  Definition tof_mul_prec n : nat := get_prec (tof_mul_env n) (cl_full_mult_out n).

  Conjecture tof_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (tof_mul_vars n) (tof_mul_env n)
      (exp_sem (tof_mul_env n) n (cl_full_mult_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> vre [+] vx [*] vy) = true.

End TofMul.

(*
QuickChick (TofMul.tof_mul_spec 60).
 *)

Module QuipperTofMul.

  Definition tof_mul_vars n := get_vars (cl_full_mult_out_place_out n).

  Definition tof_mul_env n : f_env := fun _ => n.

  Definition tof_mul_prec n : nat := get_prec (tof_mul_env n) (cl_full_mult_out_place_out n).

  Conjecture tof_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (tof_mul_vars n) (tof_mul_env n)
      (exp_sem (tof_mul_env n) n (cl_full_mult_out_place_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> vre [+] vx [*] vy) = true.

End QuipperTofMul.

(*
QuickChick (QuipperTofMul.tof_mul_spec 60).
 *)

Module TofMulParam.

  Definition tof_mul_param_vars n := get_vars (cl_nat_mult_out n (fun _ => false)).

  Definition tof_mul_param_env n : f_env := fun _ => n.

  Definition tof_mul_param_prec n : nat :=
    get_prec (tof_mul_param_env n) (cl_nat_mult_out n (fun _ => false)).

  Conjecture tof_mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (tof_mul_param_vars n) (tof_mul_param_env n)
      (exp_sem (tof_mul_param_env n) n (cl_nat_mult_out n (nth_or_false vm))
        (x_var |=> vx, y_var |=> vre))
      (x_var |=> vx, y_var |=> vre [+] vx [*] vm) = true.

End TofMulParam.

(*
QuickChick (TofMulParam.tof_mul_param_spec 60).
 *)

Module DivMod.

  Definition div_mod_vars n := get_vars (rz_div_mod_out n 1).

  Definition div_mod_env n : f_env := fun _ => S n.

  Definition div_mod_prec n : nat :=
    get_prec (div_mod_env n) (rz_div_mod_out n 1).

  Definition div_mod_spec : Checker :=
    forAll (choose (60, 60)) (fun n =>
    forAll (choose (1, 2 ^ (min n 30) - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equivb (div_mod_vars n) (div_mod_env n)
      (exp_sem (div_mod_env n) (S n) (rz_div_mod_out n m)
        (x_var |=> vx))
      (x_var |=> vx [%] m, y_var |=> vx [/] m) = true)))).

End DivMod.

(*
QuickChick DivMod.div_mod_spec.
 *)

Module AppDivMod.

  Definition div_mod_vars n := get_vars (app_div_mod_aout n 1).

  Definition div_mod_env n : f_env := fun _ => S n.

  Definition div_mod_prec n : nat :=
    get_prec (div_mod_env n) (app_div_mod_aout n 1).

  Definition div_mod_spec : Checker :=
    forAll (choose (60, 60)) (fun n =>
    forAll (choose (1, 2 ^ (min n 30) - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equivb (div_mod_vars n) (div_mod_env n)
      (exp_sem (div_mod_env n) (S n) (app_div_mod_aout n m)
        (x_var |=> vx))
      (x_var |=> vx [%] m, y_var |=> vx [/] m) = true)))).

End AppDivMod.

(*
QuickChick AppDivMod.div_mod_spec.
*)

Module TofDivMod.

  Definition tof_div_mod_vars n := get_vars (cl_div_mod_out n 1).

  Definition tof_div_mod_env n : f_env := fun _ => S n.

  Definition tof_div_mod_prec n : nat :=
    get_prec (tof_div_mod_env n) (cl_div_mod_out n 1).

  Definition tof_div_mod_spec : Checker :=
    forAll (choose (6, 6)) (fun n =>
    forAll (choose (1, 2 ^ (min n 30) - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equivb (tof_div_mod_vars n) (tof_div_mod_env n)
      (exp_sem (tof_div_mod_env n) n (cl_div_mod_out n m)
        (x_var |=> vx))
      (x_var |=> vx [%] m, z_var |=> vx [/] m) = true)))).

End TofDivMod.

(*
QuickChick TofDivMod.tof_div_mod_spec.
 *)

Module AddMul.

  Definition add_mul_vars n := get_vars (nat_con_add_mult_out n).

  Definition add_mul_env n : f_env := fun _ => n.

  Definition compute_new_re {n} (vx vy vre : Bvector n) :=
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    vre.

  Conjecture add_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (add_mul_vars n) (add_mul_env n)
      (exp_sem (add_mul_env n) n (nat_con_add_mult_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> compute_new_re vx vy vre) = true.

End AddMul.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMul.add_mul_spec 60).
 *)

Module AddMulOld.

  Definition add_mul_vars n := get_vars (nat_old_con_add_mult_out n).

  Definition add_mul_env n : f_env := fun _ => n.

  Definition compute_new_re {n} (vx vy vre : Bvector n) :=
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    vre.

  Conjecture add_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (add_mul_vars n) (add_mul_env n)
      (exp_sem (add_mul_env n) n (nat_old_con_add_mult_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> compute_new_re vx vy vre) = true.

End AddMulOld.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMulOld.add_mul_spec 60).
 *)

Module AddMulToff.

  Definition add_mul_vars n := get_vars (cl_nat_con_add_mult_out n).

  Definition add_mul_env n : f_env := fun _ => n.

  Definition compute_new_re {n} (vx vy vre : Bvector n) :=
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vx in
    let vre := vre [+] vx [*] vy in
    let vre := vre [+] vy in
    vre.

  Conjecture add_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (add_mul_vars n) (add_mul_env n)
      (exp_sem (add_mul_env n) n (cl_nat_con_add_mult_out n)
        (x_var |=> vx, y_var |=> vy, z_var |=> vre))
            (x_var |=> vx, y_var |=> vy, z_var |=> compute_new_re vx vy vre) = true.

End AddMulToff.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMulToff.add_mul_spec 60).
 *)

Module ModMul8.

  Definition n := 8.
  Definition M := 127.
  Definition A := 113.
  Definition Ainv := 9.

  Definition mod_mul_8_circ := real_modmult_rev M A Ainv n.

  Definition mod_mul_8_vars := get_vars mod_mul_8_circ.

  Definition mod_mul_8_env : f_env := fun _ => n.

  Definition mod_mul_8_spec :=
    forAll (choose (0, pred M)) (fun xv =>
    let xn := N.of_nat xv in
    checker
    (st_equivb mod_mul_8_vars mod_mul_8_env
      (exp_sem mod_mul_8_env 9 mod_mul_8_circ (x_var |=> n2bvector 8 xn))
      (y_var |=> n2bvector 8 (xn * 113 mod 127)))).

End ModMul8.

(*
QuickChick ModMul8.mod_mul_8_spec.
 *)

Module ModMul8Rz.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition c : posi := (4, 0).

  Definition n := 9.
  Definition M := 127.
  Definition A := 113.
  Definition Ainv := 9.

  Definition mod_mul_8_circ := Rev x; Rev y; rz_modmult_full y x n c A Ainv M; Rev x; Rev y.

  Definition mod_mul_8_vars := get_vars mod_mul_8_circ.

  Definition mod_mul_8_env : f_env := fun _ => n.

  Definition mod_mul_8_spec :=
    forAllShrink (choose (0, pred M)) shrink (fun xv =>
    let xn := N.of_nat xv in
    checker
    (st_equivb mod_mul_8_vars mod_mul_8_env
      (exp_sem mod_mul_8_env 9 mod_mul_8_circ (x |=> n2bvector 9 xn))
      (y |=> n2bvector 8 (xn * 113 mod 127)))).

End ModMul8Rz.

(*
QuickChick ModMul8Rz.mod_mul_8_spec.
 *)

Module AppxAdd.

  Definition appx_add_circ n b := appx_full_adder_out n (n-b).

  Definition bv_dist {n} (v v' : Bvector n) :=
    let z := Z.of_N (bvector2n v) in
    let z' := Z.of_N (bvector2n v') in
    Z.abs_N (Z.min (Z.modulo (z - z') (Z.of_N (exp2 n))) (BinInt.Z.modulo (z' - z) (Z.of_N (exp2 n)))).

  Definition st_dist n (st1 st2 : state) :=
    match get_statevector n x_var st1, get_statevector n x_var st2 with
    | Some v1, Some v2 => bv_dist v1 v2
    | _, _ => exp2 n
    end.

  Definition appx_add_check m n b : G N :=
    liftGen
      (fun l =>
        fold_left N.max
          (map
            (fun '(vx, vy) =>
             st_dist n
               (exp_sem (fun _ => n) n (appx_add_circ n b) (x_var |=> vx, y_var |=> vy))
               (x_var |=> vx [+] vy, y_var |=> vy))
            l)
          0%N)
      (vectorOf m (genPair (@gen_bvector' n) (@gen_bvector' n))).

  Conjecture appx_add_spec :
    forall (n : nat) b (vx vy : Bvector n),
    (st_dist n
      (exp_sem (fun _ => n) n (appx_add_circ n b) (x_var |=> vx, y_var |=> vy))
      (x_var |=> vx [+] vy, y_var |=> vy) <? exp2 b)%N = true.

End AppxAdd.

(* example: compute the maximum difference between the (8-1)-bit approximate adder and the 8-bit exact adder, over 10000 samples *)
(*
Sample (AppxAdd.appx_add_check 10000 8 1).
 *)
(*
QuickChick (AppxAdd.appx_add_spec).
 *)
