From Coq Require Import Arith NArith Vector Bvector.
From QuickChick Require Import QuickChick.
Require Import BasicUtility OQASM Testing RZArith CLArith.

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

  Definition x : var := 0.
  Definition y : var := 1.
  Definition c : posi := (2, 0).

  Definition tof_add_circ n := adder01 n x y c.

  Definition tof_add_env n : f_env := fun _ => n.

  Definition tof_add_prec n : nat := get_prec (tof_add_env n) (tof_add_circ n).

  Conjecture tof_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equivb (get_vars (tof_add_circ n)) (tof_add_env n)
      (exp_sem (fun _ => n) n (tof_add_circ n) (x |=> vx, y |=> vy))
          (x |=> vx, y |=> vx [+] vy) = true.

End TofAdd.

(*
QuickChick (TofAdd.tof_add_spec 60).
 *)

Module RzAdd.

  Definition x := 0.
  Definition y := 1.
  Definition ex := 2.

  Definition rz_add_circ n :=
    Rev x;
    QFT x;
    rz_full_adder x n y;
    RQFT x;
    Rev x.

  Definition rz_add_env n : f_env := fun _ => n.

  Definition rz_add_prec n : nat := get_prec (rz_add_env n) (rz_add_circ n).

  Conjecture rz_add_spec :
    forall (n : nat) (vx vy : Bvector n),
    st_equivb (get_vars (rz_add_circ n)) (rz_add_env n)
      (exp_sem (fun _ => n) n (rz_add_circ n) (x |=> vx, y |=> vy))
          (x |=> vx [+] vy, y |=> vy) = true.

End RzAdd.

(*
QuickChick (RzAdd.rz_add_spec 60).
 *)

Module AddParam.

  Definition x := 0.
  Definition re := 1.

  Definition add_param_circ n (vm : Bvector n) :=
    Rev x; QFT x; rz_adder x n (nth_or_false vm); RQFT x; Rev x.

  Definition add_param_vars n := get_vars (add_param_circ n (Bvect_false n)).

  Definition add_param_env n : f_env := fun _ => n.

  Definition add_param_prec n : nat :=
    get_prec (add_param_env n) (add_param_circ n (Bvect_false n)).

  Conjecture add_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (add_param_vars n) (add_param_env n)
      (exp_sem (add_param_env n) n (add_param_circ n vm)
        (x |=> vx))
      (x |=> vx [+] vm) = true.

End AddParam.

(*
QuickChick (AddParam.add_param_spec 60).
 *)

Module RzMul.

  Definition x := 0.
  Definition y := 1.
  Definition re := 2.

  Definition rz_mul_circ n := nat_full_mult n x y re.

  Definition rz_mul_vars n := get_vars (rz_mul_circ n).

  Definition rz_mul_env n : f_env := fun _ => n.

  Definition rz_mul_prec n : nat := get_prec (rz_mul_env n) (rz_mul_circ n).

  Conjecture rz_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (rz_mul_vars n) (rz_mul_env n)
      (exp_sem (rz_mul_env n) n (rz_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> vre [+] vx [*] vy) = true.

End RzMul.

(*
QuickChick (RzMul.rz_mul_spec 60).
 *)

Module MulParam.

  Definition x := 0.
  Definition re := 1.

  Definition mul_param_circ n (vm : Bvector n) :=
    nat_mult n x re (nth_or_false vm).

  Definition mul_param_vars n := get_vars (mul_param_circ n (Bvect_false n)).

  Definition mul_param_env n : f_env := fun _ => n.

  Definition mul_param_prec n : nat :=
    get_prec (mul_param_env n) (mul_param_circ n (Bvect_false n)).

  Conjecture mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (mul_param_vars n) (mul_param_env n)
      (exp_sem (mul_param_env n) n (mul_param_circ n vm)
        (x |=> vx, re |=> vre))
      (x |=> vx, re |=> vre [+] vx [*] vm) = true.

End MulParam.

(*
QuickChick (MulParam.mul_param_spec 60).
 *)

Module TofMul.

  Definition x  : var := 0.
  Definition y  : var := 1.
  Definition re : var := 2.
  Definition c : posi := (3, 0).

  Definition tof_mul_circ n := cl_full_mult n x y re c.

  Definition tof_mul_vars n := get_vars (tof_mul_circ n).

  Definition tof_mul_env n : f_env := fun _ => n.

  Definition tof_mul_prec n : nat := get_prec (tof_mul_env n) (tof_mul_circ n).

  Conjecture tof_mul_spec :
    forall (n : nat) (vx vy vre : Bvector n),
    st_equivb (tof_mul_vars n) (tof_mul_env n)
      (exp_sem (tof_mul_env n) n (tof_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> vre [+] vx [*] vy) = true.

End TofMul.

(*
QuickChick (TofMul.tof_mul_spec 60).
 *)

Module TofMulParam.

  Definition x  : var := 0.
  Definition re : var := 2.
  Definition c : posi := (3, 0).

  Definition tof_mul_param_circ n (vm : Bvector n) :=
    cl_nat_mult n x re c (nth_or_false vm).

  Definition tof_mul_param_vars n := get_vars (tof_mul_param_circ n (Bvect_false n)).

  Definition tof_mul_param_env n : f_env := fun _ => n.

  Definition tof_mul_param_prec n : nat :=
    get_prec (tof_mul_param_env n) (tof_mul_param_circ n (Bvect_false n)).

  Conjecture tof_mul_param_spec :
    forall (n : nat) (vm vx vre : Bvector n),
    st_equivb (tof_mul_param_vars n) (tof_mul_param_env n)
      (exp_sem (tof_mul_param_env n) n (tof_mul_param_circ n vm)
        (x |=> vx, re |=> vre))
      (x |=> vx, re |=> vre [+] vx [*] vm) = true.

End TofMulParam.

(*
QuickChick (TofMulParam.tof_mul_param_spec 60).
 *)

Module DivMod.

  Definition x  : var := 0.
  Definition ex : var := 1.

  Definition div_mod_circ n m :=
    rz_div_mod (S n) x ex m.

  Definition div_mod_vars n := get_vars (div_mod_circ n 1).

  Definition div_mod_env n : f_env := fun _ => S n.

  Definition div_mod_prec n : nat :=
    get_prec (div_mod_env n) (div_mod_circ n 1).

  Definition div_mod_spec : Checker :=
    forAll (choose (60, 60)) (fun n =>
    forAll (choose (1, 2 ^ (min n 30) - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equivb (div_mod_vars n) (div_mod_env n)
      (exp_sem (div_mod_env n) (S n) (div_mod_circ n m)
        (x |=> vx))
      (x |=> vx [%] m, ex |=> vx [/] m) = true)))).

End DivMod.

(*
QuickChick DivMod.div_mod_spec.
 *)

Module TofDivMod.

  Definition x  : var := 0.
  Definition y  : var := 1.
  Definition ex : var := 2.
  Definition c1 : posi := (3, 0).

  Definition tof_div_mod_circ n m :=
    cl_div_mod n x y ex c1 m.

  Definition tof_div_mod_vars n := get_vars (tof_div_mod_circ n 1).

  Definition tof_div_mod_env n : f_env := fun _ => S n.

  Definition tof_div_mod_prec n : nat :=
    get_prec (tof_div_mod_env n) (tof_div_mod_circ n 1).

  Definition tof_div_mod_spec : Checker :=
    forAll (choose (60, 60)) (fun n =>
    forAll (choose (1, 2 ^ (min n 30) - 1)) (fun m =>
    forAllShrink arbitrary shrink (fun vx : Bvector n =>
    dec2checker
    (st_equivb (tof_div_mod_vars n) (tof_div_mod_env n)
      (exp_sem (tof_div_mod_env n) n (tof_div_mod_circ n m)
        (x |=> vx))
      (x |=> vx [%] m, ex |=> vx [/] m) = true)))).

End TofDivMod.

(*
QuickChick TofDivMod.tof_div_mod_spec.
 *)

Module AddMul.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition re : var := 2.

  Definition add_mul_circ n := nat_con_add_mult n x y re.

  Definition add_mul_vars n := get_vars (add_mul_circ n).

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
      (exp_sem (add_mul_env n) n (add_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> compute_new_re vx vy vre) = true.

End AddMul.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMul.add_mul_spec 60).
 *)

Module AddMulOld.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition re : var := 2.

  Definition add_mul_circ n := nat_old_con_add_mult n x y re.

  Definition add_mul_vars n := get_vars (add_mul_circ n).

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
      (exp_sem (add_mul_env n) n (add_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> compute_new_re vx vy vre) = true.

End AddMulOld.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMulOld.add_mul_spec 60).
 *)

Module AddMulToff.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition re : var := 2.
  Definition c : posi := (3, 0).

  Definition add_mul_circ n := cl_nat_con_add_mult n x y re c.

  Definition add_mul_vars n := get_vars (add_mul_circ n).

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
      (exp_sem (add_mul_env n) n (add_mul_circ n)
        (x |=> vx, y |=> vy, re |=> vre))
            (x |=> vx, y |=> vy, re |=> compute_new_re vx vy vre) = true.

End AddMulToff.

(*
QuickChickWith (updMaxSuccess stdArgs 100) (AddMulToff.add_mul_spec 60).
 *)

Module ModMul8.

  Definition x : var := 0.
  Definition y : var := 1.
  Definition z : var := 2.
  Definition s : var := 3.
  Definition c : posi := (4, 0).

  Definition n := 8.
  Definition M := 127.
  Definition A := 113.
  Definition Ainv := 9.

  Definition mod_mul_8_circ := modmult (MathSpec.nat2fb M) A Ainv n x y z s c.

  Definition mod_mul_8_vars := get_vars mod_mul_8_circ.

  Definition mod_mul_8_env : f_env := fun _ => n.

  Definition mod_mul_8_spec :=
    forAll (choose (0, pred M)) (fun xv =>
    let xn := N.of_nat xv in
    checker
    (st_equivb mod_mul_8_vars mod_mul_8_env
      (exp_sem mod_mul_8_env 9 mod_mul_8_circ (x |=> n2bvector 8 xn))
      (y |=> n2bvector 8 (xn * 113 mod 127)))).

End ModMul8.

QuickChick ModMul8.mod_mul_8_spec.


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

QuickChick ModMul8Rz.mod_mul_8_spec.
