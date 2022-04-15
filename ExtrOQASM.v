(* We need to redefine trans_exp to output SQIR programs using the
   alternate gate set & prove that this new definition is equivalent
   to the old (see SQIR/utilities/AltGateSet.v and SQIR/examples/shor/AltShor.v
   for examples). *)

Require Import Prelim.
Require Import AltGateSet.
Require Import MathSpec BasicUtility OQASM OQASMProof.
Require Import RZArith.
Require Import CLArith.
Require Import OQIMP.
Require Import OracleExample.

Definition rz_ang (n:nat) : R := ((R2 * PI)%R / R2^n). (* redefined using R2 *)

Definition rrz_ang (n:nat) : R := ((R2 * PI)%R - ((R2 * PI)%R / R2^n)).

Definition ID q := AltGateSet.U1 R0 q.

Fixpoint gen_sr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => ID (find_pos f (x,0))
    | S m => (gen_sr_gate' f x m size) >> (U1 (rz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_sr_gate (f:vars) (x:var) (n:nat) := gen_sr_gate' f x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => ID (find_pos f (x,0))
    | S m => (gen_srr_gate' f x m size) >> (U1 (rrz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_srr_gate (f:vars) (x:var) (n:nat) := gen_srr_gate' f x (S n) (S n).

Fixpoint controlled_rotations_gen (f : vars) (x:var) (n : nat) (i:nat) : ucom U :=
    match n with
    | 0 | 1 => ID (find_pos f (x,i))
    | S m => (controlled_rotations_gen f x m i) >>
              (control (find_pos f (x,(m+i)%nat)) (U1 (rz_ang n) (find_pos f (x,i))))
    end.

Fixpoint QFT_gen (f : vars) (x:var) (n : nat) (size:nat) : ucom U :=
    match n with
    | 0 => ID (find_pos f (x,0))
    | S m => (QFT_gen f x m size) >>
             ((AltGateSet.H (find_pos f (x,m))) >> 
             (controlled_rotations_gen f x (size-m) m))
    end.

Fixpoint nH (f : vars) (x:var) (n:nat) (b:nat) : ucom U :=
     match n with 0 => ID (find_pos f (x,0))
               | S m => (nH f x m b) >> (AltGateSet.H (find_pos f (x,(b+m)%nat))) 
     end.

Definition trans_qft (f:vars) (x:var) (b:nat) : ucom U := 
    QFT_gen f x b b >> nH f x (vsize f x - b) b.

Definition trans_rqft (f:vars) (x:var) (b:nat) : ucom U :=
          invert (QFT_gen f x b b >> nH f x (vsize f x - b) b).

Fixpoint trans_exp' (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (ucom U * vars * (nat -> posi)) :=
    match exp with
    | SKIP p => (ID (find_pos f p), f, avs)
    | X p => (AltGateSet.X (find_pos f p), f, avs)
    | RZ q p => (U1 (rz_ang q) (find_pos f p), f, avs)
    | RRZ q p => (U1 (rrz_ang q) (find_pos f p), f, avs)
    | SR n x => (gen_sr_gate f x n, f, avs)
    | SRR n x => (gen_srr_gate f x n, f, avs)
    | Lshift x => (ID (find_pos f (x,0)), trans_lshift f x, lshift_avs dim f avs x)
    | Rshift x => (ID (find_pos f (x,0)), trans_rshift f x, rshift_avs dim f avs x)
    | Rev x => (ID (find_pos f (x,0)), trans_rev f x, rev_avs dim f avs x)
    | CU p e1 => match trans_exp' f dim e1 avs with 
                 | (e1', f',avs') => (control (find_pos f p) e1', f, avs) end
    | QFT x b => (trans_qft f x b, f, avs)
    | RQFT x b => (trans_rqft f x b, f, avs)
    | (e1 ; e2)%exp => match trans_exp' f dim e1 avs with 
                 | (e1', f', avs') => 
                        match trans_exp' f' dim e2 avs' with 
                        | (e2',f'',avs'') => (e1' >> e2', f'', avs'') end
                  end
    end.

(* In the final result, we can throw away the vars and avs *)
Definition trans_exp f dim exp avs := fst (fst (trans_exp' f dim exp avs)).

(* z = x + y (TOFF-based) *)
Definition trans_cl_adder (size:nat) :=
  trans_exp (CLArith.vars_for_adder01 size) (2 * size + 1) (CLArith.adder01_out size) (OQASMProof.avs_for_arith size).

(* z = M * x (TOFF-based) *)
Definition trans_cl_const_mul (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_nat_m size) (2 * size + 1) (CLArith.cl_nat_mult_out size (nat2fb M)) (OQASMProof.avs_for_arith size).

(* z = x * y (TOFF-based) *)
Definition trans_cl_mul (size:nat) :=
  trans_exp (CLArith.vars_for_cl_nat_full_m size) (3 * size + 1) (CLArith.cl_full_mult_out size) (OQASMProof.avs_for_arith size).

(* z = x * y (TOFF-based, Quipper inspired) *)
Definition trans_cl_mul_out_place (size:nat) :=
  trans_exp (CLArith.vars_for_cl_nat_full_out_place_m size)
           (4 * size + 1) (CLArith.cl_full_mult_out_place_out size) (OQASMProof.avs_for_arith size).

(* z = M + x (QFT-based) *)
Definition trans_rz_const_adder (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_adder size) size (RZArith.rz_adder_out size (nat2fb M)) (OQASMProof.avs_for_arith size).

(* z = x + y (QFT-based) *)
Definition trans_rz_adder (size:nat) :=
  trans_exp (RZArith.vars_for_rz_full_add size) (2 * size) (RZArith.rz_full_adder_out size) (OQASMProof.avs_for_arith size).

(* z = M * x (QFT-based) *)
Definition trans_rz_const_mul (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_nat_m size) (2 * size) (RZArith.nat_mult_out size (nat2fb M)) (OQASMProof.avs_for_arith size).

(* z = x * y (QFT-based) *)
Definition trans_rz_mul (size:nat) :=
  trans_exp (RZArith.vars_for_rz_nat_full_m size) (3 * size) (RZArith.nat_full_mult_out size) (OQASMProof.avs_for_arith size). 

(* z = x mod y,x/y (TOFF-based) *)
Definition trans_cl_div_mod (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_div_mod size) (3 * size + 1) (CLArith.cl_div_mod_out size M) (OQASMProof.avs_for_arith size). 

(* z = x mod y, x / y (QFT-based) *)
Definition trans_rz_div_mod (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_div_mod size) (2 * (S size)) (RZArith.rz_div_mod_out size M) (RZArith.avs_for_rz_div_mod size). 

(* approx moder, where shifting is using OQASM shift. *)
Definition trans_rz_div_mod_app_shift (size M:nat) :=
  trans_exp (RZArith.vars_for_app_div_mod size) (2 * (S size))
        (RZArith.app_div_mod_out size M) (RZArith.avs_for_app_div_mod size). 

(* approx moder, where shifting is using SQIR SWAPs. *)
Definition trans_rz_div_mod_app_swaps (size M:nat) :=
  trans_exp (RZArith.vars_for_app_div_mod size) (2 * (S size))
        (RZArith.app_div_mod_aout size M) (RZArith.avs_for_app_div_mod size). 

(* approx circuits. b is a number <= size for the precision. *)
Definition trans_appx_adder (size:nat) (b:nat) :=
  trans_exp (RZArith.vars_for_rz_full_add size) 
   (2 * size) (RZArith.appx_full_adder_out size b) (OQASMProof.avs_for_arith size).
Definition trans_appx_const_adder (size:nat) (b:nat) (M:nat) :=
  trans_exp (RZArith.vars_for_rz_adder size) 
   (2 * size) (RZArith.appx_adder_out size b (nat2fb M)) (OQASMProof.avs_for_arith size).
Definition trans_appx_const_sub (size:nat) (b:nat) (M:nat):=
  trans_exp (RZArith.vars_for_rz_adder size) 
   (2 * size) (RZArith.appx_sub_out size b (nat2fb M)) (OQASMProof.avs_for_arith size).

(* Modular multipliers *)
Definition trans_rz_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev M C Cinv size) (avs_for_arith size).
Definition trans_rz_modmult_rev_alt (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev_alt M C Cinv size) (avs_for_arith size).
Definition trans_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_cl (S (size))) (4*(S (size))+1)
              (real_modmult_rev M C Cinv (S (size))) (avs_for_arith (S (size))).

(* OQIMP examples *)
Definition trans_dmc_qft (size:nat) :=
   match compile_dm_qft size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (2*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmc_cl (size:nat) :=
   match compile_dm_classic size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (2*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmq_qft (size:nat) :=
   match compile_dmq_qft size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (6*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmq_cl (size:nat) :=
   match compile_dmq_classic size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (6*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Compute trans_dmq_cl 2.

Definition compile_chacha_sqir (_:unit) := (* arg. delays evaluation in extracted code *)
    match compile_chacha ()
          with None => None
             | Some (Error) => None
             | Some (Value a) => match a with (None,b,c,d) => None
                        | (Some e,sn,c,d) => 
                    Some (trans_exp (OracleExample.vars_for_chacha sn)
                 (32*18 + (S (S sn)))%nat e avs_for_chacha)
                                 end
    end.


(** Proof that these new definitions match the ones in OQASM **)

Lemma gen_sr_gate_same : forall dim f x n, 
   to_base_ucom dim (gen_sr_gate f x n) = OQASMProof.gen_sr_gate f dim x n.
Proof.
  intros dim f x n.
  unfold gen_sr_gate, OQASMProof.gen_sr_gate.
  assert (forall a b, 
          to_base_ucom dim (gen_sr_gate' f x a b) 
            = OQASMProof.gen_sr_gate' f dim x a b).
  { intros. induction a. reflexivity.
    simpl. rewrite IHa. reflexivity. }
  apply H.
Qed.

Lemma gen_srr_gate_same : forall dim f x n,
  to_base_ucom dim (gen_srr_gate f x n) = OQASMProof.gen_srr_gate f dim x n.
Proof.
  intros dim f x n.
  unfold gen_srr_gate, OQASMProof.gen_srr_gate.
  assert (forall a b, 
          to_base_ucom dim (gen_srr_gate' f x a b) 
            = OQASMProof.gen_srr_gate' f dim x a b).
  { intros. induction a. reflexivity.
    simpl. rewrite IHa. reflexivity. }
  apply H.
Qed.

Lemma controlled_rotations_gen_same : forall dim f x n i, 
  to_base_ucom dim (controlled_rotations_gen f x n i)
    = OQASMProof.controlled_rotations_gen f dim x n i.
Proof.
  intros.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  simpl in *.
  rewrite IHn.
  reflexivity.
Qed.

Lemma controlled_rotations_WF : forall f x n i,
  well_formed (controlled_rotations_gen f x n i).
Proof.
  intros.
  destruct n.
  simpl. constructor. auto.
  induction n.
  simpl. constructor. auto.
  remember (S n) as m.
  simpl.
  destruct m.
  lia.
  constructor.
  apply IHn.
  apply control'_WF.
  constructor. auto.
Qed.

Lemma QFT_gen_same : forall dim f x n size, 
  to_base_ucom dim (QFT_gen f x n size) = OQASMProof.QFT_gen f dim x n size.
Proof.
  intros.
  induction n; try reflexivity.
  simpl.
  rewrite IHn.
  rewrite <- controlled_rotations_gen_same.
  reflexivity.
Qed.

Lemma QFT_gen_WF : forall f x n size, well_formed (QFT_gen f x n size).
Proof.
  intros.
  induction n; simpl. 
  constructor. auto.
  repeat constructor. 
  apply IHn.
  apply controlled_rotations_WF.
Qed.

Lemma nH_WF : forall f x n b, well_formed (nH f x n b).
Proof.
  intros.
  induction n; simpl. 
  constructor. auto.
  repeat constructor. 
  apply IHn.
Qed.

Lemma trans_h_same : forall dim f x n b,
  to_base_ucom dim (nH f x n b) = OQASMProof.nH f dim x n b.
Proof.
   intros. induction n. reflexivity.
    simpl. rewrite IHn. reflexivity. 
Qed.

Lemma trans_qft_same : forall dim f x b,
  to_base_ucom dim (trans_qft f x b) = OQASMProof.trans_qft f dim x b.
Proof.
   intros.
   unfold trans_qft, OQASMProof.trans_qft. simpl.
   rewrite QFT_gen_same.
   rewrite trans_h_same. reflexivity. 
Qed.

Lemma trans_rqft_same : forall dim f x b,
  uc_eval dim (trans_rqft f x b) = UnitarySem.uc_eval (OQASMProof.trans_rqft f dim x b).
Proof. 
  intros. 
  unfold trans_rqft, OQASMProof.trans_rqft.
  unfold uc_eval.
  rewrite <- QFT_gen_same.
  rewrite <- trans_h_same.
  apply invert_same.
  constructor.
  apply QFT_gen_WF.
  apply nH_WF.
Qed.

Lemma gen_sr_gate'_WF : forall f x n size, well_formed (gen_sr_gate' f x n size).
Proof.
  intros. induction n; simpl. 
  constructor. reflexivity. 
  constructor. auto. constructor. reflexivity.
Qed.

Lemma gen_srr_gate'_WF : forall f x n size, well_formed (gen_srr_gate' f x n size).
Proof.
  intros. induction n; simpl. 
  constructor. reflexivity. 
  constructor. auto. constructor. reflexivity.
Qed.

Lemma trans_qft_WF : forall f x b, well_formed (trans_qft f x b).
Proof. intros. constructor. apply QFT_gen_WF. apply nH_WF. Qed.

Lemma trans_rqft_WF : forall f x b, well_formed (trans_rqft f x b).
Proof. intros. apply invert_WF. Search invert. constructor. apply QFT_gen_WF. apply nH_WF. Qed.

Lemma transexp'_WF : forall f dim exp avs u v p1,
  trans_exp' f dim exp avs = (u, v, p1) -> well_formed u.
Proof.
  intros.
  gen dim f avs.
  gen u v p1.
  induction exp; intros u v p1 dim f avs H.
  (* simple cases *)
  all: try (inversion H; subst; constructor; reflexivity).
  all: simpl in H; try inversion H; subst.
  (* CU p exp *)
  destruct (trans_exp' f dim exp avs) eqn:transexp.
  destruct p0.
  eapply IHexp in transexp.
  inversion H; subst.
  apply control'_WF. assumption.
  (* SR q x *)
  apply gen_sr_gate'_WF.
  (* SRR q x *)
  apply gen_srr_gate'_WF.
  (* QFT x *)
  apply trans_qft_WF.
  (* RQFT x *)
  apply trans_rqft_WF.
  (* exp1 ; exp2 *)
  destruct (trans_exp' f dim exp1 avs) eqn:transexp1.
  destruct p.
  destruct (trans_exp' v0 dim exp2 p0) eqn:transexp2.
  destruct p.
  inversion H; subst.
  constructor.
  eapply IHexp1. apply transexp1.
  eapply IHexp2. apply transexp2.
Qed.

Lemma vs_same_trans: forall e f dim avs, 
            snd (fst (trans_exp' f dim e avs)) = snd (fst (OQASMProof.trans_exp f dim e avs))
          /\ snd ( (trans_exp' f dim e avs)) = snd ( (OQASMProof.trans_exp f dim e avs)).
Proof.
  induction e; intros; simpl in *; eauto.
  destruct (trans_exp' f dim e avs) eqn:eq1.
  destruct p0. simpl in *.
  destruct (OQASMProof.trans_exp f dim e avs ) eqn:eq2.
  destruct p0. simpl in *. easy.
  specialize (IHe1 f dim avs).
  destruct (trans_exp' f dim e1 avs) eqn:eq1. destruct p.
  destruct (OQASMProof.trans_exp f dim e1 avs) eqn:eq3.
  destruct p.
  simpl in *. destruct IHe1. subst.
  specialize (IHe2 v0 dim p1).
  destruct (trans_exp' v0 dim e2 p1) eqn:eq2. destruct p.
  destruct (OQASMProof.trans_exp v0 dim e2 p1) eqn:eq4.
  destruct p.
  simpl in *. easy.
Qed.

Lemma is_fresh_to_base_ucom_invert :
     forall q dim u,
           UnitaryOps.is_fresh q (to_base_ucom dim (invert u)) 
                 <-> UnitaryOps.is_fresh q (to_base_ucom dim u).
Proof.
  intros. induction u.
  simpl.
  split. intros. inv H. constructor. rewrite <- IHu1. easy.
  rewrite <- IHu2. easy.
  intros. inv H. constructor. rewrite IHu2. easy.
  rewrite IHu1. easy.
  destruct u. simpl. destruct l. simpl. easy.
  destruct l. simpl. easy. simpl. easy.
  destruct l. simpl. easy.
  simpl.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  simpl.
  destruct l. simpl.
  split. intros. constructor. inv H. easy.
  intros. constructor. inv H. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl.
  split. intros. constructor. inv H. easy.
  intros. constructor. inv H. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  easy.
  destruct l. simpl. easy.
  destruct l. simpl. 
  split. intros. constructor. inv H. easy.
  intros. constructor. inv H. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. 
  split. intros.
  inv H. inv H3. inv H2. inv H3.
  inv H4. inv H6. inv H2.
  Local Transparent SQIR.Rz.
  unfold SQIR.Rz in *.
  inv H6. inv H8.
  constructor. constructor.
  constructor. constructor.
  constructor. constructor. easy.
  constructor. easy. easy.
  constructor. easy. easy.
  constructor. easy.
  intros.
  inv H. inv H3. inv H2. inv H3.
  inv H4. inv H6. inv H2.
  unfold SQIR.Rz in *.
  inv H6. inv H8.
  constructor. constructor.
  constructor. constructor.
  constructor. constructor. easy.
  constructor. easy. easy.
  constructor. easy. easy.
  constructor. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl.
  split. intros.
  inv H. inv H3. 
  inv H2. inv H3.
  inv H2. inv H4.
  inv H6. inv H3. inv H8.
  inv H2. inv H9. inv H4. inv H10. inv H6.
  inv H11. inv H3. inv H12. inv H8. inv H9.
  inv H10. inv H11. inv H12. inv H17. inv H8.
  inv H18. inv H9. inv H19. inv H10. inv H20.
  inv H11. inv H17. inv H18. inv H19. inv H20.
  inv H25. inv H12. inv H26. inv H17. inv H27. inv H18. inv H28.
  Local Transparent SQIR.CNOT.
  inv H15. inv H13.
  constructor. constructor. constructor. constructor. constructor.
  constructor. constructor. constructor. constructor. constructor.
  constructor. easy. constructor. easy. easy. constructor. easy.
  easy. constructor. easy. constructor.
  constructor. constructor. constructor. constructor.
  constructor. easy. constructor. easy.
  easy. constructor. easy. easy.
  constructor. easy. constructor. constructor.
  repeat constructor.
  Local Transparent SQIR.H SQIR.T.
  constructor. easy. 1-18:easy.
  constructor. easy. constructor;easy.
  repeat constructor; try easy.
  constructor.
  repeat constructor; try easy.
  constructor;easy.
  repeat constructor; try easy.
  intros.
  inv H. inv H3. 
  inv H2. inv H3.
  inv H2. inv H4.
  inv H6. inv H3. inv H8.
  inv H2. inv H9. inv H4. inv H10. inv H6.
  inv H11. inv H3. inv H12. inv H8. inv H9.
  inv H10. inv H11. inv H12. inv H17. inv H8.
  inv H18. inv H9. inv H19. inv H10. inv H20.
  inv H11. inv H17. inv H18. inv H19. inv H20.
  inv H25. inv H12. inv H26. inv H17. inv H27. inv H18. inv H28.
  repeat constructor; try easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  destruct l. simpl. easy.
  simpl. easy.
  Local Opaque SQIR.Rz SQIR.CNOT SQIR.H SQIR.T.
Qed.

Lemma transexp'_is_fresh : forall f dim exp avs u v p1 q,
  (* likely requires additional preconditions... *)
  trans_exp' f dim exp avs = (u, v, p1) ->
  (UnitaryOps.is_fresh q (to_base_ucom dim u) <->
   UnitaryOps.is_fresh q (fst (fst (OQASMProof.trans_exp f dim exp avs)))).
Proof.
  intros.
gen dim f avs.
  gen u v p1.
  induction exp; intros u v p1 dim f avs H; simpl in *.

all: try inversion H; subst; try reflexivity.

  (* CU p exp *)

destruct (trans_exp' f dim exp avs) eqn:transexp'.
    destruct p0.
    destruct (OQASMProof.trans_exp f dim exp avs) eqn:transexp.
    apply transexp'_WF in transexp' as eq1.
    destruct p0.
    apply IHexp in transexp'.
    inversion H; subst.
    rewrite transexp in transexp'.
    simpl in *.
    rewrite <- UnitaryOps.fresh_control.
    split.
    intros.
    apply fresh_control' in H0.
    split. destruct H0. easy. destruct H0. apply transexp'. easy.
    lia. easy. 
    intros. destruct H0.
    apply fresh_control'; try easy. lia.
    split. easy. apply transexp'; easy.
    (* SR q x *)
    rewrite gen_sr_gate_same. easy.
    (* SRR q x *)
    rewrite gen_srr_gate_same. easy.
    (* QFT x *)
    rewrite trans_qft_same. easy.
    (* RQFT x *)
    split. intros.
    assert (OQASMProof.trans_rqft v dim x b
       = UnitaryOps.invert (OQASMProof.trans_qft v dim x b)) by easy.
    rewrite H1.
    rewrite <- is_fresh_invert.
    rewrite <- trans_qft_same.
    assert (to_base_ucom dim (trans_rqft v x b) 
       = to_base_ucom dim (invert (trans_qft v x b))) by easy.
    rewrite H2 in H0.
    rewrite is_fresh_to_base_ucom_invert in H0. easy.
    intros.
    assert (OQASMProof.trans_rqft v dim x b
       = UnitaryOps.invert (OQASMProof.trans_qft v dim x b)) by easy.
    rewrite H1 in *.
    assert (to_base_ucom dim (trans_rqft v x b) 
       = to_base_ucom dim (invert (trans_qft v x b))) by easy.
    rewrite H2.
    rewrite <- is_fresh_invert in H0.
    apply is_fresh_to_base_ucom_invert.
    rewrite trans_qft_same. easy.
    (* exp1 ; exp2 *)
    specialize (vs_same_trans exp1 f dim avs) as X1. destruct X1.
    destruct (trans_exp' f dim exp1 avs) eqn:transexp1.
    destruct p.
    destruct (OQASMProof.trans_exp f dim exp1 avs) eqn:transexp2.
    destruct p.
    apply IHexp1 in transexp1 as eq1.
    simpl in *. subst.
    specialize (vs_same_trans exp2 v1 dim p2) as X1. destruct X1.
    destruct (trans_exp' v1 dim exp2 p2) eqn:transexp3.
    destruct p.
    destruct (OQASMProof.trans_exp v1 dim exp2 p2) eqn:transexp4.
    destruct p.
    eapply IHexp2 in transexp3 as eq2.
    simpl in *. subst.
    inversion H; subst.
    rewrite transexp2 in *.
    rewrite transexp4 in *. simpl in *.
    split. intros. inv H0. constructor.
    apply eq1. easy.
    apply eq2. easy.
    intros. inv H0.
    constructor. apply eq1. easy.
    apply eq2 ; easy.
Qed.

Lemma trans_exp_same : forall f dim exp avs,
  uc_eval dim (trans_exp f dim exp avs) 
    = UnitarySem.uc_eval (fst (fst (OQASMProof.trans_exp f dim exp avs))).
Proof.
  intros.
  unfold trans_exp.
  assert (forall u1 u2 f1 f2 avs1 avs2,
          trans_exp' f dim exp avs = (u1, f1, avs1) ->
          OQASMProof.trans_exp f dim exp avs = (u2, f2, avs2) ->
          uc_eval dim u1 =  UnitarySem.uc_eval u2 /\ f1 = f2 /\ avs1 = avs2).
  { generalize dependent avs.
    generalize dependent dim.
    generalize dependent f.
    induction exp; intros f dim avs u1 u2 f1 f2 avs1 avs2 H1 H2.
    
    (* simple cases *)
    all: try (inversion H1; inversion H2; subst;
              repeat split; reflexivity). 
    
    (* CU p exp *)
    simpl in H1, H2.
    destruct (trans_exp' f dim exp avs) eqn:transexp'.
    destruct p0.
    destruct (OQASMProof.trans_exp f dim exp avs) eqn:transexp.
    destruct p0.
    assert (IH:=transexp').
    eapply IHexp in IH as [? [? ?]].
    2: apply transexp.
    inversion H1; inversion H2; subst.
    repeat split; auto.
    rewrite control_correct.
    apply UnitaryOps.control_cong.
    apply H.
    rewrite transexp'_is_fresh.
    rewrite transexp. reflexivity.
    apply transexp'.
    eapply transexp'_WF. apply transexp'.

    (* SR q x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite gen_sr_gate_same.
    auto.

    (* SRR q x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite gen_srr_gate_same.
    auto.

    (* QFT x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite trans_qft_same.
    auto.

    (* RQFT x *)
    simpl in H1, H2.
    inversion H1; inversion H2; subst.
    rewrite trans_rqft_same.
    auto.

    (* exp1 ; exp2 *)
    simpl in H1, H2.
    destruct (trans_exp' f dim exp1 avs) eqn:transexp1.
    destruct p.
    destruct (OQASMProof.trans_exp f dim exp1 avs) eqn:transexp2.
    destruct p.
    eapply IHexp1 in transexp1 as [? [? ?]].
    2: apply transexp2.
    subst.
    destruct (trans_exp' v0 dim exp2 p1) eqn:transexp3.
    destruct p.
    destruct (OQASMProof.trans_exp v0 dim exp2 p1) eqn:transexp4.
    destruct p.
    eapply IHexp2 in transexp3 as [? [? ?]].
    2: apply transexp4.
    inversion H1; inversion H2; subst.
    repeat split; try reflexivity.
    unfold uc_eval in *.
    simpl.
    rewrite H, H0.
    reflexivity. }
  destruct (trans_exp' f dim exp avs) eqn:transexp1.
  destruct p.
  destruct (OQASMProof.trans_exp f dim exp avs) eqn:transexp2.
  destruct p.
  eapply H.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.
