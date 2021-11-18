Require Import Arith NArith Vector Bvector Equality MSets OrderedTypeEx Lia BasicUtility VectorStates Utilities.
Require Import PQASM MathSpec.
From QuickChick Require Import QuickChick.
Import Vector (hd, tl).
Import Decidability (dec).
Import PQASM (exp(..), CNOT).

Require FMapAVL.
Module Posi_as_OT := PairOrderedType Nat_as_OT Nat_as_OT.
Module M := FMapAVL.Make(Posi_as_OT).

Module Nat_as_OT := Update_OT Nat_as_OT.
(* Used for finite sets of variables *)
Module VarSet := Make Nat_as_OT.
Import VarSet.

Open Scope vector_scope.
Open Scope string_scope.
Open Scope positive_scope.
Open Scope N_scope.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope exp_scope.

Definition rz_val := nat.

Inductive val := nval (b:bool) (r:rz_val) | hval (b1:bool) (b2:bool) (r:rz_val) | qval (rc:rz_val) (r:rz_val).

Definition addto (r : rz_val) (n : nat) (rmax : nat) : rz_val :=
  (r + 2^(rmax - n)) mod 2^rmax.

Definition addto_n (r : rz_val) n (rmax : nat) :=
  (r + 2^rmax - 2^(rmax - n)) mod 2^rmax.

Definition state := M.t val.

Definition get_state (p : posi) (f : state) :=
  match M.find p f with
  | None => nval false 0
  | Some v => v
  end.

Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
                  | a => a
     end.

Definition hexchange (v1:val) (v2:val) :=
  match v1 with hval b1 b2 r1 => 
    match v2 with hval b3 b4 r2 => if Bool.eqb b3 b4 then v1 else hval b1 (¬ b2) r1
                | _ => v1
    end
             | _ => v1
  end.

Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | _ => false end.

Definition get_cus (n:nat) (f:state) (x:var) := 
          fun i => if i <? n then (match get_state (x,i) f with nval b r => b | _ => false end) else allfalse i.

Definition put_cus (f:posi -> val) (x:var) (g:nat -> bool) (n:nat) : (posi -> val) :=
     fun a => if fst a =? x then if snd a <? n then put_cu (f a) (g (snd a)) else f a else f a.

Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | hval b1 b2 r => Some b1
                 | _ => None
    end.

Definition get_r (v:val) :=
   match v with nval x r => r
              | qval rc r => rc
              | hval x y r => r
   end.

Definition rotate (r :rz_val) (q:nat) rmax := addto r q rmax.

Definition times_rotate (v : val) (q:nat) rmax := 
     match v with nval b r => if b then nval b (rotate r q rmax) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (rotate r q rmax)
     end.

Definition r_rotate (r :rz_val) (q:nat) rmax := addto_n r q rmax.

Definition times_r_rotate (v : val) (q:nat) rmax := 
     match v with nval b r =>  if b then nval b (r_rotate r q rmax) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (r_rotate r q rmax)
     end.

Fixpoint sr_rotate' (st: state) (x:var) (n:nat) (size:nat) rmax :=
   match n with 0 => st
              | S m => (sr_rotate' (M.add (x,m) (times_rotate (get_state (x,m) st) (size - m) rmax) st) x m size rmax)
   end.
Definition sr_rotate st x n rmax := sr_rotate' st x (S n) (S n) rmax.

Fixpoint srr_rotate' (st: state) (x:var) (n:nat) (size:nat) rmax :=
   match n with 0 => st
              | S m =>  (srr_rotate' (M.add (x,m) (times_r_rotate (get_state (x,m) st) (size - m) rmax) st) x m size rmax)
   end.
Definition srr_rotate st x n rmax := srr_rotate' st x (S n) (S n) rmax.

Fixpoint lshift' (n:nat) (size:nat) (f:state) (x:var) := 
   match n with 0 => M.add (x,0) (get_state (x,size) f) f
             | S m => M.add (x,n) (get_state (x,m) f) (lshift' m size f x)
   end.
Definition lshift (f:state) (x:var) (n:nat) := lshift' (n-1) (n-1) f x.

Fixpoint rshift' (n:nat) (size:nat) (f:state) (x:var) := 
   match n with 0 => M.add (x,size) (get_state (x,0) f) f
             | S m => M.add (x,m) (get_state (x,n) f) (rshift' m size f x)
   end.
Definition rshift (f:state) (x:var) (n:nat) := rshift' (n-1) (n-1) f x.

Fixpoint reverse' (f : state) (x : var) (n : nat) i (f' : state) :=
  match i with
  | 0 => f'
  | S i' =>
      reverse' f x n i' (M.add (x, i') (get_state (x, n - i) f) f')
  end.

Definition reverse (f:state) (x:var) (n:nat) :=
  reverse' f x n n f.

Definition h_case (v : val) (rmax : nat) :=
    match v with nval b r => if r <? 2^(rmax-1) then hval true (¬ b) r else hval false b (rotate r 1 rmax)
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1 rmax)
               | hval false false r => nval false (rotate r 1 rmax)
               | a => a
    end.

Fixpoint h_sem (f:state) (x:var) (n : nat) (rmax : nat) := 
    match n with 0 => f
              | S m => M.add (x,m) (h_case (get_state (x,m) f) rmax) (h_sem f x m rmax)
    end.

Definition up_qft (v:val) (f:rz_val) :=
   match v with nval b r => qval r f
              | a => a
   end.

Fixpoint a_nat2fb' f (n acc: nat) :=
            match n with 0 => acc
               | S m => a_nat2fb' f m (acc + Nat.b2n (f m) * 2^m)
            end.
Definition a_nat2fb f n := a_nat2fb' f n 0.

Fixpoint assign_r (f:state) (x:var) (r : nat) (n:nat) (size :nat) (rmax:nat) :=
    match n with 0 => f
    | S m =>  (assign_r (M.add (x,size - n) (up_qft (get_state (x,size - n) f) r) f) x ((r * 2) mod 2^rmax) m size rmax)
    end.

Definition turn_qft (f:state) (x:var) (n:nat) (rmax:nat) :=
      assign_r f x (2^(rmax - n) * a_nat2fb (fbrev n (get_cus n f x)) n) n rmax rmax.

Fixpoint assign_seq (f:state) (x:var) (vals : nat -> bool) (size:nat) (n:nat) :=
   match n with 0 => f
   | S m => (assign_seq (M.add (x,size-n) (nval (vals (size-n)) (get_r (get_state (x,size-n) f))) f) x vals size m)
   end.

Definition get_r_qft (f:state) (x:var) (n:nat) (rmax:nat) :=
      match get_state (x,0) f with qval rc g => fbrev n (nat2fb (g/2^(rmax-n)))
                      | _ => allfalse
      end.

Definition turn_rqft (st : state) (x:var) (n:nat) (rmax : nat) := assign_seq st x (get_r_qft st x n rmax) rmax rmax.

Fixpoint exp_sem (env:var -> nat) (rmax : nat) (e:exp) (st: state) : state :=
   match e with (SKIP p) => st
              | X p => M.add p (exchange (get_state p st)) st
              | HCNOT p1 p2 => M.add p1 (hexchange (get_state p1 st) (get_state p2 st)) st
              | CU p e' => if get_cua (get_state p st) then exp_sem env rmax e' st else st
              | RZ q p => M.add p (times_rotate (get_state p st) q rmax) st
              | RRZ q p => M.add p (times_r_rotate (get_state p st) q rmax) st
              | SR n x => sr_rotate st x n rmax (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n rmax
              | Lshift x => lshift st x (env x)
              | Rshift x => rshift st x (env x)
              | Rev x => (reverse st x (env x))
              | H x => h_sem st x (env x) rmax
              | QFT x => turn_qft st x (env x) rmax
              | RQFT x => turn_rqft st x (env x) rmax
              | e1 ; e2 => exp_sem env rmax e2 (exp_sem env rmax e1 st)
    end.

(* Bitwise xor *)
Infix "(+)" := (BVxor _) (at level 50, left associativity).

Definition show_bit b :=
  match b with
  | false => "0"
  | true => "1"
  end.

(* Order is reversed because Bvectors are little-endian *)
Fixpoint show_bvector' {n} : Bvector n -> string :=
  match n with
  | 0 => fun _ => ""
  | S n' => fun v => show_bvector' (tl v) ++ show_bit (hd v)
  end.

Instance show_bvector n : Show (Bvector n) := {| show := show_bvector' |}.

(* Lists Bvectors with one "1" flipped to "0" *)
Fixpoint shrink_bvector' {n} : Bvector n -> list (Bvector n) :=
  match n with
  | 0 => fun _ => nil
  | S n' =>
      fun v =>
      let tail := tl v in
      let shrink_tl := shrink_bvector' tail in 
      if hd v
        then cons (false :: tail) (map (Bcons true _) shrink_tl)
        else map (Bcons false _) shrink_tl
  end.

Instance shrink_bvector n : Shrink (Bvector n) :=
  {| shrink := shrink_bvector' |}.

(* Uniformly randomly selected boolean *)
Definition gen_bool : G bool := elems_ false (false :: true :: nil).

(* Uniformly randomly selected Bvector *)
Fixpoint gen_bvector' {n} : G (Bvector n) :=
  match n with
  | 0 => ret Bnil
  | S n' =>
      bind gen_bool (fun b => bind gen_bvector' (fun v => ret (b :: v)))
  end.

Instance gen_bvector n : Gen (Bvector n) := {| arbitrary := gen_bvector' |}.

(* The natural number represented in binary in the sequence of bits *)
Fixpoint bvector2n {n} : Bvector n -> N :=
  match n with
  | 0 => fun _ => N0
  | S n' =>
      fun v =>
      let tl_n := bvector2n (tl v) in
      if hd v
      then N.succ_double tl_n
      else N.double tl_n
  end.

(* Represents the natural number in binary, trucating if necessary *)
Fixpoint n2bvector n : N -> Bvector n :=
  match n with
  | 0 => fun _ => Bnil
  | S n' => fun i => N.odd i :: n2bvector n' (N.div2 i)
  end.

Definition add_bvector {n} (v v' : Bvector n) :=
  n2bvector n (bvector2n v + bvector2n v')%N.

Lemma bvector2n2bvector :
  forall n v, n2bvector n (bvector2n v) = v.
Proof.
  intros n.
  induction n as [| n IH]; intros v; dependent destruction v; try reflexivity.
  cbn - [ N.mul N.div ].
  assert
    (forall h h' (t t' : Bvector n), h = h' -> t = t' -> h :: t = h' :: t').
  { intros. subst. reflexivity. }
  apply H; destruct h; auto using Ndouble_plus_one_bit0, Ndouble_bit0.
  - rewrite N.div2_succ_double. apply IH.
  - rewrite N.div2_double. apply IH.
Qed.

Definition bvector2nat {n} (v : Bvector n) := N.to_nat (bvector2n v).

Lemma double_size :
  forall n, N.size_nat (N.double n) <= S (N.size_nat n).
Proof.
  intros [].
  - simpl. lia.
  - reflexivity.
Qed.

Lemma succ_double_size :
  forall n, N.size_nat (N.succ_double n) = S (N.size_nat n).
Proof. intros []; reflexivity. Qed.

Lemma size_bvector2n :
  forall n (v : Bvector n), N.size_nat (bvector2n v) <= n.
Proof.
  intros n. induction n as [| n IH]; intros v; simpl. try constructor.
  dependent destruction v. simpl. destruct h.
  - rewrite succ_double_size. auto using le_n_S.
  - eauto using le_trans, double_size, le_n_S.
Qed.

Lemma n2bvector2n :
  forall n i, N.size_nat i <= n -> bvector2n (n2bvector n i) = i.
Proof.
  intros n. induction n as [| n IH]; try (intros [|[]]; simpl; lia).
  intros [|[]] H; simpl; rewrite IH; simpl in *; try lia.
Qed.

(* A single-qubit state representing either |0> or |1> *)
Definition basis_val b := nval b 0.

(* The single-qubit state |0> *)
Definition zero_val := basis_val false.

(* A program state with all qubits set to |0>, used for initialization *)
Definition zero_state : state := M.empty val.

Notation "x |-> vx , st" :=
    (M.add x vx st) (at level 100, vx at next level, right associativity).
Notation "x |-> vx" := (M.add x vx zero_state) (at level 100).

Definition next_pos : posi -> posi := fun '(x, i) => (x, S i).

Fixpoint update_var' {n} (st : state) (x : posi) : Bvector n -> state :=
  match n with
  | 0 => fun _ => st
  | S n' =>
      fun vx => (x |-> basis_val (hd vx), update_var' st (next_pos x) (tl vx))
  end.

Definition update_var {n} st x : Bvector n -> state := update_var' st (x, 0).

Notation "x |=> vx , st" :=
    (update_var st x vx) (at level 100, vx at next level, right associativity).

Infix "|=>" := (update_var zero_state) (at level 100).

(* A finite set of variables (nats) *)
Definition var_set := VarSet.t.

(* Converts a decidable Prop to a boolean representing the decision *)
Definition dec2bool P `{H : Dec P} : bool :=
  let '{| dec := d |} := H in
  if d then true else false.

Lemma dec2bool_correct :
  forall P `{Dec P}, P <-> dec2bool P = true.
Proof.
  intros P H. destruct H as [[|]] eqn:E; simpl; split; auto.
  discriminate.
Qed.

(* A For_all Prop is decidable if the sub-Prop is decidable for all variables *)
Instance dec_var_set_for_all {P : var -> Prop} `{forall x, Dec (P x)} :
  forall vars, Dec (For_all P vars).
Proof.
  intros vars. constructor.
  replace P with (fun x => P x) by reflexivity.
  destruct (for_all (fun x => dec2bool (P x)) vars) eqn:E.
  - left. intros x Hi. rewrite for_all_spec in E.
    + specialize (E x Hi). simpl in E. apply dec2bool_correct in E. assumption.
    + intros y y' Hy. subst. reflexivity.
  - right. intros Hc. rewrite <- not_true_iff_false in E. apply E.
    apply for_all_spec.
    + intros y y' Hy. subst. reflexivity.
    + intros x Hx. apply dec2bool_correct. apply Hc. assumption.
Defined.

(* An environment mapping variables to their sizes *)
Definition f_env := var -> nat.

(* A Prop is true for every position in an environment *)
Definition for_all_env (P : posi -> Prop) (vars : var_set) (env : f_env) := 
  For_all (fun x => forall i, i < env x -> P (x, i)) vars.

Instance dec_val_eq :
  forall v v' : val, Dec (v = v').
Proof.
  intros v v'. constructor.
  destruct v as [b z | b0 b1 z | z0 z1 ], v' as [b' z' | b0' b1' z' | z0' z1'];
  try (right; intros H; inversion H; discriminate).
  - destruct (bool_dec b b'); try (right; intros H; inversion H; contradiction).
    subst. bdestruct (z =? z'); subst.
    + left. reflexivity.
    + right. congruence.
  - destruct (bool_dec b0 b0'), (bool_dec b1 b1');
    try (right; intros H; inversion H; contradiction).
    subst. bdestruct (z =? z'); subst.
    + left. reflexivity.
    + right. congruence.
  - bdestruct (z0 =? z0'); bdestruct (z1 =? z1'); subst;
    try (right; congruence).
    left. reflexivity.
Defined.
    
(* States are equivalent if all values in the environment are equivalent *)
Definition st_equiv vars env (st st' : state) :=
  for_all_env (fun x => (get_state x st) = (get_state x st')) vars env.

Fixpoint var_equivb (st st' : state) var n :=
  match n with
  | 0 => true
  | S n' =>
      if dec (P:=(get_state (var, n') st = get_state (var, n') st'))
      then var_equivb st st' var n'
      else false
  end.

Definition st_equivb vars env (st st' : state) :=
  for_all (fun x => var_equivb st st' x (env x)) vars.

(* Get the variables in an exp *)
Fixpoint get_vars e :=
  match e with
  | SKIP p => singleton (fst p)
  | X p => singleton (fst p)
  | CU p e' => add (fst p) (get_vars e')
  | RZ _ p => singleton (fst p)
  | RRZ _ p => singleton (fst p)
  | SR _ x => singleton x
  | SRR _ x => singleton x
  | HCNOT p1 p2 => add (fst p1) (singleton (fst p2))
  | Lshift x => singleton x
  | Rshift x => singleton x
  | Rev x => singleton x
  | QFT x => singleton x
  | RQFT x => singleton x
  | H x => singleton x
  | e1; e2 => union (get_vars e1) (get_vars e2)
  end.

(* Get the maximum precision in rotations of an exp *)
Fixpoint get_prec (env : f_env) e :=
  match e with
  | SKIP _ => 0
  | X _ => 0
  | CU _ e' => get_prec env e'
  | RZ n _ => n
  | RRZ n _ => n
  | SR n _ => n
  | SRR n _ => n
  | HCNOT _ _ => 0
  | Lshift _ => 0
  | Rshift _ => 0
  | Rev _ => 0
  | QFT x => env x
  | RQFT x => env x
  | H _ => 0
  | e1; e2 => max (get_prec env e1) (get_prec env e2)
  end.

Definition ospec m n := Bvector m -> Bvector n -> Prop.

Definition fun_adheres {m n} f (s : ospec m n) :=
  forall vx, s vx (f vx).

Definition ospec_fun {m n} f : ospec m n :=
  fun vx vy => f vx = vy.

Lemma ospec_fun_adheres :
  forall m n (f : Bvector m -> Bvector n), fun_adheres f (ospec_fun f).
Proof. congruence. Qed.

Definition ospec_bool {n} (s : Bvector n -> bool -> Prop) : ospec n 1 :=
  fun vx vy => s vx (hd vy).

Definition bool_fun_adheres {n} f (s : ospec n 1) :=
  forall vx, s vx (f vx :: Bnil).

Definition ospec_bool_fun {n} f : ospec n 1 :=
  ospec_bool (fun vx b => f vx = b).

Lemma ospec_bool_fun_adheres :
  forall n (f : Bvector n -> bool), bool_fun_adheres f (ospec_bool_fun f).
Proof.
  intros n f vx. unfold ospec_bool_fun, ospec_bool. reflexivity.
Qed.

Definition ospec_n m n (s : N -> N -> Prop) : ospec m n :=
  fun vx vy => s (bvector2n vx) (bvector2n vy).

Definition n_fun_adheres {m n} f (s : ospec m n) :=
  forall vx,
  let ny := f (bvector2n vx) in N.size_nat ny <= n /\ s vx (n2bvector n ny).

Definition ospec_n_fun m n f : ospec m n :=
  ospec_n m n (fun nx ny => f nx = ny).

Lemma ospec_n_fun_adheres :
  forall m n (f : N -> N),
  (forall nx, N.size_nat nx <= m -> N.size_nat (f nx) <= n) ->
  n_fun_adheres f (ospec_n_fun m n f).
Proof.
  intros m n f H vx. simpl. split.
  - auto using size_bvector2n.
  - unfold ospec_n_fun, ospec_n. rewrite n2bvector2n; auto using size_bvector2n.
Qed.

Definition ospec_n_bool n (s : N -> bool -> Prop) : ospec n 1 :=
  fun vx vy => s (bvector2n vx) (hd vy).

Definition ospec_n_bool_fun n f : ospec n 1 :=
  ospec_n_bool n (fun nx b => f nx = b).

Definition dec2checker P `{Dec P} := checker (dec2bool P).
