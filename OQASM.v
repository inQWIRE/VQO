Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* irrelavent vars. *)
Definition vars_neq (l:list var) := forall n m x y,
   nth_error l m = Some x ->  nth_error l n = Some y -> n <> m -> x <> y.


Inductive exp := SKIP (p:posi) | X (p:posi) | CU (p:posi) (e:exp)
        | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (p:posi) 
        | SR (q:nat) (x:var) (* a series of RZ gates for QFT mode from q down to b. *)
        | SRR (q:nat) (x:var) (* a series of RRZ gates for QFT mode from q down to b. *)
        (*| HCNOT (p1:posi) (p2:posi) *)
        | Lshift (x:var)
        | Rshift (x:var)
        | Rev (x:var)
        | QFT (x:var) (b:nat) (* H on x ; CR gates on everything within (size - b). *)
        | RQFT (x:var) (b:nat)
       (* | H (p:posi) *)
        | Seq (s1:exp) (s2:exp).

Inductive type := Had (b:nat) | Phi (b:nat) | Nor.

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.

Fixpoint exp_elim (p:exp) :=
  match p with
  | CU q p => match exp_elim p with
                 | SKIP a => SKIP a 
                 | p' => CU q p'
                 end
  | Seq p1 p2 => match exp_elim p1, exp_elim p2 with
                  | SKIP _, p2' => p2'
                  | p1', SKIP _ => p1'
                  | p1', p2' => Seq p1' p2'
                  end
  | _ => p
  end.

Definition Z (p:posi) := RZ 1 p.

Fixpoint inv_exp p :=
  match p with
  | SKIP a => SKIP a
  | X n => X n
  | CU n p => CU n (inv_exp p)
  | SR n x => SRR n x
  | SRR n x => SR n x
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | Rev x => Rev x
 (* | HCNOT p1 p2 => HCNOT p1 p2 *)
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  | QFT x b => RQFT x b
  | RQFT x b => QFT x b
  (*| H x => H x*)
  | Seq p1 p2 => inv_exp p2; inv_exp p1
   end.


Fixpoint GCCX' x n size :=
  match n with
  | O | S O => X (x,n - 1)
  | S m => CU (x,size-n) (GCCX' x m size)
  end.
Definition GCCX x n := GCCX' x n n.

Fixpoint nX x n := 
   match n with 0 => X (x,0)
            | S m => X (x,m); nX x m
   end.

(* Grover diffusion operator. *)
(*
Definition diff_half (x c:var) (n:nat) := H x ; H c ;  ((nX x n; X (c,0))). 

Definition diff_1 (x c :var) (n:nat) :=
  diff_half x c n ; ((GCCX x n)) ; (inv_exp (diff_half x c n)).
*)
(*The second implementation of grover's diffusion operator.
  The whole circuit is a little different, and the input for the diff_2 circuit is asssumed to in Had mode. *)
(*
Definition diff_2 (x c :var) (n:nat) :=
  H x ; ((GCCX x n)) ; H x.

Fixpoint is_all_true C n :=
  match n with 0 => true
           | S m => C m && is_all_true C m
  end.

Definition const_u (C :nat -> bool) (n:nat) c := if is_all_true C n then ((X (c,0))) else SKIP (c,0).

Fixpoint niter_prog n (c:var) (P : exp) : exp :=
  match n with
  | 0    => SKIP (c,0)
  | 1    => P
  | S n' => niter_prog n' c P ; P
  end.

Definition body (C:nat -> bool) (x c:var) (n:nat) := const_u C n c; diff_2 x c n.

Definition grover_e (i:nat) (C:nat -> bool) (x c:var) (n:nat) := 
        H x; H c ; ((Z (c,0))) ; niter_prog i c (body C x c n).
*)
(** Definition of Deutsch-Jozsa program. **)
(*
Definition deutsch_jozsa (x c:var) (n:nat) :=
  ((nX x n; X (c,0))) ; H x ; H c ; ((X (c,0))); H c ; H x.
*)

(* Example Circuits that are definable by OQASM. *)
(* find a number that is great-equal than 2^(n-1), assume that the number is less than 2^n *)
Fixpoint findnum' (size:nat) (x:nat) (y:nat) (i:nat) := 
       match size with 0 => i
              | S n => if y <=? x then i else findnum' n (2 * x) y (i+1)
       end.

Definition findnum (x:nat) (n:nat) := findnum' n x (2^(n-1)) 0.

(* Find the index i of a number 2^i that is x <= 2^i *)
Fixpoint findBig2n' (size:nat) (x:nat) (i:nat) :=
   match i with 0 => size
          | S m => if x <=? 2^(size-(S m)) then (size - (S m)) else findBig2n' size x m
   end.
Definition findBig2n (size:nat) (x:nat) := findBig2n' size x size.


(* Define a version of appox qft_adder with approx gates. b is the approx away number. 
   Meaning that we do not record qubits that is below b.
   Approx adder might not have a good accuracy.  *)
Fixpoint appx_full_adder' (x:var) (n:nat) (b:nat) (size:nat) (y:var) :=
  match n with
  | 0 => (SKIP (x,0))
  | S m => if b <=? m then ((CU (y,m) (SR (size - n - b) x)); appx_full_adder' x m b size y)
                      else (SKIP (x,m))
  end.
Definition appx_full_adder (x:var) (n:nat) (b:nat) (y:var) := appx_full_adder' x n b n y.

Definition rz_full_adder_form (x:var) (n:nat) (b:nat) (y:var) :=
   (Rev x; QFT x b) ; appx_full_adder x n b y ; 
  inv_exp (Rev x; QFT x b).

(* approximate x = (x % M, x / M)  circuit. *)
Definition QFTCNOT (x y : posi) := CU x (X y).
Definition div_two_spec (f:nat->bool) := fun i => f (i+1).

Fixpoint appx_adder' (x:var) (n:nat) (b:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => if b <=? m then (appx_adder' x m b size M ; 
            if M m then SR (size - n - b) x else SKIP (x,m)) else SKIP (x,m)
  end.
Definition appx_adder (x:var) (n:nat) (b:nat) (M:nat -> bool) := appx_adder' x n b n M.

Fixpoint appx_sub' (x:var) (n:nat) (b:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => if b <=? m then (appx_sub' x m b size M ;
            if M m then SRR (size - n - b) x else SKIP (x,m)) else SKIP (x,m)
  end.

Definition appx_sub (x:var) (n:nat) (b:nat) (M:nat -> bool) := appx_sub' x n b n M.

Definition appx_compare_half3 (x:var) (n:nat) (b:nat) (c:posi) (M:nat -> bool) := 
   (appx_sub x n b M) ; RQFT x b ; (QFTCNOT (x,0) c).

Fixpoint appx_moder' i (n:nat) (b:nat) (x ex:var) (M:nat -> bool) := 
     match i with 0 =>  (SKIP (x,0))
           | S j => appx_compare_half3 x n b (ex,j) M ;  Rshift x;
                     QFT x b; (CU (ex,j) ((appx_adder x n b M)));
                      (X (ex,j)); 
                       appx_moder' j n (b+1) x ex (cut_n (div_two_spec M) n)
     end.

Fixpoint nLshift x (n:nat) := match n with 0 => SKIP (x,0)
                         | S m => Lshift x ; nLshift x m
                     end.

Definition appx_div_mod (n:nat) (x ex:var) (M:nat) := 
    let i := findnum M (n-1) in 
         (Rev x); QFT x 0;
            appx_moder' (S i) n 0 x ex (nat2fb (2^i * M)); nLshift x (S i);
        inv_exp ( (Rev x); QFT x 0).


(* H; CR; ... Had(0)  H (1) Had(1) ; CR; H(2);; CR. *)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).

Definition env := Env.t type.
Definition empty_env := @Env.empty type.


(* Defining program semantic functions. *)
Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | _ => false end.


Lemma double_put_cu : forall (f:posi -> val) x v v', put_cu (put_cu (f x) v) v' = put_cu (f x) v'.
Proof.
  intros.
  unfold put_cu.
  destruct (f x). easy. easy.
Qed.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  if b then nval b (r_rotate r q) else nval b r
                  | qval rc r =>  qval rc (r_rotate r q)
     end.

Fixpoint srr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (srr_rotate' st x m size)[(x,m) |-> times_r_rotate (st (x,m)) (size - m)]
   end.
Definition srr_rotate st x n := srr_rotate' st x (S n) (S n).


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | a => a
     end.

Fixpoint lshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,0) |-> f(x,size)]
             | S m => ((lshift' m size f x)[ (x,n) |-> f(x,m)])
   end.
Definition lshift (f:posi -> val) (x:var) (n:nat) := lshift' (n-1) (n-1) f x.

Fixpoint rshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,size) |-> f(x,0)]
             | S m => ((rshift' m size f x)[(x,m) |-> f (x,n)])
   end.
Definition rshift (f:posi -> val) (x:var) (n:nat) := rshift' (n-1) (n-1) f x.

(*
Inductive varType := SType (n1:nat) (n2:nat).

Definition inter_env (enva: var -> nat) (x:var) :=
             match  (enva x) with SType n1 n2 => n1 + n2 end.
*)
(*
Definition hexchange (v1:val) (v2:val) :=
  match v1 with hval b1 b2 r1 => 
    match v2 with hval b3 b4 r2 => if eqb b3 b4 then v1 else hval b1 (¬ b2) r1
                | _ => v1
    end
             | _ => v1
  end.
*)

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun (a: var * nat) =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.

(* Semantics function for QFT gate. *)
Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (f:nat -> bool) :=
   match v with nval b r => qval r f
              | a => a
   end.

Definition lshift_fun (f:nat -> bool) (n:nat) := fun i => f (i+n).

(*A function to get the rotation angle of a state. *)
Definition get_r (v:val) :=
   match v with nval x r => r
              | qval rc r => rc
   end.


Fixpoint assign_r (f:posi -> val) (x:var) (r : nat -> bool) (n:nat) := 
    match n with 0 => f
              | S m => (assign_r f x r m)[(x,m) |-> up_qft (f (x,m)) (lshift_fun r m)]
    end.

Definition up_h (v:val)  :=
   match v with nval true r => qval r (rotate allfalse 1)
              | nval false r => qval r allfalse
              | qval r f => nval (f 0) r
   end.

Fixpoint assign_h (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h f x n m)[(x,n+m) |-> up_h (f (x,n+m))]
  end.

Definition turn_qft (st : posi -> val) (x:var) (b:nat) (rmax : nat) := 
       assign_h (assign_r st x (get_cus b st x) b) x b (rmax - b).


(* Semantic function for RQFT gate. *)
Fixpoint assign_seq (f:posi -> val) (x:var) (vals : nat -> bool) (n:nat) := 
   match n with 0 => f
              | S m => (assign_seq f x vals m)[(x,m) |-> nval (vals m) (get_r (f (x,m)))]
   end.

Fixpoint assign_h_r (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h_r f x n m)[(x,n+m) |-> up_h (f (x,n+m))]
  end.

Definition get_r_qft (f:posi -> val) (x:var) :=
      match f (x,0) with qval rc g => g
                      | _ => allfalse
      end.

Definition turn_rqft (st : posi -> val) (x:var) (b:nat) (rmax : nat) := 
           assign_h_r (assign_seq st x (get_r_qft st x) b) x b (rmax - b).


(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (env:var -> nat) (e:exp) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | CU p e' => if get_cua (st p) then exp_sem env e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | SR n x => sr_rotate st x n (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n
              | Lshift x => (lshift st x (env x))
              | Rshift x => (rshift st x (env x))
              | Rev x => (reverse st x (env x))
               | QFT x b => turn_qft st x b (env x)
               | RQFT x b => turn_rqft st x b (env x)
              | e1 ; e2 => exp_sem env e2 (exp_sem env e1 st)
    end.


Definition or_not_r (x y:var) (n1 n2:nat) := x <> y \/ n1 < n2.

Definition or_not_eq (x y:var) (n1 n2:nat) := x <> y \/ n1 <= n2.



Inductive exp_fresh (aenv:var->nat): posi -> exp -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh aenv p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh aenv p (X p')
      | sr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SR n x)
      | srr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SRR n x)
      | lshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Lshift x)
      | rshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rshift x)
      | rev_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rev x)
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh aenv p e -> exp_fresh aenv p (CU p' e)
     (* | cnot_fresh : forall p p1 p2, p <> p1 -> p <> p2 -> exp_fresh aenv p (HCNOT p1 p2) *)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RRZ q p')
       (*all qubits will be touched in qft/rqft because of hadamard*)
      | qft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (QFT x b)
      | rqft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (RQFT x b)
      | seq_fresh : forall p e1 e2, exp_fresh aenv p e1 -> exp_fresh aenv p e2 -> exp_fresh aenv p (Seq e1 e2).

(* Defining matching shifting stack. *)
Inductive sexp := Ls | Rs | Re.

Definition opp_ls (s : sexp) := match s with Ls => Rs | Rs => Ls | Re => Re end.

Definition fst_not_opp (s:sexp) (l : list sexp) := 
   match l with [] => True
              | (a::al) => s <> opp_ls a
   end.

Inductive exp_neu_l (x:var) : list sexp -> exp ->  list sexp -> Prop :=
      | skip_neul : forall l p, exp_neu_l x l (SKIP p) l
      | x_neul : forall l p,  exp_neu_l x l (X p) l
      | sr_neul : forall l y n, exp_neu_l x l (SR n y) l
      | srr_neul : forall l y n, exp_neu_l x l (SRR n y) l
      | cu_neul : forall l p e, exp_neu_l x [] e [] -> exp_neu_l x l (CU p e) l
      (*| hcnot_neul : forall l p1 p2, exp_neu_l x l (HCNOT p1 p2) l *)
      | rz_neul : forall l p q, exp_neu_l x l (RZ q p) l
      | rrz_neul : forall l p q, exp_neu_l x l (RRZ q p) l
      | qft_neul : forall l y b, exp_neu_l x l (QFT y b) l
      | rqft_neul : forall l y b, exp_neu_l x l (RQFT y b) l

      | lshift_neul_a : forall l, exp_neu_l x (Rs::l) (Lshift x) l
      | lshift_neul_b : forall l, fst_not_opp Ls l -> exp_neu_l x l (Lshift x) (Ls::l)
      | lshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Lshift y) l
      | rshift_neul_a : forall l, exp_neu_l x (Ls::l) (Rshift x) l
      | rshift_neul_b : forall l, fst_not_opp Rs l -> exp_neu_l x l (Rshift x) (Rs::l)
      | rshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rshift y) l
      | rev_neul_a : forall l, exp_neu_l x (Re::l) (Rev x) l
      | rev_neul_b : forall l, fst_not_opp Re l -> exp_neu_l x l (Rev x) (Re::l)
      | rev_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rev y) l
      | seq_neul : forall l l' l'' e1 e2, exp_neu_l x l e1 l' -> exp_neu_l x l' e2 l'' -> exp_neu_l x l (Seq e1 e2) l''.

Definition exp_neu (xl : list var) (e:exp) : Prop :=
    forall x, In x xl -> exp_neu_l x [] e [].

Definition exp_neu_prop (l:list sexp) :=
    (forall i a, i + 1 < length l -> nth_error l i = Some a -> nth_error l (i+1) <> Some (opp_ls a)).

(* Type System. *)
Inductive well_typed_exp: env -> exp -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_nor : forall env p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (X p)
    (*| x_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (X p) *)
    (*| cnot_had : forall env p1 p2, p1 <> p2 -> Env.MapsTo (fst p1) Had env -> Env.MapsTo (fst p2) Had env
                         -> well_typed_exp env (HCNOT p1 p2) *)
    | rz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RZ q p)
    | rrz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RRZ q p)
    | sr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SR m x)
    | srr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SRR m x)
    | lshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Lshift x)
    | rshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rshift x)
    | rev_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rev x).

Fixpoint get_vars e : list var :=
    match e with SKIP p => [(fst p)]
              | X p => [(fst p)]
              | CU p e => (fst p)::(get_vars e)
             (* | HCNOT p1 p2 => ((fst p1)::(fst p2)::[]) *)
              | RZ q p => ((fst p)::[])
              | RRZ q p => ((fst p)::[])
              | SR n x => (x::[])
              | SRR n x => (x::[])
              | Lshift x => (x::[])
              | Rshift x => (x::[])
              | Rev x => (x::[])
              | QFT x b => (x::[])
              | RQFT x b => (x::[])
              | Seq e1 e2 => get_vars e1 ++ (get_vars e2)
   end.


Inductive well_typed_oexp (aenv: var -> nat) : env -> exp -> env -> Prop :=
    | exp_refl : forall env e, 
                well_typed_exp env e -> well_typed_oexp aenv env e env
    | qft_nor :  forall env env' x b, b <= aenv x -> 
               Env.MapsTo x Nor env -> Env.Equal env' (Env.add x (Phi b) env)
                   -> well_typed_oexp aenv env (QFT x b) env'
    | rqft_phi :  forall env env' x b, b <= aenv x ->
               Env.MapsTo x (Phi b) env -> Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_oexp aenv env (RQFT x b) env'
    | pcu_nor : forall env p e, Env.MapsTo (fst p) Nor env -> exp_fresh aenv p e -> exp_neu (get_vars e) e ->
                       well_typed_oexp aenv env e env -> well_typed_oexp aenv env (CU p e) env
    | pe_seq : forall env env' env'' e1 e2, well_typed_oexp aenv env e1 env' -> 
                 well_typed_oexp aenv env' e2 env'' -> well_typed_oexp aenv env (e1 ; e2) env''.

Inductive exp_WF (aenv:var -> nat): exp -> Prop :=
      | skip_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (SKIP p)
      | x_wf : forall p, snd p < aenv (fst p)  -> exp_WF aenv  (X p)
      | cu_wf : forall p e, snd p < aenv (fst p)  -> exp_WF aenv  e -> exp_WF aenv  (CU p e)
    (*  | hcnot_wf : forall p1 p2, snd p1 < aenv (fst p1) 
                              -> snd p2 < aenv (fst p2)  -> exp_WF aenv  (HCNOT p1 p2) *)
      | rz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RZ q p)
      | rrz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RRZ q p)
      | sr_wf : forall n x, n < aenv x -> exp_WF aenv  (SR n x)
      | ssr_wf : forall n x, n < aenv x -> exp_WF aenv  (SRR n x)       
      | seq_wf : forall e1 e2, exp_WF aenv e1 -> exp_WF aenv  e2 -> exp_WF aenv  (Seq e1 e2)
      | lshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Lshift x)
      | rshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rshift x)
      | rev_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rev x)
      | qft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (QFT x b)
      | rqft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (RQFT x b).

Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
                | S m => if M m then init_v m x M; X (x,m) else init_v m x M
      end.

Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)

    | right_phi: forall n rc r, right_mode_val (Phi n) (qval rc r).

Definition right_mode_env (aenv: var -> nat) (env: env) (st: posi -> val)
            := forall t p, snd p < aenv (fst p) -> Env.MapsTo (fst p) t env -> right_mode_val t (st p).

(* helper functions/lemmas for NOR states. *)
Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Definition get_snd_r (f:posi -> val) (p:posi) :=
    match (f p) with qval rc r => r | _ => allfalse end.

Definition qft_uniform (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x b, Env.MapsTo x (Phi b) tenv -> 
             (forall i, i < b -> get_snd_r f (x,i) = (lshift_fun (get_r_qft f x) i)).

Definition qft_gt (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x b, Env.MapsTo x (Phi b) tenv -> (forall i,0 < b <= i -> get_r_qft f x i = false)
                                      /\ (forall j, b <= j < aenv x -> (forall i, 0 < i -> get_snd_r f (x,j) i = false )).

Definition at_match (aenv: var -> nat) (tenv:env) := forall x b, Env.MapsTo x (Phi b) tenv -> b <= aenv x.
