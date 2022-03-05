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
        | H (p:posi)
        | Seq (s1:exp) (s2:exp).

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
  | H x => H x
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

(*  Define approximate QFT in the Had basis by the extended type system. In this type system, 
    once a value is in Had basis,
     it will never be applied back to Nor domain, so that we can define more SR gates. *)
Fixpoint many_CR (x:var) (b:nat) (n : nat) (i:nat) :=
  match n with
  | 0 | 1 => SKIP (x,n)
  | S m  => if b <=? m then (many_CR x b m i ; (CU (x,m+i) (RZ n (x,i)))) else SKIP (x,m)
  end.

(* approximate QFT for reducing b ending qubits. *)
Fixpoint appx_QFT (x:var) (b:nat) (n : nat) (size:nat) :=
  match n with
  | 0    => SKIP (x,n)
  | S m => if b <=? m then appx_QFT x b m size ; (H (x,m)) ; (many_CR x b (size-m) m) else SKIP (x,m)
  end.

(* Match the K graph by LV decomposition, the following define the L part.  (H ; R(alpha)); H  |x> -> Sigma|y>. *)
Fixpoint half_k_graph (x:var) (r:nat) (size:nat) :=
   match size with 0 => SKIP (x,0)
          | S m => (H (x,m)); RZ r (x,m);half_k_graph x r m
   end.

Inductive type := Had (b:nat) | Phi (b:nat) | Nor.

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
  destruct (f x). easy. easy. easy.
Qed.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
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
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (r_rotate r q)
     end.

Fixpoint srr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (srr_rotate' st x m size)[(x,m) |-> times_r_rotate (st (x,m)) (size - m)]
   end.
Definition srr_rotate st x n := srr_rotate' st x (S n) (S n).


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
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

Definition hexchange (v1:val) (v2:val) :=
  match v1 with hval b1 b2 r1 => 
    match v2 with hval b3 b4 r2 => if eqb b3 b4 then v1 else hval b1 (¬ b2) r1
                | _ => v1
    end
             | _ => v1
  end.

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun (a: var * nat) =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.

(* Semantic definition for H gate. *)
Definition h_case (v : val) :=
    match v with nval b r => if r 0 then hval false b (rotate r 1) else hval true (¬ b) r
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1)
               | hval false false r => nval false (rotate r 1)
               | a => a
    end.

Fixpoint h_sem (f:posi -> val) (x:var) (n : nat) := 
    match n with 0 => f
              | S m => (h_sem f x m)[(x,m) |-> h_case (f (x,m))]
    end.

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
              | hval x y r => r
   end.


Fixpoint assign_r (f:posi -> val) (x:var) (r : nat -> bool) (n:nat) := 
    match n with 0 => f
              | S m => (assign_r f x r m)[(x,m) |-> up_qft (f (x,m)) (lshift_fun r m)]
    end.

Definition up_h (v:val)  :=
   match v with nval true r => qval r (rotate allfalse 1)
              | a => a
   end.

Fixpoint assign_h (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h f x n m)[(x,n-i) |-> up_h (f (x,n-i))]
  end.

Definition turn_qft (st : posi -> val) (x:var) (b:nat) (rmax : nat) := 
       assign_h (assign_r st x (get_cus (rmax - b) st x) (rmax - b)) x rmax b.


(* Semantic function for RQFT gate. *)
Fixpoint assign_seq (f:posi -> val) (x:var) (vals : nat -> bool) (n:nat) := 
   match n with 0 => f
              | S m => (assign_seq f x vals m)[(x,m) |-> nval (vals m) (get_r (f (x,m)))]
   end.

Definition up_h_r (v:val)  :=
   match v with qval r f => nval (f 0) r
           | a => a
   end. 

Fixpoint assign_h_r (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h_r f x n m)[(x,n-i) |-> up_h_r (f (x,n-i))]
  end.

Definition get_r_qft (f:posi -> val) (x:var) :=
      match f (x,0) with qval rc g => g
                      | _ => allfalse
      end.

Definition turn_rqft (st : posi -> val) (x:var) (b:nat) (rmax : nat) := 
           assign_h_r (assign_seq st x (get_r_qft st x) (rmax -b)) x rmax b.


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
               | H p => st[p |-> h_case (st p)]
               | QFT x b => turn_qft st x (env x) b
               | RQFT x b => turn_rqft st x (env x) b
              | e1 ; e2 => exp_sem env e2 (exp_sem env e1 st)
    end.
