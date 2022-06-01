Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import OQASM.
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

(* This will be replaced by PQASM. *)


(* Classical State including variable relations that may be quantum *)

(* we want to include all the single qubit gates here in the U below. *)
Inductive atype := C : atype | Q : atype | M :atype.


Definition aty_eq  (t1 t2:atype) : bool := 
   match t1 with C => match t2 with C  => true
                            | _ => false
                        end
               | Q => match t2 with Q => true
                           | _ => false
                        end
               | M => match t2 with M => true 
                           | _ => false
                        end
   end.

Notation "i '=a=' j" := (aty_eq i j) (at level 50).

Lemma aty_eqb_eq : forall a b, a =a= b = true -> a = b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. 1-3:easy.
 destruct b. 1-3:easy.
 destruct b. 1-3:easy.
Qed.

Lemma aty_eqb_neq : forall a b, a =a= b = false -> a <> b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. easy.
 easy. easy.
 destruct b. easy. easy. easy.
 destruct b. easy. easy. easy.
Qed.

Lemma aty_eq_reflect : forall r1 r2, reflect (r1 = r2) (aty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =a= r2) eqn:eq1.
  apply  ReflectT.
  apply aty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply aty_eqb_neq in eq1.
  assumption. 
Qed.

Definition meet_atype (a1 a2: atype) := 
       match a1 with Q => Some Q | C => if  (a2 =a= M) then None else Some a2
                | M => if a2 =a= M then Some M else None
        end.

Inductive varia := Var (x:var) | Index (x:var) (v:var).

Inductive singleGate := H_gate | X_gate | RZ_gate (f:nat) (*representing 1/2^n of RZ rotation. *).


Inductive aexp := BA (x:varia) | Num (n:nat) | APlus (e1:aexp) (e2:aexp).

Inductive bexp := | BEq (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp) | BTest (i:aexp) (a:aexp).


(* Define the ground term type system 
Inductive type_rotation := TV (b:aexp) | Infty.
*)

Inductive pexp := PSKIP | Assign (x:var) (n:aexp) 
              (*| InitQubit (p:posi) *) 
              (* Ethan: Init = reset = trace out = measurement... commeneted out *)
            | AppU (e:singleGate) (p:varia)
            | PSeq (s1:pexp) (s2:pexp)
            | If (x:bexp) (s1:pexp)
            | IfB (x:bexp) (s1:pexp) (s2:pexp)
            | While (b:bexp) (p:pexp)
            | Classic (p:exp) (args : list (varia))
                   (*  quantum oracle functions executing p, and a list of tuples (x,a,s)
                      the first argument is the list of variables of quantum to p,
                       the second arguments a is the phase of the post-state of x,
                       the third is the state s = f(x) as |x> -> e^2pi i * a *|s>,
                       excluding ancilla qubits  *)
            | PQFT (x:var)
            | PRQFT (x:var)
            | Meas (a:var) (x:var) (* quantum measurement on x to a classical value 'a'. *)
            | PMeas (p:var) (x:var) (a:var) (* the probability of measuring x = a assigning probability to p. *)
            | QWhile (n:aexp) (x:var) (i:var) (b:bexp) (e:pexp)
            | Amplify (x:var) (n:aexp) (* reflection on x with the form aexp x=n. l is the session. *)
            | Reflect (x:var) (p:aexp) (a1:aexp) (a2:aexp) (* reflection on two state x=a1 and x=a2 with x=a1 happens in a probablity p, a1 <> a2  *)
            | Distr (x:var) (al : list aexp) (*reflection on x = a_1 ,... x = a_n in al with equal probablity hadamard walk. 
                                               This statement basically distributes/diverges a vector x to many different vectors. *).
          (*  | CX (x:posi) (y:posi)  (* control x on to y. *)
            | CU (x:posi) (p:exp) (z:var) (args: list var) (q:aexp) (s:aexp) *)
             (* control-U on the reversible expression p from the control node x on to z. *)
(*
            | QWhile (n:aexp) (x:var) (f:aexp) (b:bexp) (e:pexp) 
                    (*max loop number of n, variable x, monotonic function f on x as x -> f(x), bool b and e.*)
            | Amplify (x:var) (n:aexp) (* reflection on x with the form aexp x=n. *)
            | Reflect (x:var) (p:aexp) (a1:aexp) (a2:aexp) (* reflection on two state x=a1 and x=a2 with x=a1 happens in a probablity p, a1 <> a2  *)
            | Distr (x:var) (al : list aexp) (*reflection on x = a_1 ,... x = a_n in al with equal probablity hadamard walk. 
                                               This statement basically distributes/diverges a vector x to many different vectors. *).
*)
Notation "p1 ; p2" := (PSeq p1 p2) (at level 50) : pexp_scope.




(* Type system -- The Static Type system, and the dynamic gradual typing part will be merged with the triple rule. *)

(*

Inductive aexp := BA (b:vari) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | AMinus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp)
           | TwoTo (e1:aexp) | XOR (e1:aexp) (e2:aexp)

with vari := Var(x:var) | Index (x:var) (a:aexp).

(*
Definition posi :Type := (var * aexp).
*)

Inductive fexp := Fixed (r:R) | FNeg (f1:fexp) | FPlus (f1:fexp) (f2:fexp) | FTimes (f1:fexp) (f2:fexp) 
        | FDiv (f1:fexp) (f2:fexp)
        | FSum (n:aexp) (i:var) (b:aexp) (f:fexp)
        | FExp (f:fexp) | FSin (f:fexp) | FCos (f:fexp)
        | FCom (f:fexp) (f1:fexp) (* a + b i *)
        | FExpI (a:aexp) (* e^ 2pi i * a *).

Inductive bexp := BEq (x:aexp) (y:aexp) | BGe (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp)
                | FEq (x:fexp) (y:fexp) | FGe (x:fexp) (y:fexp) | FLt (x:fexp) (y:fexp)
                | BTest (x:aexp) | BXOR (x:bexp) (y:bexp) | BNeg (x:bexp).
*)

Module AEnv := FMapList.Make Nat_as_OT.
Module AEnvFacts := FMapFacts.Facts (AEnv).
Definition aenv := AEnv.t atype.
Definition empty_benv := @AEnv.empty atype.

Definition stack := AEnv.t nat.
Definition empty_stack := @AEnv.empty nat.

(*
Inductive static_type := SPos (x:list vari) | SNeg (x:list vari).
*)
Definition vari_eq (x y: varia) :=
  match x with Var n => match y with Var m => (n =? m) | _ => false end
            | Index n i => match y with Index m j => (n =? m) && (i =? j) | _ => false end
  end.

Fixpoint merge_var (x: varia) (yl:list varia) :=
   match yl with [] => []
           | a::al => if vari_eq x a then a::al else a::(merge_var x al)
   end.

Definition merge_vars (xl yl: list varia) := List.fold_left (fun acc b => merge_var b acc) xl yl.

Definition meet_avtype (t1 t2: atype * list varia) :=
        match t1 with (a, xl) => match t2 with (b,yl) => 
         match meet_atype a b with None => None | Some a' => Some (a', merge_vars xl yl) end end end.

(*
Definition right_av (t1: atype * list varia) :=  match t1 with (C,xl) => length xl = 0 | (Q,xl) => length xl = 1 end.
*)

Inductive type_vari : aenv -> varia -> atype * list varia -> Prop :=
   | var_type : forall env x t, AEnv.MapsTo x t env -> type_vari env (Var x) (t,(if t =a= Q then [Var x] else []))
   | index_type : forall env x v, AEnv.MapsTo x Q env -> AEnv.MapsTo v C env -> type_vari env (Index x v) (Q,[Index x v]).

Inductive type_aexp : aenv -> aexp -> atype * list varia -> Prop :=
     ba_type : forall env b t, type_vari env b t -> type_aexp env (BA b) t
   | num_type : forall env n, type_aexp env (Num n) (C,[])
   | plus_type : forall env e1 e2 t1 t2 t3, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  meet_avtype t1 t2 = Some t3 -> 
                     type_aexp env (APlus e1 e2) t3.

Definition list_subset (al bl :list var) := (forall x, In x al -> In x bl).

Definition get_var (x : varia) := match x with Var a => a | Index b y => b end.

Definition get_core_vars (al : list varia) := map (fun a => match a with Var x => x | Index x xl => x end) al.


Inductive type_vari_list_q : aenv -> list varia -> Prop :=
     type_aexp_empty : forall env, type_vari_list_q env []
   | type_aexp_many : forall env x xs, type_vari env x (Q,[x]) -> type_vari_list_q env xs -> type_vari_list_q env (x::xs).

Inductive type_aexp_list_c : aenv -> list aexp -> Prop :=
     type_aexp_empty_c : forall env, type_aexp_list_c env nil
   | type_aexp_many_c : forall env x xs, type_aexp env x (C,[]) -> type_aexp_list_c env xs -> type_aexp_list_c env (x::xs).

Inductive type_bexp : aenv -> bexp -> atype * list varia -> Prop :=
   |  beq_type : forall env e1 e2 t1 t2 t3, type_aexp env e1 t1 -> type_aexp env e2 t2 ->
             meet_avtype t1 t2 = Some t3 -> type_bexp env (BEq e1 e2) t3
   | blt_type : forall env e1 e2 t1 t2 t3, type_aexp env e1 t1 -> type_aexp env e2 t2 ->
             meet_avtype t1 t2 = Some t3 -> type_bexp env (BLt e1 e2) t3
   | btest_type : forall env e1 e2 x, type_aexp env (BA (Var e1)) (C,[]) -> type_aexp env e2 (Q,[Var x]) 
            -> type_bexp env (BTest (BA (Var e1)) e2) (Q, [Index x e1]).

Definition pre_tenv (l:list var) (env:env) := forall x, In x l -> Env.MapsTo x Nor env.
    
Inductive stype_pexp {qenv: var -> nat} : atype -> aenv -> pexp ->  atype * list varia -> Prop :=
    | skip_stype_c : forall m env, stype_pexp m env (PSKIP) (C,[])
    | skip_stype_q : forall m env l, stype_pexp m env (PSKIP) (Q,l)
    | assign_stype_c : forall env a v, AEnv.MapsTo a C env -> type_aexp env v (C,[]) -> stype_pexp C env (Assign a v) (C,[])
    | assign_stype_m : forall env a v, AEnv.MapsTo a M env -> type_aexp env v (M,[]) -> stype_pexp C env (Assign a v) (M,[])
    | appu_stype : forall m env e p x,  type_vari env p (Q,[x]) -> stype_pexp m env (AppU e p) (Q,[x])
    | if_q : forall m env b x v e xl, type_bexp env b (Q,[Index x v]) -> AEnv.MapsTo v C env ->
                  stype_pexp Q env e (Q,xl) -> stype_pexp m env (If b e) (Q,(Index x v)::xl)
    | if_c : forall m m' env b e1 e2 xl, type_bexp env b (C,[]) -> 
                  stype_pexp m env e1 (m',xl) -> stype_pexp m env e2 (m',xl) -> stype_pexp m env (IfB b e1 e2) (m',xl)
    | class_stype : forall m env e l tenv, pre_tenv (get_vars e) tenv -> well_typed_oexp qenv tenv e tenv ->  exp_WF qenv e ->
              type_vari_list_q env l -> stype_pexp m env (Classic e l) (Q,l)
    | qft_stype : forall m env x, AEnv.MapsTo x Q env -> stype_pexp m env (PQFT x) (Q,[Var x])
    | rqft_stype : forall m env x, AEnv.MapsTo x Q env -> stype_pexp m env (PRQFT x) (Q,[Var x])
    | pmea_stype : forall m env p a x, AEnv.MapsTo a M env -> AEnv.MapsTo p M env
              -> AEnv.MapsTo x Q env -> stype_pexp m env (PMeas p x a) (Q,[Var x])
    | mea_stype : forall m env a x, AEnv.MapsTo a M env ->  AEnv.MapsTo x Q env -> stype_pexp m env (Meas a x) (Q,[Var x])
    | qwhile_stype : forall m env n x x' i b e xl, stype_pexp Q env e (Q,xl) -> ~ list_subset ([x]) (get_core_vars xl) ->
              AEnv.MapsTo x Q env -> AEnv.MapsTo i C env -> type_bexp env b (Q,[x']) -> get_var x' = x ->
              stype_pexp m env (QWhile n x i b e) (Q,(Var x)::xl)
    | amplify_stype : forall m env x n, AEnv.MapsTo x Q env -> type_aexp env n (C,[]) -> stype_pexp m env (Amplify x n) (Q,[Var x])
    | reflect_stype : forall m env x p a1 a2, AEnv.MapsTo x Q env -> type_aexp env p (C,[]) 
          -> type_aexp env a1 (C,[]) -> type_aexp env a2 (C,[]) -> stype_pexp m env (Reflect x p a1 a2) (Q,[Var x])
    | distr_stype : forall m env x al, AEnv.MapsTo x Q env -> type_aexp_list_c env al -> stype_pexp m env (Distr x al) (Q,[Var x]).


(* Type system for oqasm. *)
Definition bits := list bool.

Definition tenv := (var -> (rz_val * rz_val)). 


Definition flip_i (l:rz_val) (i:nat) := update l i (negb (l i)).
Definition exchange (env:tenv) (p:posi) :=
    match env (fst p) with (r, l) => update env (fst p) (r, (flip_i l (snd p))) end.

Definition up_phase (tenv:tenv) (x:var) (q:nat) :=
  match tenv x with (r,l) => update tenv x (rotate r q,l) end.

Definition up_phase_r (tenv:tenv) (x:var) (q:nat) :=
  match tenv x with (r,l) => update tenv x (r_rotate r q,l) end.

Definition up_phase_phi (tenv:tenv) (x:var) (n:nat) :=
  match tenv x with (r,q) => update tenv x (r, (rotate q n)) end.

Definition up_phase_phi_r (tenv:tenv) (x:var) (n:nat) :=
  match tenv x with (r, q) => update tenv x (r, (r_rotate q n)) end.


Inductive oqasm_type {qenv: var -> nat} : tenv -> exp -> tenv -> Prop :=
    skip_otype : forall tenv p, oqasm_type tenv (SKIP p) tenv
  | x_otype : forall tenv p, oqasm_type tenv (X p) (exchange tenv p)
  | cu_otype_1 : forall tenv p e, (snd (tenv (fst p))) (snd p) = false -> oqasm_type tenv (CU p e) tenv
  | cu_otype_2 : forall tenv tenv' p e,  (snd (tenv (fst p))) (snd p) = true -> oqasm_type tenv e tenv' -> oqasm_type tenv (CU p e) tenv'
  | rz_otype : forall tenv q p, oqasm_type tenv (RZ q p) (up_phase tenv (fst p) q)
  | rrz_otype : forall tenv q p, oqasm_type tenv (RRZ q p) (up_phase_r tenv (fst p) q)
  | sr_otype : forall tenv n x, oqasm_type tenv (SR n x) (up_phase_phi tenv x (S n))
  | srr_otype : forall tenv n x, oqasm_type tenv (SRR n x) (up_phase_phi_r tenv x (S n))
  | qft_otype : forall tenv x b, oqasm_type tenv (QFT x b) tenv
  | rqft_otype : forall tenv x b, oqasm_type tenv (RQFT x b) tenv
  | seq_otype : forall tenv tenv1 tenv2 s1 s2, oqasm_type tenv s1 tenv1 -> oqasm_type tenv s2 tenv2 -> oqasm_type tenv (Seq s1 s2) tenv2.

(* The dynamic type system. Symbolic type. *)
Inductive type_cfac := TMore (al:list rz_val) | TDistr.

Inductive type_elem : Type := TNor (p : (rz_val))
         | TH (r:option nat) (b: option (list (list rz_val)))
         | EN (n:nat) (r:option nat) (b: option ((list rz_val))) (t:type_cfac)
         | DFT (r:option nat) (b: option (list (list rz_val))).

Inductive se_type : Type := THT (n:nat) (r:option rz_val) (t:type_elem).

Definition type_pred := list se_type.

Definition tpred := list (list (var * nat * nat) * list se_type).

Definition eval_vari_c (s:stack) (a:varia) :=
  match a with Var x => AEnv.find x s | Index x v => None end.

Fixpoint eval_aexp_c (s:stack) (a:aexp) :=
   match a with BA x => eval_vari_c s x | Num n => Some n
    | APlus e1 e2 =>
        match eval_aexp_c s e1 with None => None | Some n1 => 
            match eval_aexp_c s e2 with None => None | Some n2 => Some (n1+n2)
            end
        end
    end.

Definition eval_bexp_c (s:stack) (c:bexp) :=
   match c with BEq e1 e2 => match eval_aexp_c s e1 with None => None
                                  | Some n1 => 
                              match eval_aexp_c s e2 with None => None
                                  | Some n2 => Some (n1 =? n2)
                              end
                            end
             | BLt e1 e2 => match eval_aexp_c s e1 with None => None
                                  | Some n1 => 
                              match eval_aexp_c s e2 with None => None
                                  | Some n2 => Some (n1 <? n2)
                              end
                            end
            | BTest i a => None
    end.

Fixpoint eval_varia_list (qenv: var -> nat) (s:stack) (l:list varia) :=
  match l with [] => Some ([])
           | (Var x)::xs => match eval_varia_list qenv s xs with None => None
                       | Some xs' => Some ((x,0,qenv x)::xs')
                            end
           | (Index x i)::xs => match eval_varia_list qenv s xs with None => None
                 | Some xs' => match AEnv.find i s with None => None
                               | Some iv => Some ((x,iv,iv+1)::xs')
                             end
                          end
  end.


Fixpoint in_session (a: (var* nat*nat)) (l:list (var*nat*nat)) (pos:nat) :=
  match l with [] => None
       | ((x,lb,rb)::xs) => 
         if fst (fst a) =? x 
                   then (if (lb <=? (snd (fst a))) && ((snd a) <=? rb) then Some (pos + (snd (fst a)) - lb) else None)
                   else in_session a xs (pos + rb - lb)
 end.

Fixpoint find_nor_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,[THT n p (TNor r)])::xl) => match in_session a x 0 with None => find_nor_env a xl 
                                       | Some pos => Some (pos,r)
                                  end
           | (_,_)::xl => find_nor_env a xl
   end.

Definition con_nor (a:nat) (b:nat) (f:nat -> bool) := cut_n (lshift_fun f a) b.

Fixpoint find_nor_env_list (al: list (var* nat*nat)) (l:tpred) :=
    match al with [] => Some nil
       | (a::bl) => match find_nor_env a l with None => None
                  | Some (pos,r) => 
               match find_nor_env_list bl l with None => None
                  | Some xl => Some (([a],[THT ((snd a) - (snd (fst a))) (Some allfalse) (TNor (con_nor pos (snd a- (snd (fst a))) r))])::xl)
                   end
              end
    end.

Fixpoint cut_n_list {A:Type} (l:list A) (n:nat) :=
  match n with 0 => []
     | S m => match l with [] => []
                  | x::xs => x::cut_n_list xs m
              end
   end.

Fixpoint shift_cut_phase_aux {A} (l:list A) (pos:nat) (n:nat) :=
     match pos with 0 => cut_n_list l n
          | S m => match l with [] => []
                   | x::xs => shift_cut_phase_aux xs m n
                   end
     end.

Definition shift_cut_phase {A} (l:option (list A)) (pos:nat) (nat:nat) := 
        match l with None => None
             | Some al => Some (shift_cut_phase_aux al pos nat)
        end.

Definition cut_type_cfac (pos:nat) (n:nat) (t:type_cfac) := 
   match t with TMore l => TMore (List.map (fun f => (cut_n (lshift_fun f pos) n)) l)
            | TDistr => TDistr
   end.

Definition cut_type (pos:nat) (n:nat) (t:type_elem) :=
   match t with TNor f => (TNor (cut_n (lshift_fun f pos) n))
              | TH r b => TH r (shift_cut_phase b pos n)
              | EN m r b tl => EN m r b (cut_type_cfac pos n tl)
              | DFT r b => DFT r b
   end.

Fixpoint cut_type_n (pos:nat) (n:nat) (l:list se_type) (i:nat) :=
    match l with [] => None
          | (THT m p a)::xs => 
      if (i <=? pos) && (pos + n <=? m + i) then Some (THT n p (cut_type (pos - i) n a))
       else cut_type_n pos n xs (i+m)
    end.

Fixpoint find_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,tl)::xl) => match in_session a x 0 with None => find_env a xl 
                                       | Some pos => Some (tl,pos)
                                  end
   end.


Fixpoint find_env_gen (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,tl)::xl) => match in_session a x 0 with None => find_env_gen a xl 
                             | Some pos => cut_type_n pos (snd a - (snd (fst a))) tl 0
                                  end
   end.

Fixpoint n_rotate (r :rz_val) (q:rz_val) (n:nat) := 
   match n with 0 => r | S m => if q m then n_rotate (rotate r n) q m else n_rotate r q m end.


Fixpoint add_phase_list (l:(list (list rz_val))) (p : rz_val) (pos:nat) (rmax:nat) :=
   match pos with 0 => match l with  | (x::xs)::xl => ((n_rotate x p rmax)::xs)::xl
                                  | _ => l
                       end
       | S m => match l with [] => [] | x::xs => x::(add_phase_list xs p pos rmax)
                end
  end.

Definition add_phase_option (b: option (list (list rz_val))) (p:option rz_val) (pos:nat) (rmax:nat) :=
    match b with None => None | Some l => 
          match p with None => None | Some new_r => Some (add_phase_list l new_r pos rmax) end end.

Definition add_phase_elem (t:type_elem) (pos:nat) (p:option rz_val) (rmax:nat) :=
   match t with TH r b => TH r (add_phase_option b p pos rmax)
             | DFT r b => DFT r (add_phase_option b p pos rmax)
             | EN n r b tl => match b with Some (b'::bl) => 
           match p with None => EN n r None tl
                      | Some p' => EN n r (Some ((n_rotate b' p' rmax)::bl)) tl 
           end
                      | _ => EN n r None tl
           end

             | _ => t
   end.


Fixpoint add_phase_aux (t:list se_type) (pos:nat) (p:option rz_val) (acc:nat) (rmax:nat) :=
   match t with [] => []
       | (THT n pa a)::xs => 
            if (acc <=? pos) && (pos <? acc + n) then (THT n pa (add_phase_elem a pos p rmax))::xs
            else (THT n pa a)::(add_phase_aux xs pos p (acc+n) rmax)
  end.

Fixpoint add_phase_env (l:tpred) (a: (var* nat*nat)) (p:option rz_val) (rmax:nat) := 
  match l with [] => []
    | ((x,tl)::xs) => match in_session a x 0 with None => ((x,tl)::add_phase_env xs a p rmax)
                             | Some pos => (x, add_phase_aux tl pos p 0 rmax)::xs
                                  end
  end.
          

Fixpoint is_had' (t:list se_type) (pos:nat) (acc:nat) := 
  match t with [] => False
        | ((THT n _ (TH r b))::xs) => 
          if (acc <=? pos) && (pos <? n + acc) then True else is_had' xs pos (acc+n)
        | ((THT n _ _)::xs) => 
          if (acc <=? pos) && (pos <? n + acc) then False else is_had' xs pos (acc+n)
  end.
Definition is_had (t:list se_type) (pos:nat) := is_had' t pos 0.

(*
Definition merge_funs (a:nat -> bool) (b:nat-> bool) (pos:nat) :=
         fun x => if x <=? pos then a x else b x.

Fixpoint con_nor_list (al: list (nat * nat * (nat -> bool))) (acc:nat -> bool) (pos:nat) :=
    match al with [] => (acc,pos)
         | (a::bl) => con_nor_list bl (merge_funs acc (con_nor a) pos) (pos + (snd (fst a)) - (fst (fst a)))
    end.

Definition get_nor_list (al: list (var* nat*nat)) (l:tpred) :=
    match find_nor_env_list al l with None => None | Some bl => Some (con_nor_list bl allfalse 0) end.
*)

Definition is_nor (t: list type_pred) := 
  fold_left (fun a b => a && 
       match b with | [THT n p (TNor b)] => true | _ => false end) t true.


Fixpoint get_var_list (x:var) (l:list (var * nat * nat)) := 
   match l with [] => None
         | ((y,lb,rb)::xl) => if x =? y then Some ((x,lb,rb),xl) 
                        else match get_var_list x xl with None => None
                                 | Some (a,bl) => Some (a,(y,lb,rb)::bl)
                             end
   end.

Definition form_session (qenv: var -> nat) (x:var) (i:nat) (l:list (var * nat * nat)) :=
    match get_var_list x l with None => if i =? 0 then Some ((x,0,1)::l)
                                 else if i+1 =? (qenv x) then Some ((x,i,qenv x)::l)
                                 else None
                  | Some ((y,lb,rb),xl) => if i =? rb then Some ((x,lb,rb+1)::xl)
                                            else if i +1 =? lb then Some ((x,i,rb)::xl)
                                 else None
    end.

Definition var_list (t:tpred) := List.fold_left (fun a b => a ++ fst b) t [].

Definition ses_elem_eq  (x y : var * nat * nat) :=
  ((fst (fst x)) =? (fst (fst y))) && ((snd (fst x)) =? (snd (fst y))) && (snd x =? snd y).

Fixpoint eq_session_elem_nor (x:var * nat * nat) (b:list se_type) (l:tpred) :=
   match l with [] => True
        | (([y],c)::xs) => if ses_elem_eq x y then (b = c) else eq_session_elem_nor x b xs
        | (_::xs) => eq_session_elem_nor x b xs
   end.

Fixpoint eq_session (l1 l2: tpred) := 
   match l1 with (([a],b)::xl) => eq_session_elem_nor a b l2 /\ eq_session xl l2
               | [] => True
               | (_::_) => False
   end.


Fixpoint collect_gphase (t:tpred) (rmax:nat) := 
   match t with [] => Some allfalse
          | ((x,[THT n (Some p) a])::tl) => match collect_gphase tl rmax with None => None
                                              | Some pa => Some (n_rotate pa p rmax)
                                         end
          | _ => None
   end.

Definition merge_funs (a:nat -> bool) (b:nat-> bool) (pos:nat) :=
         fun x => if x <=? pos then a x else b x.

Fixpoint collect_base_aux (tl:list se_type) (pos:nat) (acc: nat -> bool) := 
   match tl with [] => (acc,pos)
       | (THT n b (TNor r))::xs => collect_base_aux xs (pos+n) (merge_funs acc r pos)
       | _::xs => collect_base_aux xs pos acc
   end.

Check collect_base_aux.

Fixpoint collect_bases' (t:tpred) (pos:nat) (acc:nat -> bool) := 
   match t with [] => (acc,pos)
        | ((x,tl)::xs) => match collect_base_aux tl pos acc with (newacc,newpos)
               => collect_bases' xs newpos newacc 
              end
   end.
Definition collect_bases t := collect_bases' t 0 allfalse.

Definition level_down {A} (a :option (list A)) := match a with None => None | Some (a::l) => Some a | Some nil => None end.

Definition is_distr (t:list se_type) :=  
   match t with | (THT n a (EN b c d TDistr))::xs => True
       | _ => False
   end.

Fixpoint get_session_num (l:list (var * nat * nat)) :=
 match l with [] => 0
       | (x,lb,rb)::xs => rb-lb+(get_session_num xs)
 end.

Inductive session_system {qenv: var -> nat} {env:aenv} {rmax:nat} 
            : atype -> stack -> tpred -> pexp -> stack -> tpred -> Prop :=
    | skip_type : forall m S T, session_system m S T PSKIP S nil
    | assign_type : forall m S T a v v', eval_aexp_c S v = Some v' -> session_system m S T (Assign a v) (AEnv.add a v' S) nil
    | classic_type_nor : forall m S T e l vl tl, eval_varia_list qenv S l = Some vl -> 
                 find_nor_env_list vl T = Some tl -> session_system m S T (Classic e l) S tl
    | if_q_nor_1 : forall m S T S' T' T'' b e x y v pa tl pos,
       type_bexp env b (Q,[Index x y]) -> AEnv.MapsTo y v S
       -> session_system m S T e S' T' -> is_nor (snd (List.split T')) = true -> find_nor_env_list (var_list T') T = Some T''
        -> eq_session T' T'' -> collect_gphase T' rmax = pa -> find_env (x,v,v+1) T = Some (tl,pos)  -> is_had tl pos
         -> session_system m S T (If b e) S' (add_phase_env T (x,v,v+1) pa rmax)
    | if_q_nor_2 : forall m S T S' T' T'' b e x y v pa gp rank loc l len left_f right_f,
       type_bexp env b (Q,[Index x y]) -> AEnv.MapsTo y v S -> session_system m S T e S' T' -> is_nor (snd (List.split T')) = true
        -> find_nor_env_list (var_list T') T = Some T'' -> is_nor (snd (List.split T'')) = true -> ~ eq_session T' T''
         -> collect_gphase T' rmax = pa -> find_env_gen (x,v,v+1) T = Some (THT 1 gp (TH rank loc))
          -> collect_bases T = (right_f,len) -> collect_bases T'' = (left_f,len) -> form_session qenv x v (var_list T') = Some l 
          -> session_system m S T (If b e) S' 
      (add_phase_env ([(l,[THT (len+1) gp (EN 2 rank (level_down loc) (TMore (left_f::(right_f::nil))))])]) (x,v,v+1) pa rmax)
   | distr_type_1: forall m S T T' x l, find_nor_env_list ([(x,0,qenv x)]) T = Some T' -> 
           session_system m S T (Distr x l) S ([([(x,0,qenv x)],([THT (qenv x) None (EN (2^(qenv x)) None None TDistr)]))])
   | distr_type_2: forall m S T tl pos x l, find_env ((x,0,qenv x)) T = Some (tl,pos) -> is_distr tl ->
           session_system m S T (Distr x l) S ([([(x,0,qenv x)],([THT (qenv x) None (EN (2^(qenv x)) None None TDistr)]))])
   | qwhile_type : forall m S S' T T' T'' n x i b e gp rank loc, type_aexp env b (Q,[Var x]) 
        -> session_system m S T e S' T' -> is_nor (snd (List.split T')) = true
        -> find_nor_env_list (var_list T') T = Some T'' -> is_nor (snd (List.split T'')) = true -> ~ eq_session T' T''
         -> find_env_gen (x,0,qenv x) T = Some (THT 1 gp (TH rank loc)) ->
       session_system m S T (QWhile n x i (BTest (BA (Var i)) b) e) S'
          [((x,0,qenv x)::(var_list T'),[(THT (get_session_num ((x,0,qenv x)::(var_list T'))) None (EN (2^(qenv x)) None None TDistr))])].

