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

(* Ethan: above can be automatically generated as follows: *)
Scheme Equality for atype.
Print atype_beq.
Check atype_eq_dec.

Notation "i '=a=' j" := (aty_eq i j) (at level 50).

(* Ethan: I think a couple of these lemmas aren't necessary...
 * We can just use atype_eq_dec, right? *)
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


Inductive aexp := BA (x:varia) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | ASum (i:var) (n:aexp) (e:aexp).

Inductive bexp := | BEq (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp) | BTest (i:aexp) (a:aexp).


(* Define the ground term type system 
Inductive type_rotation := TV (b:aexp) | Infty.
*)

Inductive type_cfac := TMore (n:nat) (al:nat -> rz_val) | TDistr.

Inductive type_phase := Infy | Uni.

(*| Uni (b: nat -> rz_val) | DFT (b: nat -> rz_val). *)

Inductive type_elem : Type := TNor (p : (rz_val))
         | TH (r:type_phase)
         | EN (r:type_phase) (t:type_cfac).

Inductive se_type : Type := THT (n:nat) (t:type_elem).

Definition type_pred := se_type.

(* Ethan: I don't remember what is this tuple... *)
Definition tpred := list (list (var * nat * nat) * se_type).

Inductive pexp := PSKIP | Assign (x:var) (n:aexp) 
              (*| InitQubit (p:posi) *) 
              (* Ethan: Init = reset = trace out = measurement... commeneted out *)
            | AppU (e:singleGate) (p:varia)
            | PSeq (s1:pexp) (s2:pexp)
            | If (x:bexp) (s1:pexp)
            | IfB (x:bexp) (s1:pexp) (s2:pexp)
            | While (b:bexp) (p:pexp) (l: list (list varia * se_type))
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
            | Distr (x:var) (*reflection on x = a_1 ,... x = a_n in al with equal probablity hadamard walk. 
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

(* Ethan: Maybe same deal as before? *)
Scheme Equality for varia.
Print varia_eq_dec.

(* Ethan: This looks suspicious *)
Fixpoint merge_var (x: varia) (yl:list varia) :=
   match yl with [] => []
           | a::al => if vari_eq x a then a::al else a::(merge_var x al)
   end.

(* Ethan: Let's see... *)
Lemma bad : forall x y, merge_var x y = y.
Proof.
  induction y.
  + reflexivity.
  + case_eq (vari_eq x a); simpl.
    - intro H; rewrite H; reflexivity.
    - intro H; rewrite H; rewrite IHy; reflexivity.
Qed.

Definition merge_vars (xl yl: list varia) := List.fold_left (fun acc b => merge_var b acc) xl yl.

Definition meet_avtype (t1 t2: atype * list varia) :=
        match t1 with (a, xl) => match t2 with (b,yl) => 
         match meet_atype a b with None => None | Some a' => Some (a', merge_vars xl yl) end end end.

(*
Definition right_av (t1: atype * list varia) :=  match t1 with (C,xl) => length xl = 0 | (Q,xl) => length xl = 1 end.
*)

Inductive type_vari : aenv -> varia -> atype -> Prop :=
   | var_type : forall env x t, AEnv.MapsTo x t env -> type_vari env (Var x) t
   | index_type : forall env x v, AEnv.MapsTo x Q env -> AEnv.MapsTo v C env -> type_vari env (Index x v) Q.

Inductive type_aexp : aenv -> aexp -> atype -> Prop :=
     ba_type : forall env b t, type_vari env b t -> type_aexp env (BA b) t
   | num_type : forall env n, type_aexp env (Num n) C
   | plus_type : forall env e1 e2 t1 t2 t3, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  meet_atype t1 t2 = Some t3 -> 
                     type_aexp env (APlus e1 e2) t3
   | sum_type : forall env e i n t, 
                   type_aexp env n C -> type_aexp (AEnv.add i C env) e t -> 
                     type_aexp env (ASum i n e) t.

Definition list_subset (al bl :list var) := (forall x, In x al -> In x bl).

Definition get_var (x : varia) := match x with Var a => a | Index b y => b end.

Definition get_core_vars (al : list varia) := map (fun a => match a with Var x => x | Index x xl => x end) al.

(* Ethan: Why not just this? *)
Definition get_core_vars' (al : list varia) := map get_var al.

(* Ethan: Sanity check *)
Lemma get_core_vars'_correct : get_core_vars = get_core_vars'.
Proof.
  apply functional_extensionality.
  intro al.
  unfold get_core_vars, get_core_vars', get_var; reflexivity.
Qed.

Inductive type_vari_list_q : aenv -> list varia -> Prop :=
     type_aexp_empty : forall env, type_vari_list_q env []
   | type_aexp_many : forall env x xs, type_vari env x Q -> type_vari_list_q env xs -> type_vari_list_q env (x::xs).

Inductive type_aexp_list_c : aenv -> list aexp -> Prop :=
     type_aexp_empty_c : forall env, type_aexp_list_c env nil
   | type_aexp_many_c : forall env x xs, type_aexp env x C -> type_aexp_list_c env xs -> type_aexp_list_c env (x::xs).

Inductive type_bexp : aenv -> bexp -> atype  -> Prop :=
   |  beq_type : forall env e1 e2 t1 t2 t3, type_aexp env e1 t1 -> type_aexp env e2 t2 ->
             meet_atype t1 t2 = Some t3 -> type_bexp env (BEq e1 e2) t3
   | blt_type : forall env e1 e2 t1 t2 t3, type_aexp env e1 t1 -> type_aexp env e2 t2 ->
             meet_atype t1 t2 = Some t3 -> type_bexp env (BLt e1 e2) t3
   | btest_type : forall env e1 e2, type_aexp env (BA (Var e1)) Q -> type_aexp env e2 C 
            -> type_bexp env (BTest (BA (Var e1)) e2) Q.

Definition pre_tenv (l:list var) (env:env) := forall x, In x l -> Env.MapsTo x Nor env.


Definition join_two_ses (a:(var * nat * nat)) (b:(var*nat*nat)) :=
   match a with (x,n1,n2) => 
      match b with (y,m1,m2) => 
            if x =? y then (if n1 <=? m1 then 
                               (if n2 <? m1 then None
                                else if n2 <? m2 then Some (x,n1,m2)
                                else Some(x,n1,n2))
                            else if m2 <? n1 then None
                            else if n2 <? m2 then Some (x,m1,m2)
                            else Some (x,m1,n2))
            else None
     end
   end.

Fixpoint join_ses_aux (a:(var * nat * nat)) (l:list ((var * nat * nat))) :=
     match l with [] => ([a])
           | (x::xs) => match join_two_ses a x with None => x::join_ses_aux a xs
                                         | Some ax => ax::xs
                        end
     end.

Fixpoint join_ses (l1 l2:list ((var * nat * nat))) :=
    match l1 with [] => l2
               | x::xs => join_ses_aux x (join_ses xs l2)
   end.

Definition varia_ses (qenv:var -> nat) (s:stack) (v:varia) :=
   match v with Var x => Some ([(x,0,qenv x)])
           | Index x v => match AEnv.find v s with None => None 
                                | Some n => Some ([(x,n,n+1)])
                          end
   end.

Fixpoint varia_sess (qenv:var -> nat) (s:stack) (vl:list varia) :=
   match vl with [] => Some nil
             | x::xs => match varia_ses qenv s x with None => None
                         | Some x' =>
                        match varia_sess qenv s xs with None => None
                          | Some xs' => Some (x'++xs')
                        end
                        end
   end.

Fixpoint var_in_list (x:var) (l:list var) :=
  match l with nil => false
            | y::xs => if x =? y then true else var_in_list x xs
  end.

Fixpoint aexp_ses' (qenv:var -> nat) (l:list var) (s:stack) (v:aexp) :=
   match v with BA (Var x) => if var_in_list x l then None else varia_ses qenv s (Var x)
           | BA a => varia_ses qenv s a
           | Num n => Some nil
          | APlus x y => match aexp_ses' qenv l s x with None => None
                                       | Some l1 =>
                           match aexp_ses' qenv l s y with None => None
                                       | Some l2 => Some (join_ses l1 l2)
                           end
                         end
          | ASum i n y => match aexp_ses' qenv l s n with None => None
                                       | Some l1 =>
                           match aexp_ses' qenv (i::l) s y with None => None
                                       | Some l2 => Some (join_ses l1 l2)
                           end
                         end
   end.
Definition aexp_ses (qenv:var -> nat) (s:stack) (v:aexp) := aexp_ses' qenv nil s v.

Definition bexp_ses (qenv:var -> nat) (s:stack) (v:bexp) :=
   match v with BEq x y => match aexp_ses qenv s x with None => None
                                       | Some l1 =>
                           match aexp_ses qenv s y with None => None
                                       | Some l2 => Some (join_ses l1 l2)
                           end
                         end
             | BLt x y => match aexp_ses qenv s x with None => None
                                       | Some l1 =>
                           match aexp_ses qenv s y with None => None
                                       | Some l2 => Some (join_ses l1 l2)
                           end
                         end

             | BTest x y => match aexp_ses qenv s x with None => None
                                       | Some l1 =>
                           match aexp_ses qenv s y with None => None
                                       | Some l2 => Some (join_ses l1 l2)
                           end
                         end
   end.


(* Type system for oqasm. *)
Definition bits := list bool.

Definition tenv := (var -> (rz_val * rz_val)). 
    (* varaible -> global phase rz_val : nat -> bool (nat), nat -> bool (nat) |0010101> *)


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

Definition eval_vari_c (s:stack) (a:varia) :=
  match a with Var x => AEnv.find x s | Index x v => None end.

Check Nat.recursion.

Fixpoint eval_aexp_c (s:stack) (a:aexp) :=
   match a with BA x => eval_vari_c s x | Num n => Some n
    | APlus e1 e2 =>
        match eval_aexp_c s e1 with None => None | Some n1 => 
            match eval_aexp_c s e2 with None => None | Some n2 => Some (n1+n2)
            end
        end
    | ASum i n e =>
        match eval_aexp_c s n with None => None | Some n1 => 
             Nat.recursion (Some 0) (fun v a => match a with None => None
                                        | Some result => 
                                           match eval_aexp_c (AEnv.add i v s) e 
                                  with None => None
                                     | Some n2 => Some (result +n2)
                                           end
                                            end) n1 
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

Fixpoint in_sessions (al: list (var* nat*nat)) (l:list (var*nat*nat)) :=
  match al with [] => true
        | b::bl => match in_session b l 0 with None => false | Some pos => in_sessions bl l end
  end.


Definition atype_order (a:atype) (b:atype) :=
   match a with C => True | M => if b =a= C then False else True | Q => if b =a= Q then True else False end.

Fixpoint find_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,tl)::xl) => match in_session a x 0 with None => find_env a xl 
                                       | Some pos => Some (tl,pos)
                                  end
   end.

Fixpoint find_nor_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,THT n (TNor r))::xl) => match in_session a x 0 with None => find_nor_env a xl 
                                       | Some pos => Some (pos,r)
                                  end
           | (_,_)::xl => find_nor_env a xl
   end.

Fixpoint merge_num (l:list (var * nat * nat)) :=
   match l with [] => 0
         | (x,n1,n2)::xs => (n2 - n1)+(merge_num xs)
   end.

Fixpoint merge_nors' (t:tpred) (num:nat) (acc:nat -> bool) :=
  match t with [] => Some (num,acc)
         | (xl,THT n (TNor r))::xs => 
               merge_nors' xs (num+n) (fun i => if i <? num then acc i else 
                                   if (num <=? i) && (i <? num + n) then r i else false)
         | _ => None
  end.
Definition merge_nors (t:tpred) := merge_nors' t 0 allfalse.

Definition create_ch (t1 t2:tpred) (v:(var * nat * nat)) (a:se_type) :=
   match merge_nors t1 with None => None
          | Some (n,t1')  => 
     match merge_nors t2 with None => None
          | Some (n',t2') => 
         match a with THT m t => 
           Some ([(v::fold_left (fun a b => a ++ fst b) t1 [],
              THT (m + n) (EN Uni (TMore 2 (fun i => if i =? 0 then t1' else if i =? 1 then t2' else allfalse))))])
         end
     end
   end.

Definition to_ch (n:nat) (a1 a2: nat) := 
       THT n (EN Infy (TMore 2 (fun i => if i =? 0 then (nat2fb a1) else if i =? 1 then (nat2fb a2) else allfalse))).

Definition to_ch_distr (n:nat) := 
       THT n (EN Infy (TMore (2^n) (fun i => if i <? 2^n then (nat2fb i) else allfalse))).


Definition con_nor (a:nat) (b:nat) (f:nat -> bool) := cut_n (lshift_fun f a) b.

Fixpoint find_nor_env_list (al: list (var* nat*nat)) (l:tpred) :=
    match al with [] => Some nil
       | (a::bl) => match find_nor_env a l with None => None
                  | Some (pos,r) => 
               match find_nor_env_list bl l with None => None
                  | Some xl => Some (([a],THT ((snd a) - (snd (fst a))) (TNor (con_nor pos (snd a- (snd (fst a))) r)))::xl)
                   end
              end
    end.

Definition lshift_fun_gen {A:Type} (f:nat -> A) (n:nat) := fun i => f (i+n).

Definition all2false (x y : nat) := false.

Definition cut_n_gen (f:nat -> nat -> bool) (n:nat) := fun i => if i <? n then f i else all2false i.

Definition con_nor_phase (a:nat) (b:nat) (f:nat -> rz_val) := cut_n_gen (lshift_fun_gen f a) b.

Fixpoint find_had_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,THT n (TH r))::xl) => match in_session a x 0 with None => find_had_env a xl 
                                       | Some pos => Some (pos,r)
                                  end
           | (_,_)::xl => find_had_env a xl
   end.

Fixpoint find_had_env_list (al: list (var* nat*nat)) (l:tpred) :=
    match al with [] => Some nil
       | (a::bl) => match find_had_env a l with None => None
                  | Some (pos,Infy) => 
               match find_had_env_list bl l with None => None
                  | Some xl => Some (([a],THT ((snd a) - (snd (fst a))) (TH Infy))::xl)
                   end
                  | Some (pos,Uni) => 
               match find_had_env_list bl l with None => None
                  | Some xl => Some (([a],THT ((snd a) - (snd (fst a))) (TH Uni))::xl)
                   end
              end
    end.

Fixpoint find_ch_env (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,THT n (EN r b))::xl) => match in_session a x 0 with None => find_ch_env a xl 
                                       | Some pos => Some (pos,r)
                                  end
           | (_,_)::xl => find_ch_env a xl
   end.
(*
Fixpoint find_ch_env_list (al: list (var* nat*nat)) (l:tpred) :=
    match al with [] => Some nil
       | (a::bl) => match find_had_env a l with None => None
                  | Some (pos,Infy) => 
               match find_had_env_list bl l with None => None
                  | Some xl => Some (([a],THT ((snd a) - (snd (fst a))) (TH Infy))::xl)
                   end
                  | Some (pos,Uni) => 
               match find_had_env_list bl l with None => None
                  | Some xl => Some (([a],THT ((snd a) - (snd (fst a))) (TH Uni))::xl)
                   end
              end
    end.
*)

(* turn a qubit to phase. *)
Definition turn_nor_to_had_phase (r:rz_val) := fun x => if r x then rotate allfalse 1 else allfalse.

Fixpoint turn_nor_to_had (l:tpred) :=
   match l with [] => Some nil
           | ((x,THT n (TNor r))::xs) => 
         match turn_nor_to_had xs with None => None
             | Some xs' => Some ((x,THT n (TH Uni))::xs')
         end
          | _ => None
   end.

Fixpoint nat_recursion {A:Type} (change: (nat -> A) -> nat -> nat -> A) (f:nat -> A) (n:nat) :=
   match n with 0 => f
           | S m => nat_recursion change (change f m) m
   end.

Fixpoint turn_apply_x_nor (l:tpred) :=
   match l with [] => Some nil
           | ((x,THT n (TNor r))::xs) => 
         match turn_apply_x_nor xs with None => None
             | Some xs' => Some ((x,THT n (TNor (nat_recursion flip_i r n)))::xs')
         end
          | _ => None
   end.

Inductive th_nor_aux : (list (var * nat * nat) * se_type) ->  (list (var * nat * nat) * se_type) -> Prop :=
   th_nor_aux_infy : forall x n, th_nor_aux (x,THT n (TH Infy)) (x,THT n (TH Infy))
  | th_nor_aux_uni : forall x n , th_nor_aux (x,THT n (TH (Uni))) (x,THT n (TNor allfalse)).

Inductive turn_had_to_nor : tpred -> tpred -> Prop :=
   turn_had_to_nor_empty : turn_had_to_nor nil nil
  | turn_had_to_nor_many : forall x xs y ys, th_nor_aux x y -> turn_had_to_nor xs ys -> turn_had_to_nor (x::xs) (y::ys).

Fixpoint turn_apply_x_had (l:tpred) :=
   match l with [] => Some nil
           | ((x,THT n (TH Infy))::xs) => 
         match turn_apply_x_had xs with None => None
             | Some xs' => Some ((x,THT n ((TH Infy)))::xs')
         end
           | ((x,THT n (TH (Uni)))::xs) => 
         match turn_apply_x_had xs with None => None
             | Some xs' => Some ((x,THT n ((TH (Infy))))::xs')
         end
          | _ => None
   end.


(*prepare for oqasm_type *)
Fixpoint update_qenv (qenv: var-> nat) (l:list (var * nat * nat)) :=
  match l with [] => qenv
       | (x,n1,n2)::xs => update_qenv (update qenv x n2) xs
  end.

Definition tenv_base := fun (x:var) => (allfalse,allfalse).

Fixpoint tenv_create (l:tpred) :=
   match l with [] => Some tenv_base
        | ([(x,n1,n2)],THT n (TNor r))::xs => 
              match tenv_create xs with None => None
                | Some f => Some (update f x (allfalse,r))
              end
        | _ => None
    end.

Fixpoint tpred_nor_create (l:tpred) (tenv: (var -> (rz_val * rz_val))) :=
   match l with [] => Some nil
        | ([(x,n1,n2)],THT n (TNor r))::xs => 
              match tpred_nor_create xs tenv with None => None
                | Some xs' => 
                 match tenv x with (pha,ra) =>
                          Some (([(x,n1,n2)],THT n (TNor ra))::xs')
                 end
              end
        | _ => None
   end.

Fixpoint find_env_had (a: (var* nat*nat)) (l:tpred) :=
   match l with [] => None
           | ((x,tl)::xl) => match in_session a x 0 with None => find_env_had a xl 
                             | Some pos => match tl with (THT n (TH r)) 
                                   => Some (THT n (TH r)) | _ => find_env_had  a xl
                                          end
                              end
   end.
                                  
Definition is_nor (t: tpred) := 
  fold_left (fun a b => a && 
       match b with | (x,THT n (TNor b)) => true | _ => false end) t true.

Fixpoint is_had' (t:list se_type) (pos:nat) (acc:nat) := 
  match t with [] => False
        | ((THT n (TH r))::xs) => 
          if (acc <=? pos) && (pos <? n + acc) then True else is_had' xs pos (acc+n)
       | _ => False
  end.
Definition is_had_a (t: se_type) := match t with THT n (TH r) => True | _ => False end.

Definition is_had (t:tpred) := Forall (fun a => match a with (b,ta) => is_had_a ta end) t.

(*
Definition is_ch (t:tpred) := match t with [(a,[THT n r (EN m rb b ts)])] => True | _ => False end.
*)
(* session type *)

Inductive session_system {qenv: var -> nat} {env:aenv}
           : atype -> stack -> tpred -> pexp -> stack -> tpred -> Prop :=
    | skip_ses : forall m stack T, session_system m stack T (PSKIP) stack nil
    | assign_ses_c : forall m a v v' stack T, AEnv.MapsTo a C env -> type_aexp env v C
             -> eval_aexp_c stack v = Some v' -> session_system m stack T (Assign a v) (AEnv.add a v' stack) nil
    | assign_ses_m : forall m a v stack T, AEnv.MapsTo a M env -> type_aexp env v M
             -> session_system m stack T (Assign a v) stack nil
    | appu_ses_h_nor : forall m env p stack a T T' T'',  type_vari env p Q -> varia_ses qenv stack p = Some ([a]) ->
                 find_nor_env_list ([a]) T = Some T' -> turn_nor_to_had T' = Some T'' 
                  -> session_system m stack T (AppU H_gate p) stack T''
    | appu_ses_h_had : forall m env p stack a T T' T'',  type_vari env p Q -> varia_ses qenv stack p = Some ([a]) ->
                 find_had_env_list ([a]) T = Some T' -> turn_had_to_nor T' T'' 
                  -> session_system m stack T (AppU H_gate p) stack T''
    | appu_ses_x_nor : forall m env p stack a T T' T'',  type_vari env p Q -> varia_ses qenv stack p = Some ([a]) ->
                 find_nor_env_list ([a]) T = Some T' -> turn_apply_x_nor T' = Some T'' 
                  -> session_system m stack T (AppU X_gate p) stack T''
    | appu_ses_x_had : forall m env p stack a T T' T'',  type_vari env p Q -> varia_ses qenv stack p = Some ([a]) ->
                 find_had_env_list ([a]) T = Some T' -> turn_had_to_nor T' T'' 
                  -> session_system m stack T (AppU X_gate p) stack T''
    | class_ses_nor : forall m stack e l l' tenv T T' T'' tv tv',
          pre_tenv (get_vars e) tenv -> well_typed_oexp qenv tenv e tenv ->  exp_WF qenv e ->
          type_vari_list_q env l -> varia_sess qenv stack l = Some l' -> find_nor_env_list l' T = Some T' 
       -> tenv_create T' = Some tv -> @oqasm_type (update_qenv qenv l') tv e tv' -> tpred_nor_create T' tv' = Some T''
              -> session_system m stack T (Classic e l) stack T''
    | qif_ses_same : forall m stack stack' b e l a T t,
         type_bexp env b Q -> bexp_ses qenv stack b = Some ([a]) -> in_session a l 0 = None ->
         session_system Q stack T e stack' T -> find_env_had a T = Some t
         -> session_system m stack T (If b e) stack (([a],t)::T)
    | qif_ses : forall m stack stack' b e l a T T' T'' t,
         type_bexp env b Q -> bexp_ses qenv stack b = Some ([a]) -> in_session a l 0 = None ->
         session_system Q stack T e stack' T' -> is_nor T = true -> find_env_had a T = Some t -> is_nor T' = true -> T <> T'
         -> create_ch T T' a t = Some T'' -> session_system m stack T (If b e) stack T''
    | if_ses_true : forall m stack stack' b e1 e2 T T', type_bexp env b C -> eval_bexp_c stack b = Some true ->
                session_system Q stack T e1 stack' T' -> session_system m stack T (IfB b e1 e2) stack' T'
    | if_ses_false : forall m stack stack' b e1 e2 T T', type_bexp env b C -> eval_bexp_c stack b = Some false ->
                session_system Q stack T e2 stack' T' -> session_system m stack T (IfB b e1 e2) stack' T'
    | if_ses_m : forall m stack stack' b e1 e2 T T', type_bexp env b M -> session_system Q stack T e1 stack' T' ->
                session_system Q stack T e2 stack' T' -> session_system m stack T (IfB b e1 e2) stack' T'
    | pmea_ses : forall m stack q p a x T, AEnv.MapsTo a q env -> AEnv.MapsTo p M env -> atype_order q M ->
                 AEnv.MapsTo x Q env -> session_system m stack T (PMeas p x a) stack nil
    | mea_ses : forall m stack a x T, AEnv.MapsTo a M env ->  
                   AEnv.MapsTo x Q env -> session_system m stack T (Meas a x) stack nil
    | amplify_ses : forall m stack x n T T', AEnv.MapsTo x Q env -> type_aexp env n C 
                   -> find_had_env_list ([(x,0,qenv x)]) T = Some T' ->
                    session_system m stack T (Amplify x n) stack T'
    | reflect_ses_nor : forall m stack x p a1 a2 v1 v2 T T', AEnv.MapsTo x Q env -> type_aexp env p C -> type_aexp env a1 C
        -> type_aexp env a2 C -> find_nor_env_list ([(x,0,qenv x)]) T = Some T' -> 
        eval_aexp_c stack a1 = Some v1 -> eval_aexp_c stack a2 = Some v2 -> v1 <> v2 ->
        session_system m stack T (Reflect x p a1 a2) stack ([([(x,0,qenv x)],to_ch (qenv x) v1 v2)])
    | distr_ses_nor : forall m stack x p a1 a2 v1 v2 T T', AEnv.MapsTo x Q env -> type_aexp env p C -> type_aexp env a1 C
        -> type_aexp env a2 C -> find_nor_env_list ([(x,0,qenv x)]) T = Some T' -> 
        eval_aexp_c stack a1 = Some v1 -> eval_aexp_c stack a2 = Some v2 -> v1 <> v2 ->
        session_system m stack T (Reflect x p a1 a2) stack ([([(x,0,qenv x)],to_ch_distr (qenv x))]).
(*
    | while_ses : forall m stack b e T T' l, type_bexp env b C -> 
           (fold_left (fun a b => match a with None => None
                              | Some l => match eval_varia_list qenv stack (fst b) with None => None
                                       | Some l' => Some (l++[(l',snd b)])
                                          end
                                  end) l (Some nil)) = Some T' ->
                  session_system m stack T (While b e l) stack T'

    | qwhile_stype : forall m env n x x' i b e xl stack T, stype_pexp Q env e Q -> ~ list_subset ([x]) (get_core_vars xl) ->
              AEnv.MapsTo x Q env -> AEnv.MapsTo i C env -> type_bexp env b (Q,[x']) -> get_var x' = x ->
              session_system m env stack T (QWhile n x i b e) stack (Q,(Var x)::xl).

*)




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

(*
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


*)



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

(*
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
          
*)


(*
Definition merge_funs (a:nat -> bool) (b:nat-> bool) (pos:nat) :=
         fun x => if x <=? pos then a x else b x.

Fixpoint con_nor_list (al: list (nat * nat * (nat -> bool))) (acc:nat -> bool) (pos:nat) :=
    match al with [] => (acc,pos)
         | (a::bl) => con_nor_list bl (merge_funs acc (con_nor a) pos) (pos + (snd (fst a)) - (fst (fst a)))
    end.

Definition get_nor_list (al: list (var* nat*nat)) (l:tpred) :=
    match find_nor_env_list al l with None => None | Some bl => Some (con_nor_list bl allfalse 0) end.


Definition is_nor (t: list type_pred) := 
  fold_left (fun a b => a && 
       match b with | [THT n p (TNor b)] => true | _ => false end) t true.
*)

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

Fixpoint ses_elem_eq_list (x y: list (var * nat * nat)) (n:nat) :=
   match n with 0 => true
            | S m => match nth_error x m with Some a 
                         => match nth_error y m with Some b => (ses_elem_eq a b) && (ses_elem_eq_list x y m)
                                   | _ => false
                            end
                           | _ => false
                     end
   end.

Definition ses_elem_eq_l (x y: list (var * nat * nat)) :=
   (length x =? length y) && (ses_elem_eq_list x y (length x)).

Fixpoint eq_session_elem_nor (x:var * nat * nat) (b: se_type) (l:tpred) :=
   match l with [] => True
        | (([y],c)::xs) => if ses_elem_eq x y then (b = c) else eq_session_elem_nor x b xs
        | (_::xs) => eq_session_elem_nor x b xs
   end.

Fixpoint eq_session (l1 l2: tpred) := 
   match l1 with (([a],b)::xl) => eq_session_elem_nor a b l2 /\ eq_session xl l2
               | [] => True
               | (_::_) => False
   end.

(*
Fixpoint collect_gphase (t:tpred) (rmax:nat) := 
   match t with [] => Some allfalse
          | ((x,[THT n a])::tl) => match collect_gphase tl rmax with None => None
                                              | Some pa => Some (n_rotate pa rmax)
                                         end
          | _ => None
   end.
*)

Definition merge_funs (a:nat -> bool) (b:nat-> bool) (pos:nat) :=
         fun x => if x <=? pos then a x else b x.


Definition collect_base_aux (tl: se_type) (pos:nat) (acc: nat -> bool) := 
   match tl with  (THT n (TNor r)) => Some (merge_funs acc r pos, pos+n)
       | _ => None
   end.


Fixpoint collect_bases' (t:tpred) (pos:nat) (acc:nat -> bool) := 
   match t with [] => Some (acc,pos)
        | ((x,tl)::xs) => match collect_base_aux tl pos acc with Some (newacc,newpos)
               => collect_bases' xs newpos newacc 
                     | _ => None
              end
   end.
Definition collect_bases t := collect_bases' t 0 allfalse.

Definition level_down {A} (a :option (list A)) := match a with None => None | Some (a::l) => Some a | Some nil => None end.

Definition is_distr (t: se_type) :=  
   match t with | (THT n (EN r TDistr)) => True
       | _ => False
   end.

Fixpoint get_session_num (l:list (var * nat * nat)) :=
 match l with [] => 0
       | (x,lb,rb)::xs => rb-lb+(get_session_num xs)
 end.


(* Operation semantics. *)
Inductive cof := One | Div (n:nat) (n:nat) | CTimes (a:cof) (b:cof).


Inductive state := NTen (n:nat) (r:rz_val) (b: nat -> bool)
                 | HTen (n:nat) (r:rz_val) (p: nat -> rz_val)
                 | CTen (n:nat) (r:rz_val) (m:nat) (pl:list (rz_val * (nat -> bool))).

Definition heap := nat -> state.

Definition tpreds := list (list (var * nat * nat) * list se_type * nat).

Definition get_tpred (t:tpreds) := fst (List.split t).

Fixpoint update_session (ts:tpreds) (x:list (var * nat * nat)) (v: list se_type) :=
  match ts with [] => nil
      | (y,m,n)::xs => if ses_elem_eq_l x y then (y,v,n)::xs else (y,m,n)::(update_session xs x v)
  end.

Fixpoint get_ses_key (ts:tpreds) (x:list (var * nat * nat)) :=
   match ts with [] => None
      | (y,m,n)::xs => if ses_elem_eq_l x y then Some (m,n) else (get_ses_key xs x)
   end.

(*
Definition to_nor_state (l: list se_type) :=
  match l with [THT n (Some r) (TNor b)] => Some (NTen n r b) | _ => None end.

Definition update_nor (a:list (var * nat * nat) * list se_type) (ts:tpreds) (h:heap) :=
    match get_ses_key ts (fst a) with None => None
            | Some (t,n) => match to_nor_state t with None => None
                | Some v => Some (update_session ts (fst a) (snd a), update h n v)
                end
    end.

Fixpoint update_nor_l (al: tpred) (ts:tpreds) (h:heap) :=
    match al with [] => Some (ts,h)
          | (a::all) => match update_nor a ts h with None => None
                                  | Some (ts1,h1) => update_nor_l all ts1 h1
                       end
    end.

Fixpoint kill_sessions (t:tpreds) (l:list (var*nat*nat)) :=
   match t with [] => []
          | (x,tl,n)::xs => if in_sessions x l then kill_sessions xs l else (x,tl,n)::(kill_sessions xs l)
   end.

Definition gen_ch_tpreds (t:tpreds) (a:tpred) :=
   match a with [(l,ts)] => Some ((l,ts,(list_max (snd (List.split (kill_sessions t l)))+1))::(kill_sessions t l)
            ,(list_max (snd (List.split (kill_sessions t l)))+1),ts)
             | _ => None
   end.

Definition update_ch_heap (ts:tpreds) (h:heap) (a:tpred) :=
   match gen_ch_tpreds ts a with None => None
       | Some (tsa,n,t) => 
          match t with [THT n (Some r) (EN m (Some 1) (Some (r1::r2::nil)) (TMore (a1::a2::nil)))]
                => Some (tsa,update h n (CTen n r m ((r1,a1)::(r2,a2)::nil)))
             | _ => None
         end
   end.

Inductive pexp_sem  {qenv: var -> nat} {env:aenv} {rmax:nat} :
            atype -> tpreds -> stack -> heap -> pexp -> tpreds -> stack -> heap -> Prop :=
   | skip_sem : forall m T S R, pexp_sem m T S R PSKIP T S R
   | assign_sem : forall m T S S' R a v, 
       @session_system qenv env rmax m S (get_tpred T) (Assign a v) S' nil -> pexp_sem m T S R (Assign a v) T S' R
   | class_sem : forall m T T' S R R' e l tl, @session_system qenv env rmax m S (get_tpred T) (Classic e l) S tl -> 
             update_nor_l tl T R = Some (T',R') -> pexp_sem m T S R (Classic e l) T' S R'
   | if_h : forall m T T' S R R' b e ta pos tl x y v, 
             type_bexp env b (Q,[Index x y]) -> AEnv.MapsTo y v S ->
             find_env (x,v,v+1) (get_tpred T) = Some (ta,pos)  -> is_had ta pos -> is_ch tl ->
             @session_system qenv env rmax m S (get_tpred T) (If b e) S tl -> update_ch_heap T R tl = Some (T',R') ->
              pexp_sem m T S R (If b e) T' S R'.
*)


