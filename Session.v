Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QWhileSyntax.
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


(*
Inductive static_type := SPos (x:list vari) | SNeg (x:list vari).
*)
Inductive factor := AType (a:atype) | Ses (a:session).

Coercion AType : atype >-> factor.

Coercion Ses : session  >-> factor.

Module AEnv := FMapList.Make Nat_as_OT.
Module AEnvFacts := FMapFacts.Facts (AEnv).
Definition aenv := AEnv.t factor.
Definition empty_benv := @AEnv.empty atype.

Definition stack := AEnv.t nat.
Definition empty_stack := @AEnv.empty nat.

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


Definition union_f (t1 t2:factor) :=
   match t1 with AType a => match t2 with AType b => AType (meet_atype a b)
                                       | Ses b => Ses b
                            end
              | Ses a => match t2 with AType b => Ses a
                             | Ses b => Ses (join_ses a b)
                         end
   end.

Inductive type_aexp : aenv -> aexp -> factor -> Prop :=
   | ba_type : forall env b t, AEnv.MapsTo b t env -> type_aexp env b t
   | num_type : forall env n, type_aexp env n CT
   | plus_type : forall env e1 e2 t1 t2, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  
                     type_aexp env (APlus e1 e2) (union_f t1 t2)
   | mult_type : forall env e1 e2 t1 t2, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  
                     type_aexp env (AMult e1 e2) (union_f t1 t2).


Inductive type_vari : aenv -> varia -> factor -> Prop :=
   | aexp_type : forall env a t, type_aexp env a t -> type_vari env a t
   | index_type : forall env x a b v,
       AEnv.MapsTo x (Ses ([(x,a,b)])) env -> a <= v < b -> type_vari env (Index x (Num v)) (Ses ([(x,v,S v)]))
   | permu_type: forall env e t1 t2, Permutation t1 t2 -> type_vari env e (Ses t1) -> type_vari env e (Ses t2).


Inductive type_bexp : aenv -> bexp -> factor -> Prop :=
   | beq_type : forall env a b t1 t2 x v1 v2 v, type_vari env a t1 -> type_vari env b t2 ->
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BEq a b x (Num v)) (union_f (union_f t1 t2) (Ses ([(x,v,S v)])))
   | blt_type : forall env a b t1 t2 x v1 v2 v, type_vari env a t1 -> type_vari env b t2 ->
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BEq a b x (Num v)) (union_f (union_f t1 t2) (Ses ([(x,v,S v)])))
   | btest_type : forall env x v1 v2 v, 
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BTest x (Num v)) (Ses ([(x,v,S v)]))
   | bpermu_type: forall env e t1 t2, Permutation t1 t2 -> type_bexp env e (Ses t1) -> type_bexp env e (Ses t2).


Inductive type_exp (qenv : var -> nat) : aenv -> exp -> factor -> Prop :=
   | skip_fa : forall env x a, type_exp qenv env (SKIP x a) (Ses nil)
   | x_fa : forall env x v, type_exp qenv env (X x (Num v)) (Ses ([(x,v, S v)]))
   | rz_fa : forall env q x v, type_exp qenv env (RZ q x (Num v)) (Ses ([(x,v, S v)]))
   | rrz_fa : forall env q x v, type_exp qenv env (RRZ q x (Num v)) (Ses ([(x,v, S v)]))
   | sr_fa : forall env q x, type_exp qenv env (SR q x) (Ses ([(x,0, qenv x)]))
   | srr_fa : forall env q x, type_exp qenv env (SRR q x) (Ses ([(x,0, qenv x)]))
   | qft_fa : forall env q x, type_exp qenv env (QFT x q) (Ses ([(x,0, qenv x)]))
   | rqft_fa : forall env q x, type_exp qenv env (RQFT x q) (Ses ([(x,0, qenv x)]))
   | lft_fa : forall env x, type_exp qenv env (Lshift x) (Ses ([(x,0, qenv x)]))
   | rft_fa : forall env x, type_exp qenv env (Rshift x) (Ses ([(x,0, qenv x)]))
   | rev_fa : forall env x, type_exp qenv env (Rev x) (Ses ([(x,0, qenv x)]))
   | cu_fa : forall env x v e t1, type_exp qenv env e t1 ->
                 type_exp qenv env (CU x (Num v) e) (union_f (Ses ([(x,v, S v)])) t1)
   | seq_fa : forall env e1 t1 e2 t2, type_exp qenv env e1 t1 -> type_exp qenv env e2 t2 ->
                 type_exp qenv env (Seq e1 e2) (union_f t1 t2)
   | permu_fa: forall env e t1 t2, Permutation t1 t2 -> type_exp qenv env e (Ses t1) -> type_exp qenv env e (Ses t2).

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

Fixpoint find_env {t:Type} (l:ses_map t) (a: list (var* nat*nat)) :=
   match l with [] => None
           | ((x,tl)::xl) => if in_sessions a x then Some (x,tl) else find_env xl a
   end.

Fixpoint update_env {T:Type} (l:ses_map T) (a: list (var* nat*nat)) (t:T) :=
   match l with [] => ([(a,t)])
           | ((x,tl)::xl) => if in_sessions a x then (a,t)::xl else (x,tl)::(update_env xl a t) 
   end.

Definition gen_ses (qenv: var -> nat) (p:varia) :=
   match p with (AExp (BA x)) => Some (([(x,0,qenv x)]),qenv x)
             | Index x (Num n) => Some (([(x,n,n+1)]), 1)
             | _ => None
   end.

Definition in_ses (a: (var* nat*nat)) (b: (var*nat*nat)) :=
   match b with (x,lb,rb) =>
          (fst (fst a) =? x) && (lb <=? (snd (fst a))) && ((snd a) <=? rb) 
   end.

Fixpoint in_seses (a: (var* nat*nat)) (l: list (var*nat*nat)) :=
   match l with [] => false
           | b::bl => if in_ses a b then true else in_seses a bl
   end.

Fixpoint inter_ses (al: list (var* nat*nat)) (l:list (var*nat*nat)) :=
  match al with [] => false
      | b::bl => if in_seses b l then true else inter_ses bl l
  end.

Fixpoint remove_ses (s:session) (a: (var * nat * nat)) :=
   match s with [] => []
            | b::xl => if in_ses b a then xl else b::(remove_ses xl a)
   end.

Fixpoint find_ses_pos' (a: (var * nat * nat)) (l:session) (pos:nat) :=
   match l with [] => None
            | ((b,l,h)::xl) => if in_ses a (b,l,h) then Some (pos -l + (snd (fst a))) else find_ses_pos' a xl (pos + h - l)
   end.
Definition find_ses_pos (a: (var * nat * nat)) (l:session) :=
     match find_ses_pos' a l 0 with None => None
                    | Some pos => Some (pos, (snd a) - (snd (fst a)))
     end.


Definition remove_ses_env (env:aenv) (a:(var*nat*nat)) :=
 AEnv.map (fun f => match f with AType b => AType b | Ses b => Ses (remove_ses b a) end) env.

Inductive type_pexp (qenv : var -> nat) : aenv -> pexp -> factor -> Prop :=
  | pskip_fa: forall env, type_pexp qenv env (PSKIP) (Ses nil)
  | let_fa_1 : forall env x a e t1 t2, type_aexp env a (AType t1) ->
                   type_pexp qenv env e t2 -> type_pexp qenv env (Let x (AE a) t1 e) (union_f t1 t2)
  | let_fa_2 : forall env x y e t2, AEnv.MapsTo y (Ses ([(y,0,qenv y)])) env ->
                   type_pexp qenv (AEnv.remove y (remove_ses_env env (y,0,qenv y))) e t2 
                     -> type_pexp qenv env (Let x (Meas y) MT e) t2
  | appsu_fa_h: forall env a x lb rb,
          type_aexp env a (Ses ([(x,lb,rb)])) -> type_pexp qenv env (AppSU (RH a)) (Ses ([(x,lb,rb)]))
  | appsu_fa_qft: forall env x s, AEnv.MapsTo x (Ses s) env
             -> type_pexp qenv env (AppSU (SQFT x)) (Ses s)
  | appsu_fa_rqft: forall env x s, AEnv.MapsTo x (Ses s) env
             -> type_pexp qenv env (AppSU (SRQFT x)) (Ses s)
  | appu_fa: forall env e t, type_exp qenv env e (Ses t) -> type_pexp qenv env (AppU t e) (Ses t)
  | if_fa : forall env e b t1 t2, type_bexp env b t1 -> type_pexp qenv env e t2 -> type_pexp qenv env (If b e) (union_f t1 t2)
  | for_fa : forall env x l h b e t1 t2, type_aexp env l (AType CT) -> type_aexp env h (AType CT) -> 
                     type_bexp (AEnv.add x (AType CT) env) b t1 -> type_pexp qenv (AEnv.add x (AType CT) env) e t2
                     -> type_pexp qenv env (For x l h b e) (union_f t1 t2)
  | amplify_fa: forall env x n b s, type_aexp env n (AType b) -> AEnv.MapsTo x (Ses s) env -> 
                         type_pexp qenv env (Amplify x n) (Ses s)
  | diffuse_fa: forall env x s, AEnv.MapsTo x (Ses s) env -> type_pexp qenv env (Diffuse x) (Ses s)
  | permu_fa_p: forall env e t1 t2, Permutation t1 t2 -> type_pexp qenv env e (Ses t1) -> type_pexp qenv env e (Ses t2).


(* Ethan: This looks suspicious *)
(*
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
*)

(*
Definition right_av (t1: atype * list varia) :=  match t1 with (C,xl) => length xl = 0 | (Q,xl) => length xl = 1 end.
*)

(* Type system for oqasm. *)
Definition bits := list bool.

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

Fixpoint list_in (l:list var) (x:var) := match l with [] => false | (y::yl) => if x =? y then true else list_in yl x end.

Definition list_subset (al bl :list var) := (forall x, In x al -> In x bl).

Fixpoint oqasm_type (qenv: var -> nat) (tv:tenv) (e:exp) :=
   match e with SKIP x a => Some tv
              | (X x (Num v)) => Some (exchange tv (x,v))
              | (CU x (Num v) e) => if (snd (tv x)) v then oqasm_type qenv tv e else Some tv
              | (RZ q x (Num v)) => Some (up_phase tv x q)
              | (RRZ q x (Num v)) => Some (up_phase_r tv x q)
              | (SR n x) => Some (up_phase_phi tv x (S n))
              | (SRR n x) => Some (up_phase_phi_r tv x (S n))
              | (QFT x b) => Some tv
              | RQFT x b => Some tv
              | Seq s1 s2 => match oqasm_type qenv tv s1 with Some tv1 => oqasm_type qenv tv1 s2 | _ => None end
              | _ => None
   end.

(* assume that in a session, all variables are distinct. *)
Definition lshift_fun {A:Type} (f:nat -> A) (n:nat) := fun i => f (i+n).

Definition split_rval (r:rz_val) (i:nat) (n:nat) := cut_n (lshift_fun r i) n.

Definition combine_tenv (tv:tenv) (r:rz_val) (x:var) (i:nat) (n:nat)
    := fun y => if x =? y then 
                  match tv x with (phase,base) 
                    => (phase, fun t => if (i <=? t) && (t <? n) then r t else base t) end
                 else tv y.

Definition init_tenv : tenv := fun _ => (allfalse, allfalse).

Fixpoint gen_tenv' (r:rz_val) (l:list (var * nat * nat)) (index:nat) :=
   match l with [] => init_tenv
        | ((x,n,m)::xl) => combine_tenv (gen_tenv' r xl (index+m-n)) (split_rval r index (m-n)) x n m
   end.
Definition gen_tenv (r:rz_val) (l:session) := gen_tenv' r l 0.

Fixpoint n_rotate (r :rz_val) (q:rz_val) (n:nat) := 
   match n with 0 => r | S m => if q m then n_rotate (rotate r n) q m else n_rotate r q m end.



Fixpoint trans_tenv' (tv:tenv) (l:list (var * nat * nat)) (rmax:nat) (index:nat) :=
   match l with [] => (allfalse, allfalse)
           | ((x,n,m)::xl) =>
            match tv x with (phase,base) => 
              match trans_tenv' tv xl rmax (index + (m-n))
                with (p1,b1) => (n_rotate phase p1 rmax, fun i =>
                           if (index <=? i) && (i <? index + m - n)
                           then base (i - index + m) else b1 i)
              end
           end
   end.
Definition trans_tenv (tv:tenv) (l:session) (rmax:nat) := trans_tenv' tv l rmax 0.


Fixpoint subst_aexp (a:aexp) (x:var) (n:nat) :=
    match a with BA y => if x =? y then Num n else BA y
              | Num a => Num a
              | APlus c d => match ((subst_aexp c x n),(subst_aexp d x n)) with (Num q, Num t) =>  Num (q+t)
                                | _ => APlus (subst_aexp c x n) (subst_aexp d x n) 
                             end
              | AMult c d => match ((subst_aexp c x n),(subst_aexp d x n)) with (Num q, Num t) =>  Num (q*t)
                                | _ => AMult (subst_aexp c x n) (subst_aexp d x n) 
                             end
    end.


Definition subst_varia (a:varia) (x:var) (n:nat) :=
   match a with AExp b => AExp (subst_aexp b x n)
              | Index x v => Index x (subst_aexp v x n)
   end. 


Definition subst_bexp (a:bexp) (x:var) (n:nat) :=
    match a with BEq c d i e => BEq (subst_varia c x n) (subst_varia d x n) i (subst_aexp e x n)
              | BLt c d i e => BEq (subst_varia c x n) (subst_varia d x n) i (subst_aexp e x n)
              | BTest i e => BTest i (subst_aexp e x n)
    end.

Fixpoint subst_exp (e:exp) (x:var) (n:nat) :=
        match e with SKIP y a => SKIP y (subst_aexp a x n)
                   | X y a => X y (subst_aexp a x n) 
                   | CU y a e' => CU y (subst_aexp a x n) (subst_exp e' x n)
                   | RZ q y a => RZ q y (subst_aexp a x n)
                   | RRZ q y a => RRZ q y (subst_aexp a x n)
                   | SR q y => SR q y
                   | SRR q y => SRR q y
                   | Lshift x => Lshift x
                   | Rshift x => Rshift x
                   | Rev x => Rev x
                   | QFT x b => QFT x b
                   | RQFT x b => RQFT x b
                   | Seq s1 s2 => Seq (subst_exp s1 x n) (subst_exp s2 x n)
        end.

Definition subst_mexp (e:maexp) (x:var) (n:nat) :=
   match e with AE a => AE (subst_aexp a x n)
              | Meas y => Meas y
   end.

Check List.fold_right.
Fixpoint subst_pexp (e:pexp) (x:var) (n:nat) :=
        match e with PSKIP => PSKIP
                   | Let y a t e' => if y =? x then Let y (subst_mexp a x n) t e' else Let y (subst_mexp a x n) t (subst_pexp e' x n)
                   | AppSU (RH v) => AppSU (RH (subst_varia v x n))
                   | AppSU p => AppSU p
                   | AppU l e' => AppU l (subst_exp e' x n)
                   | If b s => If (subst_bexp b x n) (subst_pexp s x n)
                   | For i l h b p => if i =? x then For i (subst_aexp l x n) (subst_aexp h x n) b p
                                      else For i (subst_aexp l x n) (subst_aexp h x n) (subst_bexp b x n) (subst_pexp p x n)
                   | Amplify y a => Amplify y (subst_aexp a x n)
                   | Diffuse y => Diffuse y
                   | PSeq s1 s2 => PSeq (subst_pexp s1 x n) (subst_pexp s2 x n)
        end.



Definition gen_had_set (qenv: var -> nat) (s:session) (e:exp) (rmax:nat) :=
    fun i => match oqasm_type qenv (gen_tenv (nat2fb i) s) e with Some tv =>
                  match trans_tenv tv s rmax with (ph,ba) => ba end
              | _ => allfalse end.

Definition gen_ch_set (qenv: var -> nat) (st:nat -> rz_val) (s:session) (e:exp) (rmax:nat) :=
    fun i => match oqasm_type qenv (gen_tenv (st i) s) e with Some tv =>
                  match trans_tenv tv s rmax with (ph,ba) => ba end
              | _ => st i end.

Definition to_non_type (t:se_type) :=
   match t with THT n (TNor p) => THT n (TNor None)
              | THT n (TH p) => THT n (TH None)
              | THT n (CH p) => THT n (CH None)
   end.

Fixpoint to_non_types (T:tpred) (l:session) := 
   match T with [] => []
           | (al,t)::Ta => if inter_ses l al
                    then (al,to_non_type t)::(to_non_types Ta l)
                    else (al,t)::(to_non_types Ta l)
end.

Definition get_core_ses (b:bexp) :=
    match b with BEq c d x (Num v) => Some (x,v,v+1)
               | BLt c d x (Num v) => Some (x,v,v+1)
               | BTest x (Num v) => Some (x,v,v+1)
               | _ => None
    end.

Definition get_core_var (b:bexp) :=
    match b with BEq c d x a => x
               | BLt c d x a => x
               | BTest x a => x
    end.

Definition a_nat2fb f n := natsum n (fun i => Nat.b2n (f i) * 2^i).

Lemma a_nat2fb_scope : forall n f, a_nat2fb f n < 2^n.
Proof.
  induction n;intros;simpl.
  unfold a_nat2fb. simpl. lia.
  specialize (IHn f).
  unfold a_nat2fb in *. simpl.
  destruct (f n). simpl. lia.
  simpl. lia.
Qed.

Definition merge_fun (f g : rz_val) (n:nat) := fun i => if i <? n then f i else g i.

Definition join_ch_c (qenv:var -> nat) (c1:nat -> rz_val) (c2:nat -> rz_val) (n m:nat) (b:bexp) :=
   match b with BEq (AExp (BA x)) (AExp (Num a)) y (Num v) =>
         Some (2^(n-1)*m+m,fun i => if a =? a_nat2fb (c1 i) (qenv x)
                     then merge_fun (c1 i) (fb_push false (c2 i)) (n-1) else merge_fun (c1 i) (fb_push true (c2 i)) (n-1))
               | BLt (AExp (BA x)) (AExp (Num a)) y (Num v) =>
         Some ((2^(n-1)-a)*m+a*m, fun i => if a_nat2fb (c1 i) (qenv x) <? a
                     then merge_fun (c1 i) (fb_push false (c2 i)) (n-1) else merge_fun (c1 i) (fb_push true (c2 i)) (n-1))
               | BTest y (Num v) =>
         Some (2*m,fun i => if c1 i 0 then (fb_push false (c2 i)) else (fb_push true (c2 i)))
             | _ => None
   end.

Fixpoint count_ses (s:session) :=
   match s with [] => 0
          | ((x,a,b)::xl) => (b-a) + count_ses xl
   end.

Hypothesis cal_size : (nat -> rz_val) -> nat -> nat.

Definition keep_ch_c' (qenv:var -> nat) (n m:nat) (c c1:nat -> rz_val) (b:bexp) :=
   match b with BEq (AExp (BA x)) (AExp (Num a)) y (Num v) =>
     let new_f := (fun i => if a =? a_nat2fb (cut_n (c i) n) (qenv x) then merge_fun (c i) (c1 i) n else c i) in
              Some (cal_size new_f m, new_f)
               | BLt (AExp (BA x)) (AExp (Num a)) y (Num v) =>
     let new_f := (fun i => if a_nat2fb (cut_n (c i) n) (qenv x) <? a then merge_fun (c i) (c1 i) n else c i) in
              Some (cal_size new_f m, new_f)
               | BTest y (Num v) =>
     let new_f := (fun i => if c1 i 0 then merge_fun (c i) (c1 i) 1 else c i) in
              Some (cal_size new_f m, new_f)
             | _ => None
   end.
Definition keep_ch_c (qenv:var -> nat) (c c1:nat -> rz_val) (b:bexp) (s s1: session) :=
   keep_ch_c' qenv (count_ses s) (count_ses (s++s1)) c c1 b.

(* Define permutation of session vs types. *)
Definition switch_val (r:rz_val) (n m:nat) :=
     fun i => if i <? m then r (n+i) else if (m <=? i) && (i <? n+m) then r (i - m) else r i.

Definition switch_type_t (t:type_elem) (n m:nat) :=
   match t with TNor (Some r) => TNor (Some (switch_val r n m))
              | CH (Some (x,f)) => CH (Some (x,fun i => switch_val (f i) n m))
              | _ => t
   end.

Definition switch_type (t:se_type) (m:nat) :=
   match t with THT n ta => THT n (switch_type_t ta m (n-m)) end.

Inductive perm_tpred : tpred -> tpred -> Prop :=
    perm_tpred_1 : forall t1 t2 s1 s2 t,
            perm_tpred (t1++([(s1++s2,t)])++t2) (t1++([(s2++s1,(switch_type t (count_ses s1)))])++t2).

Hypothesis cal_set : (nat -> rz_val) -> session -> session -> (nat -> rz_val).

Inductive session_system {qenv: var -> nat} {rmax:nat}
           : atype -> aenv -> tpred -> pexp -> session -> se_type -> Prop :=
    | skip_ses : forall q env T l t, session_system q env T (PSKIP) l t
    | assign_ses_c : forall q env x v e T l t, session_system q env T (subst_pexp e x v) l t
                  -> session_system q env T (Let x (Num v) CT e) l t
    | assign_ses_m1 : forall q env x a e T l t, type_aexp env a MT ->
              session_system q (AEnv.add x (AType MT) env) T e l t -> session_system q env T (Let x a MT e) l t
    | assign_ses_m2 : forall env x y e T l ta t, find_env T ([(y,0,qenv y)]) = Some (([(y,0,(qenv y))]),ta) ->
              session_system MT (AEnv.add x (AType MT) env) T e l t -> session_system CT env T (Let x (Meas y) MT e) l t
    | assign_ses_m3 : forall env x y e T la l ta t, find_env T ([(y,0,qenv y)]) = Some (la,ta) ->
              session_system MT (AEnv.add x (AType MT) env) (to_non_types T la) e l t
                 -> session_system CT env T (Let x (Meas y) MT e) l t
    | appu_ses_h_nor:  forall q env T p s n, gen_ses qenv p = Some (s,n)
                  -> find_env T s = Some (s,THT n (TNor (Some allfalse))) ->
                    session_system q env T (AppSU (RH p)) s (THT n (TH (Some Uni)))
    | appu_ses_h_had:  forall q env T p s n, gen_ses qenv p = Some (s,n) -> 
                 find_env T s = Some (s,THT n (TH (Some Uni))) ->
                    session_system q env T (AppSU (RH p)) s (THT n (TNor (Some allfalse)))
    | appu_ses_h_nor_1:  forall q env T p s n b, gen_ses qenv p = Some (s,n) -> 
                         find_env T s = Some (s,THT n (TNor (Some b))) ->
                    session_system q env T (AppSU (RH p)) s (THT n (TH None))
    | appu_ses_h_ch:  forall q env T p s n b, gen_ses qenv p = Some (s,n) -> find_env T s = Some (s,THT n (CH (Some b))) ->
                    session_system q env T (AppSU (RH p)) s (THT n (CH None))
    | appu_ses_qft_nor:  forall q env T x, find_env T ([(x,0,qenv x)]) = Some (([(x,0,qenv x)]),THT (qenv x) (TNor (Some allfalse))) ->
                    session_system q env T (AppSU (SQFT x)) ([(x,0,qenv x)]) (THT (qenv x) (TH (Some Uni)))
    | appu_ses_qft_had:  forall q env T x, find_env T ([(x,0,qenv x)]) = Some (([(x,0,qenv x)]),THT (qenv x) (TH (Some Uni))) ->
         session_system q env T (AppSU (SRQFT x)) ([(x,0,qenv x)]) (THT (qenv x) (TNor (Some allfalse)))
    | appu_ses_qft_nor_1:  forall q env T x b, find_env T ([(x,0,qenv x)]) = Some (([(x,0,qenv x)]),THT (qenv x) (TNor (Some b))) ->
         session_system q env T (AppSU (SQFT x)) ([(x,0,qenv x)]) (THT (qenv x) (TH None))
    | appu_ses_nor:  forall q env T e s n b tenv ph ba, type_exp qenv env e (Ses s) -> find_env T s = Some (s, THT n (TNor (Some b)))
                -> @oqasm_type qenv (gen_tenv b s) e = Some tenv -> trans_tenv tenv s rmax = (ph,ba) ->
         session_system q env T (AppU s e) s (THT n (TNor (Some ba)))
    | appu_ses_had:  forall q env T e s n, type_exp qenv env e (Ses s) -> find_env T s = Some (s, THT n (TH (Some Uni)))
                -> session_system q env T (AppU s e) s (THT n (CH (Some ((2^n), (gen_had_set qenv s e rmax)))))
    | appu_ses_ch:  forall q env T e s s' n m b, type_exp qenv env e (Ses s) -> find_env T s = Some (s', THT n (CH (Some (m,b))))
                -> session_system q env T (AppU s e) s' (THT n (CH (Some (m,gen_ch_set qenv b s' e rmax ))))
    | qif_ses_nor : forall q env T b e n s c s' t, type_bexp env b (Ses s) -> find_env T s = Some (s, THT n (TNor (Some c))) ->
              type_pexp qenv env e (Ses s') -> find_env T s' = Some (s', t) -> session_system q env T (If b e) s' (to_non_type t)
    | qif_ses_ch: forall q env T b e n s m c s' x v n' c', type_bexp env b (Ses (s++[(x,v,S v)]))
           -> find_env T (s++[(x,v,S v)]) = Some ((s++[(x,v,S v)]), THT n (CH (Some (2^n,c)))) -> get_core_ses b = Some (x,v,S v)
            -> session_system MT env T e s' (THT n' (CH (Some (m,c'))))
              -> session_system q env T (If b e) s' (THT (n+n') (CH (join_ch_c qenv c c' n m b)))
    | qif_ses_ch_in: forall q env T b e n s m c s' m1 c1, type_bexp env b (Ses s) ->
               find_env T (s++s') = Some (s++s',THT n (CH (Some (m,c))))
            -> session_system MT env T e (s++s') (THT n (CH (Some (m1,c1))))
              -> session_system q env T (If b e) s' (THT n (CH (keep_ch_c qenv c c1 b s s')))
    | perm_ses: forall q env T T' e s t, perm_tpred T T' ->
                session_system q env T' e s t -> session_system q env T e s t
    (*TODO: the following rule is bad, we need some methods
               to say about s[v/i] and t[v/i], so s and t now need to involve variables.
            Basically saying that a for-loop is a type invariant depending on if statement. *)
    | qfor_ses_ch: forall q env T i l h b e s t, 
        (forall v, l <= v < h -> session_system q env T (If (subst_bexp b i v) (subst_pexp e i v)) s t)
              -> session_system q env T (For i (Num l) (Num h) b e) s t
    | amp_ses_ch: forall q env T x v s t, find_env T ([(x,0,qenv x)]) = Some (s,t) ->
                 session_system q env T (Amplify x (Num v)) s t
    (* TODO: we need to have a set syntax and interpretation for the CH type descrition,
               so that we are able to specify the cal_set. *)
    | dif_ses_ch_1:
       forall q env T x s n m c, find_env T ([(x,0,qenv x)]) = Some (([(x,0,qenv x)])++s,THT n (CH (Some (m,c)))) ->
                 session_system q env T (Diffuse (AExp (BA x))) (([(x,0,qenv x)])++s)
                          (THT n (CH (Some (cal_size (cal_set c ([(x,0,qenv x)]) s) m,cal_set c ([(x,0,qenv x)]) s))))
    | dif_ses_ch_2:
       forall q env T x v s n m c, find_env T ([(x,v,S v)]) = Some (([(x,v,S v)])++s,THT n (CH (Some (m,c)))) ->
                 session_system q env T (Diffuse (Index x (Num v))) (([(x,v,S v)])++s)
                          (THT n (CH (Some (cal_size (cal_set c ([(x,v,S v)]) s) m,cal_set c ([(x,v,S v)]) s)))).

(* Semantics. *)
Inductive state_elem :=
                 | Hval (b:nat -> rz_val)
               (*  | Cval (b:nat -> rz_val * rz_val) *)
                 | Fval (m:nat) (b : nat -> C * rz_val)
                 | Mval (r:R) (n:nat).

Inductive vtype := SVar (x:var) | SSes (l:session).

Definition state := list (vtype * state_elem).

Fixpoint find_qenv (l:state) (a: list (var* nat*nat)) :=
   match l with [] => None
           | ((SSes x,tl)::xl) => if in_sessions a x then Some (x,tl) else find_qenv xl a
           | ((SVar x,tl)::xl) => find_qenv xl a
   end.

Fixpoint update_qenv (l:state) (a: list (var* nat*nat)) (t:state_elem) :=
   match l with [] => ([(SSes a,t)])
           | ((SSes x,tl)::xl) => if in_sessions a x then (SSes x,t)::xl else (SSes x,tl)::(update_qenv xl a t) 
           | ((SVar x,tl)::xl) => update_qenv xl a t
   end.

Fixpoint remove_qenv (l:state) (a: list (var* nat*nat)) :=
   match l with [] => nil
           | ((SSes x,tl)::xl) => if in_sessions a x then xl else (SSes x,tl)::(remove_qenv xl a) 
           | ((SVar x,tl)::xl) => remove_qenv xl a
   end.

Fixpoint find_cenv (l:state) (a:var) :=
   match l with [] => None
           | ((SVar x,tl)::xl) => if a =? x then Some tl else find_cenv xl a
           | ((SSes x,tl)::xl) => find_cenv xl a
   end.

Fixpoint update_cenv (l:state) a (t:state_elem) :=
   match l with [] => ([(SVar a,t)])
           | ((SVar x,tl)::xl) => if a =? x then (SVar x,t)::xl else (SVar x,tl)::(update_cenv xl a t) 
           | ((SSes x,tl)::xl) => update_cenv xl a t
   end.

Definition con_nor (a:nat) (b:nat) (f:rz_val) := cut_n (@lshift_fun bool f a) b.

Definition allfalse_had := fun i:nat => fun j:nat => false.

Definition allfalse_ch := fun i:nat => (allfalse,allfalse).

Definition allfalse_fh := fun i:nat => (C0,allfalse).

Definition cut_n_rz {A:Type} (f:nat -> A) (n:nat) (de:nat -> A)
          := fun i => if i <? n then f i else de i.

Definition con_rz {A:Type} (a:nat) (b:nat) (f:nat -> A) (de:nat -> A) := cut_n_rz (@lshift_fun A f a) b de.


Definition find_val (s:state) (a:(var * nat * nat)) :=
    match find_qenv s [a] with None => None
         | Some (l,v) =>
            match find_ses_pos a l with None => 
                     match v with Mval r n => Some (Mval r n)
                               | _ => None
                     end
                     | Some (pos,n) =>
                match v with | Hval b => Some (Hval (@con_rz rz_val pos n b allfalse_had)) 
                        (*   | Cval b => Some (Cval (@con_rz (rz_val * rz_val) pos n b allfalse_ch)) *)
                           | Fval m b => Some (Fval m (@con_rz (C * rz_val) pos n b allfalse_fh)) 
                           | Mval r n => None
                end
            end
    end.
Definition update_cval (s:state) (a:var) (n:nat) :=
   match find_cenv s a with (Some (Mval r m)) => update_cenv s a (Mval r n) | _ => s end.

Fixpoint ses_len (l:list (var * nat * nat)) :=
   match l with nil => 0 | (x,l,h)::xl => (h - l) + ses_len xl end. 

Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat -> bool) (n:nat) : R :=
      turn_angle_r (fbrev n rval) n n.

Fixpoint sum_angle (r:nat -> bool) (b:nat -> rz_val) (rmax:nat) (n:nat) : C :=
   match n with 0 => C0
      | S m => (if r m then (turn_angle (b m) rmax) else C0) + sum_angle r b rmax m
   end.

Definition had_to_ch (b:nat -> rz_val) (rmax : nat) (n:nat) := 
    (fun i : nat => (sum_angle (nat2fb i) b rmax n, nat2fb i)).

Inductive pick_mea : state -> var -> nat -> (R * nat) -> Prop :=
   pick_meas : forall s x n m b i r bl, find_qenv s ([(x,0,n)]) = Some (([(x,0,n)]), Fval m b)
            -> 0 <= i < m -> b i = (r,bl) -> pick_mea s x n (Cmod r, a_nat2fb bl n).

Inductive eval_aexp : state -> aexp -> nat -> Prop :=
    | var_sem : forall s x r n, find_cenv s x = Some (Mval r n) -> eval_aexp s (BA x) n
    | num_sem : forall s n, eval_aexp s (Num n) n
    | aplus_sem: forall s e1 e2 n1 n2, eval_aexp s e1 n1 -> eval_aexp s e2 n2 -> eval_aexp s (APlus e1 e2) (n1 + n2)
    | amult_sem: forall s e1 e2 n1 n2, eval_aexp s e1 n1 -> eval_aexp s e2 n2 -> eval_aexp s (AMult e1 e2) (n1 * n2). 

Inductive eval_varia {qenv: var -> nat}: varia -> (var * nat * nat) -> Prop :=
    | aexp_sem : forall x, eval_varia (AExp (BA x)) (x,0,qenv x)
    | index_sem : forall x v, eval_varia (Index x (Num v)) (x,v,v+1).

Check Forall.

Check gen_tenv.

Check oqasm_type. 

Inductive qfor_sem  {qenv: var -> nat} {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=
  | trans_qubits: forall aenv s a a' b e, find_qenv s a = Some (a',Hval b) ->
           qfor_sem aenv s e (update_qenv s a' (Fval (2^(ses_len a')) (had_to_ch b rmax (ses_len a'))))
  | skip_sem: forall aenv s, qfor_sem aenv s PSKIP s
  | let_sem_c : forall aenv s s' x a n e, eval_aexp s a n -> qfor_sem aenv s (subst_pexp e x n) s' -> qfor_sem aenv s (Let x (AE a) CT e) s'
  | let_sem_m : forall aenv s s' x a n e, eval_aexp s a n -> qfor_sem (AEnv.add x (AType MT) aenv) (update_cval s x n) e s'
  -> qfor_sem aenv s (Let x (AE a) MT e) s'
  | let_sem_q : forall aenv s s' x a e r v, pick_mea s a (qenv a) (r,v) ->
            qfor_sem (AEnv.add x (AType MT) aenv) (update_cenv (remove_qenv s ([(a,0,qenv a)])) x (Mval r v)) e s'
                  -> qfor_sem aenv s (Let x (Meas a) MT e) s'
  | appsu_sem_h_nor : forall aenv s p a b, @eval_varia qenv p a -> find_val s a = Some (Fval 1 b) 
                 -> qfor_sem aenv s (AppSU (RH p)) (update_qenv s ([a]) (Hval (fun i => (update allfalse 0 ((snd (b 1)) i)))))
  | appsu_sem_h_had : forall aenv s p a b, @eval_varia qenv p a -> find_val s a = Some (Hval b) 
       -> qfor_sem aenv s (AppSU (RH p))
               (update_qenv s ([a]) (Fval 1 (fun i => if i =? 0 then (C0, (fun j => b j 0)) else (C0,allfalse))))
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)
  | appu_sem : forall aenv s a a' m b e, find_qenv s a = Some (a',Fval m b) -> qfor_sem aenv s (AppU a e) s
  | seq_sem: forall aenv e1 e2 s s1 s2, qfor_sem aenv s e1 s1 -> qfor_sem aenv s1 e2 s2 -> qfor_sem aenv s (PSeq e1 e2) s2
  | if_sem : forall aenv l1 l2 b e s s', type_pexp qenv aenv e (Ses l1) -> type_bexp aenv b (Ses l2) 
                -> qfor_sem aenv s e s'
     (*TODO: rewrite Fval state design, instead of function, we use list. 
        for every items in the s whose session is l1++l2, the result is 
              s[l1++l2 |-> ori_l1 ++ if s(l1) = true then s(l2)_of_l1 update to s'; otherwise s ] *)
           -> qfor_sem aenv s (If b e) s.

Inductive pexp := PSKIP 
            | Let (x:var) (n:maexp) (e:pexp)
              (*| InitQubit (p:posi) *) 
              (* Ethan: Init = reset = trace out = measurement... commeneted out *)
            | AppSU (e:single_u)
            | AppU (e:exp) 
            | PSeq (s1:pexp) (s2:pexp)
            | If (x:bexp) (s1:pexp)
            | For (x:var) (l:aexp) (h:aexp) (b:bexp) (p:pexp)
                   (*  quantum oracle functions executing p, and a list of tuples (x,a,s)
                      the first argument is the list of variables of quantum to p,
                       the second arguments a is the phase of the post-state of x,
                       the third is the state s = f(x) as |x> -> e^2pi i * a *|s>,
                       excluding ancilla qubits  *)
            | Amplify (x:var) (n:aexp) (* reflection on x with the form aexp x=n. l is the session. *)
            | Diffuse (x:varia) 


Inductive val := nval (b:bool) (r:rz_val) | qval (rc:rz_val) (r:rz_val).

Fixpoint var_in_list (x:var) (l:list var) :=
  match l with nil => false
            | y::xs => if x =? y then true else var_in_list x xs
  end.

(* Ethan: Maybe this? *)
Definition var_in_list' (x : var) (l : list var) := in_dec Nat.eq_dec x l.
Check var_in_list'.

(* Ethan: Sanity check *)
Lemma var_in_list'_correct :
  forall x l, (if var_in_list' x l then true else false) = var_in_list x l.
Proof.
  intros x l.
  induction l; simpl.
  + reflexivity.
  + destruct Nat.eq_dec.
    - subst.
      rewrite Nat.eqb_refl; trivial.
    - rewrite <- IHl.
      assert (x =? a = false) as x_neqa. {
        rewrite Nat.eqb_sym.
        rewrite Nat.eqb_neq.
        assumption.
      }
      destruct (var_in_list' x l); rewrite x_neqa; trivial.
Qed.

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


