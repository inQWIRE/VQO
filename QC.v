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
Require Import OQIMP.
Require Import QC_state.
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

(*
Inductive predi := PTrue | PFalse | PState (l:list (var * aexp)) (s:state)
                    (* quantum variable, its initial position and qubit size and the state representation*)
            | CState (b:bexp)
               (* bexp is a constant variable predicate. *)
            | PMea (x:var) (p:fexp) (n:nat) 
                (* partial measumrement on the varible x with the probability of p at a value n. *)
            | PAnd (p1:predi) (p2:predi)
            | Forall (x:var) (p1:predi) (p2:predi) (* forall x p1 => p2. need to have someway to restrict the formula. *)
            | PNot (p:predi).
*)

Inductive pattern := Adj (x:var) (* going to adj nodes. *)
                   | Match (x:var) (n:nat) (nll:list (list bool * list bool)).
                        (*n here means n bits starting from the 0 position in x. *)

(* we want to include all the single qubit gates here in the U below. *)
Inductive singleGate := H_gate | X_gate | Y_gate | RZ_gate (f:aexp) (*representing 1/2^n of RZ rotation. *).

Inductive pexp := PSKIP (a: vari) | Assign (x:var) (n:aexp) 
              (*| InitQubit (p:posi) *) 
              (* Ethan: Init = reset = trace out = measurement... commeneted out *)
            | AppU (e:singleGate) (p:vari) 
            | PSeq (s1:pexp) (s2:pexp)
            | IfExp (b:bexp) (e1:pexp) (e2:pexp) | While (b:bexp) (p:pexp)
            | Classic (p:exp) (args: list (var * aexp * aexp))
                   (*  quantum oracle functions executing p, and a list of tuples (x,a,s)
                      the first argument is the list of variables of quantum to p,
                       the second arguments a is the phase of the post-state of x,
                       the third is the state s = f(x) as |x> -> e^2pi i * a *|s>  *)
            | QFT (x:var)
            | RQFT (x:var)
            | Abort (a:var) (x:var)
            | Meas (a:var) (x:var) (* quantum measurement on x to a classical value 'a'. *)
            | PMeas (p:var) (x:var) (a:var) (* the probability of measuring x = a assigning probability to p. *)
          (*  | CX (x:posi) (y:posi)  (* control x on to y. *)
            | CU (x:posi) (p:exp) (z:var) (args: list var) (q:aexp) (s:aexp) *)
             (* control-U on the reversible expression p from the control node x on to z. *)
            | QWhile (n:aexp) (x:var) (f:aexp) (b:bexp) (e:pexp) 
                    (*max loop number of n, variable x, monotonic function f on x as x -> f(x), bool b and e.*)
            | Reflect (x:var) (l:list (aexp * state)) (* Amplitude amplication, 
                  each list is a node to amplify, (p,t), where p is the probability and t is a position. *)
                  (*we can restrict the syntax of reflect to a list of probabilty with tensor summasion formula. *)
             (*quantum while, x is a variable, represents a monotonic function variable.
                 n is the upperbound, b is the boolean formula but it needs to be monotonic. 
                e is an expression that does not contain x and no measurement.
                  an example of using QWhile is to find optimimal solution.  *)
          (*  | QWalk (e1:pexp) (e2:pexp).
            SingleTon walk step, e1 is defussion step that does not include permutation,
                      e2 is a walk step that cannot do defussion. *).

Notation "p1 ; p2" := (PSeq p1 p2) (at level 50) : pexp_scope.


(* Define the ground term type system *)
Inductive type_rotation := TV (b:aexp) | Infty.





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


Inductive static_type := SPos (x:list vari) | SNeg (x:list vari).

Definition not_Q_twice (t1 t2: atype * list vari) := match t1 with (C,xl) => True | (Q,xl) => fst t2 <> Q end.

Definition meet_avtype (t1 t2: atype * list vari) :=
        match t1 with (a, xl) => match t2 with (b,yl) => (meet_atype a b, if length xl =? 0 then yl else xl) end end.

Definition right_av (t1: atype * list vari) :=  match t1 with (C,xl) => length xl = 0 | (Q,xl) => length xl = 1 end.


Inductive type_aexp : aenv -> aexp -> atype * list vari -> Prop :=
     ba_type : forall env b t, type_vari env b t -> type_aexp env (BA b) t
   | num_type : forall env n, type_aexp env (Num n) (C,[])
   | plus_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> right_av t1 -> right_av t2 ->
                   type_aexp env e1 t1 -> type_aexp env e2 t2 -> 
                                type_aexp env (APlus e1 e2) (meet_avtype t1 t2)
   | minus_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> right_av t1 -> right_av t2 ->
                       type_aexp env e1 t1 -> type_aexp env e2 t2 -> 
                                type_aexp env (AMinus e1 e2) (meet_avtype t1 t2)
   | mult_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> 
                     type_aexp env e1 t1 -> type_aexp env e2 t2 -> right_av t1 -> right_av t2 ->
                                type_aexp env (AMult e1 e2) (meet_avtype t1 t2)
   | twoto_type : forall env e1, type_aexp env e1 (C,[]) -> type_aexp env (TwoTo e1) (C,[]) 
   | app_type : forall env f e1 t1, type_aexp env e1 t1 -> right_av t1
                                    -> AEnv.MapsTo f C env -> type_aexp env (App f e1) t1
   | fexp_type : forall env e1, type_aexp env e1 (C,[]) -> type_aexp env (FExpI e1) (C,[])
   | faddexp_type : forall env e1 e2, type_bexp env e1 (C,[]) -> type_aexp env e2 (C,[]) -> type_aexp env (FAddExpI e1 e2) (C,[])
   | getp_type : forall env e1 t, type_state env e1 t -> right_av t -> type_aexp env (GetP e1) t
   | left_type : forall env e1 t, type_state env e1 t -> right_av t -> type_aexp env (Left e1) t
   | right_type : forall env e1 t, type_state env e1 t -> right_av t -> type_aexp env (Right e1) t

with type_aexp_list : aenv -> list aexp -> Prop :=
   | alist_empty_type : forall env, type_aexp_list env []
   | alist_many_type : forall env e el, type_aexp env e (C,[]) -> type_aexp_list env el -> type_aexp_list env (e::el)

with type_vari : aenv -> vari -> atype * list vari -> Prop :=
   | var_type : forall env x t, AEnv.MapsTo x t env -> type_vari env (Var x) (t,(if t =a= Q then [Var x] else []))
   | index_type : forall env x el t, AEnv.MapsTo x t env -> type_aexp_list env el -> type_vari env (Index x el) 
                         (t,if t =a= Q then [Index x el] else [])

with type_vari_list : aenv -> list vari -> atype * list vari -> Prop :=
   | vlist_empty_type : forall env, type_vari_list env [] (Q,[])
   | vlist_many_type : forall env e el xl xll, type_vari env e (Q,xl)
               -> type_vari_list env el (Q,xll) -> type_vari_list env (e::el) (Q,xl++xll)

with type_bexp : aenv -> bexp -> atype * list vari -> Prop :=
   | bfalse_type : forall env, type_bexp env BFalse (C,[])
   | btrue_type : forall env, type_bexp env BTrue (C,[])
   |  beq_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> right_av t1 -> right_av t2 ->
                type_aexp env e1 t1 -> type_aexp env e2 t2 
               -> type_bexp env (BEq e1 e2) (meet_avtype t1 t2)
   | blt_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> right_av t1 -> right_av t2 ->
                      type_aexp env e1 t1 -> type_aexp env e2 t2 
               -> type_bexp env (BLt e1 e2) (meet_avtype t1 t2)
   | bge_type : forall env e1 e2 t1 t2, not_Q_twice t1 t2 -> right_av t1 -> right_av t2 ->
                   type_aexp env e1 t1 -> type_aexp env e2 t2 
               -> type_bexp env (BGe e1 e2) (meet_avtype t1 t2)
   | btest_type : forall env x t, type_vari env x t -> type_bexp env (BTest x) t
   | bxor_type : forall env e1 e2 t1 t2, type_bexp env e1 t1 -> type_bexp env e2 t2 
               -> type_bexp env (BXOR e1 e2) (meet_avtype t1 t2)
   | bneg_type : forall env e1 t1, type_bexp env e1 t1 -> type_bexp env (BNeg e1) t1

with type_vs_list : aenv -> list (list vari * state) -> atype -> Prop :=
   | vslist_empty_type : forall env, type_vs_list env [] Q
   | vslist_many_type : forall env x e el t xl, type_vari_list env x (Q,xl) -> type_state env e t
                          -> type_vs_list env el Q -> type_vs_list env ((x,e)::el) Q

with type_state_list : aenv -> list state -> atype * list vari -> Prop :=
    | state_empty_type : forall env, type_state_list env [] (Q,[])
    | state_many_type : forall env e el xl xll, type_state env e (Q,xl)
             -> type_state_list env el (Q,xll) -> type_state_list env (e::el) (Q,xl++xll)

with type_state : aenv -> state -> atype * list vari -> Prop :=
        | sa_type : forall aenv xl tl l, type_vari_list aenv xl (Q,tl) -> type_vs_list aenv l Q -> type_state aenv (SA xl l) (Q,tl)
        | ket_type : forall aenv b x, type_bexp aenv b (Q,x) -> type_state aenv (ket b) (Q,x)
        | qket_type : forall aenv p b x, type_aexp aenv p (Q,x) -> type_bexp aenv b (Q,x) -> type_state aenv (qket p b) (Q,x)
        | site_type : forall aenv b e1 e2 t x, type_bexp aenv b t -> type_state aenv e1 (Q,x)
               -> type_state aenv e2 (Q,x) -> type_state aenv (SITE b e1 e2) (Q,x)
        | splus_type : forall aenv e1 e2 x, type_state aenv e1 (Q,x) -> type_state aenv e2 (Q,x) -> type_state aenv (SPlus e1 e2) (Q,x)
        | tensor_type : forall aenv el t, type_state_list aenv el t -> type_state aenv (Tensor el) t
        | sigma_type : forall aenv n i b s t, type_aexp aenv n (C,[]) -> type_aexp (AEnv.add i C aenv) b (C,[]) ->
                                    type_state (AEnv.add i C aenv) s t -> type_state aenv (Sigma n i b s) t
        | ntensor_type : forall aenv n i b s t, type_aexp aenv n (C,[]) -> type_aexp (AEnv.add i C aenv) b (C,[]) ->
                                    type_state (AEnv.add i C aenv) s t -> type_state aenv (NTensor n i b s) t.

Definition list_subset (al bl :list var) := (forall x, In x al -> In x bl).

Definition get_var (x : vari) := match x with Var a => a | Index b y => b end.

Definition get_core_vars (al : list vari) := map (fun a => match a with Var x => x | Index x xl => x end) al.

Inductive stype_aexp_list {l:list var} {env:aenv} : list (var * aexp * aexp) -> Prop :=
    aexp_list_empty : stype_aexp_list nil
   | aexp_list_many : forall a e1 e2 xl el1 el2, stype_aexp_list xl -> type_aexp env e1 (Q,el1)
         -> list_subset (get_core_vars el1) l -> type_aexp env e2 (Q,el2)
       -> list_subset (get_core_vars el2) l -> stype_aexp_list xl -> stype_aexp_list ((a,e1,e2)::xl).

Inductive stype_pexp : atype -> aenv -> pexp -> Prop :=
    | skip_stype : forall m env a, stype_pexp m env (PSKIP a)
    | assign_stype : forall env a v, AEnv.MapsTo a C env -> type_aexp env v (C,[]) -> stype_pexp C env (Assign a v)
    | appu_stype : forall m env e p x,  type_vari env p (Q,[x]) -> stype_pexp m env (AppU e p)
    | seq_stype : forall m env e1 e2, stype_pexp m env e1 -> stype_pexp m env e2 -> stype_pexp m env (PSeq e1 e2)
    | if_stype_c : forall m l env b e1 e2, type_bexp env b (m,l)
                          -> stype_pexp m env e1 -> stype_pexp m env e2 -> stype_pexp C env (IfExp b e1 e2)
    | if_stype_q : forall l env b e1 e2, type_bexp env b (Q,l)
                          -> stype_pexp Q env e1 -> stype_pexp Q env e2 -> stype_pexp Q env (IfExp b e1 e2)
    | class_stype : forall m env p l, @stype_aexp_list (map (fun a => fst (fst a)) l) env l -> stype_pexp m env (Classic p l)
    | qft_stype : forall m env x, AEnv.MapsTo x Q env -> stype_pexp m env (QFT x)
    | rqft_stype : forall m env x, AEnv.MapsTo x Q env -> stype_pexp m env (RQFT x)
    | meas_stype : forall m env x y, AEnv.MapsTo y Q env  -> AEnv.MapsTo x C env -> stype_pexp m env (Meas x y)
    | pmeas_stype : forall m env p x y, AEnv.MapsTo y Q env  -> AEnv.MapsTo x C env 
                    -> AEnv.MapsTo p C env -> stype_pexp m env (PMeas p x y)
    | while_stype : forall env b p, type_bexp env b (C,[]) -> stype_pexp C env p -> stype_pexp C env (While b p)
    | qwhile_stype : forall m env n x f b e a c, type_aexp env n (C,[]) -> type_aexp env f (Q,[a])
             -> get_var a = x -> type_bexp env b (Q,[c]) -> get_var c = x
               -> stype_pexp Q env e -> stype_pexp m env (QWhile n x f b e)
    | reflect_stype : forall m env x l, AEnv.MapsTo x Q env -> stype_pexp m env (Reflect x l).



Inductive type_elem : Type := TNor (b:bexp) | TH (b:list aexp) (r:nat) (* phase rotation and rank. *)
             | TC (b:list aexp) (r:nat) (l: list type_pred)  (*phase rank and variables that are entangled *)
             | DFT (b:aexp) | RDFT (b:aexp)

with type_pred := TT (l:list type_pred) | THT (n:aexp) (t:type_elem). (* tensor of n. *)


Definition tpred := list (list (var * aexp * aexp) * type_pred).


Definition testbit (n:nat) (i:nat) := N.testbit_nat (N.of_nat n) i.

Fixpoint ntestbit (n:nat) (m:nat) :=
     match m with 0 => false
              | S i => xorb (testbit n i) (ntestbit n i)
     end.

Fixpoint eval_aexp (env: var -> option nat) (a:aexp) :=
  match a with BA (Var x) => env x
             | BA (Index x al) => match al with [] => None | a::all => 
                                    match eval_aexp env a with None => None 
                                                      | Some av => 
                                      match env x with None => None
                                               | Some xv => if testbit xv av then Some 1 else Some 0
                                      end
                                    end
                                 end
            | APlus e1 e2 => match eval_aexp env e1 with None => None
                                        | Some av =>
                               match eval_aexp env e2 with None => None
                                        | Some bv => Some (av + bv)
                               end
                             end

            | AMinus e1 e2 => match eval_aexp env e1 with None => None
                                        | Some av =>
                               match eval_aexp env e2 with None => None
                                        | Some bv => Some (av - bv)
                               end
                             end

            | AMult e1 e2 => match eval_aexp env e1 with None => None
                                        | Some av =>
                               match eval_aexp env e2 with None => None
                                        | Some bv => Some (av * bv)
                               end
                             end

            | TwoTo e1 => match eval_aexp env e1 with None => None
                                        | Some av => Some (2 ^ av)
                             end

            | _ => None
   end.

Fixpoint eval_bexp (env: var -> option nat) (qenv: var-> nat) (a:bexp) :=
  match a with BFalse => Some false | BTrue => Some true
             | BEq x y => match eval_aexp env x with None => None
                                 | Some av => 
                           match eval_aexp env y with None => None
                              | Some bv => Some (av =? bv)
                           end
                          end

             | BGe x y => match eval_aexp env x with None => None
                                 | Some av => 
                           match eval_aexp env y with None => None
                              | Some bv => Some (bv <=? av)
                           end
                          end

             | BLt x y => match eval_aexp env x with None => None
                                 | Some av => 
                           match eval_aexp env y with None => None
                              | Some bv => Some (bv <? av)
                           end
                          end

             | BTest (Var x) => match env x with None => None
                                | Some xv => Some (ntestbit xv (qenv x))
                               end

             | BTest (Index x al) =>
                  match al with [] => None | a::all => 
                    match eval_aexp env a with None => None
                      | Some av => 
                      match env x with None => None
                                | Some xv => Some (testbit xv av)
                               end
                   end
                  end

             | BXOR x y => match eval_bexp env qenv x with None => None
                                 | Some av => 
                           match eval_bexp env qenv y with None => None
                              | Some bv => Some (xorb av bv)
                           end
                          end

             | BAnd x y => match eval_bexp env qenv x with None => None
                                 | Some av => 
                           match eval_bexp env qenv y with None => None
                              | Some bv => Some (andb av bv)
                           end
                          end

             | BNeg x => match eval_bexp env qenv x with None => None
                                 | Some av => Some (negb av)
                          end

            | _ => None
   end.


Fixpoint in_session_var_v (env: var -> option nat) (qenv: var-> nat) (y:var) (l :list (var * aexp * aexp))  :=
   match l with [] => false
             | ((x,l,r)::xs) =>
            if x =? y then match eval_bexp env qenv (BAnd (BEq l (Num 0)) (BEq r (Num (qenv x))))
                             with | Some true => true
                                  | _ => in_session_var_v env qenv y xs
                           end
                      else in_session_var_v env qenv y xs
   end.

Fixpoint in_session_index_v (env: var -> option nat) (qenv: var-> nat) (y:var) (i:aexp) (l :list (var * aexp * aexp))  :=
   match l with [] => false
             | ((x,l,r)::xs) =>
            if (x =? y) then match eval_bexp env qenv 
                           (BAnd (BAnd (BAnd (BGe (Num 0) l) (BGe l i)) (BLt i r)) (BGe r (Num (qenv x))))
                             with | Some true => true
                                  | _ => in_session_index_v env qenv y i xs
                           end
                      else in_session_index_v env qenv y i xs
  end.

Fixpoint in_session_vars_v (P: var -> option nat) (qenv: var-> nat) (y:var) (ts:tpred) :=
  match ts with [] => None
            | ((xl,t)::xll) => if in_session_var_v P qenv y xl then Some (xl,t) else in_session_vars_v P qenv y xll
  end.

Fixpoint in_session_indexs_v (P:var -> option nat) (qenv: var-> nat) (y:var) (i:aexp) (ts:tpred) :=
  match ts with [] => None
            | ((xl,t)::xll) => if in_session_index_v P qenv y i xl then Some (xl,t) else in_session_indexs_v P qenv y i xll
  end.

Definition in_sessions_v (P:var -> option nat) (qenv: var-> nat) (a:vari) (ts:tpred) :=
  match a with Var y => in_session_vars_v P qenv y ts
            | Index y al => (match hd_error al with None => None
                                  | Some aa => in_session_indexs_v P qenv y aa ts
                            end)
  end.


Inductive type_eq : type_pred -> type_pred -> Prop :=
   type_sum_eq : forall t n i, i < n -> type_eq (THT (Num n) t) (TT ((THT (Num i) t)::(THT (Num (n-i)) t)::nil))
  | type_sum_eq_m : forall t n i r l, i < n -> type_eq (TT (r++(THT (Num n) t)::l)) (TT (r++((THT (Num i) t)::(THT (Num (n-i)) t)::l)))
  | type_sum_eq_a :  forall t n i r l, i < n -> type_eq (TT (r++((THT (Num i) t)::(THT (Num (n-i)) t)::l))) (TT ((r++((THT (Num n) t)::l))))
  | type_empty_eq : forall t n, type_eq (TT ((THT n t)::nil)) (THT n t)
  | type_zero_eq : forall t r l, type_eq (TT (r++((THT (Num 0) t)::l))) (TT (r++l)).


(*
Inductive type_elem : Type := TNor (b:bexp) | TH (b:type_rotation) (r:nat) (* phase rotation and rank. *)
             | TC (b:type_rotation) (r:nat) (l: list type_pred)  (*phase rank and variables that are entangled *)
             | DFT (b:type_rotation) | RDFT (b:type_rotation)

with type_pred := TT (l:list type_pred) | THT (n:aexp) (t:type_elem). (* tensor of n. *)


Definition tpred := list (list (var * aexp * aexp) * type_pred).
Inductive singleGate := H_gate | X_gate | Y_gate | RZ_gate (f:aexp) (*representing 1/2^n of RZ rotation. *).
*)

Fixpoint count_num' (l :list (var * aexp * aexp)) (x:var) acc := 
   match l with [] => None
         | ((y,(Num a),(Num b))::xs) => if x =? y then Some acc else count_num' xs x (acc+(b-a))
         | a::xs => None
   end.
Definition count_num (l :list (var * aexp * aexp)) (x:var) (i:nat) := count_num' l x i.


Fixpoint count_type_pred a := 
    match a with TT l => (fold_left (fun a b => a+(count_type_pred b)) l 0) | THT (Num n) t => n | _ => 0 end.


Definition count_type (t: type_elem) := 
   match t with TNor a => 1 | TH b r => 1 | TC b r l => (fold_left (fun a b => a+(count_type_pred b)) l 0) | _ => 0 end.


Definition change_type_one (t: type_elem) (op:singleGate) :=
   match op with X_gate => match t with TNor b => Some (TNor (BNeg b)) | TH (a::al) r => Some (TH ((AMinus (Num 0) a)::al) r) | _ => None end
               | RZ_gate b => match t with TNor b => Some (TNor b) | TH (a::al) r => Some (TH ((APlus a b)::al) r) | _ => None end
               | H_gate => match t with TNor b => Some (TH ([Num 0]) 0) 
                       | TH ((Num a)::l) r =>
                             if a =? 0 then (if r =? 1 then Some (TNor BFalse) else Some (TH l (r-1)))
                             else if a =? 1 then (if r =? 1 then Some (TNor BTrue) else Some (TH l (r-1)))
                             else Some (TH (Num 0::l) (r+1))
                | _ => None end
               | _ => None
   end.

Inductive change_type : type_pred -> nat -> singleGate -> type_pred -> Prop :=
    change_type_eq : forall t n op t', type_eq t t' -> change_type t n op t'
  | change_type_ex : forall t tl tl' n op, count_type_pred t <= n -> 
                    change_type (TT (tl)) (n-count_type_pred t) op (TT tl') ->
                     change_type (TT (t::tl)) (n-count_type_pred t) op (TT (t::tl'))
  | change_type_0 : forall t t' tl op, (change_type_one t op) = Some t' -> 
                change_type (TT ((THT (Num 1) t)::tl)) 0 op (TT ((THT (Num 1) t')::tl))
  | change_type_hit : forall tl n m b r l l' op, n < m ->
                change_type (TT l) n op (TT l') ->
                change_type (TT ((THT (Num m) (TC b r l))::tl)) n op (TT ((THT (Num m) (TC b r l'))::tl)).

Inductive session_system {P: var -> option nat} {qenv: var -> nat} {T : tpred} 
            : atype -> aenv -> pexp -> list (list (var * aexp * aexp) * type_pred) -> Prop :=
    | skip_type : forall m env a l t, in_sessions_v P qenv a T = Some (l,t) -> session_system m env (PSKIP a) [(l,t)]
    | assign_type : forall env a v, type_aexp env v (C,[]) -> session_system C env (Assign a v) nil
    | appu_type : forall m env p e x a al av num l t t', type_vari env p (Q,[Index x (a::al)])
              -> in_sessions_v P qenv (Index x (a::al)) T = Some (l,t) -> eval_aexp P a = Some av ->
              count_num l x av = Some num -> change_type t num e t' -> session_system m env (AppU e p) [(l,t')]
    | seq_type : forall m env e1 e2 l1 l2, session_system m env e1 l1 
             -> session_system m env e2 l2 -> session_system m env (PSeq e1 e2) (l1++l2)
    | classic_type : forall m env e args xl, type_vari_list env (List.map (fun arg => Var (fst (fst arg))) args) (Q,xl) 
                 -> session_system m env (Classic e args) nil
    | if_type_q_1 : forall m env b e1 e2 x l, type_bexp env b (Q,[x]) -> session_system Q env e1 l -> session_system Q env e2 l ->
                                                     session_system m env (IfExp b e1 e2) l.
(*
            | Classic (p:exp) (args: list (var * aexp * aexp))

    | if_type_c : forall env b e1 e2 l1 l2, type_bexp env b (C,[]) -> session_system C env e1 l1 -> session_system C env e2 l2 ->
                    session_system C env (IfExp b e1 e2) l1.

    | if_type_cq : forall env b e1 e2 l, type_bexp env b (C,[]) -> session_system Q env e1 l -> session_system Q env e2 l ->
                                        session_system Q env (IfExp b e1 e2) l
*)

    | if_type_q_1 : forall m env b e1 e2 x l, type_bexp env b (Q,[x]) -> session_system Q env e1 l -> session_system Q env e2 l ->
                                                     session_system m env (IfExp b e1 e2) l
    | classic_type : forall m env e args xl, type_vari_list env (List.map (fun arg => Var (fst (fst arg))) args) (Q,xl) 
                 -> session_system m env (Classic e args) xl
    | qft_type : forall m env x a, type_vari env (Var x) (Q,a) -> session_system m env (QFT x) a
    | rqft_type : forall m env x a, type_vari env (Var x) (Q,a) -> session_system m env (RQFT x) a
    | abort_type : forall env a x t, type_vari env (Var a) (C,[]) -> type_vari env (Var x) t -> session_system C env (Abort a x) (snd t)
    | meas_type : forall env a x t, type_vari env (Var a) (C,[]) -> type_vari env (Var x) t-> session_system C env (Meas a x) (snd t)
    | pmeas_type : forall env p a x t, type_vari env (Var p) (C,[]) -> type_vari env (Var a) (C,[])
                        -> type_vari env (Var x) t -> session_system C env (PMeas p x a) (snd t)
    | while_type : forall m env p b al, type_bexp env b (C,[]) -> session_system m env p al -> session_system m env (While b p) al
    | qwhile_type : forall m env p al n x f b, type_aexp env n (C,[]) ->  AEnv.MapsTo x Q env
                   -> type_aexp env f (Q,[Var x]) -> type_bexp env b (Q,[Var x]) ->
                      session_system m env p al -> session_system m env (QWhile n x f b p) al
    | reflect_type : forall m env x l, AEnv.MapsTo x Q env -> session_system m env (Reflect x l) [Var x].

Axiom aexp_eq_dec : aexp -> aexp -> bool.

Fixpoint aexp_list_eq_dec (a b : list aexp) :=
   match (a,b) with ([], []) => true
              | (x::xl,y::yl) => aexp_eq_dec x y && aexp_list_eq_dec xl yl
              | (_,_) => false
   end.

Definition vari_eq_dec (a b: vari) :=
   match a with Var x => match b with Var y => x =? y
                                 | Index y z => false
                         end
             | Index x u => match b with Var y => false
                                  | Index y z => (x =? y) && aexp_list_eq_dec u z
                            end
   end.

Fixpoint vari_list_eq_dec (a b : list vari) :=
   match (a,b) with ([], []) => true
              | (x::xl,y::yl) => vari_eq_dec x y && vari_list_eq_dec xl yl
              | (_,_) => false
   end.


Axiom satisfy : cpred -> bool. (* decide P to be satisfiable or not. *)

Fixpoint in_session_var (P:cpred) (qenv: var-> nat) (y:var) (l :list (var * aexp * aexp))  :=
   match l with [] => false
             | ((x,l,r)::xs) =>
            if x =? y then (satisfy ((CState (BAnd (BEq l (Num 0)) (BEq r (Num (qenv x)))))::P))
                      else in_session_var P qenv y xs
  end.

Fixpoint in_session_index (P:cpred) (qenv: var-> nat) (y:var) (i:aexp) (l :list (var * aexp * aexp))  :=
   match l with [] => false
             | ((x,l,r)::xs) =>
            if (x =? y) && (satisfy ((CState (BAnd (BAnd (BAnd (BGe (Num 0) l) (BGe l i)) (BLt i r)) (BGe r (Num (qenv x)))))::P))
                   then true else in_session_index P qenv y i xs
  end.

Fixpoint in_session_vars (P:cpred) (qenv: var-> nat) (y:var) (ts:tpred) :=
  match ts with [] => None
            | ((xl,t)::xll) => if in_session_var P qenv y xl then Some (xl,t) else in_session_vars P qenv y xll
  end.

Fixpoint in_session_indexs (P:cpred) (qenv: var-> nat) (y:var) (i:aexp) (ts:tpred) :=
  match ts with [] => None
            | ((xl,t)::xll) => if in_session_index P qenv y i xl then Some (xl,t) else in_session_indexs P qenv y i xll
  end.

Definition in_sessions (P:cpred) (qenv: var-> nat) (a:vari) (ts:tpred) :=
  match a with Var y => in_session_vars P qenv y ts
            | Index y al => (match hd_error al with None => None
                                  | Some aa => in_session_indexs P qenv y aa ts
                            end)
  end.




(*
Fixpoint get_var (x : vari) := match x with Var a => a | Index b y => get_var b end.

Fixpoint vars (x: list vari) := 
   match x with [] => []
          | (a::al) => (get_var a)::(vars al)
   end.

Definition get_var_static (x:static_type) := match x with SPos a => vars a | SNeg a => vars a end.


Fixpoint get_var_pexp (p:pexp) :=
   match p with PSKIP a => List.fold_left (fun acc x => (collect_var_basic x)++acc) a []
           | Assign x n => (x::collect_var_aexp n)
           | AppU e p => collect_var_basic p
           | PSeq s1 s2 => (get_var_pexp s1)++(get_var_pexp s2)
           | IfExp b e1 e2 => (collect_var_bexp b)++(get_var_pexp e1)++(get_var_pexp e2)
           | While b p => (collect_var_bexp b)++(get_var_pexp p)
           | Classic p args => List.map (fun x => fst (fst x)) args
           | QFT x => [x]
           | RQFT x => [x]
           | Abort a x => (a::x::nil)
           | Meas a x => (a::x::nil)
           | PMeas p x a => (p::a::x::nil)
           | QWhile n x f b e => x::(collect_var_aexp n)++(collect_var_aexp f)++(collect_var_bexp b)++(get_var_pexp e)
           | Reflect x xl => [x]
   end.


Inductive session_weak_match : list static_type -> list static_type -> Prop := 
   session_weak_empty : session_weak_match nil nil
  | session_weak_many : forall a b l1 l2, (get_var_static a) = (get_var_static b) 
              -> session_weak_match l1 l2 -> session_weak_match (a::l1) (b::l2).

Inductive session_match : list static_type -> list static_type -> Prop := 
    session_empty : session_match nil nil
  | session_many_pos : forall a b l1 l2, vars a = vars b -> session_match l1 l2 -> 
                               session_match ((SPos a)::l1) ((SPos b)::l2)
  | session_many_neg : forall a b l1 l2, vars a = vars b -> session_match l1 l2 -> 
                               session_match ((SNeg a)::l1) ((SNeg b)::l2).

Fixpoint all_pos (l:list static_type) := match l with [] => True
                           | (SPos a)::xl => all_pos xl
                           | a::xl => False
          end.

Fixpoint all_neg (l:list static_type) := match l with [] => True
                           | (SNeg a)::xl => all_neg xl
                           | a::xl => False
          end.

Definition valid_branch (l1 l2: list static_type) :=
     (all_pos l1 /\ all_pos l2) \/ (all_pos l1 /\ all_neg l2) \/ (all_pos l2 /\ all_neg l1).


Inductive type_system : atype -> aenv -> pexp -> list static_type -> Prop :=
    | skip_type : forall m env a, type_system m env (PSKIP a) [SNeg a]
    | assign_type : forall m env a v, type_aexp env v C -> type_system m env (Assign a v) nil
    | appu_type : forall m env e p, type_vari env p Q -> type_system m env (AppU e p) [SPos ([p])]
    | seq_type : forall m env e1 e2 l1 l2, type_system m env e1 l1 -> type_system m env e2 l2 -> type_system m env (PSeq e1 e2) (l1++l2)
    | if_type_c : forall env b e1 e2 l1 l2, type_bexp env b C -> type_system C env e1 l1 -> type_system C env e2 l2 ->
                   session_weak_match l1 l2 -> type_system C env (IfExp b e1 e2) l1
    | if_type_cq : forall env b e1 e2 l1 l2, type_bexp env b C -> type_system Q env e1 l1 -> type_system Q env e2 l2 ->
                   session_match l1 l2 -> type_system Q env (IfExp b e1 e2) l1
    | if_type_q_1 : forall m env b e1 e2 l1 l2, type_bexp env b Q -> type_system Q env e1 l1 -> type_system Q env e2 l2 ->
                   session_weak_match l1 l2 -> valid_branch l1 l2 -> all_pos l1  -> type_system m env (IfExp b e1 e2) l1
    | if_type_q_2 : forall m env b e1 e2 l1 l2, type_bexp env b Q -> type_system Q env e1 l1 -> type_system Q env e2 l2 ->
                   session_weak_match l1 l2 -> valid_branch l1 l2 -> all_pos l2  -> type_system m env (IfExp b e1 e2) l2
    | classic_type : forall m env e args, (forall a b c, In (a,b,c) args -> type_vari env (Var a) Q)
                 -> type_system m env (Classic e args) ([SPos (List.map (fun arg => Var (fst (fst arg))) args)])
    | qft_type : forall m env x, type_vari env (Var x) Q -> type_system m env (QFT x) ([SPos ([Var x])])
    | rqft_type : forall m env x, type_vari env (Var x) Q -> type_system m env (RQFT x) ([SPos ([Var x])])
    | abort_type : forall env a x, type_vari env (Var a) C -> type_vari env (Var x) Q -> type_system C env (Abort a x) ([SPos ([Var x])])
    | meas_type : forall env a x, type_vari env (Var a) C -> type_vari env (Var x) Q -> type_system C env (Meas a x) ([SPos ([Var x])])
    | pmeas_type : forall env p a x, type_vari env (Var p) C -> type_vari env (Var a) C
                        -> type_vari env (Var x) Q -> type_system C env (PMeas p x a) ([SPos ([Var x])])
    | while_type : forall m env p b al, (forall x, In x (collect_var_bexp b) -> AEnv.MapsTo x C env) ->
            type_system m env p al -> type_system m env (While b p) al
    | qwhile_type : forall m env p al n x f b, (forall y, In y (collect_var_aexp n) -> AEnv.MapsTo y C env) ->
                      AEnv.MapsTo x Q env -> (forall y, In y (collect_var_aexp f) -> y <> x -> AEnv.MapsTo y C env) ->
                      (forall y, In y (collect_var_bexp b) -> y <> x -> AEnv.MapsTo y C env) ->
                      type_system m env p al -> type_system m env (QWhile n x f b p) al
    | reflect_type : forall m env x l, AEnv.MapsTo x Q env -> type_system m env (Reflect x l) ([SPos ([Var x])]).
*)


(* Definition Type predicates that will be used in triple. *)

Inductive mode := Qmode (x:var) | Cmode.

Definition check_mode (a:mode) (b:var) := match a with Cmode => True | Qmode x => (x <> b) end.



(*
Inductive type_pred : Type := TAll (t:type_elem) | TITE (x:var) (bl: list (bexp * type_elem)).
*)

Fixpoint subst_num_aexp (a:aexp) (x:var) (b:aexp) :=
   match a with BA (Var y) => if x =? y then b else BA (Var y)
           |  APlus e1 e2 => APlus (subst_num_aexp e1 x b) (subst_num_aexp e2 x b)
           |  AMinus e1 e2 => AMinus (subst_num_aexp e1 x b) (subst_num_aexp e2 x b)
           |  AMult e1 e2 => AMult (subst_num_aexp e1 x b) (subst_num_aexp e2 x b)
           |  TwoTo e1 => TwoTo (subst_num_aexp e1 x b)
           |  App f e1 => App f (subst_num_aexp e1 x b)
           | a => a
   end.


Fixpoint subst_num_bexp (b:bexp) (x:var) (a:aexp) :=
   match b with BFalse => BFalse | BTrue => BTrue
            | BEq u v => BEq (subst_num_aexp u x a) (subst_num_aexp v x a) 
            | BGe u v => BGe (subst_num_aexp u x a) (subst_num_aexp v x a) 
            | BLt u v => BLt (subst_num_aexp u x a) (subst_num_aexp v x a) 
            | BAnd  u v => BAnd (subst_num_bexp u x a) (subst_num_bexp v x a)
            | BNeg u => BNeg (subst_num_bexp u x a)
            | a => a
   end.

(*
Inductive qtype := QS (t:type_pred) | QC (t:type_pred).
*)
(*
Inductive qtype := QS (l:list type_elem) | QC (vl:list (var * nat)) (l:list type_elem).

Inductive pexp_type : Type := Proba | Class | QMix (p:qtype) | Bot.


Definition type_env := (var * nat -> pexp_type).

Definition num_env := (var -> nat).

Definition value_env := (var -> nat).
Definition is_q_type (t:pexp_type) := match t with (QMix a) => True | _ => False end.


Definition add_p_env (p:pexp_type) (ty:type_elem) :=
    match p with (QMix (QS qs)) => (QMix (QS (ty::qs)))
               | a => a
    end.

Definition rm_elem_env (p:pexp_type) :=
    match p with (QMix (QS (a::qs))) => (QMix (QS (qs)))
               | a => a
    end.

Fixpoint eupdates_elem (tv:type_env) (x:var) (n:nat) (p:type_elem) := 
        match n with 0 => tv
            | S m => (eupdates_elem tv x m p)[(x,m) |-> add_p_env (tv (x,m)) p]
        end.

Fixpoint eupdates_rm (tv:type_env) (x:var) (n:nat) := 
        match n with 0 => tv
            | S m => (eupdates_rm tv x m)[(x,m) |-> rm_elem_env (tv (x,m))]
        end.

Fixpoint eupdate_list (tv:type_env) (l:list (var*nat)) (p:pexp_type) := 
        match l with [] => tv
            | (a::al) => (eupdate_list tv al p)[a |-> p]
        end.

Definition change_entangle (p:pexp_type) (l: list (var *nat)) :=
    match p with QMix (QS a) => QMix (QC l a)
             | a => a
    end.

Fixpoint eupdates_elem_ent (tv:type_env) (x:var) (n:nat) (p:list (var * nat)) := 
        match n with 0 => tv
            | S m => (eupdates_elem_ent tv x m p)[(x,m) |-> change_entangle (tv (x,m)) p]
        end.
*)
Definition azero :=  (Num 0).

Definition tazero := TV ( (Num 0)).




(*
Inductive tpred_elem := Uniform (x:posi) (p:pexp_type) | Binary (x:posi) (b:bexp) (p1:pexp_type) (p2:pexp_type).
*)

(*TODO: chage type predicate to a triple of (P, S, T) where S is a tuple of (var, list var)
  mapping from a ghost variable to a region of qubit array variables. P maps from ghost variable to type (CH type),
   t maps from qubit variable to type *)


Definition var_eqs := list ((var * aexp) * list (var * aexp)).
(*
Fixpoint subst_var_aexp (a:aexp) (x:var) (y:var) :=
   match a with BA b => BA (subst_var_vari b x y)
              | Num n => Num n
              | APlus e1 e2 => APlus (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
              | AMinus e1 e2 => AMinus (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
              | AMult e1 e2 => AMult (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
              | TwoTo e1 => TwoTo (subst_var_aexp e1 x y) 
              | App f e1 => if f =? x then App y (subst_var_aexp e1 x y) else App f (subst_var_aexp e1 x y)
   end

with subst_var_vari (a:vari) (x:var) (y:var) :=
   match a with Var q => if q =? x then Var y else Var q
             | Index q a => if q =? x then Index y (subst_var_aexp a x y) else Index q (subst_var_aexp a x y)
   end

with subst_var_bexp (b:bexp) (x:var) (y:var) :=
   match b with BFalse => BFalse | BTrue => BTrue
           | BEq e1 e2 => BEq (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
           | BGe e1 e2 => BGe (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
           | BLt e1 e2 => BLt (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
           | FEq e1 e2 => FEq e1 e2
           | FGe e1 e2 => FGe e1 e2
           | FLt e1 e2 => FLt e1 e2
           | BTest e1 e2 => BTest (subst_var_aexp e1 x y) (subst_var_aexp e2 x y)
           | BXOR e1 e2 => BXOR (subst_var_bexp e1 x y) (subst_var_bexp e2 x y)
           | BITE e1 e2 e3 => BITE (subst_var_bexp e1 x y) (subst_var_bexp e2 x y) (subst_var_bexp e3 x y)
           | BNeg e1 => BNeg (subst_var_bexp e1 x y)
  end.
*)


Fixpoint subst_aexp (a:aexp) (x:var) (y:aexp) :=
   match a with BA (Var q) => if q =? x then y else BA (Var q)
              | BA (Index q al) => BA (Index q (map (fun a => subst_aexp a x y) al))
              | Num n => Num n
              | APlus e1 e2 => APlus (subst_aexp e1 x y) (subst_aexp e2 x y)
              | AMinus e1 e2 => AMinus (subst_aexp e1 x y) (subst_aexp e2 x y)
              | AMult e1 e2 => AMult (subst_aexp e1 x y) (subst_aexp e2 x y)
              | TwoTo e1 => TwoTo (subst_aexp e1 x y) 
              | App f e1 => App f (subst_aexp e1 x y)
           | FExpI a => FExpI (subst_aexp a x y)
           | FAddExpI b a => FAddExpI (subst_bexp b x y) (subst_aexp a x y)

           | GetP s => GetP s
           | Left s => Left s
           | Right s => Right s
   end

with subst_bexp (b:bexp) (x:var) (y:aexp) :=
   match b with BFalse => BFalse | BTrue => BTrue
           | BEq e1 e2 => BEq (subst_aexp e1 x y) (subst_aexp e2 x y)
           | BGe e1 e2 => BGe (subst_aexp e1 x y) (subst_aexp e2 x y)
           | BLt e1 e2 => BLt (subst_aexp e1 x y) (subst_aexp e2 x y)
           | BTest (Var q) => BTest (Var q)
           | BTest (Index q al) => BTest (Index q (map (fun a => subst_aexp a x y) al))
           | BXOR e1 e2 => BXOR (subst_bexp e1 x y) (subst_bexp e2 x y)
           | BAnd e1 e2 => BAnd (subst_bexp e1 x y) (subst_bexp e2 x y)
           | BITE e1 e2 e3 => BITE (subst_bexp e1 x y) (subst_bexp e2 x y) (subst_bexp e3 x y)
           | BNeg e1 => BNeg (subst_bexp e1 x y)
           | GetB s => GetB s
  end.


Inductive qstate_equiv: var-> state -> var -> state -> Prop :=
   | ket_qket : forall new b,  qstate_equiv new (ket b) new (qket (FExpI (Num 0)) b)
   | ten_sigma : forall new n i q s, qstate_equiv new (NTensor n i (Num 0) (qket q s))
                   (fresh new) (Sigma (TwoTo n) (new) (Num 0) (NTensor n i (Num 0) (qket q s)))
   | plus_sigma_1 : forall new q b, qstate_equiv new (SPlus (qket q b) (qket q (BNeg b)))
                   (fresh new) (Sigma (Num 2) (new) (Num 0) (qket q (BXOR (BTest ( (Index new [(Num 0)]))) b)))
   | plus_sigma_2 : forall new q b, qstate_equiv new (SPlus (qket q (BNeg b)) (qket q b))
                   (fresh new) (Sigma (Num 2) (new) (Num 0) (qket q (BXOR (BNeg (BTest ((Index new [ (Num 0)])))) b)))
   | ten_sigma_sigma: forall new n i j q b, qstate_equiv new (NTensor n i (Num 0) (Sigma (Num 2) j (Num 0) (qket q b)))
                   (fresh new) (Sigma (TwoTo n) (new) (Num 0) (NTensor n i (Num 0)
             (qket q (BITE (BTest (Index new [(BA (Var j))])) (subst_bexp b j (Num 0)) (subst_bexp b j (Num 1))))))
(*
   | tensor_sub_1 : forall new new' s1 s1' s2, qstate_equiv new s1 new' s1' ->  qstate_equiv new (Tensor s2 s1) new' (Tensor s2 s1')
   | tensor_sub_2 : forall new new' s1 s1' s2, qstate_equiv new s1 new' s1' ->  qstate_equiv new (Tensor s2 s1) new' (Tensor s2 s1')
*)
   | tensor_cut : forall new n i m q b, qstate_equiv new (NTensor n i m (qket q b))
                 new (Tensor ((qket q (subst_bexp b i m)):: (NTensor n i (APlus m (Num 1)) (qket q b))::nil))
   | tensor_merge : forall new n i m b q b', subst_bexp b i n = b' -> 
            qstate_equiv new (Tensor ((NTensor n i m (qket q b)):: (qket q b')::nil)) new (NTensor (APlus n (Num 1)) i m (qket q b)).
     
Definition change_h (s:state) :=
   match s with (NTensor n i s (qket q b)) => (NTensor n i s (SPlus (qket q b) (qket q (BNeg b))))
              | (NTensor n i s (Sigma (Num 2) j (Num 0)  (qket q b))) => (NTensor n i s  (qket q (subst_bexp b j (Num 0))))
       | a => a
   end.

Definition change_h_single (s:state) :=
  match s with (Tensor ((NTensor n i m st):: (qket q b):: st')) => 
           (Tensor ((NTensor n i m st):: (SPlus (qket q b) (qket q (BNeg b))):: st'))
       | a => a
  end.

Definition vari_eq (a:vari) (b:vari) :=
    match a with Var x => match b with Var y => x =? y
                                     | _ => false
                          end
              | Index x xl => false
    end.

Fixpoint list_vari_mem (a:vari) (l:list vari) :=
    match l with [] => false
             | x::xs => if vari_eq a x then true else list_vari_mem a xs
    end.

Fixpoint subst_add_aexp (a:aexp) x (xa: state) :=
   match a with BA b => BA (subst_add_vari b x xa)
              | Num n => Num n
              | APlus e1 e2 => APlus (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
              | AMinus e1 e2 => AMinus (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
              | AMult e1 e2 => AMult (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
              | TwoTo e1 => TwoTo (subst_add_aexp e1 x xa)
              | App f e1 => App f (subst_add_aexp e1 x xa)
              | FExpI e1 => FExpI (subst_add_aexp e1 x xa)
              | FAddExpI e1 e2 => FAddExpI (subst_add_bexp e1 x xa) (subst_add_aexp e2 x xa)
              | GetP e1 => GetP (subst_add_state e1 x xa)
              | Left e1 => Left (subst_add_state e1 x xa)
              | Right e1 => Right (subst_add_state e1 x xa)
   end

with subst_add_vari (v:vari) (x:var) (xa: state) :=
    match v with Var x => Var x | Index x al => Index x (map (fun a => subst_add_aexp a x xa) al) end

with subst_add_bexp (b:bexp) x (xa: state) :=
   match b with BFalse => BFalse | BTrue => BTrue
          | BEq e1 e2 => BEq (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
          | BGe e1 e2 => BGe (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
          | BLt e1 e2 => BLt (subst_add_aexp e1 x xa) (subst_add_aexp e2 x xa)
          | BTest e2 => BTest (subst_add_vari e2 x xa)
          | BXOR e1 e2 => BXOR (subst_add_bexp e1 x xa) (subst_add_bexp e2 x xa)
          | BITE b e1 e2 => BITE (subst_add_bexp b x xa) (subst_add_bexp e1 x xa) (subst_add_bexp e2 x xa)
          | BNeg e1 => BNeg (subst_add_bexp e1 x xa)
          | BAnd e1 e2 => BAnd (subst_add_bexp e1 x xa) (subst_add_bexp e2 x xa)
          | GetB e1 => GetB (subst_add_state e1 x xa)
   end

with subst_add_state (v:state) x (xa: state) :=
  match v with SA xl al => if list_vari_mem (Var x) xl then SA xl (([Var x],xa)::al)
                           else SA xl al
             | ket b => ket (subst_add_bexp b x xa)
             | qket p b => qket (subst_add_aexp p x xa) (subst_add_bexp b x xa)
             | SITE b e1 e2 => SITE (subst_add_bexp b x xa) (subst_add_state e1 x xa) (subst_add_state e2 x xa)
             | SPlus e1 e2 => SPlus (subst_add_state e1 x xa) (subst_add_state e2 x xa)
             | Tensor el => Tensor (map (fun a => subst_add_state a x xa) el)
             | Sigma n i b e1 => Sigma (subst_add_aexp n x xa) i (subst_add_aexp b x xa) (subst_add_state e1 x xa)
             | NTensor n i b e1 => NTensor (subst_add_aexp n x xa) i (subst_add_aexp b x xa) (subst_add_state e1 x xa)
  end.

Fixpoint subst_add_cpred (c:cpred_elem) x (xa: state) :=
   match c with PFalse => PFalse
     | CState b => CState (subst_add_bexp b x xa)
     | QState e1 e2 => QState (subst_add_state e1 x xa) (subst_add_state e2 x xa)
     | QIn p a e1 => QIn (subst_add_aexp p x xa) (subst_add_aexp a x xa) (subst_add_state e1 x xa)
     | PNot p => PNot (subst_add_cpred p x xa)
     | CForall xs p1 p2 => if list_mem x xs then CForall xs p1 p2 else 
                    CForall xs (map (fun a => subst_add_cpred a x xa) p1) (subst_add_cpred p2 x xa)
     | Valid r b => Valid (subst_add_bexp r x xa) (subst_add_bexp b x xa)
   end.


Fixpoint isubst_add_aexp (a:aexp) x (i:aexp) (xa: state) :=
   match a with BA b => BA (isubst_add_vari b x i xa)
              | Num n => Num n
              | APlus e1 e2 => APlus (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
              | AMinus e1 e2 => AMinus (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
              | AMult e1 e2 => AMult (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
              | TwoTo e1 => TwoTo (isubst_add_aexp e1 x i xa)
              | App f e1 => App f (isubst_add_aexp e1 x i xa)
              | FExpI e1 => FExpI (isubst_add_aexp e1 x i xa)
              | FAddExpI e1 e2 => FAddExpI (isubst_add_bexp e1 x i xa) (isubst_add_aexp e2 x i xa)
              | GetP e1 => GetP (isubst_add_state e1 x i xa)
              | Left e1 => Left (isubst_add_state e1 x i xa)
              | Right e1 => Right (isubst_add_state e1 x i xa)
   end

with isubst_add_vari (v:vari) (x:var) i (xa: state) :=
    match v with Var x => Var x | Index x al => Index x (map (fun a => isubst_add_aexp a x i xa) al) end

with isubst_add_bexp (b:bexp) x i (xa: state) :=
   match b with BFalse => BFalse | BTrue => BTrue
          | BEq e1 e2 => BEq (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
          | BGe e1 e2 => BGe (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
          | BLt e1 e2 => BLt (isubst_add_aexp e1 x i xa) (isubst_add_aexp e2 x i xa)
          | BTest e2 => BTest (isubst_add_vari e2 x i xa)
          | BXOR e1 e2 => BXOR (isubst_add_bexp e1 x i xa) (isubst_add_bexp e2 x i xa)
          | BITE b e1 e2 => BITE (isubst_add_bexp b x i xa) (isubst_add_bexp e1 x i xa) (isubst_add_bexp e2 x i xa)
          | BNeg e1 => BNeg (isubst_add_bexp e1 x i xa)
          | BAnd e1 e2 => BAnd (isubst_add_bexp e1 x i xa) (isubst_add_bexp e2 x i xa)
          | GetB e1 => GetB (isubst_add_state e1 x i xa)
   end

with isubst_add_state (v:state) x i (xa: state) :=
  match v with SA xl al => if list_vari_mem (Var x) xl then SA xl (([Index x [i]],xa)::al)
                           else SA xl al
             | ket b => ket (isubst_add_bexp b x i xa)
             | qket p b => qket (isubst_add_aexp p x i xa) (isubst_add_bexp b x i xa)
             | SITE b e1 e2 => SITE (isubst_add_bexp b x i xa) (isubst_add_state e1 x i xa) (isubst_add_state e2 x i xa)
             | SPlus e1 e2 => SPlus (isubst_add_state e1 x i xa) (isubst_add_state e2 x i xa)
             | Tensor el => Tensor (map (fun a => isubst_add_state a x i xa) el)
             | Sigma n a b e1 => Sigma (isubst_add_aexp n x i xa) a (isubst_add_aexp b x i xa) (isubst_add_state e1 x i xa)
             | NTensor n a b e1 => NTensor (isubst_add_aexp n x i xa) a (isubst_add_aexp b x i xa) (isubst_add_state e1 x i xa)
  end.

Fixpoint isubst_add_cpred (c:cpred_elem) x i (xa: state) :=
   match c with PFalse => PFalse
     | CState b => CState (isubst_add_bexp b x i xa)
     | QState e1 e2 => QState (isubst_add_state e1 x i xa) (isubst_add_state e2 x i xa)
     | QIn p a e1 => QIn (isubst_add_aexp p x i xa) (isubst_add_aexp a x i xa) (isubst_add_state e1 x i xa)
     | PNot p => PNot (isubst_add_cpred p x i xa)
     | CForall xs p1 p2 => if list_mem x xs then CForall xs p1 p2 else 
                    CForall xs (map (fun a => isubst_add_cpred a x i xa) p1) (isubst_add_cpred p2 x i xa)
     | Valid r b => Valid (isubst_add_bexp r x i xa) (isubst_add_bexp b x i xa)
   end.




Fixpoint list_equal (al bl : list vari) :=
  match (al,bl) with ([],[]) => true | (a::xl,b::yl) => (vari_eq_dec a b) && list_equal xl yl  | _ => false end.


Fixpoint subst_adds_aexp (a:aexp) (xa: list vari * state) :=
   match a with BA b => BA (subst_adds_vari b xa)
              | Num n => Num n
              | APlus e1 e2 => APlus (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
              | AMinus e1 e2 => AMinus (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
              | AMult e1 e2 => AMult (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
              | TwoTo e1 => TwoTo (subst_adds_aexp e1 xa)
              | App f e1 => App f (subst_adds_aexp e1 xa)
              | FExpI e1 => FExpI (subst_adds_aexp e1 xa)
              | FAddExpI e1 e2 => FAddExpI (subst_adds_bexp e1 xa) (subst_adds_aexp e2 xa)
              | GetP e1 => GetP (subst_adds_state e1 xa)
              | Left e1 => Left (subst_adds_state e1 xa)
              | Right e1 => Right (subst_adds_state e1 xa)
   end

with subst_adds_vari (v:vari) (xa: list vari * state) :=
    match v with Var x => Var x | Index x al => Index x (map (fun a => subst_adds_aexp a xa) al) end

with subst_adds_bexp (b:bexp) (xa: list vari * state) :=
   match b with BFalse => BFalse | BTrue => BTrue
          | BEq e1 e2 => BEq (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
          | BGe e1 e2 => BGe (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
          | BLt e1 e2 => BLt (subst_adds_aexp e1 xa) (subst_adds_aexp e2 xa)
          | BTest e2 => BTest (subst_adds_vari e2 xa)
          | BXOR e1 e2 => BXOR (subst_adds_bexp e1 xa) (subst_adds_bexp e2 xa)
          | BITE b e1 e2 => BITE (subst_adds_bexp b xa) (subst_adds_bexp e1 xa) (subst_adds_bexp e2 xa)
          | BNeg e1 => BNeg (subst_adds_bexp e1 xa)
          | BAnd e1 e2 => BAnd (subst_adds_bexp e1 xa) (subst_adds_bexp e2 xa)
          | GetB e1 => GetB (subst_adds_state e1 xa)
   end

with subst_adds_state (v:state) (xa: list vari * state) :=
  match v with SA xl al => if list_equal (fst xa) xl  then SA xl (xa::al)
                           else SA xl al
             | ket b => ket (subst_adds_bexp b xa)
             | qket p b => qket (subst_adds_aexp p xa) (subst_adds_bexp b xa)
             | SITE b e1 e2 => SITE (subst_adds_bexp b xa) (subst_adds_state e1 xa) (subst_adds_state e2 xa)
             | SPlus e1 e2 => SPlus (subst_adds_state e1 xa) (subst_adds_state e2 xa)
             | Tensor el => Tensor (map (fun a => subst_adds_state a xa) el)
             | Sigma n i b e1 => Sigma (subst_adds_aexp n xa) i (subst_adds_aexp b xa) (subst_adds_state e1 xa)
             | NTensor n i b e1 => NTensor (subst_adds_aexp n xa) i (subst_adds_aexp b xa) (subst_adds_state e1 xa)
  end.

Fixpoint subst_adds_cpred (c:cpred_elem) (xa: list vari * state) :=
   match c with PFalse => PFalse
     | CState b => CState (subst_adds_bexp b xa)
     | QState e1 e2 => QState (subst_adds_state e1 xa) (subst_adds_state e2 xa)
     | QIn p a e1 => QIn (subst_adds_aexp p xa) (subst_adds_aexp a xa) (subst_adds_state e1 xa)
     | PNot p => PNot (subst_adds_cpred p xa)
     | CForall xs p1 p2 => CForall xs (map (fun a => subst_adds_cpred a xa) p1) (subst_adds_cpred p2 xa)
     | Valid r b => Valid (subst_adds_bexp r xa) (subst_adds_bexp b xa)
   end.

Definition  subst_adds_cpreds (c:list cpred_elem) (xa: list vari * state) :=
        List.map (fun a => subst_adds_cpred a xa) c.

Inductive triple {env:aenv} : var -> (var_eqs * tpred * cpred) -> pexp -> var -> (var_eqs * tpred * cpred)  -> Prop :=
     (*| conjSep : forall e P P' Q, triple P e P' -> triple (PAnd P Q) e (PAnd P' Q). *)
     | eqs_comm : forall new x y T V e, triple new (x++y,T,V) e new (y++x,T,V)
     | tpred_comm : forall new x y A V e, triple new (A,x++y,V) e new (A,y++x,V)
     | vpred_comm : forall new x y A T e, triple new (A,T,x++y) e new (A,T,y++x)
     | equiv_app : forall new new' x s s' e A T V, qstate_equiv new s new' s' -> triple new (A,T,(QState x s)::V) e new' (A,T,(QState x s)::V).
     | appH_1 : forall new x n T P , 
         triple new ((([(x,n)], (TAll TNor)))::T,
           (map (fun a => subst_add_cpred a x (NTensor n new (Num 0)
                          (SPlus (qket (GetP (SA ((Index x [BA (Var new)])::nil) [])) BFalse)
                                 (SITE (GetB (SA ((Index x [BA (Var new)])::nil) []))
                                     (qket (GetP (SA ((Index x [BA (Var new)])::nil) [])) BTrue)
                                       (qket (AMult (AMinus (Num 0) (Num 1)) (GetP (SA ((Index x [BA (Var new)])::nil) []))) BTrue))))) P))
              (AppU H_gate (Var x)) (fresh new) ((([(x,n)], (TAll (TH (TV (Num 0))))))::T,  P)
     | appH_2 : forall new x i n T P , 
         triple new ((([(x,n)], (TAll TNor)))::T,
           (map (fun a => isubst_add_cpred a x i (NTensor n new (Num 0)
                          (SPlus (qket (GetP (SA ((Index x [BA (Var new)])::nil) [])) BFalse)
                                 (SITE (GetB (SA ((Index x [BA (Var new)])::nil) []))
                                     (qket (GetP (SA ((Index x [BA (Var new)])::nil) [])) BTrue)
                                       (qket (AMult (AMinus (Num 0) (Num 1)) (GetP (SA ((Index x [BA (Var new)])::nil) []))) BTrue))))) P))
              (AppU H_gate (Index x ([i]))) (fresh new) ((([(x,n)], (TAll (TH (TV (Num 0))))))::T,  (CState (BEq i (Num 0)))::P)

     | if_1 : forall new new' new'' b e1 e2 x n y bl ba r a l T P be1 be2, type_bexp env b (Q,[Index x [a]]) -> In (ba,TH r) bl -> 
         type_system Q env e1 l -> 
         triple new (T,subst_adds_cpreds P (l,be1)) e1 new' (T,P) ->
         triple new' (T,subst_adds_cpreds P (l,be2)) e2 new'' (T,P) ->
         triple new ((([(x,n)], TITE y bl))::T, (subst_adds_cpreds P ((Index x [a])::l,
                           SPlus (Tensor ((ket b)::[be1])) (Tensor ((ket (BNeg b))::[be2])))))
              (IfExp b e1 e2) new'' ((([(x,n)], (TAll (TH (TV (Num 0))))))::T,  (CState (subst_num_bexp ba y a))::P)
     | if_2 : forall new new' new'' b e1 e2 x n r l T P be1 be2, type_bexp env b (Q,[Var x]) -> type_system Q env e1 l -> 
         triple new (T,subst_adds_cpreds P (l,be1)) e1 new' (T,P) ->
         triple new' (T,subst_adds_cpreds P (l,be2)) e2 new'' (T,P) ->
         triple new ((([(x,n)], TAll (TH r)))::T, (subst_adds_cpreds P ((Var x)::l,
                Sigma n new'' (Num 0) (SPlus (Tensor ((ket (subst_bexp b x (BA (Var new''))))::[be1]))
                     (Tensor ((ket (subst_bexp b x (BA (Var new''))))::[be2]))) )))
              (IfExp b e1 e2) (fresh new'') ((([(x,n)], (TAll (TH (TV (Num 0))))))::T, 
                         (PNot (Valid (BAnd (BGe (BA (Var x)) (Num 0)) (BLt (BA (Var x)) n)) (BNeg b)))::
                                    (PNot (Valid (BAnd (BGe (BA (Var x)) (Num 0)) (BLt (BA (Var x)) n)) b))::P)

     | qwhile_rule : forall new new' T P m n x f b e xl r, type_bexp env b (Q,[Var x]) -> type_system Q env e xl -> 
         triple (fresh new) (T,(CState (BGe (BA (Var x)) (BA (Var new))))::(CState (subst_bexp b x (BA (Var new))))::[QState (SA ((Var x)::xl) []) P])
               e new' (T,[QState (SA ((Var x)::xl) []) P]) ->
         triple new ((([(x,n)], TAll (TH r)))::T, [QState (SA ((Var x)::xl) []) (Sigma m x (Num 0) P)])
              (QWhile m x f b e) new' ((([(x,n)], TAll (TH r)))::T, 
                 (CState (BNeg (subst_bexp b x m)))::[QState (SA ((Var x)::xl) []) (Sigma m x (Num 0) P)]).
(*
            | QWhile (n:aexp) (x:var) (f:aexp) (b:bexp) (e:pexp) 


     | tensorSep_1 : forall new x qs P P' Q e T V, 
           triple new (( ([(x)]), P)::qs, T, V) e new (( ([(x)]), P')::qs, T, V) ->
           triple new (( ([(x)]), (Tensor P Q))::qs, T, V) e new (( ([(x)]), (Tensor P' Q))::qs, T, V)
           (* Ethan: Bigger space = need more variables? *)
     | tensorSep_2 : forall new x P Q Q' e qs T V, 
           triple new (( ([(x)]), Q)::qs,T,V) e new (( ([(x)]), Q')::qs,T,V) ->
           triple new (( ([(x)]), (Tensor P Q))::qs,T,V) e new (( ([(x)]), (Tensor P Q'))::qs,T,V)
     | tensorSep_3 : forall new x m n ys y i  e s s' qs ts t T V, 
           triple new ((x::ys, (NTensor m y i s))::qs,((x,m)::ts,t)::T,V)
                      e new ((x::ys, (NTensor m y i s'))::qs,((x,m)::ts,t)::T,V) ->
           triple new ((x::ys, (Tensor (NTensor m y i s) (NTensor n y m s)))::qs,((x,n)::ts,t)::T,V) 
                       e new ((x::ys, (Tensor (NTensor m y i s') (NTensor n y m s)))::qs,((x,n)::ts,t)::T,(CState (BGe n m))::V).
     | appH_1 : forall new x n s qs T P , 
         triple new (([x], s)::qs,(([(x,n)], (TAll TNor)))::T, P)
              (AppU H_gate (Var x)) new (([x], (change_h s))::qs, (([(x,n)], (TAll (TH (TV (Num 0))))))::T,  P)
     | appH_2 : forall new x n s qs T P , 
         triple new (([x], s)::qs,(([(x,n)], (TAll (TH (TV (Num 0))))))::T, P)
              (AppU H_gate (Var x)) new (([x], (change_h s))::qs, (([(x,n)], (TAll TNor)))::T,  P)
     | appH_3 : forall new x i n s qs T P , 
         triple new (([x], s)::qs,(([(x,n)], (TAll TNor)))::T, P)
              (AppU H_gate (Index x i)) (fresh new) (([x], (change_h_single s))::qs,
                   (([(x,n)], (TITE new (BLt (BA (Var new)) (Num 1)) 
                          ((TH (TV (Num 0)))) (TNor))))::T,  (CState (BEq i (Num 0)))::(CState (BLt i n))::P)
     | appH_4 : forall new x i n s qs T P , 
         triple new (([x], s)::qs,(([(x,n)], (TAll TNor)))::T, P)
              (AppU H_gate (Index x i)) (fresh new) (([x], (change_h_single s))::qs,
                   (([(x,n)], (TITE new (BLt (BA (Var new)) (Num 1)) 
                          ((TC ([x]) (TV (Num 0)))) (TNor))))::T,  (CState (BEq i (Num 0)))::(CState (BLt i n))::P)
     | appH_5 : forall new x i n j m tv s qs T P , 
         triple new (([x], s)::qs,(([(x,n)], (TITE j (BLt (BA (Var j)) m) 
                          ((TH tv)) (TNor))))::T, P)
              (AppU H_gate (Index x i)) (fresh new) (([x], (change_h_single s))::qs,
                   (([(x,n)], (TITE j (BLt (BA (Var j)) (APlus m (Num 1))) 
                          ((TH tv)) (TNor))))::T,  (CState (BEq i n))::(CState (BLt i n))::P)
     | if_1 : forall new new' new'' b e1 e2 V T P V' T' P', type_bexp env b C ->
                  triple new (V,T,(CState b)::P) (IfExp b e1 e2) new' (V',T',P') ->
                  triple new' (V,T,(PNot (CState b))::P) (IfExp b e1 e2) new'' (V',T',P') ->
                          triple new (V,T,P) (IfExp b e1 e2) new'' (V',T',P')
     | if_2 : forall new new' new'' b e1 e2 V T P V' T' P', type_bexp env b Q ->
                  triple new (V,T,(CState b)::P) (IfExp b e1 e2) new' (V',T',P') ->
                  triple new' (V,T,(PNot (CState b))::P) (IfExp b e1 e2) new'' (V',T',P') ->
                          triple new (V,T,P) (IfExp b e1 e2) new'' (V',T',P').
*)
(*

            | IfExp (b:bexp) (e1:pexp) (e2:pexp) | While (b:bexp) (p:pexp)
            | Classic (p:exp) (args: list (var * aexp * aexp))

*)

(* Ethan: Need discussion and example to understand how num_env works *)
(* Old Type system
Inductive type_system : mode -> num_env * type_env -> pexp -> num_env * type_env -> Prop :=
    | seq_type : forall m s1 s2 tv tv' tv'', type_system m tv s1 tv' -> type_system m tv' s1 tv'' -> type_system m tv (PSeq s1 s2) tv''.
    | app_h_type_1 : forall m S tv x n, tv (x,n) = QMix (QS nil) -> check_mode m x ->
                type_system m (S,tv) (AppU H_gate (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ([TH tazero])))]))
    | app_h_type_2 : forall m S tv qs x n, tv (x,n) = QMix (QS ((TH tazero)::qs)) -> check_mode m x ->
                type_system m (S,tv) (AppU H_gate (x,BA (Num n)))(S, (tv[(x,n) |-> (QMix (QS qs))]))
    | app_qft_type_1 : forall m S tv x, check_mode m x ->
                (forall i, i < S x -> tv (x,i) = QMix (QS (([]))))
                -> type_system m (S,tv) (QFT x) (S,(eupdates_elem tv x (S x) (TQFT tazero)))
    | app_qft_type_2 : forall m S tv x r qs, check_mode m x ->
                (forall i, i < S x -> tv (x,i) = QMix (QS (((TQFT r)::qs))))
                -> type_system m (S,tv) (QFT x) (S,(eupdates_rm tv x (S x) ))


    | app_rqft_type_1 : forall m S tv qs x n, check_mode m x ->
                S x = n -> (forall i r, i < n -> tv (x,i) = QMix (QS ((TH r)::qs)))
                -> type_system m (S,tv) (RQFT x) (S,(eupdates_elem tv x n (TRQFT Infty)))
    | app_rqft_type_2 : forall m S tv qs x n, check_mode m x ->
                S x = n -> (forall i , i < n -> tv (x,i) = QMix (QS ((TQFT tazero)::qs)))
                -> type_system m (S,tv) (RQFT x) (S,(eupdates_rm tv x n ))
    | app_cx_type_1 : forall ma S tv qs r x n y m, check_mode ma x -> check_mode ma y ->
                     tv (x,n)= QMix (QS ((TH r)::qs)) -> tv (y,m) = QMix (QS nil)
                -> type_system ma (S,tv) (CX (x,BA (Num n)) (y,BA (Num m))) 
                         (S,tv[(x,n) |-> (QMix (QC ((x,n)::((y,m)::nil)) ((TH r)::qs)))]
                                [(y,m) |-> (QMix (QC ((x,n)::((y,m)::nil)) ((TH r)::qs)))])
    | app_cx_type_2 : forall ma S tv vs qs x n y m, check_mode ma x -> check_mode ma y ->
               tv (x,n)= QMix (QC vs (qs)) -> tv (y,m) = QMix (QS nil)
                -> type_system ma (S,tv) (CX (x,BA (Num n)) (y,BA (Num m))) (S,eupdate_list tv ((y,m)::vs) (QMix (QC ((y,m)::vs) (qs))))
    | app_x_type_1 : forall ma S tv x n, check_mode ma x -> tv (x,n) = QMix (QS nil)
                -> type_system ma (S,tv) (AppU X_gate (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ([])))]))
    | app_x_type_2 : forall ma S tv x n r qs, check_mode ma x -> tv (x,n) = QMix (QS ((TH (TV r))::qs))
                -> type_system ma (S,tv) (AppU X_gate (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ((TH (TV (APlus r (BA (Num 1)))))::qs)))]))
    | app_rz_type_1 : forall ma S tv x n r, check_mode ma x -> tv (x,n) = QMix (QS ([]))
                -> type_system ma (S,tv) (AppU (RZ_gate r) (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ([])))]))
    | app_rz_type_2 : forall ma S tv x n q r qs, check_mode ma x -> tv (x,n) = QMix (QS ((TH (TV r))::qs))
                -> type_system ma (S,tv) (AppU (RZ_gate q) (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ((TH (TV (APlus r q)))::qs)))]))
    | assign_type : forall ma S tv x v n, S x = v -> (forall i, i < v -> tv (x,i) = Class)
                -> type_system ma (S,tv) (Assign x n) (S,tv)
    | qwhile_type : forall S tv n x f b e, (forall y i, In y (collect_var_bexp b) -> x <> y -> i < S y -> (tv (y,i) = Proba \/ tv  (y,i) = Class)) ->
          type_system (Qmode x) (S,tv) e (S,tv) -> type_system Cmode (S,tv) (QWhile n x f b e) (S,tv)
    | while_type : forall S tv b e, (forall y i, In y (collect_var_bexp b) -> i < S y -> (tv (y,i) = Proba \/ tv  (y,i) = Class)) ->
          type_system Cmode (S,tv) e (S,tv) -> type_system Cmode (S,tv) (While b e) (S,tv)
    | mea_type : forall S tv a x, (forall i, i < S a -> tv (a,i) = Class) -> (forall i, i < S x -> is_q_type (tv (x,i))) ->
                     type_system Cmode (S,tv) (Meas a x) (S,tv)
    | pmea_type : forall S tv p a x, (forall i, i < S a -> tv (a,i) = Proba) ->
         (forall i, i < S a -> tv (a,i) = Class) -> (forall i, i < S x -> is_q_type (tv (x,i))) ->
                     type_system Cmode (S,tv) (PMeas p a x) (S,tv)
    | class_type : forall ma S tv x p args q s, (forall y i, In y args -> i < S y -> tv (y,i) = Class) ->
          (forall i, i < S x -> is_q_type (tv (x,i))) -> (forall y, In y (collect_var_aexp s) -> y = x \/ In y args) ->
           type_system ma (S,tv) (Classic x p args q s) (S,tv)
    | cu_type_1 : forall ma S tv x a z p args q, (forall y i, In y args -> i < S y -> tv (y,i) = Class) ->
          (is_q_type (tv (x,a))) -> (forall i, i < S z -> (tv (z,i)) = QMix (QS nil)) ->
           type_system ma (S,tv) (CU (x,(BA (Num a))) p z args q (BA (Var x))) (S,tv)
    | cu_type_2 : forall ma S tv x a z p args q n qs, n <> 0 ->
           (forall y i, In y args -> i < S y -> tv (y,i) = Class) -> tv (x,a) = QMix (QS qs) ->
           type_system ma (S,tv) (CU (x,(BA (Num a)))
              p z args q (APlus (BA (Var x)) (BA (Num n)))) 
           (S,eupdates_elem_ent (eupdate tv (x,a) (QMix (QC ((x,a)::(z,0)::nil) qs))) z (S z) ((x,a)::(z,0)::nil)) .


Definition change_h (s:state) :=
   match s with (Tensor s1 (NTensor n i b (ket ( (Num 0))))) => 
         Tensor s1 (Tensor (Sigma ( (Num 2)) i ( (Num 0)) (ket ( (Var i)))) 
                  (NTensor n i (APlus b ( (Num 1))) (ket ( (Num 0)))))
       | a => a
   end.

Inductive state :Type :=
             | STrue (* meaning that the initial state with any possible values. *)
             | ket (b:bexp) (*normal state |0> false or |1> true *)
             | qket (p:fexp) (b:bexp)
             | SPlus (s1:state) (s2:state)  (* Let's say that we only allow |0> + |1> first. *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).










Definition add_num (x:aexp) (n:nat) := 
    match x with APlus e1 (BA (Num m)) => APlus e1 (BA (Num (m+n)))
               | APlus (BA (Num m)) e2 => APlus (BA (Num (m+n))) e2
               | a => APlus a (BA (Num n))
    end.

(* Ethan: Maybe just `fst` instead of match? *)
Definition in_set (x:var) (l:list (var * basic)) :=
     match List.split l with (la,lb) => In x la end.


Check List.find.

Definition in_set_bool (x:var) (l:list (var * basic)) :=
     match List.split l with (la,lb) => match List.find (fun y => y =? x) la with Some _ => true | _ => false end end.

(* Ethan: Maybe better version below *)
Definition in_set_bool' (x : var) (l : list (var * basic)) :=
  in_dec Nat.eq_dec x (fst (List.split l)).

Inductive eq_state : state -> state -> Prop :=
      | tensor_assoc : forall s1 s2 s3, eq_state (Tensor s1 (Tensor s2 s3)) (Tensor (Tensor s1 s2) s3)
      | tensor_break_1 : forall n i j s,
           eq_state (NTensor n i j s) (Tensor s  (NTensor n i (add_num j 1) s))
      | tensor_empty : forall n i a s,
           eq_state (Tensor a (NTensor n i n s)) a.

Inductive eq_cpred : cpred -> cpred -> Prop :=
      | cpred_comm: forall x y, eq_cpred (x++y) (y++x).

Inductive eq_qpred : qpred -> qpred -> Prop :=
      | qpred_comm: forall x y, eq_qpred (x++y) (y++x)
      | qpred_join : forall vs vsa s s1 qs, 
            eq_qpred ((PState vs s)::(PState vsa s1)::qs) (PState (vs++vsa) (Tensor s s1)::qs).


Inductive eq_tpred : tpred -> tpred -> Prop :=
      | tpred_comm: forall x y, eq_tpred (x++y) (y++x).

*)
(* Classical State including variable relations that may be quantum *)



(*
Inductive eq_pred : predi -> predi -> Prop :=
      | and_comm : forall s1 s2, eq_pred (PAnd s1 s2) (PAnd s2 s1)
      | and_assoc : forall s1 s2 s3, eq_pred (PAnd s1 (PAnd s2 s3)) (PAnd (PAnd s1 s2) s3)
      | and_tensor : forall l1 l2 s1 s2, eq_pred (PAnd (PState l1 s1) (PState l2 s2)) (PState (l1++l2) (Tensor s1 s2)).
*)

(* Ethan: Currently only works on 0?
 * Also why is this construction necessary if we already have tensor rules?
 *)



(* effects of applying cx. 
Fixpoint change_cx_aux_1 (s:state) :=
     match s with Sigma n i b s => Sigma n i b (change_cx_aux_1 s)
       | NTensor n i b (ket (BA (Num 0))) => Tensor (NTensor n i b (ket (BA (Num 0)))) ((ket (BA (Num 1))))
       | NTensor n i b (ket (BA (Num 1))) => Tensor (NTensor n i b (ket (BA (Num 1)))) ((ket (BA (Num 0))))
     | a => a
    end.

Fixpoint change_cx_aux (s:state) :=
     match s with Sigma n i b s => Sigma n i b (change_cx_aux s)
       | NTensor n i b s => NTensor n i (APlus b (BA (Num 1))) s
     | a => a
    end.

Definition change_cx (s:state) := 
   match s with (Tensor s1 (NTensor n i b (ket (BA (Num 0)))))
       => (Tensor (change_cx_aux s1) (NTensor n i (APlus b (BA (Num 1))) (ket (BA (Num 0))))) 
      | (Tensor s1 (NTensor n i b (ket (BA (Num 1)))))
       => (Tensor (change_cx_aux_1 s1) (NTensor n i (APlus b (BA (Num 1))) (ket (BA (Num 1))))) 
      | a => a
   end.

Definition add_phi (s:state) (p:aexp) := 
   match s with SPlus s1 (qket f s2) => SPlus s1 (qket (FTimes (FExpI p) f) s2)
    | a => a
   end.
*)

(*
            | CU (x:posi) (p:exp) (z:var) (args: list var) (p:aexp) (s:aexp)


     | appCX_1 : forall x i y j s v,  get_ket s x i = Some v -> is_ket s y j ->
         triple s (CX (x,(Num i)) (y,(Num j))) (change_cx_1 s y j v)
     | appCX_2 : forall x i y j s u v q,  get_sigma s x i = Some (u,v) -> is_ket s y j ->
         triple s (CX (x,(Num i)) (y,(Num j))) (PAnd (turn_cx_2 s y j q)
                       (Forall q (PAnd (CState (BLe (BA (Num 0)) (BA (Var q)))) (CState (BLt (BA (Var q)) (BA v))))
                           (CState (BEq (Index (x,(Num i)) (BA (Var q))) (Index (y,(Num j)) (BA (Var q)))))))
     | appState : forall P l x n i b e q, in_set x l ->
         triple (PAnd P (PState l (NTensor (n:aexp) (i:var) (b:aexp) (ket e)))) (State x)
                (PAnd P (PState l (NTensor (n:aexp) (i:var) (b:aexp) (Sigma (BA (Num 2)) q (BA (Num 0)) (times_phase q b)))))
     | appCU : forall P l s1 s s' x p y j m k q b, in_set x l -> in_set y l ->
         triple (PState ([(y,Num m)]) s) (Classic p) (PState ([(y,Num m)]) s') ->
         triple (PAnd P (PState ((x,Num (j+1))::((y, Num m)::[]))
                 (Tensor (Tensor (NTensor (BA (Num j)) k (BA (Num 0)) s1) (Sigma (BA (Num 2)) q (BA (Num 0)) (ket b))) s)))
                    (CU (x,(Num j)) p y)
                 (PAnd P (PState ((x,Num (j+1))::((y, Num m)::[]))
                 (Tensor (NTensor (BA (Num j)) k (BA (Num 0)) s1) 
                     (SPlus (Tensor (ket (BA (Num 0))) s) (Tensor (ket (BA (Num 1))) s'))))).
*)

(*
Inductive singleGate := H_gate | X_gate | Y_gate | RZ_gate (f:basic) (*representing 1/2^n of RZ rotation. *).

Inductive pexp := PSKIP | Abort | Assign (x:var) (n:aexp) 
              | InitQubit (p:posi) | AppU (e:singleGate) (p:posi) 
            | PSeq (s1:pexp) (s2:pexp)
            | IfExp (b:bexp) (e1:pexp) (e2:pexp) | While (b:bexp) (p:pexp)
            | Classic (x:var) (p:exp) (*quantum of oracle computation. we use exp first (OQASM) for simplicity *)
            | State (x:var)  (* We first assume that we have H first. state prepreation of n H. *)
            | QFT (x:var)
            | RQFT (x:var)
            | Meas (a:var) (x:var) (* quantum measurement on x to a classical value 'a'. *)
            | PMeas (p:var) (x:var) (a:var) (* the probability of measuring x = a assigning probability to p. *)
            | CX (x:posi) (y:posi)  (* control x on to y. *)
            | CU (x:posi) (p:exp) (z:var) (* control-U on the reversible expression p from the control node x on to z. *)
            | QWhile (n:aexp) (x:var) (f:nat -> nat) (b:bexp) (e:pexp) 
                    (*max loop number of n, variable x, monotonic function f, bool b and e.*)
            | Reflect (x:var) (l:list (fexp * state)) (* Amplitude amplication, 

*)

Definition is_0 (s:state) (n:nat) :=
    match s with NTensor n i b (ket (BA (Num 0))) => True
              | _ => False
    end.

(*
Definition is_ket_elem (s:state ) (n:nat) :=
    match s with NTensor m i b (ket ba) => True
               | _ => False
    end.

Fixpoint is_ket (s:predi) (x:var) (n:nat) :=
    match s with PAnd p1 p2 => 
       (is_ket p1 x n \/ is_ket p2 x n)
       | PState l s => if in_set_bool x l then is_ket_elem s n else False
       | a => False
    end.

Definition change_h (s:state) (n:nat) :=
   match s with NTensor n i b (ket (BA (Num 0))) => 
         Tensor (Tensor (NTensor (AMinus (BA (Var i)) b) i b (ket (BA (Num 0)))) 
                 (Sigma (BA (Num 2)) i (BA (Num 0)) (ket (BA (Var i)))))
                (NTensor n i (APlus (AMinus (BA (Num i)) b) (BA (Num 1))) (ket (BA (Num 0)))) 
     | a => a
   end.


Definition change_cx_1_elem (s:state) (n:nat) (b2:aexp) :=
   match s with NTensor n i b (ket b1) => 
         Tensor (Tensor (NTensor (AMinus (BA (Var i)) b) i b ((ket b1))) 
                 ((ket (XOR b1 (b2)))))
                (NTensor n i (APlus (AMinus (BA (Num i)) b) (BA (Num 1))) (ket b1)) 
     | a => a
   end.

Fixpoint change_cx_1 (s:predi) (x:var) (n:nat) (b2:aexp) :=
    match s with PAnd p1 p2 => PAnd (change_cx_1 p1 x n b2) (change_cx_1 p2 x n b2)
       | PState l s => if in_set_bool x l then (PState l (change_cx_1_elem s n b2)) else PState l s
       | a => a
    end.

Definition get_ket_elem (s:state ) (n:nat) :=
    match s with NTensor m i b (ket ba) => Some ba
               | _ => None
    end.

Fixpoint get_ket (s:predi) (x:var) (n:nat) :=
    match s with PAnd p1 p2 => 
       (match get_ket p1 x n with None => get_ket p2 x n | Some v => Some v end)
       | PState l s => if in_set_bool x l then get_ket_elem s n else None
       | a => None
    end.

Definition get_sigma_elem (s:state ) (n:nat) :=
    match s with Sigma (BA b) i b1 c => Some (i,b)
               | _ => None
    end.

Fixpoint get_sigma (s:predi) (x:var) (n:nat) :=
    match s with PAnd p1 p2 => 
       (match get_sigma p1 x n with None => get_sigma p2 x n | Some v => Some v end)
       | PState l s => if in_set_bool x l then get_sigma_elem s n else None
       | a => None
    end.

Definition turn_cx_2_elem (s:state) (n:nat) (q:var) :=
   match s with NTensor n i b (ket b1) => 
         Tensor (Tensor (NTensor (AMinus (BA (Var i)) b) i b ((ket b1))) 
                 ((Sigma (BA (Num 2)) q (BA (Num 0)) (ket (BA (Var q))))))
                (NTensor n i (APlus (AMinus (BA (Num i)) b) (BA (Num 1))) (ket b1)) 
     | a => a
   end.

Fixpoint turn_cx_2 (s:predi) (x:var) (n:nat) (q:var) :=
    match s with PAnd p1 p2 => PAnd (turn_cx_2 p1 x n q) (turn_cx_2 p2 x n q)
       | PState l s => if in_set_bool x l then (PState l (turn_cx_2_elem s n q)) else PState l s
       | a => a
    end.

Definition times_phase (q:var) (b:aexp) := qket (AMult (BA (Var q)) b) (BA (Var q)).

Inductive triple : predi -> pexp -> predi -> Prop :=
     | conjSep : forall e P P' Q, triple P e P' -> triple (PAnd P Q) e (PAnd P' Q)
     | tensorSep_1 : forall x n P P' Q e , 
           triple (PState ([(x,Num n)]) P) e (PState ([(x,Num n)]) P') ->
           triple (PState ([(x,Num n)]) (Tensor P Q)) e (PState ([(x,Num n)]) (Tensor P' Q))
     | tensorSep_2 : forall x n P Q Q' e , 
           triple (PState ([(x,Num n)]) Q) e (PState ([(x,Num n)]) Q') ->
           triple (PState ([(x,Num n)]) (Tensor P Q)) e (PState ([(x,Num n)]) (Tensor P Q'))
     | appH : forall x i s n, is_0 s i ->
         triple (PState ([(x,Num n)]) s)
              (AppH (x,(Num i))) (PState ([(x,Num n)]) (change_h s i))
     | appCX_1 : forall x i y j s v,  get_ket s x i = Some v -> is_ket s y j ->
         triple s (CX (x,(Num i)) (y,(Num j))) (change_cx_1 s y j v)
     | appCX_2 : forall x i y j s u v q,  get_sigma s x i = Some (u,v) -> is_ket s y j ->
         triple s (CX (x,(Num i)) (y,(Num j))) (PAnd (turn_cx_2 s y j q)
                       (Forall q (PAnd (CState (BLe (BA (Num 0)) (BA (Var q)))) (CState (BLt (BA (Var q)) (BA v))))
                           (CState (BEq (Index (x,(Num i)) (BA (Var q))) (Index (y,(Num j)) (BA (Var q)))))))
     | appState : forall P l x n i b e q, in_set x l ->
         triple (PAnd P (PState l (NTensor (n:aexp) (i:var) (b:aexp) (ket e)))) (State x)
                (PAnd P (PState l (NTensor (n:aexp) (i:var) (b:aexp) (Sigma (BA (Num 2)) q (BA (Num 0)) (times_phase q b)))))
     | appCU : forall P l s1 s s' x p y j m k q b, in_set x l -> in_set y l ->
         triple (PState ([(y,Num m)]) s) (Classic p) (PState ([(y,Num m)]) s') ->
         triple (PAnd P (PState ((x,Num (j+1))::((y, Num m)::[]))
                 (Tensor (Tensor (NTensor (BA (Num j)) k (BA (Num 0)) s1) (Sigma (BA (Num 2)) q (BA (Num 0)) (ket b))) s)))
                    (CU (x,(Num j)) p y)
                 (PAnd P (PState ((x,Num (j+1))::((y, Num m)::[]))
                 (Tensor (NTensor (BA (Num j)) k (BA (Num 0)) s1) 
                     (SPlus (Tensor (ket (BA (Num 0))) s) (Tensor (ket (BA (Num 1))) s'))))).
*)
(*
Inductive state :Type :=
             | STrue (* meaning that the initial state with any possible values. *)
             | ket (b:basic) (*normal state |0> false or |1> true *)
             | Plus (phasea: basic) (phaseb: basic)
     (* state R*|x>_m or R*|n>_m where n is a number or x is a variable.
        m is the number of qubits in R*|..> *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).



Inductive predi := PTrue | PFalse | PState (l:list (var * nat)) (s:state)
                    (* quantum variable, its qubit size and the state representation*)
            | CState (b:bexp)
               (* bexp is a constant variable predicate. *)
            | PMea (x:var) (p:R) (n:nat) 
                (* partial measumrement on the varible x with the probability of p at a value n. *)
            | PAnd (p1:predi) (p2:predi)
            | PNot (p:predi).

(*
      | TQWhile : forall P x y n b e,
           triple ((PAnd P (PAnd ((Bool b)) (Bool (BLe y n)))))  e P ->
           triple (PSum (x) P) (QWhile x n b e) (PAnd (PSum (x) P) (PNot (Bool b)))
      | TReflect : forall a n x i,
           triple (PSum (x) (PState (Ket a n [Var x]))) (Reflect (x,i)) (PSum (x) (PState (Ket a n [Var x]))).
*)


(* here. *)
Definition subst_var (x:var) (y:var) (z:var) := if x =? y then z else x.

Definition substb (b:bexp) (x:var) (y:var) :=
   match b with BEq u v => BEq (subst_var u x y) (subst_var v x y)
            | BLt u v => BLt (subst_var u x y) (subst_var v x y)
            | BLe u v => BLe (subst_var u x y) (subst_var v x y)
   end.


Fixpoint subst (p:predi) (x:var) (y:var) :=
   match p with PTrue => PTrue | PFalse => PFalse
    | PEeq u v => PEeq (subst_var u x y) (subst_var v x y)
    | PSum u p => PSum (subst_var u x y) (subst p x y)
    | PAnd p1 p2 => PAnd (subst p1 x y) (subst p2 x y)
    | PNot p => PNot (subst p x y)
    | Bool b => Bool (substb b x y)
    | PState s => PState s
   end.

Inductive triple : predi -> pexp -> predi -> Prop :=
      | TQWhile : forall P x y n b e,
           triple ((PAnd P (PAnd ((Bool b)) (Bool (BLe y n)))))  e P ->
           triple (PSum (x) P) (QWhile x n b e) (PAnd (PSum (x) P) (PNot (Bool b)))
      | TReflect : forall a n x i,
           triple (PSum (x) (PState (Ket a n [Var x]))) (Reflect (x,i)) (PSum (x) (PState (Ket a n [Var x]))).
*)


(* An example expressions for pexp. This is the C-Uf gate in Shor's algorithm *)
(*
Fixpoint shor_u' (x:var) (y:var) (n:nat) (size:nat) :=
    match n with 0 => PSKIP (x,0)
        | S m => PCU (x,size - n) (PUf m y) ; shor_u' x y m size
    end.
Definition shor_u (x:var) (y:var) (n:nat) := shor_u' x y n n.


Inductive numvar := Num (n:nat) | Var (x:var) | FunApp (x:var) (y:var).

Inductive state :Type :=
             | STrue (* meaning that the initial state with any possible values. *)
             | Ket (phase:R) (n:nat) (x:list numvar)
     (* state R*|x>_m or R*|n>_m where n is a number or x is a variable.
        m is the number of qubits in R*|..> *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             | Plus (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             | Sigma (n:nat) (N:nat) (s:state) (* the state represents Sigma_0^n s,
                                               e.g. 1/(sqrt N) * Sigma n (ket n x) is Sigma_0^n |x> *)
             | NTensor (n:nat) (s:state) (* the state represents Tensor_0^n s
                                       e.g. 1/(sqrt N) * Tensor n (Plus (Ket 1 0) (Ket 1 1) is Tensor_0^n (|0> + |1>) *)
             | Const (p:R) (n:nat) (* a constant of evaluating a group of qubits.
                                       n is range from 0 to 2^n-1,
                                      and it's the decimal representation of the binary array measured from n qubits. *)
             | When (s:state) (x:var) (p:R) (n:nat) 
                          (*This is the resulting state of a partial measurement on x. 
                             The meaning is that when x is evaluated as n
                                   with the probablity p, what happen in the other qubits s. *).


(* if a state as x |-> s \ {1,...,n}, while the size of x is n, then  x |-> s \ {1,...,n} is equal to True. *)
Inductive hstate :Type := SWithout (s:state) (l : list posi).


(*A state is defined as a list of either a tuple of list variables and a hstate, or a tuple of position and a state. 
   The list [A1,A2,A3,...,] means that A1 /\ A2 /\ A3 /\ ... *)
Inductive hpiece : Type := Group (x:var) (h:hstate) | Single (p:posi) (s:state).


(* This gives the syntax of QC. *)
Inductive qexp := 
        | Pexp (e:pexp)
        | QH (x:var)
        | QSKIP (p:posi)
        | QQFT (x:var)
        | QRQFT (x:var)
        (* The above operations are gates, and they are applied on a group of qubits. *)
        | Mea (x:var) (*mesuarement /partial measurement *) 
        | QCU (p:posi) (e:qexp)
        | App (f:var) (xl : list var) (*function application. f is a function name that is defined. *)
        | Qload (x:var) (d:var) (* loading a data from the database d from the address x.
                                   x could be in superposition, Its definition is f(|x>,d) { Pload x d }. *)
        | QSeq (s1:qexp) (s2:qexp).

Notation "p1 ;; p2" := (QSeq p1 p2) (at level 50) : pexp_scope.

Inductive qc := QUf (f:var) (xl: list numvar) (yl:list var) (e:pexp)
            (*QUf is a function to write oracles. f is the name, xl is the list of qubits,
              and yl is the list of normal variables.
              P is a state representing the precondition, and Q is the post-condition.
              The function input arguments are dependently typed.
               So users can write f (|x> |0>, ...) to claim that the second argument is |0>. *)
             | Cfun (f:var) (xl: list (var * list numvar * state * state)) (e:qexp)
            (* Cfun is a function header for a qexp. Its argument xl 
                     is a list of oracles with the oracle input arguments and pre/post-conditions. *)
             | QCSeq (s1:qc) (s2:qc).

Notation "p1 ;;; p2" := (QCSeq p1 p2) (at level 50) : pexp_scope.


Fixpoint QPE_aux (x:var) (y:var) (n:nat) (size:nat) :=
    match n with 0 => QSKIP (x,0)
           | S m => QCU (x,size - n) (Pexp (PUf size y));; QPE_aux x y m size
    end.

Definition QPE (f:var) (x:var) (y:var) (n:nat) := 
   Cfun f [] (QH x;; QPE_aux x y n n ;; QRQFT x;; Mea x).

Definition Shor (g:var) (f:var) (x:var) (y:var) (uf:var) (U:var) (n:nat) := 
   QUf g (Var x:: (Var y::[])) [] (shor_u x y n)
          ;;; Cfun f [(U,(Var x:: (Num 0)::[]),STrue,(Sigma n (2^n) (Ket (1:R) (2*n) (Var x::FunApp uf x::[]))))] 
             (QH x;; App U ( x:: y::[]) ;; Mea y ;; QRQFT x;; Mea x).



(*Equavalent relation: We need to implement equivalent relations on state representations,
   so that we can create a proof system for discover properties about an algorithm. *)

(* Here are some eqiv relations on the states. *)

(*Forall states 1/sqrt N * Sigma_0^N |x>_n = NTensor_0^n 1/sqrt 2 (|0> + |1>) where N = 2^n *)

(*Forall states R * Sigma_i=0^N Sigma_j=0^N s = Sigma_j=0^N Sigma_i=0^N s *)

(*Forall states R * NTensor_i=0^N Sigma_j=0^N s = Sigma_j=0^N NTensor_i=0^N s *)


(*Forall states exists x. R_1(x) = gen(R_a1,R_a2,...,R_an)   R_2(x) = gen(R_b1,R_b2,...,R_bn) ==>
       (R_a1 * |0> + R_b1 * |1>) tensor 
            (R_a2 * |0> + R_b2 * |1>) tensor .... tensor (R_an * |0> + R_bn * |1>)
                    = Tensor_0^n 1/sqrt 2 (R_1*|0> + R_2*|1>) *)



(*
Quantum Walk algorithm implementation.


First NAND quantum walk algorithm.
*)

(*

Implement max T number of DW step as a control DW as CU-DW appeared in the QPE. |t> is the source of the CU.

For the quantum walk step, use QRAM load instead of a quantum walk U operation. Possibly.
 OR maybe using U as a way of analyzing the algorithm.

For the defusion step, implement a data-structure as node = {type:2 qubit, state v: n: qubit, next: node).
We load a data (a,v) as a tuple where a is the type (either left, or 3-degree or r' or r''). 
We use CU-gate to apply different operation on t according to a. 
If a = leaf, we do oracle application on v as (-1)^(xv) * |v>, 
if a = 3-degree, we apply reflection on |c> (coin qubits), (-1/3 ...)
if a = r', we apply reflection on |c> (-2/sqrt n, ...)

This is implementable in the current QC.
*)
*)

*)

