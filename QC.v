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
(**********************)
(** Unitary Programs **)
(**********************)


Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

(* This will be replaced by PQASM. *)
(* For simplicity, let's assume that we deal with natural number arithemtic first. *)
Inductive basic := Var (x:var) | Num (n:nat).

Inductive aexp := BA (b:basic) | APlus (e1:aexp) (e2:aexp) | AMinus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp)
           | TwoTo (e1:basic) | XOR (e1:aexp) (e2:aexp) | Index (x:posi) (a:aexp).

Definition posi :Type := (var * aexp).

(* Ethan: exp here doesn't look right *)
Print exp.
Inductive fexp := Fixed (r:R) | FNeg (f1:fexp) | FPlus (f1:fexp) (f2:fexp) | FTimes (f1:fexp) (f2:fexp) 
        | FDiv (f1:fexp) (f2:fexp)
        | FSum (n:aexp) (i:var) (b:aexp) (f:fexp)
        | FExp (f:fexp) | FSin (f:exp) | FCos (f:exp)
        | FCom (f:exp) (f1:exp) (* a + b i *).

Inductive bexp := BEq (x:aexp) (y:aexp) | BGe (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp)
                | FEq (x:fexp) (y:fexp) | FGe (x:fexp) (y:fexp) | FLt (x:fexp) (y:aexp).


        

(*Pattern for walk. goto is describing matching patterns such as
    match |01> -> |10> | |00> -> |11> ...
    three type restriction: 
    1.left-hand and right hand must have the same number of bits.
    2. the number of cases are exactly 2^n where n is the bit number.
    3. only permutation, both the left and right bitstrings must be distinct. *)
(* Ethan: This doesn't make sense. *)
Inductive numvar := NNum (n:nat) | NVar (x:var) | NFunApp (x:var) (y:var).

Definition rz_val := nat.

Definition addto (r : rz_val) (n : nat) (rmax : nat) : rz_val :=
  (r + 2^(rmax - n)) mod 2^rmax.

Definition addto_n (r : rz_val) n (rmax : nat) :=
  (r + 2^rmax - 2^(rmax - n)) mod 2^rmax.

Definition rotate (r :rz_val) (q:nat) rmax := addto r q rmax.


(* Quantum State *)
Inductive state :Type :=
             | STrue (* meaning that the initial state with any possible values. *)
             | ket (b:aexp) (*normal state |0> false or |1> true *)
             | qket (p:fexp) (b:aexp)
             | SPlus (s1:state) (s2:state)  (* Let's say that we only allow |0> + |1> first. *)
             (* Ethan: Not + below *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).

(* Ethan: What is this...
 * Can we have records with named fields?
 * This is really not self-documenting.
 *)
Inductive qpred_elem := PState (l:list (var * aexp)) (s:state).

Definition qpred := list (qpred_elem).


(* Classical State including variable relations that may be quantum *)
(* Ethan: Need explanation on the forall rule.
 * Not sure which parameter is what *)
Inductive cpred_elem := PFalse | CState (b:bexp) | POr (p1:cpred_elem) (p2:cpred_elem) 
             | PNot (p:cpred_elem) | Forall (xs:list var) (p1:list cpred_elem) (p2:cpred_elem).

Definition cpred := list cpred_elem.

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

(* Ethan: By allowing RZ and CX gates, the user can write arbitrary circuit.
 * We don't want to handle arbitrarily large matrices, right?
 *)
Inductive pexp := PSKIP | Abort | Assign (x:var) (n:aexp) 
              (* Ethan: Init = reset = trace out = measurement... *)
              | InitQubit (p:posi) | AppU (e:singleGate) (p:posi) 
            | PSeq (s1:pexp) (s2:pexp)
            | IfExp (b:bexp) (e1:pexp) (e2:pexp) | While (b:bexp) (p:pexp)
            (* Ethan: What's args? *)
            | Classic (x:var) (p:exp) (args: list var) (*quantum of oracle computation. we use exp first (OQASM) for simplicity *)
            | State (x:var)  (* We first assume that we have H first. state prepreation of n H. *)
            | QFT (x:var)
            | RQFT (x:var)
            | Meas (a:var) (x:var) (* quantum measurement on x to a classical value 'a'. *)
            (* Ethan: Why is a "var" here? *)
            | PMeas (p:var) (x:var) (a:var) (* the probability of measuring x = a assigning probability to p. *)
            | CX (x:posi) (y:posi)  (* control x on to y. *)
            | CU (x:posi) (p:exp) (z:var) (args: list var) (* control-U on the reversible expression p from the control node x on to z. *)
            | QWhile (n:aexp) (x:var) (f:nat -> nat) (b:bexp) (e:pexp) 
                    (*max loop number of n, variable x, monotonic function f, bool b and e.*)
            | Reflect (x:var) (l:list (fexp * state)) (* Amplitude amplication, 
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

Inductive type_elem : Type := TH (b:type_rotation) | TQFT (b:type_rotation) | TRQFT (b:type_rotation).

Inductive qtype := QS (l:list type_elem) | QC (vl:list (var * nat)) (l:list type_elem).

Inductive pexp_type : Type := Proba | Class | QMix (p:qtype) | Bot.

Definition type_env := (var * nat -> pexp_type).

Definition num_env := (var -> nat).

Definition value_env := (var -> nat).

Definition azero := BA (Num 0).

Definition tazero := TV (BA (Num 0)).

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

(* Ethan: Need discussion and example to understand how num_env works *)
Inductive type_system : num_env * type_env -> pexp -> num_env * type_env -> Prop :=
    | seq_type : forall s1 s2 tv tv' tv'', type_system tv s1 tv' -> type_system tv' s1 tv'' -> type_system tv (PSeq s1 s2) tv''
    | app_h_type_1 : forall S tv x n, tv (x,n) = QMix (QS nil)
                -> type_system (S,tv) (AppU H_gate (x,BA (Num n))) (S, (tv[(x,n) |-> (QMix (QS ([TH tazero])))]))
    | app_h_type_2 : forall S tv qs x n, tv (x,n) = QMix (QS ((TH tazero)::qs))
                -> type_system (S,tv) (AppU H_gate (x,BA (Num n)))(S, (tv[(x,n) |-> (QMix (QS qs))]))
    | app_rqft_type_1 : forall S tv qs x n,
                S x = n -> (forall i r, i < n -> tv (x,i) = QMix (QS ((TH r)::qs)))
                -> type_system (S,tv) (RQFT x) (S,(eupdates_elem tv x n (TRQFT Infty)))
    | app_rqft_type_2 : forall S tv qs x n,
                S x = n -> (forall i , i < n -> tv (x,i) = QMix (QS ((TQFT tazero)::qs)))
                -> type_system (S,tv) (RQFT x) (S,(eupdates_rm tv x n ))
    | app_cx_type_1 : forall S tv qs r x n y m, tv (x,n)= QMix (QS ((TH r)::qs)) -> tv (y,m) = QMix (QS nil)
                -> type_system (S,tv) (CX (x,BA (Num n)) (y,BA (Num m))) 
                         (S,tv[(x,n) |-> (QMix (QC ((x,n)::((y,m)::nil)) ((TH r)::qs)))]
                                [(y,m) |-> (QMix (QC ((x,n)::((y,m)::nil)) ((TH r)::qs)))])
    | app_cx_type_2 : forall S tv vs qs x n y m, tv (x,n)= QMix (QC vs (qs)) -> tv (y,m) = QMix (QS nil)
                -> type_system (S,tv) (CX (x,BA (Num n)) (y,BA (Num m))) (S,eupdate_list tv ((y,m)::vs) (QMix (QC ((y,m)::vs) (qs)))).


(* Definition Type predicates that will be used in triple. *)
Inductive tpred_elem := Uniform (x:posi) (p:pexp_type) | Binary (x:posi) (b:bexp) (p1:pexp_type) (p2:pexp_type).

Definition tpred := list (tpred_elem).



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
Definition change_h (s:state) :=
   match s with (Tensor s1 (NTensor n i b (ket (BA (Num 0))))) => 
         Tensor s1 (Tensor (Sigma (BA (Num 2)) i (BA (Num 0)) (ket (BA (Var i)))) 
                  (NTensor n i (APlus b (BA (Num 1))) (ket (BA (Num 0)))))
       | a => a
   end.

Inductive triple : (qpred * tpred * cpred) -> pexp -> (qpred * tpred * cpred)  -> Prop :=
     (*| conjSep : forall e P P' Q, triple P e P' -> triple (PAnd P Q) e (PAnd P' Q). *)
     | tensorSep_1 : forall x n qs P P' Q e T V, 
           triple ((PState ([(x,BA (Num n))]) P)::qs, T, V) e ((PState ([(x,BA (Num n))]) P')::qs, T, V) ->
           (* Ethan: Bigger space = need more variables? *)
           triple ((PState ([(x,BA (Num n))]) (Tensor P Q))::qs, T, V) e ((PState ([(x,BA (Num n))]) (Tensor P' Q))::qs, T, V)
     | tensorSep_2 : forall x n P Q Q' e qs T V, 
           triple ((PState ([(x,BA (Num n))]) Q)::qs,T,V) e ((PState ([(x,BA (Num n))]) Q')::qs,T,V) ->
           triple ((PState ([(x,BA (Num n))]) (Tensor P Q))::qs,T,V) e ((PState ([(x,BA (Num n))]) (Tensor P Q'))::qs,T,V)
     | tensorSep_3 : forall x m n ys y i  e s s' qs T V, m <= n ->
           triple ((PState ((x,BA (Num m))::ys) (NTensor (BA (Num m)) y i s))::qs,T,V)
                      e ((PState ([(x,BA (Num m))]) (NTensor (BA (Num m)) y i s'))::qs,T,V) ->
           triple ((PState ((x,BA (Num n))::ys) (Tensor (NTensor (BA (Num m)) y i s) (NTensor (BA (Num n)) y (BA (Num m)) s)))::qs,T,V) 
                       e ((PState ([(x,BA (Num n))]) (Tensor (NTensor (BA (Num m)) y i s') (NTensor (BA (Num n)) y (BA (Num m)) s)))::qs,T,V)
     | appH : forall x p1 p2 i j t1 qs s T P , 
         triple ((PState ([(x,p1)]) s)::qs, (Binary (x,p2) (BLt p2 i) t1 (QMix (QS (nil))))::T, P)
              (AppU H_gate (x,j)) ((PState ([(x,p1)]) (change_h s))::qs, (Binary (x,p2) (BLt p2 (APlus i (BA (Num 1)))) 
                            t1 (QMix (QS ([TH (TV (BA (Num 0)))]))))::T,  (CState (BEq i j))::P).
(*
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




