Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import OQASM.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Inductive pexp := Oexp (e:exp) | H (p:posi) | PSeq (s1:pexp) (s2:pexp).

Notation "p1 [;] p2" := (PSeq p1 p2) (at level 50) : exp_scope.

Fixpoint inv_pexp p :=
  match p with
  | Oexp a => Oexp (inv_exp a)
  | H p => H p
  | PSeq p1 p2 => inv_pexp p2 [;] inv_pexp p1
   end.


(* This is the semantics for basic gate set of the language. *)
Fixpoint pexp_sem (env:var -> nat) (e:pexp) (st: posi -> val) : (posi -> val) :=
   match e with (Oexp e') => (exp_sem env e' st)
               | H p => st[p |-> up_h (st p)]
              | e1 [;] e2 => pexp_sem env e2 (pexp_sem env e1 st)
    end.


Inductive well_typed_pexp (aenv: var -> nat) : env -> pexp -> env -> Prop :=
    | oexp_type : forall env e env', well_typed_oexp aenv env e env' -> well_typed_pexp aenv env (Oexp e) env'
    | rz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_pexp aenv env (Oexp (RZ q p)) env
    | rrz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_pexp aenv env (Oexp (RRZ q p)) env
    | h_nor : forall env env' p, Env.MapsTo (fst p) Nor env -> snd p = 0 ->
                  Env.Equal env' (Env.add (fst p) (Had 0) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | h_had : forall env env' p b, Env.MapsTo (fst p) (Had b) env -> snd p = S b ->
              Env.Equal env' (Env.add (fst p) (Had (S b)) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | pe_seq : forall env env' env'' e1 e2, well_typed_pexp aenv env e1 env' -> 
                 well_typed_pexp aenv env' e2 env'' -> well_typed_pexp aenv env (e1 [;] e2) env''.

Inductive pexp_WF (aenv:var -> nat): pexp -> Prop :=
     | oexp_WF : forall e, exp_WF aenv e -> pexp_WF aenv (Oexp e)
     | h_wf : forall p, snd p < aenv (fst p) -> pexp_WF aenv (H p)
      | pseq_wf : forall e1 e2, pexp_WF aenv e1 -> pexp_WF aenv  e2 -> pexp_WF aenv  (PSeq e1 e2).

(*
               | H p => st[p |-> up_h (st p)]

      | h_fresh : forall p p1 , p <> p1 -> exp_fresh aenv p (H p1)

      | h_neul : forall l y, exp_neu_l x l (H y) l

    | rz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_exp AE env (RZ q p)
    | rrz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_exp AE env (RRZ q p)

              | H p => ((fst p)::[])

    | h_nor : forall env env' p, Env.MapsTo (fst p) Nor env -> snd p = 0 ->
                  Env.Equal env' (Env.add (fst p) (Had 0) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | h_had : forall env env' p b, Env.MapsTo (fst p) (Had b) env -> snd p = S b ->
              Env.Equal env' (Env.add (fst p) (Had (S b)) env) ->  
                  well_typed_pexp aenv env (H p) env'

      | h_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (H p).

*)

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
  | 0    => Oexp (SKIP (x,n))
  | S m => if b <=? m then ((appx_QFT x b m size)) [;] (H (x,m))
                    [;] (Oexp (many_CR x b (size-m) m)) else Oexp (SKIP (x,m))
  end.

(* Match the K graph by LV decomposition, the following define the L part.  (H ; R(alpha)); H  |x> -> Sigma|y>. *)
Fixpoint half_k_graph (x:var) (r:nat) (size:nat) :=
   match size with 0 => (Oexp (SKIP (x,0)))
          | S m => (H (x,m)) [;] (Oexp (RZ r (x,m))) [;] half_k_graph x r m
   end.
