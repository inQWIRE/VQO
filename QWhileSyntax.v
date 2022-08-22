Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
(*Require Import OQASM.*)
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
Inductive atype := C : atype | M :atype.

Definition aty_eq  (t1 t2:atype) : bool := 
   match t1 with C => match t2 with C  => true
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
 destruct a. destruct b. easy. easy.
 destruct b. 1-2:easy.
Qed.

Lemma aty_eqb_neq : forall a b, a =a= b = false -> a <> b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. easy.
 easy.
 destruct b. easy. easy.
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
       match a1 with C => C
                | M => a2
        end.


Inductive aexp := BA (x:var) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp).

Coercion BA : var >-> aexp.

Coercion Num: nat >-> aexp.


Notation "e0 [+] e1" := (APlus e0 e1) (at level 50) : pexp_scope.
Notation "e0 [*] e1" := (AMult e0 e1) (at level 50) : pexp_scope.

Inductive varia := AExp (x:aexp) | Index (x:var) (v:aexp).

Coercion AExp : aexp >-> varia.

Notation "e0 [ e1 ]" := (Index e0 e1) (at level 50) : pexp_scope.

Inductive singleGate := H_gate | X_gate | RZ_gate (f:nat) (*representing 1/2^n of RZ rotation. *).

Inductive bexp := | BEq (x:varia) (y:varia) (i:var) (a:aexp)
                  | BLt (x:varia) (y:varia) (i:var) (a:aexp) | BTest (i:var) (a:aexp).

Notation "e0 [=] e1 @ e3 [ e4 ]" := (BEq e0 e1 e3 e4) (at level 50) : pexp_scope.

Notation "e0 [<] e1 @ e3 [ e4 ]" := (BLt e0 e1 e3 e4) (at level 50) : pexp_scope.

Notation "* e0 [ e1 ]" := (BTest e0 e1) (at level 50) : pexp_scope.

(* Define the ground term type system 
Inductive type_rotation := TV (b:aexp) | Infty.
*)

Definition type_cfac : Type := nat -> rz_val.

Inductive type_phase :=  Uni.

(*| Uni (b: nat -> rz_val) | DFT (b: nat -> rz_val). *)

Inductive type_elem : Type := TNor (p : option (rz_val))
         | TH (r:option type_phase)
         | CH (t:option (nat * type_cfac)).

Inductive se_type : Type := THT (n:nat) (t:type_elem).

Definition type_pred := se_type.

(* Ethan: I don't remember what is this tuple... *)
Definition session := list (var * nat * nat).

Definition tpred := list (session * se_type).

Inductive maexp := AE (n:aexp) | Meas (a:var).

Coercion AE : aexp >-> maexp.

Inductive exp := SKIP (x:var) (a:aexp) | X (x:var) (a:aexp)
        | CU (x:var) (a:aexp) (e:exp)
        | RZ (q:nat) (x:var) (a:aexp)  (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (x:var) (a:aexp)  
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

Inductive type := Phi (b:nat) | Nor.

Inductive single_u := RH (p:varia) | SQFT (x:var) | SRQFT (x:var).

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
     (*reflection on x = a_1 ,... x = a_n in al with equal probablity hadamard walk. 
        This statement basically distributes/diverges a vector x to many different vectors. *).
          (*  | CX (x:posi) (y:posi)  (* control x on to y. *)
            | CU (x:posi) (p:exp) (z:var) (args: list var) (q:aexp) (s:aexp) *)
             (* control-U on the reversible expression p from the control node x on to z. *)

Notation "p1 ; p2" := (PSeq p1 p2) (at level 50) : pexp_scope.

Notation "p1 [<-] p2" := (AppU p1 p2) (at level 50) : pexp_scope.

