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
           | TwoTo (e1:basic) | XOR (e1:aexp) (e2:aexp) | Index (x:var) (a:aexp).

Definition posi :Type := (var * aexp).

Inductive fexp := Fixed (r:R) | FNeg (f1:fexp) | FPlus (f1:fexp) (f2:fexp) | FTimes (f1:fexp) (f2:fexp) 
        | FDiv (f1:fexp) (f2:fexp)
        | FSum (n:aexp) (i:var) (b:aexp) (f:fexp)
        | FExp (f:fexp) | FSin (f:fexp) | FCos (f:fexp)
        | FCom (f:fexp) (f1:fexp) (* a + b i *)
        | FExpI (a:aexp) (* e^ 2pi i * a *).

Inductive bexp := BEq (x:aexp) (y:aexp) | BGe (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp)
                | FEq (x:fexp) (y:fexp) | FGe (x:fexp) (y:fexp) | FLt (x:fexp) (y:fexp).

Definition collect_var_basic (b:basic) :=
      match b with Var x => ([x]) | Num n => nil end.

Fixpoint collect_var_aexp (a:aexp) :=
    match a with BA a => collect_var_basic a
              | APlus e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | AMinus e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | AMult e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | XOR e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | Index x e2 =>  x::((collect_var_aexp e2))
              | TwoTo e => collect_var_basic e
    end.

Fixpoint collect_var_fexp (a:fexp) :=
    match a with Fixed a => nil
              | FNeg e1 =>  (collect_var_fexp e1)
              | FPlus e1 e2 =>  (collect_var_fexp e1)++(collect_var_fexp e2)
              | FTimes e1 e2 =>  (collect_var_fexp e1)++(collect_var_fexp e2)
              | FDiv e1 e2 =>  (collect_var_fexp e1)++(collect_var_fexp e2)
              | FSum a i b f =>  (collect_var_aexp a)++(collect_var_aexp b)++(collect_var_fexp f)
              | FCom e1 e2 => (collect_var_fexp e1)++(collect_var_fexp e2)
              | FExp e1 => (collect_var_fexp e1)
              | FSin e1 => (collect_var_fexp e1)
              | FCos e1 => (collect_var_fexp e1)
              | FExpI e1 => collect_var_aexp e1
    end.

Definition collect_var_bexp (b:bexp) :=
   match b with BEq x y => (collect_var_aexp x)++(collect_var_aexp y)
              | BGe x y => (collect_var_aexp x)++(collect_var_aexp y)
              | BLt x y => (collect_var_aexp x)++(collect_var_aexp y)
              | FEq x y => (collect_var_fexp x)++(collect_var_fexp y)
              | FGe x y => (collect_var_fexp x)++(collect_var_fexp y)
              | FLt x y => (collect_var_fexp x)++(collect_var_fexp y)
   end.

(*Pattern for walk. goto is describing matching patterns such as
    match |01> -> |10> | |00> -> |11> ...
    three type restriction: 
    1.left-hand and right hand must have the same number of bits.
    2. the number of cases are exactly 2^n where n is the bit number.
    3. only permutation, both the left and right bitstrings must be distinct. *)
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
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).

Inductive qpred_elem := PState (l:list (var * aexp)) (s:state).

Definition qpred := list (qpred_elem).

Inductive cpred_elem := PFalse | CState (b:bexp) | POr (p1:cpred_elem) (p2:cpred_elem) 
             | PNot (p:cpred_elem) | Forall (xs:list var) (p1:list cpred_elem) (p2:cpred_elem).

Definition cpred := list cpred_elem.


