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
Inductive basic := Var (x:var) | Num (n:nat) | Bool (b:bool) | Fixed (n:nat).

Inductive aexp := BA (b:basic) | APlus (e1:aexp) (e2:aexp) | AMinus (e1:aexp) (e2:aexp) | TwoTo (e1:basic).

Inductive bexp := BEq (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp) | BLe (x:aexp) (y:aexp).

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


Inductive predi := PTrue | PFalse | PState (l:list (var * basic)) (s:state)
                    (* quantum variable, its qubit size and the state representation*)
            | CState (b:bexp)
               (* bexp is a constant variable predicate. *)
            | PMea (x:var) (p:R) (n:nat) 
                (* partial measumrement on the varible x with the probability of p at a value n. *)
            | PAnd (p1:predi) (p2:predi)
            | PNot (p:predi).


Inductive pattern := Adj (x:var) (* going to adj nodes. *)
                   | Match (x:var) (n:nat) (nll:list (list bool * list bool)).
                        (*n here means n bits starting from the 0 position in x. *)

Definition posi :Type := (var * basic).

Inductive pexp := PSKIP | Abort | Assign (x:var) (n:nat) 
              | InitQubit (p:posi) | AppU (e:pexp) (p:posi) 
            | PSeq (s1:pexp) (s2:pexp)
            | IfExp (b:bexp) (e1:pexp) (e2:pexp) | While (b:bexp) (p:pexp)
            | AppH (p:posi)
            | State (x:var)
            | QFT (x:var)
            | RQFT (x:var)
            | Meas (x:var)
            | CX (x:posi) (y:posi)
            | CU (x:posi) (y:prog) (z:var)
            | QWhile (n:var) (x:var) (f:nat -> nat) (b:bexp) (e:pexp)
            | Reflect (p:posi)
             (*quantum while, x is a variable, represents a monotonic function variable.
                 n is the upperbound, b is the boolean formula but it needs to be monotonic. 
                e is an expression that does not contain x and no measurement.
                  an example of using QWhile is to find optimimal solution.  *)
            | QWalk (e1:pexp) (e2:pexp).
           (* SingleTon walk step, e1 is defussion step that does not include permutation,
                      e2 is a walk step that cannot do defussion. *)

Notation "p1 ; p2" := (PSeq p1 p2) (at level 50) : pexp_scope.

Definition add_num (x:aexp) (n:nat) := 
    match x with APlus e1 (BA (Num m)) => APlus e1 (BA (Num (m+n)))
               | APlus (BA (Num m)) e2 => APlus (BA (Num (m+n))) e2
               | a => APlus a (BA (Num n))
    end.


Inductive eq_state : state -> state -> Prop :=
      | tensor_assoc : forall s1 s2 s3, eq_state (Tensor s1 (Tensor s2 s3)) (Tensor (Tensor s1 s2) s3)
      | tensor_break_1 : forall n i j s,
           eq_state (NTensor n i j s) (Tensor s  (NTensor n i (add_num j 1) s))
      | tensor_empty : forall n i a s,
           eq_state (Tensor a (NTensor n i n s)) a.


Inductive triple : predi -> pexp -> predi -> Prop :=
     | appH : forall x i y n b s P, 
         triple (PAnd (PState ([(x,Num n)]) (NTensor (BA (Num n)) y (BA b) s)) P)
              (AppH (x,i)) (PAnd (PState ([(x,Num n)]) 
                    (Tensor (NTensor (BA (Num n)) y (BA b) s) s (NTensor (BA (Num n)) y (BA b) s) )) P).



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





