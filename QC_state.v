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


(* compilation to Z3. *)
Inductive ze_qubit_elem := znone | zsome (n:aexp).

Definition ze_arr_elem :Set :=  (ze_qubit_elem * ze_qubit_elem).

Inductive z3_exp := z3_ba (a:aexp)
                 | z3_lem (a:ze_arr_elem).

Inductive z3_pred := ztrue | zfalse
    | zqeq (a:z3_exp) (b:z3_exp)
    | zeq (a:z3_exp) (b:z3_exp) 
    | zle (a:z3_exp) (b:z3_exp) | zlt (a:z3_exp) (b:z3_exp)
    | znot (a:z3_pred) | zand (a:z3_pred) (b:z3_pred)
    | zimply (a:z3_pred) (b:z3_pred)
    | lambdaITE (x:var) (b:z3_pred) (l:z3_pred) (r:z3_pred) | ite (b:z3_pred) (l:z3_pred) (r:z3_pred)
    | zread (a:basic) (n:aexp) | write (a:basic) (n:aexp) (v:ze_arr_elem)
    | zset (a:basic) (p:basic) (v:ze_arr_elem) (s:basic)
    | zsetInf (a:basic) (p:basic) (v:ze_arr_elem)
    | zcopy (a:basic) (p:basic) (b:basic) (q:basic) (s:basic)
    | zcopyInf (a:basic) (p:basic) (b:basic) (q:basic)
    | zforall (x:var) (a:z3_pred).


Axiom var_num_map : var -> nat.

Axiom encode_fexp : fexp -> aexp.

Definition fresh (l:nat) := l +1.

(*
Definition elem_diff x n y m u v :=
     zforall u (zforall v (zimply (zand (zand (zle (z3_plus x (z3_ba (Num 0))) (z3_ba (Var u))) 
               (zlt (z3_ba (Var u)) (z3_plus x n))) 
         (zand (zle (z3_plus y (z3_ba (Num 0))) (z3_ba (Var v))) 
               (zlt (z3_ba (Var v)) (z3_plus y m)))) (znot (zeq (z3_ba (Var u)) (z3_ba (Var v)))))).

Definition set_diff :var := 1.

Fixpoint set_elem_diff_aux (x:var) (l:list var) (freshs:nat) :=
    match l with [] => (ztrue,freshs)
            | y::ys => let u := fresh freshs in let v := fresh (fresh freshs) in
          match (set_elem_diff_aux x ys (fresh (fresh freshs))) with (next1,fre) =>
          (zand (elem_diff (z3_ba (Var (var_map x))) (z3_ba (Var (var_map y)))
                 (z3_ba (Num (var_num_map x))) (z3_ba (Num (var_num_map y))) u v) next1,fre)
          end
    end.

Fixpoint set_elem_diff (l:list var) (freshs:nat) :=
      match l with [] => ztrue
                 | (x::xs) =>
               match set_elem_diff_aux x xs freshs with (new,fre) => 
                   zand new (set_elem_diff xs fre)
               end
      end.
*)

Definition subst_basic (v:basic) (x:var) (i:nat) :=
  match v with Var y => if x =? y then Num i else Var y
            | Num a => Num a
  end.

Fixpoint subst_aexp (a:aexp) (x:var) (i:nat) :=
    match a with BA b => BA (subst_basic b x i)
             | APlus e1 e2 => APlus (subst_aexp e1 x i) (subst_aexp e2 x i)
             | AMinus e1 e2 => AMinus (subst_aexp e1 x i) (subst_aexp e2 x i)
             | AMult e1 e2 => AMult (subst_aexp e1 x i) (subst_aexp e2 x i)
             | TwoTo e1 => TwoTo (subst_basic e1 x i)
             | XOR e1 e2 => XOR (subst_aexp e1 x i) (subst_aexp e2 x i)
             | Index y a => if y =? x then Index y a else Index y (subst_aexp a x i)
    end.

Definition trans_qubit (v:state) (x:var) (i:aexp)  :=
    match v with ket a => Some (ite (zeq (z3_ba a) (z3_ba (BA (Num 0))))
                                    (write (Var x) i (zsome (BA (Num 1)), znone))
                                    (write (Var x) i (znone,zsome (BA (Num 1)))))
                | qket p a => Some (ite (zeq (z3_ba a) (z3_ba (BA (Num 0))))
                                    (write (Var x) i (zsome (encode_fexp p), znone))
                                    (write (Var x) i (znone,zsome (encode_fexp p))))
                | SPlus (qket p a) (qket q b) =>
                              Some (zand
                                      (write (Var x) i (zsome (encode_fexp p), zsome (encode_fexp q)))
                                      (zand (zeq (z3_ba a) (z3_ba (BA (Num 0))))
                                            (zeq (z3_ba b) (z3_ba (BA (Num 1))))))
                | Sigma (BA (Num 2)) j b (ket a) =>
                              Some (zand
                                      (write (Var x) i (zsome (BA (Num 1)), zsome (BA (Num 1))))
                                      (zand (zeq (z3_ba (subst_aexp a j 0)) (z3_ba (BA (Num 0))))
                                            (zeq (z3_ba (subst_aexp a j 1)) (z3_ba (BA (Num 1))))))
                | Sigma (BA (Num 2)) j b (qket p a) =>
                              Some (zand
                                      (write (Var x) i (zsome (encode_fexp p), zsome (encode_fexp p)))
                                      (zand (zeq (z3_ba (subst_aexp a j 0)) (z3_ba (BA (Num 0))))
                                            (zeq (z3_ba (subst_aexp a j 1)) (z3_ba (BA (Num 1))))))

               | _ => None
    end.

Fixpoint trans_tensor' (v:state) (x:var) (i:aexp) :=
   match v with NTensor h y l s =>
       match trans_qubit s x (BA (Var y)) with None => None
                 | Some p => Some (zand (lambdaITE y (zand (zle (z3_ba i) (z3_ba (BA (Var y)))) (zlt (z3_ba (BA (Var y))) (z3_ba h)))
                                       p (zread (Var x) (BA (Var y)))) (zeq (z3_ba i) (z3_ba l)),h)
       end
             | Tensor s1 s2 => match trans_tensor' s1 x i with None => None
                                           | Some (p1,h1) => 
                                match trans_tensor' s2 x h1 with None => None
                                          | Some (p2,h2) => 
                                     Some (zand p1 p2, h2)
                                end
                              end
    | _ => None
   end.
Definition trans_tensor (v:state) (x:var) (n:nat) := 
       match trans_tensor' v x (BA (Num 0)) with None => None
                                  | Some (p,h) => Some (zand p (zeq (z3_ba h) (z3_ba (BA (Num n)))))
       end.


(* 

              | NTensor n i b s => 
              | Sigma n i b s => 


             | STrue (* meaning that the initial state with any possible values. *)
             | ket (b:aexp) (*normal state |0> false or |1> true *)
             | qket (p:fexp) (b:aexp)
             | SPlus (s1:state) (s2:state)  (* Let's say that we only allow |0> + |1> first. *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).


Inductive aexp := BA (b:basic) | APlus (e1:aexp) (e2:aexp) | AMinus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp)
           | TwoTo (e1:basic) | XOR (e1:aexp) (e2:aexp) | Index (x:var) (a:aexp).
*)
