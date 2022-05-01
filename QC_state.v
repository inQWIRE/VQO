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

Inductive aexp := BA (b:vari) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | AMinus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp)
           | TwoTo (e1:aexp) | App (f:var) (x:aexp) (* uninterpreted function. *)

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

Inductive bexp := BFalse | BTrue
                | BEq (x:aexp) (y:aexp) | BGe (x:aexp) (y:aexp) | BLt (x:aexp) (y:aexp)
                | FEq (x:fexp) (y:fexp) | FGe (x:fexp) (y:fexp) | FLt (x:fexp) (y:fexp)
                | BTest (i:aexp) (x:aexp) (* bit test on x[i] *)
                | BXOR (x:bexp) (y:bexp) | BITE (x:bexp) (e1:bexp) (e2:bexp) | BNeg (x:bexp).


Fixpoint collect_var_aexp (a:aexp) :=
    match a with BA a => collect_var_basic a
              | Num x => nil
              | APlus e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | AMinus e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | AMult e1 e2 =>  (collect_var_aexp e1)++(collect_var_aexp e2)
              | TwoTo e => collect_var_aexp e
              | App f x => f::(collect_var_aexp x)
    end

with  collect_var_basic (b:vari) :=
      match b with Var x => ([x]) | Index x e2 =>  x::((collect_var_aexp e2)) end.

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

Fixpoint collect_var_bexp (b:bexp) :=
   match b with BTrue => nil | BFalse => nil
              | BEq x y => (collect_var_aexp x)++(collect_var_aexp y)
              | BGe x y => (collect_var_aexp x)++(collect_var_aexp y)
              | BLt x y => (collect_var_aexp x)++(collect_var_aexp y)
              | FEq x y => (collect_var_fexp x)++(collect_var_fexp y)
              | FGe x y => (collect_var_fexp x)++(collect_var_fexp y)
              | FLt x y => (collect_var_fexp x)++(collect_var_fexp y)
              | BXOR x y => (collect_var_bexp x)++(collect_var_bexp y)
              | BITE x y z => (collect_var_bexp x)++(collect_var_bexp y)++(collect_var_bexp z)
              | BNeg x => (collect_var_bexp x)
              | BTest i x => collect_var_aexp i++collect_var_aexp x
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
             | ket (b:bexp) (*normal state |0> false or |1> true *)
             | qket (p:fexp) (b:bexp)
             | SPlus (s1:state) (s2:state)  (* Let's say that we only allow |0> + |1> first. *)
             | Tensor (s1:state) (s2:state) (* |x> + |y> state. x and y are not equal *)
             (* | Plus (s1:state) (s2:state) |x> + |y> state. x and y are not equal *)
             | Sigma (n:aexp) (i:var) (b:aexp) (s:state) (* represent 1/sqrt{2^n} Sigma^n_{i=b} s *)
             | NTensor (n:aexp) (i:var) (b:aexp) (s:state) (* represent Tensor^n_{i=b} s *).

Definition qpred := list (list var * state).

Inductive cpred_elem := PFalse | CState (b:bexp) | POr (p1:cpred_elem) (p2:cpred_elem) 
             | PNot (p:cpred_elem) | Forall (xs:list var) (p1:list cpred_elem) (p2:cpred_elem).

Definition cpred := list cpred_elem.

Definition fresh (l:nat) := l +1.
(* compilation to Z3. *)

Inductive z3_exp := z3_var (x:var)
                 | z3_bit (n:ze_qubit_elem)
                 | Pair (a:ze_qubit_elem) (z2:ze_qubit_elem)
                 | ite (b:z3_pred) (l:z3_exp) (r:z3_exp)
                 | lambdaITE (x:var) (b:z3_pred) (l:z3_exp) (r:z3_exp)
                 | zread (a:z3_exp) (b:aexp)
                 | zwrite (a:z3_exp) (n:aexp) (v:z3_exp)
                 | zset (a:z3_exp) (p:aexp) (v:z3_exp) (s:aexp)
                 | zsetInf (a:z3_exp) (p:aexp) (v:z3_exp)
                 | zcopy (a:z3_exp) (p:aexp) (b:z3_exp) (q:z3_exp) (s:aexp)
                 | zcopyInf (a:z3_exp) (p:aexp) (b:z3_exp) (q:z3_exp)
                 | intRead (x:z3_exp) (a:aexp) | intValue (n:aexp)

with z3_pred := ztrue | zfalse
    | zqeq (a:z3_exp) (b:z3_exp)
    | zeq (a:aexp) (b:aexp) 
    | zle (a:aexp) (b:aexp) | zlt (a:aexp) (b:aexp)
    | znot (a:z3_pred) | zand (a:z3_pred) (b:z3_pred)
    | zor (a:z3_pred) (b:z3_pred)
    | zimply (a:z3_pred) (b:z3_pred)
    | zforall (x:var) (a:z3_pred)

with ze_qubit_elem := znone | zsome (n:aexp) | elem_var (x:var) 
       | zget (a:z3_exp) (b:aexp) (c:z3_exp) | ztimes (n1:aexp) (z:ze_qubit_elem).

(*
Definition write_left (a:z3_exp) (n:aexp) (v:aexp) := zwrite a n (Pair ((zsome v)) (zget a n (intValue (BA (Num 1))))).

Definition write_right (a:z3_exp) (n:aexp) (v:aexp) := zwrite a n (Pair (zget a n (intValue (BA (Num 0)))) ( (zsome v))).


Axiom var_num_map : var -> nat.

Axiom encode_fexp : fexp -> aexp.

Definition fresh (l:nat) := l +1.
*)
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

(*
Definition subst_basic (v:basic) (x:var) (i:nat) :=
  match v with Var y => if x =? y then Num i else Var y
            | Num a => Num a
  end.

Fixpoint subst_aexp (a:aexp) (x:var) (i:nat) :=
    match a with BA b => BA (subst_basic b x i)
             | APlus e1 e2 => APlus (subst_aexp e1 x i) (subst_aexp e2 x i)
             | AMinus e1 e2 => AMinus (subst_aexp e1 x i) (subst_aexp e2 x i)
             | AMult e1 e2 => AMult (subst_aexp e1 x i) (subst_aexp e2 x i)
             | TwoTo e1 => TwoTo (subst_aexp e1 x i)
             | XOR e1 e2 => XOR (subst_aexp e1 x i) (subst_aexp e2 x i)
             | Index y a => if y =? x then Index y a else Index y (subst_aexp a x i)
    end.

Definition trans_qubit (v:state) (x:z3_exp) (i:aexp)  :=
    match v with ket a => Some (ite (zeq (a) ((BA (Num 0))))
                                    (zwrite ( x) i (Pair (zsome (BA (Num 1))) znone))
                                    (zwrite ( x) i (Pair znone (zsome (BA (Num 1))))), ztrue)
                | qket p a => Some (ite (zeq ( a) ( (BA (Num 0))))
                                    (zwrite ( x) i (Pair (zsome (encode_fexp p)) znone))
                                    (zwrite ( x) i (Pair znone (zsome (encode_fexp p)))),ztrue)
                | SPlus (qket p a) (qket q b) =>
                              Some (zwrite ( x) i (Pair (zsome (encode_fexp p)) (zsome (encode_fexp q))),
                                      (zand (zeq ( a) ( (BA (Num 0))))
                                            (zeq ( b) ( (BA (Num 1))))))
                | Sigma (BA (Num 2)) j b (ket a) =>
                              Some (zwrite ( x) i (Pair (zsome (BA (Num 1))) (zsome (BA (Num 1)))),
                                      (zand (zeq ( (subst_aexp a j 0)) ( (BA (Num 0))))
                                            (zeq ( (subst_aexp a j 1)) ( (BA (Num 1))))))
                | Sigma (BA (Num 2)) j b (qket p a) =>
                              Some (zwrite ( x) i (Pair (zsome (encode_fexp p)) (zsome (encode_fexp p))),
                                      (zand (zeq ( (subst_aexp a j 0)) ( (BA (Num 0))))
                                            (zeq ( (subst_aexp a j 1)) ( (BA (Num 1))))))
                | _ => None
   end.

Definition trans_qubit_one (v:state) (x:z3_exp) (i:aexp) (y:z3_exp) (ind:var) (m:nat)  :=
    match v with ket a => Some (zwrite y i (z3_bit (zget x i (intValue (subst_aexp a ind m)))))
               | qket p a => Some (zwrite y i (z3_bit (ztimes (encode_fexp p) (zget x i (intValue (subst_aexp a ind m))))))
             | _ => None
   end.


Fixpoint trans_tensor' (v:state) (x:z3_exp) (i:aexp) (yh:z3_exp) :=
   match v with NTensor h y l s =>
       match trans_qubit s x (BA (Var y)) with None => None
                 | Some (ps,pr) => Some ((lambdaITE y (zand (zle ( i) ( (BA (Var y)))) (zlt ( (BA (Var y))) ( h)))
                                       ps (zread x (BA (Var y)))), zand pr (zeq ( i) ( l)),h)
       end
             | Tensor s1 s2 => match trans_tensor' s1 x i yh with None => None
                                           | Some (p1,pr1,h1) => 
                                match trans_tensor' s2 p1 h1 yh with None => None
                                          | Some (p2,pr2,h2) => 
                                     Some (p2, zand pr1 pr2, h2)
                                end
                              end
            | Sigma (BA (Num 2)) j b (NTensor h k l s) =>
                  match trans_qubit_one s x (BA (Var k)) yh j 0 with None => None 
                        | Some p1 => 
                     match trans_qubit_one s x (BA (Var k)) yh j 1 with None => None 
                        | Some p2 => Some (lambdaITE k (zand (zle i (BA (Var k))) (zlt ( (BA (Var k))) ( h)))
                                             (ite (zeq (BA (Var j)) (BA (Num 0))) p1 p2) 
                                             (zread yh (BA (Var k))), (zeq ( i) ( l)),h)
                     end 
                 end
    | a => match trans_qubit a x i with None => None | Some (p,pr) => Some (p,pr,APlus i (BA (Num 1))) end
   end.
Definition trans_tensor (v:state) (x:z3_exp) (n:nat) (yh:var) := 
       match trans_tensor' v x (BA (Num 0)) (z3_var yh) with None => None
                                  | Some (p,pr,h) => Some (p,zand pr (zeq ( h) ( (BA (Num n)))),h)
       end.


Definition is_tensor (v:state) := match v with NTensor h y l s => true | Tensor s1 s2 => true | _ => false end.


Definition trans_sigma (v:state) (x:var) (n:nat) (y:var) (z:var) (fresh:var) := 
    match v with | Sigma (TwoTo q) j b s =>
     let u := fresh in let v := fresh+1 in let w := fresh+2 in
       Some (z3_var z, zforall u (zforall v (zimply (zand (zand (zle (BA (Num 0)) (BA (Var v))) (zlt (BA (Var v)) q))
                            (zor (zqeq ( (intRead (z3_var u) (BA (Var v)))) ( (intValue (BA (Num 0)))))
                                 (zqeq ( (intRead (z3_var u) (BA (Var v)))) ( (intValue (BA (Num 1)))))))
                     (zqeq (lambdaITE w ((zand (zle (BA (Num 0)) (BA (Var v))) (zlt (BA (Var v)) q)))
                                        (zread (z3_var z) (BA (Var w)))
                                        (zread (z3_var z) (BA (Num 0))))
                           (lambdaITE w ((zand (zle (BA (Num 0)) (BA (Var v))) (zlt (BA (Var v)) q)))
                                        (z3_bit (zget (z3_var x) (BA (Var w)) (intRead (z3_var u) (BA (Var w)))))
                                        (zread (z3_var x) (BA (Num 0))))))), fresh+3)
       
    | a => match trans_tensor a (z3_var x) n y with None => None
            | Some (p,pr,h) => Some (p,pr,fresh)
           end
    end.
*)
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
