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
(** Session Definitions **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Local Open Scope nat_scope.

Inductive in_session : list (var*nat*nat) -> list (var*nat*nat) -> Prop :=
     in_session_rule : forall a b c d, b = c++a++d -> in_session a b.

Inductive in_ses_pos : list (var*nat*nat) -> list (var*nat*nat) -> nat * nat -> Prop :=
   find_pos: forall a b c d, b = c++a++d -> in_ses_pos a b (length c, length c + length a).



Definition type_cfac : Type := nat -> rz_val.

Inductive type_phase :=  Uni.

(*| Uni (b: nat -> rz_val) | DFT (b: nat -> rz_val). *)
Inductive type_elem : Type := TNor (p : option (rz_val))
         | TH (r:option type_phase)
         | CH (t:option (nat * type_cfac)).

Inductive se_type : Type := THT (n:nat) (t:type_elem).

Definition type_map := list (session * se_type).

Fixpoint ses_len (l:list (var * nat * nat)) :=
   match l with nil => 0 | (x,l,h)::xl => (h - l) + ses_len xl end. 

Inductive subtype : se_type -> se_type -> Prop :=
   | nor_ch_none: forall n, subtype (THT n (TNor None)) (THT n (CH None))
   | nor_ch: forall n p, subtype (THT n (TNor (Some p))) 
           (THT n (CH (Some (1,fun i => if i =? 0 then p else allfalse))))
   | ch_nor: forall n b, subtype (THT n (CH (Some (1,b)))) (THT n (TNor (Some (b 0))))
   | had_ch: forall n p, subtype (THT n (TH p)) (THT n (CH (Some ((2^n),(fun i => nat2fb i)))))
   | ch_had: forall p, p 0 = nat2fb 0 -> p 1 = nat2fb 1 -> 
           subtype (THT 1 (CH (Some (2,p)))) (THT 1 (TH None))
   | ch_none: forall n p, subtype (THT n (CH (Some p))) (THT n (CH None)).

Definition join_val {A:Type} (n :nat) (r1 r2:nat -> A) := fun i => if i <? n then r1 n else r2 (i-n).

Definition lshift_fun {A:Type} (f:nat -> A) (n:nat) := fun i => f (i+n).

Definition join_nor_val (n:nat) (r1 r2:option rz_val) :=
   match (r1,r2) with (Some ra1,Some ra2) => Some (join_val n ra1 ra2)
                   | (_,_) => None
   end.

Definition join_had_val (n:nat) (r1 r2:option type_phase) :=
   match (r1,r2) with (Some Uni,Some Uni) => Some Uni
                   | (_,_) => None
   end.

Fixpoint car_s (i:nat) (n:nat) (m:nat) (r1:rz_val) (r2 : type_cfac) : type_cfac := 
    match n with 0 => (fun x => allfalse)
              | S n' => (fun x => if x =? i+n' then join_val m r1 (r2 n') else car_s i n' m r1 r2 x)
    end.
Fixpoint car_fun (size n m:nat) (r1 r2: type_cfac) :=
   match n with 0 => (fun x => allfalse)
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s (m * n') m size (r1 n') r2 x
                        else car_fun size n' m r1 r2 x)
   end.

Definition join_ch_val (size:nat) (r1 r2:option (nat * type_cfac)) :=
   match (r1,r2) with (Some (n,r1),Some (m,r2)) => Some (m*n,car_fun size n m r1 r2)
                   | (_,_) => None
   end.

Inductive times_type: se_type -> se_type -> se_type -> Prop :=
  | nor_nor_to: forall n m p1 p2,
               times_type (THT n (TNor p1)) (THT m (TNor p2)) (THT (n+m) (TNor (join_nor_val n p1 p2)))
  | had_had_to: forall n m p1 p2,
               times_type (THT n (TH p1)) (THT m (TH p2)) (THT (n+m) (TH (join_had_val n p1 p2)))
  | ch_ch_to : forall n m p1 p2,
               times_type (THT n (CH p1)) (THT m (CH p2)) (THT (n+m) (CH (join_ch_val n p1 p2))).

Definition split_nor_val (n:nat) (r:option rz_val) :=
   match r with None => (None,None)
             | Some ra => (Some (cut_n ra n), Some (lshift_fun ra n))
   end.

Definition split_had_val (n:nat) (r:option type_phase) :=
   match r with None => (None,None)
             | Some Uni => (Some Uni, Some Uni)
   end.

Inductive split_type: nat -> se_type -> se_type * se_type -> Prop :=
  | nor_split: forall n m r r1 r2, split_nor_val n r = (r1,r2)
                -> split_type n (THT (n+m) (TNor (r))) ((THT n (TNor r1)),(THT m (TNor r2)))
  | had_split: forall n m r r1 r2, split_had_val n r = (r1,r2)
                -> split_type n (THT (n+m) (TH (r))) ((THT n (TH r1)),(THT m (TH r2)))
  | ch_split: forall n m num r r1 r2, join_ch_val n (Some (num,r1)) (Some(1,r2)) = (Some (num,r))
                -> split_type n (THT (n+m) (CH (Some (num,r)))) ((THT n (CH (Some (num,r1)))),(THT m (CH (Some (1,r2))))).

Definition mut_nor_aux (pos n m: nat) (r : rz_val) :=
    fun i => if i <? pos then r i
      else if (pos <=? i) && (i <? pos + m) then r (i+n)
      else if (pos + m <=? i) && (i <? pos + m + n) then r (i - m)
      else r i.

Definition mut_nor (pos n m:nat) (r: option rz_val) :=
   match r with None => None | Some ra => Some (mut_nor_aux pos n m ra) end.


Definition mut_ch_aux (pos n m: nat) (r : type_cfac) : type_cfac :=
    fun i => mut_nor_aux pos n m (r i).

Definition mut_ch (pos n m : nat) (r : option (nat * type_cfac)) :=
  match r with None => None | Some (len,ra) => Some (len, mut_ch_aux pos n m ra) end.

Inductive mut_type: nat -> nat -> nat -> se_type -> se_type -> Prop :=
  | nor_mut: forall pos n m len r,
             mut_type pos n m (THT len (TNor (r))) (THT len (TNor (mut_nor pos n m r)))
  | had_mut: forall pos n m len r, mut_type pos n m (THT len (TH (r))) (THT len (TH r))
  | ch_mut: forall pos n m len r, mut_type pos n m (THT len (CH r)) (THT len (CH (mut_ch pos n m r))).

Inductive env_equiv : type_map -> type_map -> Prop :=
     | env_comm :forall a1 a2, env_equiv (a1++a2) (a2++a1)
     | env_sub: forall x v u a, subtype v u -> env_equiv ((x,v)::a) ((x,u)::a)
     | env_mut: forall l1 l2 a b v u S, mut_type (ses_len l1) (ses_len ([a])) (ses_len ([b])) v u ->
                 env_equiv ((l1++(a::b::l2),v)::S) ((l1++(b::a::l2),u)::S)
     | env_merge: forall x v y u a vu, times_type v u vu -> env_equiv ((x,v)::((y,u)::a)) ((x++y,vu)::a)
     | env_split: forall x y v v1 v2 a, split_type (ses_len x) v (v1,v2) -> env_equiv ((x++y,v)::a) ((x,v1)::(y,v2)::a).

Inductive find_env {A:Type}: list (session * A) -> session -> option (session * A) -> Prop :=
  | find_env_empty : forall l, find_env nil l None
  | find_env_many_1 : forall S x y t, in_session x y -> find_env ((y,t)::S) x (Some (y,t))
  | find_env_many_2 : forall S x y v t, ~ in_session x y -> find_env S y t -> find_env ((x,v)::S) y t.

Inductive find_type : type_map -> session -> option (session * se_type) -> Prop :=
    | find_type_rule: forall S S' x t, env_equiv S S' -> find_env S' x t -> find_type S x t.


Inductive update_env {A:Type}: list (session * A) -> session -> A -> list (session * A) -> Prop :=
  | up_env_empty : forall l t, update_env nil l t ([(l,t)])
  | up_env_many_1 : forall S x t t', update_env ((x,t)::S) x t' ((x,t')::S)
  | up_env_many_2 : forall S S' x y t t', x <> y -> update_env S x t' S' -> update_env ((y,t)::S) x t' ((y,t)::S').

(* Define semantic state equations. *)

Inductive state_elem :=
                 | Nval (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b:nat -> R * rz_val * rz_val) 
                 | Fval (m:nat) (b : nat -> C * rz_val).

Definition qstate := list (session * state_elem).

Fixpoint n_rotate (rmax:nat) (r1 r2:rz_val) :=
   match rmax with 0 => r1
              | S n => if r2 n then n_rotate n (addto r1 n) r2 else n_rotate n r1 r2
   end.

Fixpoint sum_rotate (n:nat) (b:nat->bool) (rmax:nat) (r:nat -> rz_val) :=
   match n with 0 => allfalse
             | S m => if b m then n_rotate rmax (sum_rotate m b rmax r) (r m) else sum_rotate m b rmax r
   end.
Definition sum_rotates (n:nat) (rmax:nat) (r:nat -> rz_val) :=
    fun i => if i <? 2^n then ( (1/sqrt (2^n))%R,sum_rotate n (nat2fb i) rmax r,nat2fb i) else (0%R,allfalse,allfalse).

Fixpoint r_n_rotate (rmax:nat) (r1 r2:rz_val) :=
   match rmax with 0 => r1
              | S n => if r2 n then r_n_rotate n (addto_n r1 n) r2 else r_n_rotate n r1 r2
   end.

Definition a_nat2fb f n := natsum n (fun i => Nat.b2n (f i) * 2^i).

Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat -> bool) (n:nat) : R :=
      turn_angle_r (fbrev n rval) n n.

Definition get_amplitude (rmax:nat) (n:nat) (r1:R) (r2:rz_val) : C := 
    r1 * Cexp (2*PI * (turn_angle r2 rmax)).

Inductive state_same {rmax:nat} : nat -> state_elem -> state_elem -> Prop :=
   | nor_ch_ssame: forall n r, state_same n (Nval r)
             (Cval 1 (fun i => if i =? 0 then (0%R,allfalse,r) else (0%R,allfalse,allfalse)))
   | ch_nor_ssame: forall n r, state_same n (Cval 1 r) (Nval (snd (r 0)))
   | fch_nor_ssame: forall n r, state_same n (Fval 1 r) (Nval (snd (r 0)))
   | had_ch_ssame : forall n r, state_same n (Hval r) (Cval (2^n) (sum_rotates n rmax r))
   | ch_had_ssame: forall r a e1 e2, r 0 = (a,e1,nat2fb 0) -> 
            r 1 = (a,e2,nat2fb 1) -> state_same 1 (Cval 2 r) (Hval (fun i => r_n_rotate rmax e2 e1))
   | ch_fch_ssame: forall n m r, state_same n (Cval m r) 
                (Fval m (fun i => (get_amplitude rmax (2*n) (fst (fst (r i))) (snd (fst (r i))), snd (r i)))).

Definition mut_had_state (pos n m: nat) (r : (nat -> rz_val)) :=
    fun i => if i <? pos then r i
      else if (pos <=? i) && (i <? pos + m) then r (i+n)
      else if (pos + m <=? i) && (i <? pos + m + n) then r (i - m)
      else r i.

Definition mut_ch_state (pos n m:nat) (r : nat -> R * rz_val * rz_val) :=
    fun i => (fst (fst (r i)),snd (fst (r i)), mut_nor_aux pos n m (snd (r i))).

Definition mut_fch_state (pos n m:nat) (r : nat -> C * rz_val) :=
    fun i => (fst (r i), mut_nor_aux pos n m (snd (r i))).

Definition join_cval (rmax:nat) (m:nat) (r1 r2: R * rz_val * rz_val) :=
     (((fst (fst r1)) * (fst (fst r2)))%R,n_rotate rmax (snd (fst r1)) (snd (fst r2)),join_val m (snd r1) (snd r2)).

Fixpoint car_s_ch (rmax:nat) (i:nat) (n:nat) (m:nat) (r1:R*rz_val*rz_val) (r2 : nat -> R*rz_val*rz_val) := 
    match n with 0 => (fun x => (0%R,allfalse,allfalse))
              | S n' => (fun x => if x =? i+n' 
                  then join_cval rmax m r1 (r2 n') else car_s_ch rmax i n' m r1 r2 x)
    end.
Fixpoint car_fun_ch (rmax size n m:nat) (r1 r2: nat -> R * rz_val * rz_val) :=
   match n with 0 => (fun x => (0%R,allfalse,allfalse))
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s_ch rmax (m * n') m size (r1 n') r2 x
                        else car_fun_ch rmax size n' m r1 r2 x)
   end.

Definition join_fval (m:nat) (r1 r2: C * rz_val) : C * rz_val :=
     (((fst r1) * (fst r2))%C,join_val m (snd r1) (snd r2)).

Fixpoint car_s_fch (i:nat) (n:nat) (m:nat) (r1:C * rz_val) (r2 : nat -> C * rz_val) := 
    match n with 0 => (fun x => (C0,allfalse))
              | S n' => (fun x => if x =? i+n' 
                  then join_fval m r1 (r2 n') else car_s_fch i n' m r1 r2 x)
    end.
Fixpoint car_fun_fch (size n m:nat) (r1 r2: nat -> C * rz_val) :=
   match n with 0 => (fun x => (C0,allfalse))
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s_fch (m * n') m size (r1 n') r2 x
                        else car_fun_fch size n' m r1 r2 x)
   end.


Inductive mut_state: nat -> nat -> nat -> state_elem -> state_elem -> Prop :=
  | nor_mut_state: forall pos n m r,
             mut_state pos n m (Nval r) (Nval (mut_nor_aux pos n m r))
  | had_mut_state: forall pos n m r, mut_state pos n m (Hval r) (Hval (mut_had_state pos n m r))
  | ch_mut_state: forall pos n m num r, mut_state pos n m (Cval num r) (Cval num (mut_ch_state pos n m r))
  | fch_mut_state: forall pos n m num r, mut_state pos n m (Fval num r) (Fval num (mut_fch_state pos n m r)).

Inductive times_state {rmax:nat}: nat -> state_elem -> state_elem -> state_elem -> Prop :=
  | state_nor_nor_to: forall n p1 p2,
               times_state n (Nval p1) (Nval p2) (Nval (join_val n p1 p2))
  | state_had_had_to: forall n p1 p2,
               times_state n (Hval p1) (Hval p2) (Hval (join_val n p1 p2))
  | state_ch_ch_to : forall n m1 m2 p1 p2,
               times_state n (Cval m1 p1) (Cval m2 p2) (Cval (m1*m2) (car_fun_ch rmax n m1 m2 p1 p2))
  | state_fch_fch_to : forall n m1 m2 p1 p2,
               times_state n (Fval m1 p1) (Fval m2 p2) (Fval (m1*m2) (car_fun_fch n m1 m2 p1 p2)).

Definition cut_n_rz (f:nat -> rz_val) (n:nat) := fun i => if i <? n then f i else allfalse.

Inductive split_state {rmax:nat}: nat -> state_elem -> state_elem * state_elem -> Prop :=
  | nor_split_state: forall n r, split_state n (Nval r) (Nval (cut_n r n), Nval (lshift_fun r n))
  | had_split_state: forall n r, split_state n (Hval r) (Hval (cut_n_rz r n), Hval (lshift_fun r n))
  | ch_split_state: forall n m r r1 r2, car_fun_ch rmax n m 1 r1 r2 = r
                -> split_state n (Cval m r) (Cval m r1, Cval 1 r2)
  | fch_split_state: forall n m r r1 r2, car_fun_fch n m 1 r1 r2 = r
                -> split_state n (Fval m r) (Fval m r1, Fval 1 r2).


Inductive state_equiv {rmax:nat} : qstate -> qstate -> Prop :=
     | state_comm :forall a1 a2, state_equiv (a1++a2) (a2++a1)
     | state_sub: forall x v u a, @state_same rmax (ses_len x) v u -> state_equiv ((x,v)::a) ((x,u)::a)
     | state_mut: forall l1 l2 a b v u S, mut_state (ses_len l1) (ses_len ([a])) (ses_len ([b])) v u ->
                 state_equiv ((l1++(a::b::l2),v)::S) ((l1++(b::a::l2),u)::S)
     | state_merge: forall x v y u a vu, @times_state rmax (ses_len x) v u vu -> state_equiv ((x,v)::((y,u)::a)) ((x++y,vu)::a)
     | state_split: forall x y v v1 v2 a, @split_state rmax (ses_len x) v (v1,v2) -> state_equiv ((x++y,v)::a) ((x,v1)::(y,v2)::a).


Inductive find_state {rmax} : qstate -> session -> option (session * state_elem) -> Prop :=
    | find_state_rule: forall S S' x t, @state_equiv rmax S S' -> find_env S' x t -> find_state S x t.


