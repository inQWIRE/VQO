(* Classical distributions, finite support *)

Require Import List.
Require Import Reals.
Import ListNotations.
Open Scope list_scope.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.

(* Sum of list of real numbers *)
Fixpoint sumR (lst : list R) : R :=
  match lst with
  | head :: tail => head + sumR tail
  | nil => 0
  end.

(* Distribution with finite support.
 *
 * This is missing quite a bit of reasonable features.
 * Particularly, we can't check two distrs are equal mathematically...
 * There is no way to simplify by collating terms either.
 * It might be better to find and use a library. *)
Record distr (T : Type) := make_distr {
  probabilities : list (T * R);
  probability_wf : forall (i : nat),
    (* Tried nth instead of nth_error. Can't come up with good default val. *)
    match nth_error probabilities i with
    | None => True
    | Some element => let p := snd element in (p >= 0)%R /\ (p <= 1)%R
    end;
  distr_is_full :
    sumR (map snd probabilities) = 1%R;
}.

Lemma singleton_distr_wf :
  forall T (t : T) i,
    match nth_error [(t, 1%R)] i with
    | None => True
    | Some element => let p := snd element in (p >= 0)%R /\ (p <= 1)%R
    end.
Proof.
  intros.
  case_eq i.
  + simpl. lra.
  + intros. simpl.
    assert (H0 : @nth_error (T * R) [] n = None).
      rewrite nth_error_None.
      unfold length.
      lia.
    rewrite H0.
    trivial.
Qed.

Lemma singleton_distr_full :
  forall T (t : T),
    sumR (map snd [(t, 1%R)]) = 1%R.
Proof.
  intros.
  simpl.
  lra.
Qed.

Require Import BasicUtility.
Require Import Matrix.
Require QC.
Require Import FMaps.
Module VarMap := FMapList.Make(Nat_as_OT).

Variant cval :=
| bool_val (val : bool)
| int_val (val : Z).

(* This has to be done before Import QC *)
(* Otherwise there'd be notation issues *)
Record interp_env_t := interp_env {
  num_qubits : nat;
  c_env : VarMap.t cval;
  (* This seems clunky.
   * Not sure of a better way though.
   *)
  q_env : Vector (2 ^ num_qubits);
  q_env_addressing : posi -> nat;
}.

Import QC.

(* Currently bexp doesn't take a bool_val.
 * We can only compare two int_vals...
 *
 * The QHL paper supports classical boolean values.
 *)
Definition interp_bexp (e : bexp) (env : interp_env_t) : option bool :=
  let '(op, lhs, rhs) :=
    match e with
    | BEq x y => (Z.eqb, x, y)
    | BLt x y => (Z.ltb, x, y)
    | BLe x y => (Z.leb, x, y)
    end
  in
  match VarMap.find lhs env.(c_env) with
  | Some (int_val lval) =>
    match VarMap.find rhs env.(c_env) with
    | Some (int_val rval) =>
      Some (op lval rval)
    | _ => None
    end
  | _ => None
  end.

(* Naive attempt 1.
 * Doesn't work quite well for the following reasons:
 * 1. "While" doesn't terminate, so an interpreter just can't be written.
 * 2. Quantum computing is inherently random.
 *    Many instructions cannot be implemented without specifying distributions.
 *)
(** Abandoned **)
(**
Fixpoint interp (inst : pexp) (env : interp_env_t) : option interp_env_t :=
  match inst with
  | PSKIP => Some env
  | Abort => None
  | Assign x n => (* can only assign positive numbers? *)
      let val := int_val (Z.of_nat n) in
      Some (interp_env
        env.(num_qubits)
        (VarMap.add x val env.(c_env))
        env.(q_env)
        env.(q_env_addressing))
  | Meas p => None (* Partial measurement not implemented *)
  | InitQubit p => None (* Overwriting is equivalent to partial measurement *)
  | AppU u p => None (* u isn't the right type? Should be Matrix, not pexp *)
  | PSeq p1 p2 =>
    match interp p1 env with
    | Some env' => interp p2 env'
    | None => None
    end
  | IfExp b p_t p_f =>
    interp (if interp_bexp b env then p_t else p_f) env
  (* Can't write as an interpreter/fixpoint. *)
  (* "While" doesn't always terminate. *)
  (* In fact that also means that we can't compile "While" to OpenQASM 2. *)
  (* OpenQASM 3 though... maybe? *)
  | While b p => None
  (* Not yet implemented *)
  | _ => None
  end.
**)

(* New definition as relation *)
(* Does this look too much like Hoare triples? *)
Inductive OpSemStep_pointwise : interp_env_t -> pexp -> option (distr interp_env_t) -> Prop :=
| SemSkip : forall (env : interp_env_t),
  OpSemStep_pointwise env PSKIP (Some (make_distr
                           interp_env_t
                           [(env, 1)]
                           (singleton_distr_wf interp_env_t env)
                           (singleton_distr_full interp_env_t env)))
| SemAbort : forall (env : interp_env_t),
  OpSemStep_pointwise env Abort None
| SemAssign : forall (env : interp_env_t) (x : var) (n : nat),
  let new_env :=
    let val := int_val (Z.of_nat n) in
    interp_env env.(num_qubits) (VarMap.add x val env.(c_env)) env.(q_env) env.(q_env_addressing)
  in
  OpSemStep_pointwise env (Assign x n) (Some (make_distr interp_env_t
                                        [(new_env, 1)]
                                        (singleton_distr_wf interp_env_t new_env)
                                        (singleton_distr_full interp_env_t new_env)))
(* | SemMeas TODO *)
(* | SemInitQubit TODO *)
(* | SemAppU TODO *)
(* | SemIf TODO *)
(* | SemWhile TODO *)
(* | SemReflect TODO *)
(* | SemQWalk TODO *)
.

Inductive OpSemStep : distr interp_env_t -> pexp -> distr interp_env_t -> Prop :=
(* | SemFromPointwise : TODO
 *
 * Extend the version above.
 * Take distr instead of a single point.
 *
 * Challenges:
 * 1) Interface mismatch.
 *    There does not seem to be a way to say when part of the distribution aborts.
 *    Maybe we should just remove the distr_is_full requirement?
 *    Sub-distributions seem fine.
 * 2) Without library support, this may be more tedious than it should be...
 *    Step 1.
 *      Every relation ~ can be naturally generalized from A ~ B to (distr A) ~ (distr B).
 *      Do that for OpSemStep_pointwise.
 *    Step 2.
 *      Roughly speaking, we'll end up with (distr (distr B)).
 *      We can collate that back into (distr B).
 *)
| SemSeq : forall env env' env'' inst1 inst2,
  OpSemStep env inst1 env' ->
  OpSemStep env' inst2 env'' ->
  OpSemStep env (PSeq inst1 inst2) env''
(* There is an argument to define SemSkip here, instead of pointwise above. *)
.
