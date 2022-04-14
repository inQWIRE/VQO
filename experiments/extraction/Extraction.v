Require Coq.extraction.Extraction.
Require Import Reals.
Require Import AltGateSet.
Require Import OQASMProof.
Require Import CLArith.
Require Import RZArith.
Require Import ExtrOQASM.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Custom extraction files. *)
Require ExtrOcamlList.
Require ExtrOcamlR.
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".
Extract Inlined Constant R8 => "8.0".

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.
Extract Inductive nat => int [ "0" "succ" ] (* fix to bug in current lib *)
  "(fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))".
Extract Inlined Constant Init.Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.leb => "(<=)".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Init.Nat.sub => "(fun x y -> max 0 (x-y))".
Extract Inlined Constant IZR => "float_of_int".
Extract Inlined Constant Coq.Reals.Rpow_def.pow => "(fun r n -> r ** (float_of_int n))".

Extract Inlined Constant N.of_nat => "(fun x -> x)". (* id *)

Extract Constant id_nat => "fun x : int -> x". (* add type annotation *) 

(* Perform extraction *)
Separate Extraction
    (* OQASM Toffoli-based modular multiplier *)
    ExtrOQASM.trans_modmult_rev
    
    (* OQASM QFT-based modular multiplier *)
    ExtrOQASM.trans_rz_modmult_rev
    ExtrOQASM.trans_rz_modmult_rev_alt (* What is this?? *)
    
    (* OQASM Toffoli-based adders/multipliers *)
    ExtrOQASM.trans_cl_adder
    ExtrOQASM.trans_cl_const_mul
    ExtrOQASM.trans_cl_mul
    ExtrOQASM.trans_cl_mul_out_place (* Quipper's implementation *)
    
    (* OQASM QFT-based adders/multipliers *)
    ExtrOQASM.trans_rz_const_adder
    ExtrOQASM.trans_rz_adder
    ExtrOQASM.trans_rz_const_mul
    ExtrOQASM.trans_rz_mul
    ExtrOQASM.trans_appx_adder       (* uses AQFT *)
    ExtrOQASM.trans_appx_const_adder (* uses AQFT *)
    ExtrOQASM.trans_appx_const_sub   (* uses AQFT *)
    
    (* OQASM Toffoli-based divmod *)
    ExtrOQASM.trans_cl_div_mod
    
    (* OQASM QFT-based divmod *)
    ExtrOQASM.trans_rz_div_mod
    ExtrOQASM.trans_rz_div_mod_app_shift (* approx w/ OQASM shift *)
    ExtrOQASM.trans_rz_div_mod_app_swaps (* approx w/ SQIR SWAPs *)
    
    (* OQIMP examples*)
    ExtrOQASM.trans_dmc_qft
    ExtrOQASM.trans_dmc_cl
    ExtrOQASM.trans_dmq_qft
    ExtrOQASM.trans_dmq_cl
    ExtrOQASM.compile_collision_sqir 
    
    (* gate decomposition pass *)
    AltGateSet.decompose_to_voqc_gates.
