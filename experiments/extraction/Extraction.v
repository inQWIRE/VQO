Require Coq.extraction.Extraction.
Require Import Reals.
Require Import AltGateSet.
Require Import ExtrOQASM.
Require Import CLArith.
Require Import RZArith.

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
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.sub => "(-)".
Extract Inlined Constant IZR => "float_of_int".
Extract Inlined Constant Coq.Reals.Rpow_def.pow => "(fun r n -> r ** (float_of_int n))".
Extract Inlined Constant N.of_nat => "(fun x -> x)". (* id *)

(* Perform extraction *)
Separate Extraction
    (* VQO classical modular multiplier *)
    ExtrOQASM.trans_modmult_rev
    
    (* VQO QFT-based modular multiplier *)
    ExtrOQASM.trans_rz_modmult_rev
    ExtrOQASM.trans_rz_modmult_rev_alt (* What is this?? *)
    
    (* VQO classical adders/multipliers *)
    ExtrOQASM.trans_cl_adder
    ExtrOQASM.trans_cl_const_mul
    ExtrOQASM.trans_cl_mul
    ExtrOQASM.trans_cl_mul_out_place (* Quipper's implementation *)
    
    (* VQO QFT-based adders/multipliers *)
    ExtrOQASM.trans_rz_const_adder
    ExtrOQASM.trans_rz_adder
    ExtrOQASM.trans_rz_const_mul
    ExtrOQASM.trans_rz_mul
    
    (* VQO TOFF-based divmod *)
    ExtrOQASM.trans_cl_mod
    ExtrOQASM.trans_cl_div
    ExtrOQASM.trans_cl_div_mod
    
    (* VQO QFT-based divmod *)
    ExtrOQASM.trans_rz_mod
    ExtrOQASM.trans_rz_div
    ExtrOQASM.trans_rz_div_mod
    ExtrOQASM.trans_rz_div_mod_app_shift (* approx w/ OQASM shift *)
    ExtrOQASM.trans_rz_div_mod_app_swaps (* approx w/ SQIR SWAPs *)
    
    (* OQIMP examples*)
    ExtrOQASM.trans_dmc_qft
    ExtrOQASM.trans_dmc_cl
    ExtrOQASM.trans_dmq_qft
    ExtrOQASM.trans_dmq_cl
    
    (* decomposition pass *)
    AltGateSet.decompose_to_voqc_gates

    (* repeated add/mult experiments *)
    ExtrOQASM.trans_rz_add_mul_opt
    ExtrOQASM.trans_rz_add_mul
    ExtrOQASM.trans_cl_add_mul

    (* approximate arithmetic, b arg should be <= size *)
    ExtrOQASM.trans_appx_adder
    ExtrOQASM.trans_appx_const_adder
    ExtrOQASM.trans_appx_const_sub.