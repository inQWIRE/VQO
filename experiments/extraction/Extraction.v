Require Coq.extraction.Extraction.
Require Import AltGateSet.
Require Import ExtrOQASM.
Require Import CLArith.
Require Import ModMult.
Require Import RZArith.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.
Extract Inlined Constant Nat.eqb => "(=)".

(* Custom extraction files. *)
Require ExtrOcamlList.
Require ExtrOcamlR.
Extract Inlined Constant R2 => "2.0".
Extract Inlined Constant R4 => "4.0".

(* Perform extraction *)
Separate Extraction 
    (* RCIR modular multiplier *)
    ModMult.modmult_rev 
    ExtrOQASM.bc2ucom
    
    (* VQO classical modular multiplier *)
    ExtrOQASM.trans_modmult_rev
    
    (* VQO QFT-based modular multiplier *)
    ExtrOQASM.trans_rz_modmult_rev
    
    (* VQO classical adders/multipliers *)
    ExtrOQASM.trans_cl_adder
    ExtrOQASM.trans_cl_const_mul
    ExtrOQASM.trans_cl_mul
    
    (* VQO QFT-based adders/multpliers *)
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
    
    (* OQIMP examples*)
    ExtrOQASM.trans_dmc_qft
    ExtrOQASM.trans_dmc_cl
    ExtrOQASM.trans_dmq_qft
    ExtrOQASM.trans_dmq_cl
    
    (* decomposition pass *)
    AltGateSet.decompose_CU1_and_C3X

    (* Liyi's new stuff *)
    ExtrOQASM.trans_rz_add_mul_opt
    ExtrOQASM.trans_rz_add_mul
    ExtrOQASM.trans_cl_add_mul.
