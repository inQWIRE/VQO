open Printf

open AltGateSet
open ExtrOQASM
open OQASM
(*open OracleExample*)

(* print an OQASM program (for debugging) *)
let rec print_exp' (e:exp) indent =
  let tabs = String.make indent '\t' in
  match e with
  | SKIP (x,i) -> printf "%sSKIP (%d,%d)\n" tabs x i
  | X (x,i) -> printf "%sX (%d,%d)\n" tabs x i
  | CU ((x,i),e) -> (printf "%sCU (%d,%d)\n" tabs x i ; print_exp' e (indent + 1))
  | RZ (n,(x,i)) -> printf "%sRZ %d (%d,%d)\n" tabs n x i
  | RRZ (n,(x,i)) -> printf "%sRRZ %d (%d,%d)\n" tabs n x i
  | SR (n,x) -> printf "%sSR %d %d\n" tabs n x
  | SRR (n,x) -> printf "%sSRR %d %d\n" tabs n x
  | Lshift x -> printf "%sLSHIFT %d\n" tabs x
  | Rshift x -> printf "%sRSHIFT %d\n" tabs x
  | Rev x -> printf "%sREV %d\n" tabs x
  | QFT (x,n) -> printf "%sQFT %d %d\n" tabs n x
  | RQFT (x,n) -> printf "%sRQFT %d %d\n" tabs n x
  | Seq (e1,e2) -> (print_exp' e1 indent ; print_exp' e2 indent)

let print_exp e = print_exp' e 0

(* find max qubit value used (hacky) *)
let rec get_dim_aux (u : coq_U ucom) acc =
  match u with
  | Coq_useq (u1, u2) -> get_dim_aux u1 (get_dim_aux u2 acc)
  | Coq_uapp (_, _, qs) -> List.fold_left max acc qs
let get_dim u = 1 + get_dim_aux u 0

(* write to qasm file *)
let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (1, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (1, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (1, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (1, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (1, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (2, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_CU1 (r), [a;b]) -> (fprintf oc "cu1(%f) q[%d], q[%d];\n" r a b ; k ())
  | Coq_uapp (2, U_CH, [a;b]) -> (fprintf oc "ch q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (3, U_CCU1 (r), [a;b;c]) -> (fprintf oc "ccu1(%f) q[%d], q[%d], q[%d];\n" r a b c ; k ())
  | Coq_uapp (3, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (4, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" a b c d ; k ())
  (* badly typed case (e.g. App2 of U_H) *)
  | _ -> failwith "ERROR: Failed to write qasm file"

(* insert measurements to get simulation results *)
let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : coq_U ucom) =
  let dim = get_dim u in
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   (*fprintf oc "creg c[%d];\n" dim;*)
   fprintf oc "\n";
   ignore(sqir_to_qasm oc (decompose_to_voqc_gates u) (fun _ -> ()));
   (*ignore(write_measurements oc dim);*)
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end *)
   close_out oc)

(* function to count gates 
  Output order: X, H, U1, CX, CH, CU1, CCX, CCU1, C3X *)
let rec count_gates_aux (u : coq_U ucom) acc =
  let (x,h,u1,cx,ch,cu1,ccx,ccu1,c3x) = acc in
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (1, U_X, _) -> (1+x,h,u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (1, U_H, _) -> (x,1+h,u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (1, U_U1 _, _) -> (x,h,1+u1,cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CX, _) -> (x,h,u1,1+cx,ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CH, _) -> (x,h,u1,cx,1+ch,cu1,ccx,ccu1,c3x)
  | Coq_uapp (2, U_CU1 _, _) -> (x,h,u1,cx,ch,1+cu1,ccx,ccu1,c3x)
  | Coq_uapp (3, U_CCX, _) -> (x,h,u1,cx,ch,cu1,1+ccx,ccu1,c3x)
  | Coq_uapp (3, U_CCU1 _, _) -> (x,h,u1,cx,ch,cu1,ccx,1+ccu1,c3x)
  | Coq_uapp (4, U_C3X, _) -> (x,h,u1,cx,ch,cu1,ccx,ccu1,1+c3x)
  (* unexpected gate type *)
  | _ -> failwith "ERROR: Failed to count gates"
let count_gates u = count_gates_aux u (0,0,0,0,0,0,0,0,0)

let print_and_write_file circ fname =
  let (x,h,u1,cx,ch,cu1,ccx,ccu1,c3x) = count_gates circ in
  (printf "\t%d qubits, { " (get_dim circ);
  if x > 0 then printf "X : %d, " x;
  if h > 0 then printf "H : %d, " h;
  if u1 > 0 then printf "U1 : %d, " u1;
  if cx > 0 then printf "CX : %d, " cx;
  if ch > 0 then printf "CH : %d, " ch;
  if cu1 > 0 then printf "CU1 : %d, " cu1;
  if ccx > 0 then printf "CCX : %d, " ccx;
  if ccu1 > 0 then printf "CCU1 : %d, " ccu1;
  if c3x > 0 then printf "C3X : %d, " c3x;
  printf " }\n%!";
  write_qasm_file fname circ)

let log2 m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0))

let log2up m = int_of_float (ceil (log10 (float_of_int (2 * m)) /. log10 2.0))

let run_modmult_experiments c cinv m =
  if (c * cinv) mod m <> 1
  then failwith "Invalid inputs to run_modmult_experiments"
  else 
    let n = log2up m in
    let fname = string_of_int (log2 m) ^ ".qasm" in
    
    let _ = printf "Generating circuit for RZArith.real_rz_modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (trans_rz_modmult_rev m c cinv n) ("rz-mod-mul-" ^ fname) in

    let _ = printf "Generating circuit for RZArith.real_rz_modmult_rev_alt, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (trans_rz_modmult_rev_alt m c cinv n) ("rz-mod-mul-alt-" ^ fname) in

    let _ = printf "Generating circuit for CLArith.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (trans_modmult_rev m c cinv n) ("cl-mod-mul-" ^ fname) in
    
    ();;

let run_adders size m =
  let size_of_m = log2 m in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_adders"
  else
    let _ = printf "Generating circuit for TOFF-based adder, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_cl_adder size) ("cl-adder-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant adder, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_const_adder size m) ("rz-const-adder-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based adder, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_rz_adder size) ("rz-adder-" ^ fname) in
    
    ();;

let run_multipliers size m =
  let size_of_m = log2 m in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_multipliers"
  else
    let _ = printf "Generating circuit for TOFF-based constant multiplier, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_const_mul size m) ("cl-const-mul-" ^ fname) in

    let _ = printf "Generating circuit for TOFF-based multiplier, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_cl_mul size) ("cl-mul-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant multiplier, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_const_mul size m) ("rz-const-mul-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based multiplier, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_rz_mul size) ("rz-mul-" ^ fname) in
    
    let _ = printf "Generating circuit for TOFF-based (Quipper inspired) multiplier, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_cl_mul_out_place size) ("cl-mul-quipper-" ^ fname) in

    ();;

let run_div_mod size m =
  let size_of_m = log2 m in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_multipliers"
  else
    let _ = printf "Generating circuit for TOFF-based constant modder/divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_div_mod size m) ("cl-div-mod-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant modder/divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_div_mod size m) ("rz-div-mod-" ^ fname) in
    
    ();;

let run_approx size m b =
  let size_of_m = log2 m in
  let fname = (string_of_int size) ^ ".qasm" in
  if (size < size_of_m) || (b > size)
  then failwith "Invalid inputs to run_approx"
  else
    let _ = printf "Generating circuit for approximate QFT-based adder, inputs size=%d b=%d...\n%!" size b in
    let _ = print_and_write_file (trans_appx_adder size b) ("rz-add-appx-" ^ fname) in

    let _ = printf "Generating circuit for approximate QFT-based constant adder, inputs size=%d m=%d b=%d...\n%!" size m b in
    let _ = print_and_write_file (trans_appx_const_adder size b m) ("rz-const-add-appx-" ^ fname) in

    let _ = printf "Generating circuit for approximate QFT-based constant subtractor, inputs size=%d m=%d b=%d...\n%!" size m b in
    let _ = print_and_write_file (trans_appx_const_sub size b m) ("rz-const-sub-appx-" ^ fname) in

    let _ = printf "Generating circuit for approximate QFT-based div-mod (w/out SWAPs), inputs size=%d m=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_div_mod_app_shift size m) ("rz-div-mod-appx-" ^ fname) in

    let _ = printf "Generating circuit for approximate QFT-based div-mod (with SWAPs), inputs size=%d m=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_div_mod_app_swaps size m) ("rz-div-mod-appx-swaps-" ^ fname) in

    ();;

let run_partial_eval size =
  let fname = (string_of_int size) ^ ".qasm" in
  let _ = printf "Generating circuits for partial eval experiments, input size=%d...\n%!" size in
  match trans_dmc_qft size with 
  | None -> printf "ERROR: trans_dmc_qft returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-rz-const-" ^ fname);
  match trans_dmc_cl size with 
  | None -> printf "ERROR: trans_dmc_cl returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-cl-const-" ^ fname);
  match trans_dmq_qft size with 
  | None -> printf "ERROR: trans_dmq_qft returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-rz-" ^ fname);
  match trans_dmq_cl size with 
  | None -> printf "ERROR: trans_dmq_cl returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-cl-" ^ fname);
  ();;

(* Experiments for paper: *)
(*run_modmult_experiments 139 117 173;;
run_adders 16 38168;;
run_multipliers 16 38168;;
run_div_mod 16 38168;;
run_approx 16 38168 15;;
run_partial_eval 16;;*)r

match compile_collision_sqir with
| None -> printf "ERROR: compile_collision_sqir returned None\n"
| Some c -> print_and_write_file c "chacha-oracle.qasm"