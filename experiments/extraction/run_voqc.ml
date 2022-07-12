open Printf
open Voqc.Qasm
open Voqc.Main

(* Simple program to optimize circuits using VOQC & write to 'results.csv' *)

let optimize_and_write_result oc inf =
  let (c, n) = read_qasm inf in
  let c' = optimize c in
  fprintf oc "%s,%d,%d\n" inf n (count_total c');;

let oc = open_out "results.csv" in
let _ = fprintf oc "Name,Num qubits,Num gates\n" in
let quipper_files = List.map (fun f -> Filename.concat "quipper_files" f) 
                             (List.filter (fun x -> Filename.extension x = ".qasm") 
                                          (Array.to_list (Sys.readdir "quipper_files"))) in
let vqo_files = List.map (fun f -> Filename.concat "vqo_files" f) 
                         (Array.to_list (Sys.readdir "vqo_files")) in
List.iter (optimize_and_write_result oc) quipper_files;
List.iter (optimize_and_write_result oc) vqo_files
