open Arg
open Hifirrtl_lang
open Printf

(*let () =
  (* 调整 GC 参数，减小 Major GC 频率，提高性能 *)
  let open Gc in
  let c = get () in
  set { c with
    minor_heap_size = 64 * 1024 * 1024;  (* minor heap 大小，默认 256KB，增大到 4MB *)
    major_heap_increment = 256;         (* major heap 每次增长量，默认 128，增大到 256 *)
    space_overhead = 180;               (* 允许的空间开销百分比，默认 80，适当放宽 *)
    max_overhead = 500;
    allocation_policy = 2;   (* First-fit 分配策略 *)}*)

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon file =
  let hif_ast = Parser.hiparse file in 
  Ast.pp_fcircuit stdout hif_ast

let () = parse args anon usage
