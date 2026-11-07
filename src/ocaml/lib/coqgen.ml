open Hifirrtl_lang
open Extraction

module H = HiFirrtl_with_implicit_widths
module E = Env_with_implicit_widths
module F = HiEnv_with_implicit_widths
module I = Firrtl_with_implicit_widths

let nat (x : 'a) = string_of_int (Obj.magic x : int)
let q s = "@" ^ s ^ " VarOrder.T"

let pp_fgtyp = function
  | E.Fuint n -> Printf.sprintf "(Fuint %d)" n
  | E.Fsint n -> Printf.sprintf "(Fsint %d)" n
  | E.Fclock -> "Fclock" | E.Freset -> "Freset" | E.Fasyncreset -> "Fasyncreset"

let rec pp_type = function
  | F.Gtyp t -> Printf.sprintf "(%s %s)" "Gtyp" (pp_fgtyp t)
  | F.Atyp (t,n) -> Printf.sprintf "(%s %s %d)" "Atyp" (pp_type t) n
  | F.Btyp f -> Printf.sprintf "(%s %s)" "Btyp" (pp_fields f)
and pp_fields = function
  | F.Fnil -> "(Fnil)"
  | F.Fflips (v,fl,t,tl) ->
      Printf.sprintf "(%s %s %s %s %s)" "Fflips" (nat v)
        (match fl with F.Flipped -> "Flipped" | F.Nflip -> "Nflip")
        (pp_type t) (pp_fields tl)

let rec pp_ref = function
  | H.Eid v -> Printf.sprintf "(%s %s)" (q "Eid") (nat v)
  | H.Esubfield (r,v) -> Printf.sprintf "(%s %s %s)" (q "Esubfield") (pp_ref r) (nat v)
  | H.Esubindex (r,n) -> Printf.sprintf "(%s %s %d)" (q "Esubindex") (pp_ref r) n
  | H.Esubaccess (r,e) -> Printf.sprintf "(%s %s %s)" (q "Esubaccess") (pp_ref r) (pp_expr e)
and pp_bits bs =
  let one = function true -> "true" | false -> "false" in
  "[::" ^ String.concat "; " (List.map one bs) ^ "]"
and pp_expr = function
  | H.Econst (t,b) -> Printf.sprintf "(%s %s %s)" (q "Econst") (pp_fgtyp t) (pp_bits b)
  | H.Ecast (c,e) -> Printf.sprintf "(%s %s %s)" (q "Ecast") (pp_cast c) (pp_expr e)
  | H.Eprim_unop (o,e) -> Printf.sprintf "(%s %s %s)" (q "Eprim_unop") (pp_unop o) (pp_expr e)
  | H.Eprim_binop (o,a,b) -> Printf.sprintf "(%s %s %s %s)" (q "Eprim_binop") (pp_binop o) (pp_expr a) (pp_expr b)
  | H.Emux (a,b,c) -> Printf.sprintf "(%s %s %s %s)" (q "Emux") (pp_expr a) (pp_expr b) (pp_expr c)
  | H.Evalidif (c,e) -> Printf.sprintf "(%s %s %s)" (q "Evalidif") (pp_expr c) (pp_expr e)
  | H.Eref r -> Printf.sprintf "(%s %s)" (q "Eref") (pp_ref r)
and pp_cast = function I.AsUInt -> "AsUInt" | I.AsSInt -> "AsSInt" | I.AsClock -> "AsClock" | I.AsAsync -> "AsAsync"
and pp_unop = function
  | I.Upad n -> Printf.sprintf "(Upad %d)" n | I.Ushl n -> Printf.sprintf "(Ushl %d)" n | I.Ushr n -> Printf.sprintf "(Ushr %d)" n
  | I.Ucvt -> "Ucvt" | I.Uneg -> "Uneg" | I.Unot -> "Unot" | I.Uandr -> "Uandr" | I.Uorr -> "Uorr" | I.Uxorr -> "Uxorr"
  | I.Uextr(a,b) -> Printf.sprintf "(Uextr %d %d)" a b | I.Uhead n -> Printf.sprintf "(Uhead %d)" n | I.Utail n -> Printf.sprintf "(Utail %d)" n
and pp_cmp = function I.Blt->"Blt"|I.Bleq->"Bleq"|I.Bgt->"Bgt"|I.Bgeq->"Bgeq"|I.Beq->"Beq"|I.Bneq->"Bneq"
and pp_binop = function
 | I.Badd->"Badd"|I.Bsub->"Bsub"|I.Bmul->"Bmul"|I.Bdiv->"Bdiv"|I.Brem->"Brem"|I.Bdshl->"Bdshl"|I.Bdshr->"Bdshr"|I.Band->"Band"|I.Bor->"Bor"|I.Bxor->"Bxor"|I.Bcat->"Bcat"
 | I.Bcomp c -> "(Bcomp " ^ pp_cmp c ^ ")"

let rec seq f = function [] -> "[::]" | x::xs -> "[:: " ^ f x ^ (List.fold_left (fun s x -> s ^ ";\n" ^ f x) "" xs) ^ "]"
let pp_mem_port p = Printf.sprintf "(@mk_mem_port VarOrder.T %s %s %s %s %s)" (nat p.H.id) (nat p.addr) (nat p.en) (nat p.clk) (nat p.mask)
let pp_mem m =
  Printf.sprintf "(@mk_fmem VarOrder.T %s %d %s %s %d %d %s)"
    (pp_type m.H.data_type) m.depth (seq pp_mem_port m.reader) (seq pp_mem_port m.writer)
    m.read_latency m.write_latency
    (match m.read_write with I.Coq_old -> "old" | I.Coq_new -> "new" | I.Coq_undefined -> "undefined")
let rec pp_stmt = function
 | H.Sskip -> "(@Sskip VarOrder.T)"
 | H.Swire(v,t) -> Printf.sprintf "(%s %s %s)" (q "Swire") (nat v) (pp_type t)
 | H.Snode(v,e) -> Printf.sprintf "(%s %s %s)" (q "Snode") (nat v) (pp_expr e)
 | H.Sfcnct(r,e) -> Printf.sprintf "(%s %s %s)" (q "Sfcnct") (pp_ref r) (pp_expr e)
 | H.Sinvalid r -> Printf.sprintf "(%s %s)" (q "Sinvalid") (pp_ref r)
 | H.Sinst(v,m) -> Printf.sprintf "(%s %s %s)" (q "Sinst") (nat v) (nat m)
 | H.Sreg(v,r) -> Printf.sprintf "(%s %s (@mk_freg VarOrder.T %s %s %s))" (q "Sreg") (nat v) (pp_type r.H.coq_type) (pp_expr r.clock) (pp_rst r.reset)
 | H.Smem(v,m) -> Printf.sprintf "(%s %s %s)" (q "Smem") (nat v) (pp_mem m)
 | H.Swhen(c,a,b) -> Printf.sprintf "(%s %s %s %s)" (q "Swhen") (pp_expr c) (pp_stmts a) (pp_stmts b)
and pp_rst = function H.NRst -> "(@NRst VarOrder.T)" | H.Rst(a,b) -> Printf.sprintf "(Rst %s %s)" (pp_expr a) (pp_expr b)
and pp_stmts s = match s with H.Qnil -> "(" ^ q "Qnil" ^ ")" | H.Qcons(a,b) -> "(" ^ q "Qcons" ^ " " ^ pp_stmt a ^ " " ^ pp_stmts b ^ ")"
let pp_port = function H.Finput(v,t)->Printf.sprintf "(%s %s %s)" (q "Finput") (nat v) (pp_type t)|H.Foutput(v,t)->Printf.sprintf "(%s %s %s)" (q "Foutput") (nat v) (pp_type t)
let stmt_list s =
  let rec go acc = function H.Qnil -> List.rev acc | H.Qcons (x, xs) -> go (x :: acc) xs in
  go [] s

let chunks n xs =
  let rec take k acc rest =
    if k = 0 || rest = [] then (List.rev acc, rest)
    else take (k - 1) (List.hd rest :: acc) (List.tl rest)
  in
  let rec loop acc rest =
    if rest = [] then List.rev acc
    else let (a, b) = take n [] rest in loop (a :: acc) b
  in loop [] xs

let pp_stmt_seq_list xs =
  List.fold_right (fun x tail -> Printf.sprintf "(%s %s %s)" (q "Qcons") (pp_stmt x) tail) xs ("(" ^ q "Qnil" ^ ")")

let emit_qcat oc =
  output_string oc "Fixpoint generated_qcat (s1 s2 : hfstmt_seq VarOrder.T) : hfstmt_seq VarOrder.T :=\n";
  output_string oc "  match s1 with\n  | Qnil => s2\n  | Qcons h t => Qcons h (generated_qcat t s2)\n  end.\n\n"

(* Emit every definition into the same .v file.  Statement chunks are kept
   small so that Coq never has to parse one deeply nested Qcons term. *)
let emit_module oc idx m =
  let (v, ports, stmts, ctor) = match m with
    | H.FInmod (v,p,s) -> (v,p,s,"FInmod")
    | H.FExmod (v,p,s) -> (v,p,s,"FExmod")
  in
  let chunks = chunks 1000 (stmt_list stmts) in
  let names = List.mapi (fun i _ -> Printf.sprintf "generated_module_%d_stmts_%d" idx i) chunks in
  List.iter2 (fun name xs -> Printf.fprintf oc "Definition %s : hfstmt_seq VarOrder.T :=\n  %s.\n\n" name (pp_stmt_seq_list xs)) names chunks;
  let stmt_expr = match names with
    | [] -> "(@Qnil VarOrder.T)"
    | n :: ns -> List.fold_left (fun acc x -> Printf.sprintf "(generated_qcat %s %s)" acc x) n ns
  in
  let modname = Printf.sprintf "generated_module_%d" idx in
  Printf.fprintf oc "Definition %s : @hfmodule VarOrder.T :=\n  (%s %s %s %s).\n\n" modname (q ctor) (nat v) (seq pp_port ports) stmt_expr;
  modname


let pp_prop_expr e = pp_expr e
let emit_verification oc (tc : Transhiast_without_inline.translated_circuit) =
  output_string oc "\n(* Generated verification properties. *)\n";
  output_string oc "Definition generated_hvalue_true (v : Semantics_with_implicit_widths.hvalue) : Prop := match v with | Semantics_with_implicit_widths.Gval (Env_with_implicit_widths.Fuint 1) b => b != [:: false] | _ => False end.\n";
  output_string oc "Definition generated_expr_true (e : (@HiFirrtl_with_implicit_widths.hfexpr VarOrder.T)) (sem : Var.VM.t Semantics_with_implicit_widths.hvalue) : Prop := match Semantics_with_implicit_widths.eval_hfexpr e sem sem with | Some v => generated_hvalue_true v | None => False end.\n";
  output_string oc "Definition generated_circuit_value (external_inputs : Var.VM.t Semantics_with_implicit_widths.hvalue) : option (Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) := circuit_value_with_memory generated_modules generated_top None external_inputs.\n";
  output_string oc "Fixpoint generated_assert_instances (module_id : VarOrder.T) (p : Var.VM.t Semantics_with_implicit_widths.hvalue -> Prop) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) (xs : list (Semantics_with_implicit_widths.SVM.key * VarOrder.T)) : Prop := match xs with | [::] => True | (path, actual) :: tl => ((actual != module_id) \\/ match Semantics_with_implicit_widths.SVM.find path states with | Some sem => p sem | None => False end) /\\ generated_assert_instances module_id p states tl end.\n";
  output_string oc "Fixpoint generated_assume_instances (module_id : VarOrder.T) (p : Var.VM.t Semantics_with_implicit_widths.hvalue -> Prop) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) (xs : list (Semantics_with_implicit_widths.SVM.key * VarOrder.T)) : Prop := match xs with | [::] => True | (path, actual) :: tl => ((actual != module_id) \\/ match Semantics_with_implicit_widths.SVM.find path states with | Some sem => p sem | None => False end) /\\ generated_assume_instances module_id p states tl end.\n";
  output_string oc "Definition generated_instances (module_id : VarOrder.T) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assert_instances module_id (fun _ => True) states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.\n";
  let emit_local kind x =
    let n = Printf.sprintf "generated_%s_%s" kind x.Transhiast_without_inline.name in
    Printf.fprintf oc "Definition %s_local (sem : Var.VM.t Semantics_with_implicit_widths.hvalue) : Prop := generated_expr_true %s sem -> generated_expr_true %s sem.\n" n (pp_expr x.enable) (pp_expr x.predicate); n
  in
  let an = List.map (emit_local "assert" ) tc.assertions in
  let un = List.map (emit_local "assume" ) tc.assumes in
  let fold_assumes = List.fold_left (fun acc n -> acc ^ " /\\ " ^ n ^ "_all states") "True" un in
  List.iter (fun x -> Printf.fprintf oc "Definition generated_%s_%s_all (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assert_instances %d generated_assert_%s_local states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.\n" "assert" x.Transhiast_without_inline.name x.module_id x.Transhiast_without_inline.name) tc.assertions;
  List.iter (fun x -> Printf.fprintf oc "Definition generated_%s_%s_all (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assume_instances %d generated_assume_%s_local states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.\n" "assume" x.Transhiast_without_inline.name x.module_id x.Transhiast_without_inline.name) tc.assumes;
  Printf.fprintf oc "Definition generated_all_assumptions (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := %s.\n" fold_assumes;
  List.iteri (fun i x -> Printf.fprintf oc "Lemma generated_assert_%d : forall external_inputs states, generated_circuit_value external_inputs = Some states -> generated_all_assumptions states -> generated_assert_%s_all states.\nAdmitted.\n" i x.Transhiast_without_inline.name) tc.assertions

let emit_file oc (tc : Transhiast_without_inline.translated_circuit) =
  match tc.circuit with
  | H.Fcircuit (v, modules) ->
      output_string oc "From Coq Require Import ZArith.\nFrom mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.\nFrom simplssrlib Require Import Types SsrOrder Var.\nFrom nbits Require Import NBits.\nFrom firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_for_circuit Semantics_with_memory.\n\nLocal Open Scope N_scope.\n\n";
      emit_qcat oc;
      let names = List.mapi (emit_module oc) modules in
      Printf.fprintf oc "Definition generated_modules : seq (@hfmodule VarOrder.T) :=\n  %s.\n\n" (seq (fun x -> x) names);
      Printf.fprintf oc "Definition generated_top := %s.\nDefinition generated_circuit : @hfcircuit VarOrder.T :=\n  (%s generated_top generated_modules).\n" (nat v) (q "Fcircuit");
      emit_verification oc tc
