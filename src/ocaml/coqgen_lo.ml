open Hifirrtl_lang
open Ast
let seq xs = "[:: " ^ String.concat "; " xs ^ "]"
let ctor n xs = "(@" ^ n ^ " VarOrder.T " ^ String.concat " " xs ^ ")"
let ground = function
 | Gtyp (Fuint w) when w > 0 -> Printf.sprintf "(Fuint %d)" w
 | Gtyp (Fsint w) when w > 0 -> Printf.sprintf "(Fsint %d)" w
 | Gtyp Fclock -> "Fclock" | Gtyp Fasyncreset -> "Fasyncreset"
 | _ -> failwith "low FIRRTL requires explicit ground types"
let rec path = function Eid x -> x | Esubfield(r,f) -> path r ^ "." ^ f
 | _ -> failwith "array reference is not low FIRRTL"
let emit_file oc (Fcircuit(top,mods)) =
 let verification = ref [] in
 let ids = Hashtbl.create 100 in
 let id s = match Hashtbl.find_opt ids s with Some n -> "(N.of_nat " ^ string_of_int n ^ ")"
   | None -> let n=Hashtbl.length ids in Hashtbl.add ids s n; "(N.of_nat " ^ string_of_int n ^ ")" in
 let modname = function FInmod(n,_,_) | FExmod(n,_,_) -> n in
 List.iter (fun m -> ignore(id ("module:"^modname m))) mods;
 let module_defs = List.mapi (fun idx m ->
 let name,ports,body,kind = match m with FInmod(n,p,s)->n,p,s,"FInmod" | FExmod(n,p,s)->n,p,s,"FExmod" in
 let local s = id (name ^ ":" ^ s) in
 let refid r = local(path r) in
 let rec expr = function
 | Eref r -> ctor "Eref" [refid r]
 | Econst(t,z) -> let ty=ground(Gtyp t) in let w= match t with Fuint w|Fsint w->w|_->failwith "noninteger literal" in
   ctor "Econst" [ty;seq(List.init w (fun i -> if Z.testbit z i then "true" else "false"))]
 | Ecast(o,e) -> ctor "Ecast" [(match o with AsUInt->"AsUInt"|AsSInt->"AsSInt"|AsClock->"AsClock"|AsAsync->"AsAsync");expr e]
 | Eprim_unop(o,e) -> ctor "Eprim_unop" [Coqgen.pp_unop (Transhiast.trans_eunop o);expr e]
 | Eprim_binop(o,a,b) -> ctor "Eprim_binop" [Coqgen.pp_binop (Transhiast.trans_ebinop o);expr a;expr b]
 | Emux(c,a,b)->ctor "Emux" [expr c;expr a;expr b]
 | Evalidif(c,e)->ctor "Evalidif" [expr c;expr e] in
 let port prefix = function Finput(v,t)->ctor "Finput" [local(prefix^v);ground t] | Foutput(v,t)->ctor "Foutput" [local(prefix^v);ground t] in
 let rec stmts = function Qnil->[] | Qcons(s,tl)->stmt s @ stmts tl
 and stmt = function
 | Sskip -> ["(@Sskip VarOrder.T)"]
 | Swire(v,t)->[ctor "Swire" [local v;ground t]]
 | Snode(v,e)->[ctor "Snode" [local v;expr e]]
 | Sfcnct(r,e)->[ctor "Sfcnct" [refid r;expr e]]
 | Sinvalid r->[ctor "Sinvalid" [refid r]]
 | Sreg(v,r)->let clk=match r.clock with Eref r->refid r|_->failwith "register clock must be reference" in
   let rst=match r.reset with NRst->"(@NRst VarOrder.T)"|Rst(a,b)->ctor "Rst" [expr a;expr b] in
   [ctor "Sreg" [ctor "mk_freg" [local v;ground r.coq_type;clk;rst]]]
 | Smem(v,m)->let field p f=local(v^"."^p^"."^f) in
   let rd p=ctor "mk_freader_port" (List.map (field p) ["addr";"data";"en";"clk"]) in
   let wr p=ctor "mk_fwriter_port" (List.map (field p) ["addr";"data";"en";"clk";"mask"]) in
   [ctor "Smem" [ctor "mk_fmem" [local v;ground m.data_type;string_of_int m.depth;seq(List.map rd m.reader);seq(List.map wr m.writer);string_of_int m.read_latency;string_of_int m.write_latency;(match m.read_write with Coq_old->"old"|Coq_new->"new"|Coq_undefined->"undefined")]]]
 | Sinst(v,m)->let target=List.find (fun x->modname x=m) mods in
   let ps=match target with FInmod(_,p,_)|FExmod(_,p,_)->p in
   [ctor "Sinst" [ctor "mk_finst" [local v;id("module:"^m);seq(List.map (port (v^".")) ps)]]]
 | Sassert(_,property,enable,label) ->
   verification := ("assert",id("module:"^name),label,expr enable,expr property) :: !verification; []
 | Sassume(_,property,enable,label) ->
   verification := ("assume",id("module:"^name),label,expr enable,expr property) :: !verification; []
 | Swhen _ -> failwith "when is not supported in low input"
 | Sinferport _ -> failwith "inferred memory port is not low FIRRTL" in
 (* Render statements first, preserving the existing identifier allocation
    order; emit ports first for readability. *)
 let statements = stmts body in
 let port_terms = List.map (port "") ports in
 let base = Printf.sprintf "lo_module_%d" idx in
 let definitions suffix typ terms =
   let names = List.mapi (fun i _ -> Printf.sprintf "%s_%s_%d" base suffix i) terms in
   let lines = List.map2 (fun n term ->
     Printf.sprintf "Definition %s : %s VarOrder.T := %s.\n" n typ term) names terms in
   (String.concat "" lines, names)
 in
 let port_defs, port_names = definitions "port" "fport" port_terms in
 let stmt_defs, stmt_names = definitions "stmt" "fstmt" statements in
 port_defs ^
 Printf.sprintf "Definition %s_ports : seq (fport VarOrder.T) := %s.\n\n" base (seq port_names) ^
 stmt_defs ^
 Printf.sprintf "Definition %s_stmts : seq (fstmt VarOrder.T) := %s.\n\n" base (seq stmt_names) ^
 Printf.sprintf "Definition %s : fmodule VarOrder.T := %s.\n\n" base
   (ctor kind [id("module:"^name); base ^ "_ports"; base ^ "_stmts"])) mods in
 output_string oc "From Coq Require Import ZArith.\nFrom mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.\nFrom simplssrlib Require Import Var.\nFrom firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths LoCircuit LoVerification.\n";
 List.iter (output_string oc) module_defs;
 Printf.fprintf oc "Definition generated_lo_circuit : fcircuit VarOrder.T := %s.\n" (ctor "Fcircuit" [id("module:"^top);seq(List.mapi(fun i _->"lo_module_"^string_of_int i) mods)])
;
 List.iteri (fun i (kind,mid,_label,en,prop) ->
   Printf.fprintf oc "Definition lo_%s_%d_module : VarOrder.T := %s.\nDefinition lo_%s_%d_enable : fexpr VarOrder.T := %s.\nDefinition lo_%s_%d_predicate : fexpr VarOrder.T := %s.\n" kind i mid kind i en kind i prop)
   (List.rev !verification);
 let props = List.mapi (fun i (kind,mid,label,_,_) ->
   let escaped = String.concat "_" (String.split_on_char ' ' label) in
   let safe = String.map (fun c -> match c with 'a'..'z'|'A'..'Z'|'0'..'9'|'_' -> c | _ -> '_') escaped in
   let n = Printf.sprintf "lo_%s_%s_%d" kind safe i in
   Printf.fprintf oc "Definition %s (states : LoCircuit.circuit_state) : Prop := LoVerification.all_instances generated_lo_circuit %s lo_%s_%d_enable lo_%s_%d_predicate states.\n" n mid kind i kind i;
   kind,n) (List.rev !verification) in
 let assumes = List.filter_map (fun (kind,n) -> if kind="assume" then Some(n ^ " states") else None) props in
 Printf.fprintf oc "Definition lo_all_assumptions (states : LoCircuit.circuit_state) : Prop := %s.\n"
   (match assumes with []->"True" | _ -> String.concat " /\\ " assumes);
 output_string oc "Definition generated_lo_run := LoCircuit.run_circuit generated_lo_circuit.\n";
 output_string oc "Definition lo_assumptions_along inputs : Prop := LoVerification.assumptions_along generated_lo_circuit inputs lo_all_assumptions.\n";
 List.iter (fun (kind,n) -> if kind="assert" then
   Printf.fprintf oc "Lemma %s_valid : forall inputs result, generated_lo_run inputs = Some result -> lo_assumptions_along inputs -> %s (LoCircuit.final_state result).\nAdmitted.\n" n n) props
