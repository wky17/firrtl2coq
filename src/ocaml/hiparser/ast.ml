type var = string

type fgtyp =
| Fuint of int
| Fsint of int
| Fuint_implicit of int
| Fsint_implicit of int
| Fclock
| Freset
| Fasyncreset

type fflip =
| Flipped
| Nflip

type ftype =
| Gtyp of fgtyp
| Atyp of ftype * int
| Btyp of ffield
and ffield =
| Fnil
| Fflips of var * fflip * ftype * ffield

type ucast =
| AsUInt
| AsSInt
| AsClock
| AsAsync

type eunop =
| Upad of int
| Ushl of int
| Ushr of int
| Ucvt
| Uneg
| Unot
| Uandr
| Uorr
| Uxorr
| Uextr of int * int
| Uhead of int
| Utail of int

type bcmp =
| Blt
| Bleq
| Bgt
| Bgeq
| Beq
| Bneq

type ebinop =
| Badd
| Bsub
| Bmul
| Bdiv
| Brem
| Bcomp of bcmp
| Bdshl
| Bdshr
| Band
| Bor
| Bxor
| Bcat

type hfexpr =
| Econst of fgtyp * Z.t
| Ecast of ucast * hfexpr
| Eprim_unop of eunop * hfexpr
| Eprim_binop of ebinop * hfexpr * hfexpr
| Emux of hfexpr * hfexpr * hfexpr
(*| Evalidif of hfexpr * hfexpr*)
| Eref of href
and href =
| Eid of var
| Esubfield of href * var
| Esubindex of href * int
| Esubaccess of href * hfexpr

type mem_port = { id : var; addr : var;
                  en : var; clk : var;
                  mask : var }

type ruw =
| Coq_old
| Coq_new
| Coq_undefined

type hfmem = { data_type : ftype; depth : int; reader : mem_port list;
               writer : mem_port list; read_latency : int;
               write_latency : int; read_write : ruw }

type rst =
| NRst
| Rst of hfexpr * hfexpr

type hfreg = { coq_type : ftype; clock : hfexpr; reset : rst }

let mk_freg t c e1 e2 = { coq_type = t; clock = c; reset = Rst(e1,e2) }
let mk_freg_non t c = { coq_type = t; clock = c; reset = NRst}
let mk_fmem e z1 z2 z3 vl1 vl2 r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl1; writer = vl2; read_write = r }
let mk_fmem_non e z1 z2 z3 r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = []; writer = []; read_write = r }
let mk_fmem_r e z1 z2 z3 vl r = { data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl; writer = []; read_write = r }

type hfstmt =
| Sskip
| Swire of var * ftype
| Sreg of var * hfreg
| Smem of var * hfmem
| Sinst of var * var
| Snode of var * hfexpr
| Sfcnct of href * hfexpr
| Sinvalid of href
| Sinferport of var * href * hfexpr
| Swhen of hfexpr * hfstmt_seq * hfstmt_seq
and hfstmt_seq =
| Qnil
| Qcons of hfstmt * hfstmt_seq

let rec qcat s1 s2 =
  match s1 with
  | Qnil -> s2
  | Qcons (h1, tl1) -> Qcons (h1, (qcat tl1 s2))

type hfport =
| Finput of var * ftype
| Foutput of var * ftype

type hfmodule =
| FInmod of var * hfport list * hfstmt_seq
| FExmod of var * hfport list * hfstmt_seq

type hfcircuit =
| Fcircuit of var * hfmodule list

type file = hfcircuit

(** pretty printer **)

let pp_gtyp out ty =
 match ty with
 | Fuint s -> output_string out "(Fuint "; output_string out (Int.to_string s); output_string out ")"
 | Fsint s -> output_string out "(Fsint "; output_string out (Int.to_string s); output_string out ")"
 | Fuint_implicit s -> output_string out "Fuint_implicit"
 | Fsint_implicit s -> output_string out "Fsint_implicit"
 | Freset -> output_string out "Freset"
 | Fasyncreset -> output_string out "Fasyncreset"
 | Fclock -> output_string out "Fclock"

let pp_flip out fl = 
  match fl with
  | Flipped -> output_string out "flip "
  | Nflip -> output_string out ""

let rec pp_type out ty = 
  match ty with
  | Gtyp gt -> output_string out "(Gtyp "; pp_gtyp out gt; output_string out ")"
  | Atyp (atyp, n) -> output_string out "(Atyp "; pp_type out atyp; output_string out ("["^(Int.to_string n)^"]")
  | Btyp btyp -> output_string out "({"; pp_btyp out btyp; output_string out "})";

and pp_btyp out ty = 
  match ty with
  | Fnil -> output_string out "Fnil"
  | Fflips (v, fl, ft, ff) -> pp_flip out fl; output_string out (v^" : "); pp_type out ft; output_string out "; "; pp_btyp out ff; output_string out ")"

let pp_cast out cst = 
 match cst with
 | AsUInt -> output_string out "AsUInt"
 | AsSInt -> output_string out "AsSInt"
 | AsClock -> output_string out "AsUint "
 | AsAsync ->  output_string out "AsAsync"
 
let pp_unop out op =
 match op with
 | Upad s -> output_string out "(Upad "; output_string out (Int.to_string s); output_string out ")" 
 | Ushl s -> output_string out "(Ushl "; output_string out (Int.to_string s); output_string out")"
 | Ushr s -> output_string out "(Ushr "; output_string out (Int.to_string s); output_string out")"
 | Ucvt -> output_string out "Ucvt"
 | Uneg -> output_string out "Uneg"
 | Unot -> output_string out "Unot "
 | Uandr -> output_string out "Uandr"
 | Uorr -> output_string out "Uorr"
 | Uxorr -> output_string out "Uxorr"
 | Uextr (s1, s2) -> output_string out "(Uextr "; output_string out (Int.to_string s1);  output_string out " "; output_string out (Int.to_string s2); output_string out")"
 | Uhead s -> output_string out "(Uhead "; output_string out (Int.to_string s); output_string out")"
 | Utail s -> output_string out "(Utail "; output_string out (Int.to_string s); output_string out")"
 (*| Ubits (s1,s2)  -> output_string out "(Ubits "; output_string out (Int.to_string s1); output_string out " "; output_string out (Int.to_string s2); output_string out")"
 | Uincp -> output_string out "Uincp"
 | Udecp -> output_string out "Udecp"
 | Usetp -> output_string out "Usetp"
 | _ -> output_string out "" *)

let pp_comp out cmp = 
 match cmp with
 | Blt -> output_string out "Blt" 
 | Bleq -> output_string out "Bleq"
 | Bgt -> output_string out "Bgt"
 | Bgeq -> output_string out "Bgeq"
 | Beq -> output_string out "Beq"
 | Bneq -> output_string out "Bneq"
      
let pp_binop out op =
 match op with
 | Badd -> output_string out "Badd "
 | Bsub -> output_string out "Bsub "
 | Bmul -> output_string out "Bmul"
 | Bdiv -> output_string out "Bdiv"
 | Brem -> output_string out "Brem"
 | Bcomp s -> output_string out "Bcomp("; pp_comp out s; output_string out")"
 | Bdshl -> output_string out "Bdshl "
 | Bdshr -> output_string out "Bdshr "
 | Band -> output_string out "Band "
 | Bor -> output_string out "Bor "
 | Bxor -> output_string out "Bxor "
 | Bcat -> output_string out "Bcat "
 (*| Bsdiv -> output_string out "Bsdiv "
 | Bsrem -> output_string out "Bsrem "
 | _ -> output_string out "" *)
         
let rec pp_expr out e =
 match e with
 | Econst (ty, s) -> output_string out "(econst "; pp_gtyp out ty; output_string out " [::b"; output_string out (Z.format "%b" s) ; output_string out"])"
 | Eref v -> output_string out "(eref "; pp_ref out v; output_string out ")"
 | Eprim_unop (op, e1) -> output_string out "(eprim_unop "; pp_unop out op; pp_expr out e1; output_string out ")"
 | Eprim_binop (bop, e1, e2) -> output_string out "(eprim_binop "; pp_binop out bop; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
 | Emux (e1,e2,e3)  -> output_string out "(emux "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out " "; pp_expr out e3; output_string out " "; output_string out ")"
 (*| Evalidif (e1,e2)  -> output_string out "(evalidif "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"*)
 | Ecast (s, e) -> output_string out "(ecast "; pp_cast out s; output_string out " "; pp_expr out e; output_string out ")";

and pp_ref out ref = 
 match ref with
 | Eid v -> output_string out "(eid "; output_string out v; output_string out ")"
 | Esubfield (ref1, v) -> pp_ref out ref1; output_string out "."; output_string out v
 | Esubindex (ref1, n) -> pp_ref out ref1; output_string out "["; output_string out ((Int.to_string n)^"]")
 | Esubaccess (ref1, e) -> pp_ref out ref1; output_string out "."; pp_expr out e

 let pp_ruw out e = 
 match e with
 | Coq_old -> output_string out "old"
 | Coq_new -> output_string out "new"
 | Coq_undefined -> output_string out "undefined"

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl = output_string out "[::"; List.iter (fun c -> pp_port out c; output_string out "") pl;  output_string out "]\n";
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "(Finput "; output_string out (v^" : "); pp_type out ty; output_string out ")\n"
  | Foutput (v, ty) -> output_string out "(Foutput "; output_string out (v^" : "); pp_type out ty; output_string out ")\n"                 
                       
let rec pp_statements out sl = 
  match sl with
  | Qnil -> output_string out "Fnil"
  | Qcons (s, ss) -> pp_statement out s; pp_statements out ss
                             
and pp_statement out s =
  match s with
  | Sskip -> output_string out "sskip\n"
  | Swire (v, ty) -> output_string out "(swire "; output_string out (v^" : "); pp_type out ty; output_string out ")\n"
  | Smem (v, m) -> output_string out "smem ( "; output_string out (v^" : "); (*pp_type out (m.data_type); output_string out "Depth ";
   output_string out (Int.to_string m.depth); output_string out " ReadL "; output_string out (Int.to_string m.read_latency); output_string out " WriteL "; 
   output_string out (Int.to_string m.write_latency); output_string out "  Reader "; List.iter (fun c ->  output_string out (c^" "); output_string out "") m.reader; 
   output_string out " Writer "; List.iter (fun c ->  output_string out (c^" "); output_string out "") m.writer; output_string out " "; output_string out " RuW "; 
   pp_ruw out (m.read_write);*) output_string out ")\n"
  | Sfcnct (e1, e2) -> output_string out "(sfcnct "; pp_ref out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Sinvalid v -> output_string out "(sinvalid "; pp_ref out v; output_string out ")\n"
  | Sreg (v, r) ->
     (match r.reset with
     | NRst -> output_string out "sreg ( "; output_string out (v^" : "); pp_type out (r.coq_type); output_string out " "; pp_expr out r.clock; output_string out " NRst)\n"
     | Rst (e1, e2) ->
        output_string out "sreg ( "; output_string out (v^" : "); pp_type out (r.coq_type); output_string out " "; pp_expr out r.clock; output_string out " (rrst "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out "))\n")
  | Snode (v, e) -> output_string out "(snode "; output_string out (v^" : "); pp_expr out e; output_string out ")\n"
  | Sinst (v, e) -> output_string out "(sinst "; output_string out (v^" "); output_string out "of "; output_string out e; output_string out ")\n"
  | Swhen (c, s1, s2) -> output_string out "(swhen "; pp_expr out c; output_string out "\nthen [::"; pp_statements out s1; output_string out "]\nelse \n [::"; pp_statements out s2; output_string out "])\n"
  | Sinferport _ -> output_string out "inferport\n"
          
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "(FInmod "; output_string out (v^"\n"); pp_ports out pl; output_string out "[:: "; pp_statements out sl; output_string out "]).\n"
  | FExmod (v, pl, sl) -> output_string out "(FExmod "; output_string out (v^"\n"); pp_ports out pl; output_string out "[:: "; pp_statements out sl; output_string out "]).\n"
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | Fcircuit (v, fmod) -> output_string out "(FCircuit "; output_string out (v^"\n"); pp_modules out fmod; output_string out ")\n"

let pp_file out fc = pp_fcircuit out fc

let rec size_of_ftype = function
| Gtyp _ -> Stdlib.Int.succ 0
| Atyp (t0, n) -> (size_of_ftype t0) * n
| Btyp b -> size_of_fields b

(** val size_of_fields : ffield -> int **)

and size_of_fields = function
| Fnil -> 0
| Fflips (_, _, t0, fs) -> (size_of_ftype t0) + (size_of_fields fs)
