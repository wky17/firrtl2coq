open Hifirrtl_lang
open Printf
open Extraction
open Big_int_Z

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

module IntPair = struct
  type t = int * int
  let compare = Stdlib.compare
end
 
module IntPairMap = Map.Make(IntPair)

let lookup_id map name context =
  match StringMap.find_opt name map with
  | Some (n :: _) -> n
  | Some [] -> failwith (Printf.sprintf "%s: empty numbering for `%s`" context name)
  | None -> failwith (Printf.sprintf "%s: missing numbering for `%s`" context name)

let rec mapbtyp_helper v (map, flag, flag') ft = (* 这里flag是list，flag'是int *)
  match ft with
  | Ast.Gtyp _ -> (StringMap.add v (flag' :: flag) map, flag' + 1)
  | Ast.Atyp (atyp, _) -> (*mapbtyp_helper (v^"[0]") (StringMap.add v (flag' :: flag) map, flag, flag' + 1) atyp*)
                            mapbtyp_helper v (map, flag, flag') atyp
  | Ast.Btyp btyp -> let map0 = StringMap.add v (flag' :: flag) map in
                     let (map1, _, flag'0) = mapbtyp v (map0, (flag' :: flag), 0) btyp in (map1, flag' + 1)
  and mapbtyp v (map, flag, flag') btyp =
  match btyp with 
  | Ast.Fnil -> (map, flag, flag')
  | Ast.Fflips (fv, _, ft, ff) -> let map0 = StringMap.add (v^"."^fv) (flag' :: flag) map in
                                  let (map1, flag'0) = mapbtyp_helper (v^"."^fv) (map0, flag, flag') ft in
                                  mapbtyp v (map1, flag, flag'0) ff

let rec mapftype v (map, flag) ft = (* 这里flag是int *)
match ft with
| Ast.Gtyp _ -> ((StringMap.add v [flag] map), flag+1)
| Ast.Atyp (atyp, _) -> (*mapftype (v^"[0]") (StringMap.add v [flag] map, flag + 1) atyp*)mapftype v (map, flag) atyp
| Ast.Btyp btyp -> let (map0, _, _) = mapbtyp v (StringMap.add v [flag] map, [flag], 0) btyp in
                   (map0, flag + 1)
  
let mapport (((map, map_i), flag), tmap) p = 
  match p with
  | Ast.Finput (v, ty) -> let (map0, flag0) = mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  | Ast.Foutput (v, ty) -> let (map0, flag0) = mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)

let rec mapstmt (((map, map_i), flag), tmap) stmt = 
  match stmt with
  | Ast.Swire (v, ty) -> let (map0, flag0) = mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  | Ast.Sreg (v, r) -> let (map0, flag0) = mapftype v (map, flag) r.coq_type in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v r.coq_type tmap)
  | Ast.Smem (v, _) -> (((StringMap.add v [flag] map, IntMap.add flag v map_i), flag + 1), tmap)
  | Ast.Snode (v, e) -> (match Nodehelper.type_of_hfexpr e tmap with
                      | Some ty -> let (map0, flag0) = mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
                      | None -> printf "%s wrong expr type\n" v; Ast.pp_expr stdout e; (((map, map_i), flag), tmap))
  | Ast.Sinst (v, _) -> (((StringMap.add v [flag] map, IntMap.add flag v map_i), flag + 1), tmap)
  | Ast.Sinferport (v, r, _) -> (match Nodehelper.type_of_ref r tmap with
                      | Some ty -> let (map0, flag0) = mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
                      | None -> (((map, map_i), flag), tmap))
  | Ast.Swhen (_, s1, s2) -> mapstmts (mapstmts (((map, map_i), flag), tmap) s1) s2
  | _ -> (((map, map_i),flag), tmap)

 and mapstmts (((map, map_i), flag), tmap) stmts = 
  match stmts with
  | Ast.Qnil -> (((map, map_i), flag), tmap)
  | Ast.Qcons (s, ss) -> mapstmts (mapstmt (((map, map_i), flag), tmap) s) ss

let mapmod (((map, map_i), flag), tmap) m =  
  match m with 
  | Ast.FInmod (_, pl, sl) -> let (((map0, map0_i), flag0), tmap0) = List.fold_left mapport (((map, map_i), flag), tmap) pl in
                              mapstmts (((map0, map0_i), flag0),tmap0) sl 
  | _ -> (((map, map_i), flag), tmap)

let mapcir cir = 
  match cir with
  | Ast.Fcircuit (_, ml) -> mapmod (((initmap_s, initmap_i), 0), initmap_s) (Stdlib.List.hd ml)

(*transast*)

let trans_fgtyp ty = 
  match ty with
  | Ast.Fuint s -> Env_with_implicit_widths.Fuint s
  | Ast.Fsint s -> Env_with_implicit_widths.Fsint s
  | Ast.Fuint_implicit s -> Env_with_implicit_widths.Fuint s
  | Ast.Fsint_implicit s -> Env_with_implicit_widths.Fsint s
  | Ast.Fclock -> Env_with_implicit_widths.Fclock
  | Ast.Freset -> Env_with_implicit_widths.Freset
  | Ast.Fasyncreset -> Env_with_implicit_widths.Fasyncreset

let trans_flip f = 
  match f with
  | Ast.Flipped -> HiEnv_with_implicit_widths.Flipped
  | Ast.Nflip -> HiEnv_with_implicit_widths.Nflip

let trans_ucast a_ucast = 
  match a_ucast with
  | Ast.AsUInt -> Firrtl_with_implicit_widths.AsUInt
  | Ast.AsSInt -> Firrtl_with_implicit_widths.AsSInt
  | Ast.AsClock -> Firrtl_with_implicit_widths.AsClock
  | Ast.AsAsync -> Firrtl_with_implicit_widths.AsAsync

let trans_eunop a_eunop = 
  match a_eunop with
  | Ast.Upad s -> Firrtl_with_implicit_widths.Upad s
  | Ast.Ushl s -> Firrtl_with_implicit_widths.Ushl s
  | Ast.Ushr s -> Firrtl_with_implicit_widths.Ushr s
  | Ast.Ucvt -> Firrtl_with_implicit_widths.Ucvt
  | Ast.Uneg -> Firrtl_with_implicit_widths.Uneg
  | Ast.Unot -> Firrtl_with_implicit_widths.Unot
  | Ast.Uandr -> Firrtl_with_implicit_widths.Uandr
  | Ast.Uorr -> Firrtl_with_implicit_widths.Uorr
  | Ast.Uxorr -> Firrtl_with_implicit_widths.Uxorr
  | Ast.Uextr (s1, s2) -> Firrtl_with_implicit_widths.Uextr (s1, s2)
  | Ast.Uhead s -> Firrtl_with_implicit_widths.Uhead s
  | Ast.Utail s -> Firrtl_with_implicit_widths.Utail s

let trans_cmp a_cmp = 
  match a_cmp with
  | Ast.Blt -> Firrtl_with_implicit_widths.Blt
  | Ast.Bleq -> Firrtl_with_implicit_widths.Bleq
  | Ast.Bgt -> Firrtl_with_implicit_widths.Bgt
  | Ast.Bgeq -> Firrtl_with_implicit_widths.Bgeq
  | Ast.Beq -> Firrtl_with_implicit_widths.Beq
  | Ast.Bneq -> Firrtl_with_implicit_widths.Bneq

let trans_ebinop a_ebinop = 
  match a_ebinop with
  | Ast.Badd -> Firrtl_with_implicit_widths.Badd
  | Ast.Bsub -> Firrtl_with_implicit_widths.Bsub
  | Ast.Bmul -> Firrtl_with_implicit_widths.Bmul
  | Ast.Bdiv -> Firrtl_with_implicit_widths.Bdiv
  | Ast.Brem -> Firrtl_with_implicit_widths.Brem
  | Ast.Bcomp s -> Firrtl_with_implicit_widths.Bcomp (trans_cmp s)
  | Ast.Bdshl -> Firrtl_with_implicit_widths.Bdshl
  | Ast.Bdshr -> Firrtl_with_implicit_widths.Bdshr
  | Ast.Band -> Firrtl_with_implicit_widths.Band
  | Ast.Bor -> Firrtl_with_implicit_widths.Bor
  | Ast.Bxor -> Firrtl_with_implicit_widths.Bxor
  | Ast.Bcat -> Firrtl_with_implicit_widths.Bcat

(*let bits_of_z (size : int) (z : Z.t) =
    let binstr =
      if z >= Z.zero then
        Z.format ("%0" ^ (string_of_int size) ^ "b") z
      else
        Z.format ("%0" ^ (string_of_int size) ^ "b")
          (Z.add (Z.pow (Z.of_int 2) size) z) in
    let rec helper i max str res =
      if i >= max then res
      else match String.get str i with
      | '0' -> helper (succ i) max str (false::res)
      | '1' -> helper (succ i) max str (true::res)
      | _ -> assert false in
    helper 0 (String.length binstr) binstr []*)

(* 定义函数，计算二进制表示的长度 *)
let binary_length (signed : bool) (n: Z.t) : int =
  if n = Z.zero then 1  (* 特殊情况：0 的补码表示为 "0"，长度为 1 *)
  else let bits = Z.numbits (Z.abs n) in
    if signed then
      if n > Z.zero then
        bits + 1
      else if (Z.popcount (Z.abs n)) = 1 then bits
        else bits + 1
    else bits

(* NBits stores the least significant bit first. Keep the declared width;
   emitting the most significant bit first reverses every FIRRTL literal. *)
let int_to_bool_list n width =
  List.init width (fun index -> Z.testbit n index)

(* 主函数：将整数转换为指定位长的二进制补码表示，并用 bool list 表示 *)
let bits_of_z (n: Z.t) (bit_length: int) : bool list =
  (* 计算 2^bit_length 的值 *)
  let two_power_bit_length = Z.shift_left Z.one bit_length in
  (* 计算补码表示 *)
  let twos_complement =
    if n >= Z.zero then
      Z.rem n two_power_bit_length
    else
      Z.add two_power_bit_length (Z.rem n two_power_bit_length)
  in
  (* 将补码表示转换为布尔列表 *)
  int_to_bool_list twos_complement bit_length

let rec trans_ftype v ty map = 
  match ty with
  | Ast.Gtyp gt -> HiEnv_with_implicit_widths.Gtyp (trans_fgtyp gt)
  | Ast.Atyp (atyp, n) -> HiEnv_with_implicit_widths.Atyp (trans_ftype v atyp map, n)
  | Ast.Btyp btyp -> HiEnv_with_implicit_widths.Btyp (trans_btyp v btyp map)

and trans_btyp v btyp map =
  match btyp with
  | Ast.Fnil -> HiEnv_with_implicit_widths.Fnil
  | Ast.Fflips (fv, fl, ft, ff) -> (*printf "%s\n" (v^"."^fv);*) HiEnv_with_implicit_widths.Fflips (Obj.magic (Stdlib.List.hd (StringMap.find (v^"."^fv) map)), trans_flip fl, trans_ftype (v^"."^fv) ft map, (trans_btyp v ff map))

let rec find_nat4v ref =
  match ref with
  | Ast.Eid v -> v
  | Ast.Esubfield (ref1, v) -> (find_nat4v ref1)^"."^v
  | Ast.Esubindex (ref1, _) -> (find_nat4v ref1) (*"["^(Stdlib.Int.to_string n)^"]"*)
  | Ast.Esubaccess (ref1, _) -> (find_nat4v ref1)

let rec trans_ref ref map = 
  match ref with
  | Ast.Eid v -> HiFirrtl_with_implicit_widths.Eid (Obj.magic (lookup_id map v "trans_ref"))
  | Ast.Esubfield (r, _) -> HiFirrtl_with_implicit_widths.Esubfield (trans_ref r map, Obj.magic (lookup_id map (find_nat4v ref) "trans_ref field"))
  | Ast.Esubindex (r, n) -> HiFirrtl_with_implicit_widths.Esubindex (trans_ref r map, n)
  | Ast.Esubaccess (r, e) -> HiFirrtl_with_implicit_widths.Esubaccess (trans_ref r map, trans_expr e map)

and trans_expr e map = 
  match e with
  | Ast.Econst (ty, s) -> (match ty with
    | Ast.Fuint_implicit _ -> HiFirrtl_with_implicit_widths.Econst (trans_fgtyp (Ast.Fuint (binary_length false s)), bits_of_z s (binary_length false s))
    | Ast.Fsint_implicit _ -> HiFirrtl_with_implicit_widths.Econst (trans_fgtyp (Ast.Fsint (binary_length true s)), bits_of_z s (binary_length true s))
    | _ -> HiFirrtl_with_implicit_widths.Econst (trans_fgtyp ty, bits_of_z s (Env_with_implicit_widths.sizeof_fgtyp (trans_fgtyp ty))))
  | Ast.Eref v -> HiFirrtl_with_implicit_widths.Eref (trans_ref v map)
  | Ast.Eprim_unop (op, e1) -> HiFirrtl_with_implicit_widths.Eprim_unop(trans_eunop op, trans_expr e1 map)
  | Ast.Eprim_binop (bop, e1, e2) -> HiFirrtl_with_implicit_widths.Eprim_binop(trans_ebinop bop, trans_expr e1 map, trans_expr e2 map)
  | Ast.Emux (e1,e2,e3) -> HiFirrtl_with_implicit_widths.Emux(trans_expr e1 map, trans_expr e2 map, trans_expr e3 map)
  | Ast.Evalidif (e1,e2) -> HiFirrtl_with_implicit_widths.Evalidif(trans_expr e1 map, trans_expr e2 map)
  | Ast.Ecast (s, e) -> HiFirrtl_with_implicit_widths.Ecast(trans_ucast s, trans_expr e map)
  
let trans_ruw r = 
  match r with
  | Ast.Coq_old -> Firrtl_with_implicit_widths.Coq_old
  | Ast.Coq_new -> Firrtl_with_implicit_widths.Coq_new
  | Ast.Coq_undefined -> Firrtl_with_implicit_widths.Coq_undefined

let trans_rst rst map = 
  match rst with
  | Ast.NRst -> HiFirrtl_with_implicit_widths.NRst
  | Ast.Rst (e1, e2) -> HiFirrtl_with_implicit_widths.Rst(trans_expr e1 map, trans_expr e2 map)

let mk_freg t c r = { HiFirrtl_with_implicit_widths.coq_type = t; clock = c; reset = r}

let rec trans_stmt s map res tmap = 
  match s with
  | Ast.Sskip -> HiFirrtl_with_implicit_widths.Qcons (HiFirrtl_with_implicit_widths.Sskip, res)
  | Ast.Swire (v, ty) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl_with_implicit_widths.Swire(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sfcnct (ref, e) -> let ns = HiFirrtl_with_implicit_widths.Sfcnct((trans_ref ref map), trans_expr e map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sinvalid ref -> let ns = HiFirrtl_with_implicit_widths.Sinvalid ((trans_ref ref map)) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Snode (v, e) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl_with_implicit_widths.Snode(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_expr e map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sreg (v, r) -> (*printf "%s\n" v;*) 
                let ns = HiFirrtl_with_implicit_widths.Sreg (Obj.magic (Stdlib.List.hd (StringMap.find v map)), mk_freg (trans_ftype v r.coq_type map) (trans_expr r.clock map) (trans_rst r.reset map)) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  (*| Ast.Sinferport (v, Eid r, e_clock) -> let ty = StringMap.find r tmap in
                               let fv = Obj.magic (Stdlib.List.hd (StringMap.find v map)) in
                               let s1 = HiFirrtl_with_implicit_widths.Sreg (fv, mk_freg (trans_ftype v (Gtyp ty) map) (trans_expr e_clock map) HiFirrtl_with_implicit_widths.NRst) in
                               let s2 = HiFirrtl_with_implicit_widths.Sfcnct(Eid fv, Eref (trans_ref (Eid r) map)) in
                               let s3 = HiFirrtl_with_implicit_widths.Sfcnct(trans_ref (Eid r) map, HiFirrtl_with_implicit_widths.Eref (Eid fv)) in
                    HiFirrtl_with_implicit_widths.Qcons (s3, Qcons (s2, Qcons (s1, res))*)
  | Ast.Swhen (c, s1, s2) -> let ns = HiFirrtl_with_implicit_widths.Swhen (trans_expr c map, trans_stmts s1 map HiFirrtl_with_implicit_widths.Qnil tmap, trans_stmts s2 map HiFirrtl_with_implicit_widths.Qnil tmap) in
                    HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | _ -> res


and trans_stmts ss map res tmap =
  match ss with
  | Ast.Qnil -> res
  | Ast.Qcons (s, st) -> trans_stmts st map (trans_stmt s map res tmap) tmap

let trans_port p map = 
  match p with
  | Ast.Finput (v, ty) -> (*printf "%s\n" v;*) HiFirrtl_with_implicit_widths.Finput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)
  | Ast.Foutput (v, ty) -> (*printf "%s\n" v;*) HiFirrtl_with_implicit_widths.Foutput(Obj.magic (Stdlib.List.hd (StringMap.find v map)), trans_ftype v ty map)

let rec revstmts sts res = 
  match sts with 
  | HiFirrtl_with_implicit_widths.Qnil -> res
  | Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | HiFirrtl_with_implicit_widths.Swhen (c, s1, s2) -> HiFirrtl_with_implicit_widths.Qcons ((HiFirrtl_with_implicit_widths.Swhen (c, revstmts s1 HiFirrtl_with_implicit_widths.Qnil, revstmts s2 HiFirrtl_with_implicit_widths.Qnil)), res)
  | _ -> HiFirrtl_with_implicit_widths.Qcons (st, res)

let trans_mod m map flag tmap = 
  match m with
  | Ast.FInmod (_, pl, sl) -> let newstmts = trans_stmts sl map HiFirrtl_with_implicit_widths.Qnil tmap in
                              HiFirrtl_with_implicit_widths.FInmod(Obj.magic flag, List.map (fun a -> trans_port a map) pl, revstmts newstmts HiFirrtl_with_implicit_widths.Qnil)
  | Ast.FExmod (_, pl, sl) -> let newstmts = trans_stmts sl map HiFirrtl_with_implicit_widths.Qnil tmap in
                              HiFirrtl_with_implicit_widths.FExmod(Obj.magic flag, List.map (fun a -> trans_port a map) pl, revstmts newstmts HiFirrtl_with_implicit_widths.Qnil)

let trans_cir cir map flag tmap = 
  match cir with
  | Ast.Fcircuit (_, ml) -> HiFirrtl_with_implicit_widths.Fcircuit ((Obj.magic flag), (trans_mod (Stdlib.List.hd ml) map (flag + 1) tmap) :: [])

let process_string str suffix =
  let len = String.length str in
  if len >= 4 && String.sub str (len - 4) 4 = ".fir" then
    String.sub str 0 (len - 4) ^ suffix
  else
    str 

let hiparse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

(*let pp_gtyp out ty =
  match ty with
  | Env_with_implicit_widths.Fuint s -> output_string out "(Fuint "; output_string out (Stdlib.Int.to_string s); output_string out ")"
  | Fsint s -> output_string out "(Fsint "; output_string out (Stdlib.Int.to_string s); output_string out ")"
  | Freset -> output_string out "Freset"
  | Fasyncreset -> output_string out "Fasyncreset"
  | Fclock -> output_string out "Fclock"
 
let pp_flip out fl = 
  match fl with
  | HiEnv_with_implicit_widths.Flipped -> output_string out "flip "
  | Nflip -> output_string out ""

let rec pp_ftype out ty = 
  match ty with
  | HiEnv_with_implicit_widths.Gtyp gt -> output_string out "(Gtyp "; pp_gtyp out gt; output_string out ")"
  | Atyp (atyp, n) -> output_string out "(Atyp "; pp_ftype out atyp; output_string out ("["^(Stdlib.Int.to_string n)^"]")
  | Btyp btyp -> output_string out "({"; pp_fbtyp out btyp; output_string out "})";
 
and pp_fbtyp out ty = 
  match ty with
  | Fnil -> output_string out "Fnil"
  | Fflips (v, fl, ft, ff) -> pp_flip out fl; output_string out ((Stdlib.Int.to_string v)^" : "); pp_ftype out ft; output_string out "; "; pp_fbtyp out ff; output_string out ")"

let rec pp_expr out e =
 match e with
 | HiFirrtl_with_implicit_widths.Econst (ty, s) -> output_string out "(econst "; pp_gtyp out ty; output_string out " [::b?])"
 | Eref v -> output_string out "(eref "; pp_ref out v; output_string out ")"
 | Eprim_unop (op, e1) -> output_string out "(eprim_unop ?"; pp_expr out e1; output_string out ")"
 | Eprim_binop (bop, e1, e2) -> output_string out "(eprim_binop ?"; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
 | Emux (e1,e2,e3)  -> output_string out "(emux "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out " "; pp_expr out e3; output_string out " "; output_string out ")"
 (*| Evalidif (e1,e2)  -> output_string out "(evalidif "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"*)
 | Ecast (s, e) -> output_string out "(ecast ?"; output_string out " "; pp_expr out e; output_string out ")";

and pp_ref out ref = 
 match ref with
 | Eid v -> output_string out (Stdlib.Int.to_string v)
 | Esubfield (ref1, v) -> pp_ref out ref1; output_string out "."; output_string out (Stdlib.Int.to_string v)
 | Esubindex (ref1, n) -> pp_ref out ref1; output_string out "["; output_string out ((Stdlib.Int.to_string n)^"]")
 | Esubaccess (ref1, e) -> pp_ref out ref1; output_string out "."; pp_expr out e

let rec pp_stmts out sl = 
  match sl with
  | HiFirrtl_with_implicit_widths.Qnil -> output_string out ""
  | Qcons (s, ss) -> pp_stmt out s; pp_stmts out ss
                             
and pp_stmt out s =
  match s with
  | Sskip -> output_string out "sskip\n"
  | Swire (v, ty) -> output_string out "swire "; output_string out ((Stdlib.Int.to_string v)^" : "); pp_ftype out ty; output_string out "\n"
  | Smem (v, m) -> output_string out "smem\n"
  | Sfcnct (e1, e2) -> pp_ref out e1; output_string out " <= "; pp_expr out e2; output_string out "\n"
  | Sinvalid v -> output_string out "sinvalid\n"
  | Sreg (v, r) -> output_string out "sreg \n" ; output_string out ((Stdlib.Int.to_string v)^" : ")
  | Snode (v, e) -> output_string out "snode\n"
  | Sinst (v, e) -> output_string out "sinst\n"
  | Swhen (c, s1, s2) -> output_string out "swhen cond :"; output_string out "\nthen [::"; pp_stmts out s1; output_string out "]\nelse \n [::"; pp_stmts out s2; output_string out "])\n"

let pp_fmodule out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "(FInmod "; output_string out ((Stdlib.Int.to_string v)^"\n"); pp_fports out pl; output_string out "[:: "; pp_stmts out sl; output_string out "]).\n"
  | FExmod (v, pl, sl) -> output_string out "(FExmod "; output_string out ((Stdlib.Int.to_string v)^"\n"); pp_fports out pl; output_string out "[:: "; pp_stmts out sl; output_string out "]).\n"
          
let pp_fmodules out fmod = List.iter (fun c -> pp_fmodule out c) fmod

let pp_fircircuit out fc =
  match fc with
  | Fcircuit (v, fmod) -> output_string out "(FCircuit "; output_string out ((Stdlib.Int.to_string v)^"\n"); pp_fmodules out fmod; output_string out ")\n"
*)
