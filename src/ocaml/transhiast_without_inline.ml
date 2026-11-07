open Hifirrtl_lang
open Printf
open Nodehelper
open Extraction
open Big_int_Z

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
module IntMap = Map.Make(Stdlib.Int)
let initmap_i = IntMap.empty

let rec pl2btyp pl = 
  match pl with
  | [] -> Ast.Fnil
  | (Ast.Finput (v, ty)) :: tl -> Ast.Fflips (v, Ast.Nflip, ty, pl2btyp tl)
  | (Ast.Foutput (v, ty)) :: tl -> Ast.Fflips (v, Ast.Flipped, ty, pl2btyp tl)

let rec mapstmt modplmap (((map, map_i), flag), tmap) stmt = 
  match stmt with
  | Ast.Swire (v, ty) -> let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
                        (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  | Ast.Sreg (v, r) -> let (map0, flag0) = Transhiast.mapftype v (map, flag) r.coq_type in 
                        (((map0, IntMap.add flag v map_i), flag0), StringMap.add v r.coq_type tmap)
  | Ast.Smem (v, m) ->
      let addr_width depth =
        let rec loop w p = if p >= depth then max 1 w else loop (w + 1) (p * 2) in
        loop 0 1
      in
      let addr_ty = Ast.Gtyp (Ast.Fuint (addr_width m.depth)) in
      let field_types = ["addr", addr_ty; "en", Ast.Gtyp (Ast.Fuint 1);
                         "clk", Ast.Gtyp Ast.Fclock; "mask", Ast.Gtyp (Ast.Fuint 1);
                         "data", m.data_type] in
      let rec fields = function
        | [] -> Ast.Fnil
        | (n, ty) :: tl -> Ast.Fflips (n, Ast.Nflip, ty, fields tl)
      in
      let port_type = Ast.Btyp (fields field_types) in
      let ports = List.sort_uniq String.compare (m.reader @ m.writer) in
      let mem_type = Ast.Btyp (fields (List.map (fun p -> (p, port_type)) ports)) in
      let (map0, flag0) = Transhiast.mapftype v (map, flag) mem_type in
      let tmap0 = StringMap.add v mem_type tmap in
      let add_port_number (mp, fi, vi) port =
        let paths = port :: List.map (fun (f, _) -> port ^ "." ^ f) field_types in
        List.fold_left (fun (mp, fi, vi) name ->
          let full = v ^ "." ^ name in
          if StringMap.mem full mp then (mp, fi, vi)
          else (StringMap.add full [fi] mp, fi + 1, IntMap.add fi full vi))
          (mp, fi, vi) paths
      in
      let st0 = (map0, flag0, map_i) in
      let st1 = List.fold_left add_port_number st0 ports in
      let (map1, flag1, map_i1) = st1 in
      (((map1, map_i1), flag1), tmap0)
  | Ast.Snode (v, e) -> (match Nodehelper.type_of_hfexpr e tmap with
                      | Some ty -> let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
                          (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
                      | None -> printf "%s wrong expr type\n" v; Ast.pp_expr stdout e; (((map, map_i), flag), tmap))
  | Ast.Sinst (v, mv) -> let pl = StringMap.find mv modplmap in
    let ty = Ast.Btyp (pl2btyp pl) in 
    let (map0, flag0) = Transhiast.mapftype v (map, flag) ty in 
    (((map0, IntMap.add flag v map_i), flag0), StringMap.add v ty tmap)
  (*| Ast.Sinferport (v, r, _) -> (match type_of_ref r tmap with
                      | Some ty -> (mapftype v (map, flag) ty, StringMap.add v ty tmap)
                      | None -> ((map, flag), tmap)*)
  | Ast.Swhen (_, s1, s2) -> mapstmts modplmap (mapstmts modplmap (((map, map_i), flag), tmap) s1) s2
  | _ -> (((map, map_i), flag), tmap)

and mapstmts modplmap (((map, map_i), flag), tmap) stmts = 
  match stmts with
  | Ast.Qnil -> (((map, map_i), flag), tmap)
  | Ast.Qcons (s, ss) -> mapstmts modplmap (mapstmt modplmap (((map, map_i), flag), tmap) s) ss

let mapmod m modplmap =  
  match m with 
  | Ast.FInmod (mv, pl, sl) -> 
    let (((map0, map0_i), flag0), tmap0) = List.fold_left Transhiast.mapport (((initmap_s, initmap_i), 0), initmap_s) pl in
    let (((map1, map1_i), _), tmap1) = mapstmts modplmap (((map0, map0_i), flag0), tmap0) sl in (((mv, map1), map1_i), tmap1)
  | FExmod (mv, _, _) -> (((mv, initmap_s), initmap_i), initmap_s)

let rec mapmodl ((modmap, flag), map) modplmap ml =
  match ml with
  | [] -> ((modmap, flag), map)
  | hd :: tl -> let (((hd_v, hd_map), hd_map_i), hd_tmap) = mapmod hd modplmap in
    mapmodl (((StringMap.add hd_v flag modmap), flag + 1), StringMap.add hd_v ((hd_map, hd_map_i), hd_tmap) map) modplmap tl

let mapcir cir = 
  match cir with
  | Ast.Fcircuit (_, ml) -> let modplmap = List.fold_left (fun acc m -> 
      match m with
      | Ast.FInmod (mv, pl, _) -> StringMap.add mv pl acc
      | FExmod (mv, pl, _) -> StringMap.add mv pl acc) initmap_s ml in
    mapmodl ((initmap_s, 0), initmap_s) modplmap ml 
  (* 第一个是 module name string -> module name num, 第二个是 当前对module的标号, 
     第三个是 module name string -> (module内变量名 string 含subfield -> num list, num -> string, string -> ftype)) *)

(* transast *)

let rec trans_stmt s map res tmap modmap = 
  match s with
  | Ast.Sskip -> HiFirrtl_with_implicit_widths.Qcons (HiFirrtl_with_implicit_widths.Sskip, res)
  | Ast.Swire (v, ty) -> 
                let ns = HiFirrtl_with_implicit_widths.Swire(Obj.magic (Stdlib.List.hd (StringMap.find v map)), Transhiast.trans_ftype v ty map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sfcnct (ref, e) -> 
                let new_ref = Transhiast.trans_ref ref map in 
                let ns = HiFirrtl_with_implicit_widths.Sfcnct((Transhiast.trans_ref ref map), Transhiast.trans_expr e map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sinvalid ref -> 
                let ns = HiFirrtl_with_implicit_widths.Sinvalid ((Transhiast.trans_ref ref map)) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Snode (v, e) -> 
                let ns = HiFirrtl_with_implicit_widths.Snode(Obj.magic (Stdlib.List.hd (StringMap.find v map)), Transhiast.trans_expr e map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sreg (v, r) -> 
                let ns = HiFirrtl_with_implicit_widths.Sreg (Obj.magic (Stdlib.List.hd (StringMap.find v map)), 
                    Transhiast.mk_freg (Transhiast.trans_ftype v r.coq_type map) (Transhiast.trans_expr r.clock map) (Transhiast.trans_rst r.reset map)) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  (*| Ast.Sinferport (v, r, e_clock) -> (match type_of_ref r tmap with
                  | Some ty -> let fv = Obj.magic (Stdlib.List.hd (StringMap.find v map)) in
                               let s1 = HiFirrtl_with_implicit_widths.Sreg (fv, Transhiast.mk_freg (Transhiast.trans_ftype v ty map) (Transhiast.trans_expr e_clock map) HiFirrtl_with_implicit_widths.NRst) in
                               let s2 = HiFirrtl_with_implicit_widths.Sfcnct(Eid fv, Eref (Transhiast.trans_ref r map)) in
                               let s3 = HiFirrtl_with_implicit_widths.Sfcnct(Transhiast.trans_ref r map, HiFirrtl_with_implicit_widths.Eref (Eid fv)) in
                    HiFirrtl_with_implicit_widths.Qcons (s3, Qcons (s2, Qcons (s1, res)))
                  | None -> res*)
  | Ast.Smem (v, m) ->
                let ns = HiFirrtl_with_implicit_widths.Smem
                  (Obj.magic (Stdlib.List.hd (StringMap.find v map)),
                   trans_hfmem v m map) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sinst (v, modv) -> 
                let ns = HiFirrtl_with_implicit_widths.Sinst (Obj.magic (Stdlib.List.hd (StringMap.find v map)), Obj.magic (StringMap.find modv modmap)) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)
  | Ast.Sassert _ -> res
  | Ast.Sassume _ -> res
  | Ast.Swhen (c, s1, s2) -> let ns = HiFirrtl_with_implicit_widths.Swhen (Transhiast.trans_expr c map, trans_stmts s1 map HiFirrtl_with_implicit_widths.Qnil tmap modmap, trans_stmts s2 map HiFirrtl_with_implicit_widths.Qnil tmap modmap) in
                HiFirrtl_with_implicit_widths.Qcons (ns, res)


and trans_stmts ss map res tmap modmap =
  match ss with
  | Ast.Qnil -> res
  | Ast.Qcons (s, st) -> trans_stmts st map (trans_stmt s map res tmap modmap) tmap modmap

and trans_mem_port map name =
  let key = name in
  let id = Obj.magic (Stdlib.List.hd (StringMap.find key map)) in
  let field f = Obj.magic (Stdlib.List.hd (StringMap.find (key ^ "." ^ f) map) : int) in
  { HiFirrtl_with_implicit_widths.id = id; addr = field "addr"; en = field "en";
    clk = field "clk"; mask = field "mask" }

and trans_hfmem v m map =
  { HiFirrtl_with_implicit_widths.data_type = Transhiast.trans_ftype v m.data_type map;
    depth = m.depth;
    reader = List.map (fun p -> trans_mem_port map (v ^ "." ^ p)) m.reader;
    writer = List.map (fun p -> trans_mem_port map (v ^ "." ^ p)) m.writer;
    read_latency = m.read_latency;
    write_latency = m.write_latency;
    read_write = Transhiast.trans_ruw m.read_write }


type assertion_metadata = { module_id : int; name : string; enable : HiFirrtl_with_implicit_widths.hfexpr; predicate : HiFirrtl_with_implicit_widths.hfexpr }
type assume_metadata = assertion_metadata
type translated_circuit = { circuit : HiFirrtl_with_implicit_widths.hfcircuit; assertions : assertion_metadata list; assumes : assume_metadata list }

let rec collect_verification module_id map = function
  | Ast.Qnil -> ([], [])
  | Ast.Qcons (stmt, rest) ->
      let a0, u0 = match stmt with
        | Ast.Sassert (clock, enable, predicate, name) ->
            ([{module_id; name; enable=Transhiast.trans_expr enable map; predicate=Transhiast.trans_expr predicate map}], [])
        | Ast.Sassume (clock, enable, predicate, name) ->
            ([], [{module_id; name; enable=Transhiast.trans_expr enable map; predicate=Transhiast.trans_expr predicate map}])
        | Ast.Swhen (_, yes, no) ->
            let a1,u1 = collect_verification module_id map yes in
            let a2,u2 = collect_verification module_id map no in (a1 @ a2, u1 @ u2)
        | _ -> ([], [])
      in
      let ar, ur = collect_verification module_id map rest in (a0 @ ar, u0 @ ur)

let trans_mod m modmap map = 
  match m with
  | Ast.FInmod (mv, pl, sl) -> 
    let flag = StringMap.find mv modmap in
    let ((hd_map, _), hd_tmap) = StringMap.find mv map in
    (*StringMap.iter (fun v e -> output_string stdout (v^" : ["); Stdlib.List.iter (printf "%d;") e; output_string stdout "]\n") hd_map; *)
    let newstmts = trans_stmts sl hd_map HiFirrtl_with_implicit_widths.Qnil hd_tmap modmap in
    HiFirrtl_with_implicit_widths.FInmod(Obj.magic flag, List.map (fun a -> Transhiast.trans_port a hd_map) pl, Transhiast.revstmts newstmts HiFirrtl_with_implicit_widths.Qnil)
  | Ast.FExmod (mv, _, _) -> 
    let flag = StringMap.find mv modmap in
    HiFirrtl_with_implicit_widths.FExmod(Obj.magic flag, [], HiFirrtl_with_implicit_widths.Qnil)

let rec trans_modl ml modmap map = 
  match ml with
  | [] -> []
  | hd :: tl -> 
    let fmod = trans_mod hd modmap map in
    fmod :: (trans_modl tl modmap map)

let trans_cir cir modmap map =
  match cir with
  | Ast.Fcircuit (cv, ml) ->
    let circuit = HiFirrtl_with_implicit_widths.Fcircuit ((Obj.magic (StringMap.find cv modmap)),
      (trans_modl ml modmap map)) in
    let assertions, assumes = List.fold_left (fun (aa, uu) m ->
      match m with
      | Ast.FInmod (mv, _, stmts) ->
          let mid = StringMap.find mv modmap in
          let ((mm, _), _) = StringMap.find mv map in
          let a,u = collect_verification mid mm stmts in (aa @ a, uu @ u)
      | Ast.FExmod _ -> (aa, uu)) ([], []) ml in
    { circuit; assertions; assumes }
