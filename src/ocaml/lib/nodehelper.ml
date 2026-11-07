open Hifirrtl_lang
open Extraction.Ssrnat
open Extraction.Eqtype

module StringMap = Map.Make(String)

let rec pp_ref = function
  | Ast.Eid v -> v
  | Ast.Esubfield (r, v) -> pp_ref r ^ "." ^ v
  | Ast.Esubindex (r, n) -> Printf.sprintf "%s[%d]" (pp_ref r) n
  | Ast.Esubaccess (r, _) -> pp_ref r ^ "[<access>]"

(** val type_of_ref :
      HiF.href -> (ftype * fcomponent) VM.t -> ftype option **)

  let rec type_of_ref r tmap =
    match r with
    | Ast.Eid v ->
        (match StringMap.find_opt v tmap with
         | Some x -> Some x
         | None ->
             Printf.eprintf "type_of_ref: missing identifier `%s`\n%!" v;
             None)
    | Esubfield (r0, v) ->
      (match type_of_ref r0 tmap with
       | Some f ->
         (match f with
          | Ast.Btyp fs ->
            let rec aux = function
            | Ast.Fnil -> None
            | Fflips (v', _, t0, fxs) ->
              if (String.equal v v')
              then Some t0
              else aux fxs
            in aux fs
          | _ -> None)
       | None -> None)
    | Esubindex (r0, _) ->
      (match type_of_ref r0 tmap with
       | Some f -> (match f with
                    | Atyp (ty, _) -> Some ty
                    | _ -> None)
       | None -> None)
    | Esubaccess (r0, _) ->
      (match type_of_ref r0 tmap with
       | Some f -> (match f with
                    | Atyp (ty, _) -> Some ty
                    | _ -> None)
       | None -> None)

  (** val fgtyp_mux : fgtyp -> fgtyp -> fgtyp option **)

  let fgtyp_mux x y =
    match x with
    | Ast.Fuint wx ->
      (match y with
       | Ast.Fuint wy -> Some (Ast.Fuint (maxn wx wy))
       | _ -> None)
    | Fsint wx ->
      (match y with
       | Fsint wy -> Some (Fsint (maxn wx wy))
       | _ -> None)
    | Fclock -> (match y with
                 | Fclock -> Some Fclock
                 | _ -> None)
    | Freset -> (match y with
                 | Freset -> Some Freset
                 | _ -> None)
    | Fasyncreset ->
      (match y with
       | Fasyncreset -> Some Fasyncreset
       | _ -> None)

  (** val ftype_mux : ftype -> ftype -> ftype option **)

  let rec ftype_mux x y =
    match x with
    | Ast.Gtyp tx ->
      (match y with
       | Ast.Gtyp ty ->
         (match fgtyp_mux tx ty with
          | Some fgt -> Some (Ast.Gtyp fgt)
          | None -> None)
       | _ -> None)
    | Atyp (tx, nx) ->
      (match y with
       | Atyp (ty, ny) ->
         if eq_op nat_eqType (Obj.magic nx) (Obj.magic ny)
         then (match ftype_mux tx ty with
               | Some fat -> Some (Atyp (fat, nx))
               | None -> None)
         else None
       | _ -> None)
    | Btyp fx -> (match y with
                  | Btyp fy -> ffield_mux fx fy
                  | _ -> None)

  (** val ffield_mux : ffield -> ffield -> ftype option **)

  and ffield_mux f1 f2 =
    match f1 with
    | Fnil ->
      (match f2 with
       | Fnil -> Some (Btyp Fnil)
       | Fflips (_, _, _, _) -> None)
    | Fflips (v1, f, t1, fs1) ->
      (match f with
       | Flipped -> None
       | Nflip ->
         (match f2 with
          | Fnil -> None
          | Fflips (v2, f0, t2, fs2) ->
            (match f0 with
             | Flipped -> None
             | Nflip ->
               if (String.equal v1 v2)
               then (match ffield_mux fs1 fs2 with
                     | Some f3 ->
                       (match f3 with
                        | Btyp bf ->
                          (match ftype_mux t1 t2 with
                           | Some ft ->
                             Some (Btyp (Fflips (v1, Nflip, ft, bf)))
                           | None -> None)
                        | _ -> None)
                     | None -> None)
               else None)))

let binary_length (signed : bool) (n: Z.t) : int =
if n = Z.zero then 1  (* 特殊情况：0 的补码表示为 "0"，长度为 1 *)
else let bits = Z.numbits (Z.abs n) in
  if signed then
    if n > Z.zero then
      bits + 1
    else if (Z.popcount (Z.abs n)) = 1 then bits
      else bits + 1
  else bits
  
  (** val type_of_hfexpr :
      HiF.hfexpr -> (ftype * fcomponent) VM.t -> ftype option **)

  let rec type_of_hfexpr e tmap =
    match e with
    | Ast.Econst (Ast.Fuint_implicit _, bs) -> Some (Ast.Gtyp (Fuint (binary_length false bs)))
    | Ast.Econst (Fsint_implicit _, bs) -> Some (Ast.Gtyp (Fsint (binary_length true bs)))
    | Ast.Econst (t0, _) -> Some (Ast.Gtyp t0)
    | Ecast (u, e1) ->
      (match u with
       | AsUInt ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fuint w))
                | Fsint w -> Some (Gtyp (Fuint w))
                | _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0))))
             | _ -> None)
          | None -> None)
       | AsSInt ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fsint w))
                | Fsint w -> Some (Gtyp (Fsint w))
                | _ -> Some (Gtyp (Fsint (Stdlib.Int.succ 0))))
             | _ -> None)
          | None -> None)
       | AsClock ->
         (match type_of_hfexpr e1 tmap with
          | Some f -> (match f with
                       | Gtyp _ -> Some (Gtyp Fclock)
                       | _ -> None)
          | None -> None)
       | AsAsync ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp _ -> Some (Gtyp Fasyncreset)
             | _ -> None)
          | None -> None))
    | Eprim_unop (e0, e1) ->
      (match e0 with
       | Upad n ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fuint (maxn w n)))
                | Fsint w -> Some (Gtyp (Fsint (maxn w n)))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Ushl n ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fuint (addn w n)))
                | Fsint w -> Some (Gtyp (Fsint (addn w n)))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Ushr n ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fuint (maxn (subn w n) 0)))
                | Fsint w ->
                  Some (Gtyp (Fsint (maxn (subn w n) (Stdlib.Int.succ 0))))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Ucvt ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
                | Fsint w -> Some (Gtyp (Fsint w))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Uneg ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
                | Fsint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Unot ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> Some (Gtyp (Fuint w))
                | Fsint w -> Some (Gtyp (Fuint w))
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Uextr (n1, n2) ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w ->
                  if (&&) (leq n2 n1) (leq (Stdlib.Int.succ n1) w)
                  then Some (Gtyp (Fuint
                         (addn (subn n1 n2) (Stdlib.Int.succ 0))))
                  else None
                | Fsint w ->
                  if (&&) (leq n2 n1) (leq (Stdlib.Int.succ n1) w)
                  then Some (Gtyp (Fuint
                         (addn (subn n1 n2) (Stdlib.Int.succ 0))))
                  else None
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Uhead n ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w -> if leq n w then Some (Gtyp (Fuint n)) else None
                | Fsint w -> if leq n w then Some (Gtyp (Fuint n)) else None
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Utail n ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w ->
                  if leq n w then Some (Gtyp (Fuint (subn w n))) else None
                | Fsint w ->
                  if leq n w then Some (Gtyp (Fuint (subn w n))) else None
                | _ -> None)
             | _ -> None)
          | None -> None)
       | _ ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
                | Fsint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
                | _ -> None)
             | _ -> None)
          | None -> None))
    | Eprim_binop (e0, e1, e2) ->
      (match e0 with
       | Badd ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 ->
                           Some (Gtyp (Fuint
                             (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 ->
                           Some (Gtyp (Fsint
                             (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bsub ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 ->
                           Some (Gtyp (Fuint
                             (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 ->
                           Some (Gtyp (Fsint
                             (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bmul ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 -> Some (Gtyp (Fsint (addn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bdiv ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint _ -> Some (Gtyp (Fuint w1))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint _ ->
                           Some (Gtyp (Fsint (addn w1 (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Brem ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 -> Some (Gtyp (Fuint (minn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 -> Some (Gtyp (Fsint (minn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bcomp _ ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint _ ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint _ ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bdshl ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 ->
                           Some (Gtyp (Fuint
                             (subn
                               (addn
                                 (expn (Stdlib.Int.succ (Stdlib.Int.succ 0))
                                   w2) w1) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 ->
                           Some (Gtyp (Fsint
                             (subn
                               (addn
                                 (expn (Stdlib.Int.succ (Stdlib.Int.succ 0))
                                   w2) w1) (Stdlib.Int.succ 0))))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bdshr ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint _ -> Some (Gtyp (Fuint w1))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint _ -> Some (Gtyp (Fsint w1))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | Bcat ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None)
       | _ ->
         (match type_of_hfexpr e1 tmap with
          | Some f ->
            (match f with
             | Gtyp f0 ->
               (match f0 with
                | Fuint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fuint w2 -> Some (Gtyp (Fuint (maxn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | Fsint w1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some f1 ->
                     (match f1 with
                      | Gtyp f2 ->
                        (match f2 with
                         | Fsint w2 -> Some (Gtyp (Fuint (maxn w1 w2)))
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | _ -> None)
          | None -> None))
    | Emux (c, e1, e2) ->
      (match type_of_hfexpr c tmap with
       | Some f ->
         (match f with
          | Gtyp f0 ->
            (match f0 with
             | Fuint _ ->
               (match type_of_hfexpr e1 tmap with
                | Some t1 ->
                  (match type_of_hfexpr e2 tmap with
                   | Some t2 -> ftype_mux t1 t2
                   | None -> None)
                | None -> None)
             | _ -> None)
          | _ -> None)
       | None -> None)
    | Evalidif (_, e1) -> type_of_hfexpr e1 tmap
    | Eref r -> type_of_ref r tmap
