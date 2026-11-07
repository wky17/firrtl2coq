From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph div ssrint ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
Semantics_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* value of ref expressions.
   We need both sem_old and sem_new:
   sem_old is used to read Esubaccess indices, sem_new is used to read the actual value *)

Record memory_layout := {
  ml_data_type : ftype;
  ml_depth : nat;
  ml_readers : seq (HiF.mem_port);
  ml_writers : seq (HiF.mem_port);
  ml_read_write : ruw
}.

Definition memory_map := VM.t memory_layout.

Definition empty_memory_map : memory_map := VM.empty memory_layout.

Fixpoint find_mem_port (p : VarOrder.T) (ps : seq (HiF.mem_port)) : option (HiF.mem_port) :=
  match ps with
  | [::] => None
  | x :: xs => if x.(id) == p then Some x else find_mem_port p xs
  end.

Fixpoint array_nth (n : nat) (av : array_value) : option hvalue :=
  match n, av with
  | 0, Acons v _ => Some v
  | n'.+1, Acons _ tl => array_nth n' tl
  | _, _ => None
  end.

Definition memory_zero (t : ftype) : option hvalue :=
  match t with
  | Gtyp (Fuint w) => Some (Gval (Fuint w) (zeros w))
  | Gtyp (Fsint w) => Some (Gval (Fsint w) (zeros w))
  | _ => None
  end.

Definition eval_memory_reader_data
  (mm : memory_map) (mem port : VarOrder.T)
  (sem_old sem_new : VM.t hvalue) : option hvalue :=
  match VM.find mem mm with
  | Some ml =>
      match find_mem_port port (ml_readers ml),
            VM.find mem sem_old with
      | Some mp, Some (Aval elt av) =>
          match VM.find (addr mp) sem_old,
                VM.find (en mp) sem_old,
                VM.find (mask mp) sem_old with
          | Some (Gval (Fuint _) a), Some (Gval (Fuint _) en_v), Some (Gval (Fuint _) mask_v) =>
              if is_zero en_v then Some (Undefinedonpurpose elt)
              else if is_zero mask_v then memory_zero elt
              else array_nth (to_nat a) av
          | _, _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Fixpoint eval_href_with_memory (mm : memory_map) (r : HiF.href) (sem_old sem_new: VM.t hvalue) : option hvalue :=
  match r with
  | Esubfield (Esubfield (Eid mem) port) data =>
      match eval_memory_reader_data mm mem port sem_old sem_new with
      | Some v => Some v
      | None => None
      end
  | Eid v => VM.find v sem_new
  | Esubfield r' v => match eval_href_with_memory mm r' sem_old sem_new with
                      | Some bv => match convert_to_bundle_value bv with
                                   | Some fv => (fix aux fx := match fx with
                                                               | Bflips v' f t fxs => if (v == v') then Some t else aux fxs
                                                               | Bnil => None
                                                               end) fv
                                   | _ => None
                                   end
                      | _ => None
                      end
  | Esubindex r' n => match eval_href_with_memory mm r' sem_old sem_new with
                      | Some av => match convert_to_array_value av with
                                   | Some (_, fv) => (fix aux fx m := match fx, m with
                                                                      | Acons t fxs, m'.+1 => aux fxs m'
                                                                      | Acons t _, 0 => Some t 
                                                                      | _, _ => None
                                                                      end) fv n
                                   | _ => None
                                   end
                      | _ => None
                      end
  | Esubaccess r' e => match eval_hfexpr_with_memory mm e sem_old sem_old with
                       | Some (Gval (Fuint _) val) => match eval_href_with_memory mm r' sem_old sem_new with
                                                      | Some av => match convert_to_array_value av with 
                                                                   | Some (_, fv) => (fix aux fx m := match fx, m with
                                                                                                      | Acons t fxs, m'.+1 => aux fxs m'
                                                                                                      | Acons t _, 0 => Some t 
                                                                                                      | _, _ => None
                                                                                                      end) fv (to_nat val)
                                                                   | None => None
                                                                   end
                                                      | None => None
                                                      end
                       | Some (Needtobedefined (Gtyp (Fuint _)))
                       | Some (Uninitialized (Gtyp (Fuint _))) => match eval_type_of_ref r' sem_new with
                                                                  | Some (Atyp elt _) => Some (Needtobedefined elt)
                                                                  | _ => None
                                                                  end
                       | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match eval_type_of_ref r' sem_new with
                                                                       | Some (Atyp elt _) => Some (Undefinedonpurpose elt)
                                                                       | _ => None
                                                                       end
                       | _ => None
                       end
  end
(* Expression evaluation, value *)
with eval_hfexpr_with_memory (mm : memory_map) (exp : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (Gval (Fuint w1) (zext_to w1 c))
                  | Fsint w2 => if (size c) > w2 then None else Some (Gval (Fsint w2) (sext_to w2 c))
                  | _ => None
                  end
  | Eref r => eval_href_with_memory mm r sem_old sem_new
  | Evalidif c e => match eval_hfexpr_with_memory mm c sem_old sem_new with
                    | Some (Gval (Fuint _) vc) =>
                        if is_zero vc then option_map Undefinedonpurpose (eval_type_of_expr e sem_new)
                        else eval_hfexpr_with_memory mm e sem_old sem_new
                    | _ => None
                    end
  | Ecast AsUInt e => match eval_hfexpr_with_memory mm e sem_old sem_new with
                      | Some (Gval (Fuint          w) val)
                      | Some (Gval (Fsint          w) val) => Some (Gval (Fuint w) val)
                      | Some (Gval _                  val) => Some (Gval (Fuint 1) val)
                      | Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp (Fsint          w))) => Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp _                 )) => Some (Undefinedonpurpose (Gtyp (Fuint          1)))
                      | Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Uninitialized      (Gtyp (Fuint          w)))
                      | Some (Uninitialized      (Gtyp (Fsint          w))) => Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp _                 ))
                      | Some (Uninitialized      (Gtyp _                 )) => Some (Needtobedefined    (Gtyp (Fuint          1)))
                      | _ => None
                      end
  | Ecast AsSInt e => match eval_hfexpr_with_memory mm e sem_old sem_new with 
                      | Some (Gval (Fuint          w) val)
                      | Some (Gval (Fsint          w) val) => Some (Gval (Fsint w) val)
                      | Some (Gval _                  val) => Some (Gval (Fsint          1) val)
                      | Some (Undefinedonpurpose (Gtyp (Fuint          w)))
                      | Some (Undefinedonpurpose (Gtyp (Fsint          w))) => Some (Undefinedonpurpose (Gtyp (Fsint          w)))
                      | Some (Undefinedonpurpose (Gtyp _                 )) => Some (Undefinedonpurpose (Gtyp (Fsint          1)))
                      | Some (Needtobedefined    (Gtyp (Fuint          w)))
                      | Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Uninitialized      (Gtyp (Fuint          w)))
                      | Some (Uninitialized      (Gtyp (Fsint          w))) => Some (Needtobedefined    (Gtyp (Fsint          w)))
                      | Some (Needtobedefined    (Gtyp _                 ))
                      | Some (Uninitialized      (Gtyp _                 )) => Some (Needtobedefined    (Gtyp (Fsint          1)))
                      | _ => None
                      end
  | Ecast AsClock e => match eval_hfexpr_with_memory mm e sem_old sem_new with 
                       | Some (Gval _ val) => Some (Gval Fclock [::lsb val])
                       | Some (Undefinedonpurpose (Gtyp _)) => Some (Undefinedonpurpose (Gtyp Fclock))
                       | Some (Needtobedefined    (Gtyp _))
                       | Some (Uninitialized      (Gtyp _)) => Some (Needtobedefined    (Gtyp Fclock))
                       | _ => None
                       end
  | Ecast AsAsync e => match eval_hfexpr_with_memory mm e sem_old sem_new with
                       | Some (Gval _ val) => Some (Gval Fasyncreset [::lsb val])
                       | Some (Undefinedonpurpose (Gtyp _)) => Some (Undefinedonpurpose (Gtyp Fasyncreset))
                       | Some (Needtobedefined    (Gtyp _))
                       | Some (Uninitialized      (Gtyp _)) => Some (Needtobedefined    (Gtyp Fasyncreset))
                       | _ => None
                       end
(*| Ecast AsReset e => match eval_hfexpr_with_memory mm e sem_old with Some (Gval (Fuint 1) val) => Some (Gval Freset [::lsb val]) | _ => None end *)
  | Eprim_binop op e1 e2 => match eval_hfexpr_with_memory mm e1 sem_old sem_new, eval_hfexpr_with_memory mm e2 sem_old sem_new with
                            | Some val1, Some val2 => eval_binop op val1 val2
                            | _, _ => None
                            end
  | Eprim_unop op e1 => match eval_hfexpr_with_memory mm e1 sem_old sem_new with
                        | Some val => eval_unop op val
                        | None => None
                        end
  | Emux c e1 e2 => match eval_hfexpr_with_memory mm c sem_old sem_new with
                    | Some (Gval (Fuint _) valc) => if is_zero valc then match eval_hfexpr_with_memory mm e2 sem_old sem_new, eval_type_of_expr e1 sem_new with
                                                                         | Some val2, Some ty1 => extend_hvalue_as_type val2 ty1
                                                                         | _, _ => None
                                                                         end
                                                                    else match eval_hfexpr_with_memory mm e1 sem_old sem_new, eval_type_of_expr e2 sem_new with
                                                                         | Some val1, Some ty2 => extend_hvalue_as_type val1 ty2
                                                                         | _, _ => None
                                                                         end
                    | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match eval_type_of_expr e1 sem_new, eval_type_of_expr e2 sem_new with (* need to find result type *)
                                                                    | Some ft1, Some ft2 => option_map Undefinedonpurpose (ftype_mux true ft1 ft2)
                                                                    | _, _ => None
                                                                    end
                    | Some (Needtobedefined    (Gtyp (Fuint _)))
                    | Some (Uninitialized      (Gtyp (Fuint _))) => match eval_type_of_expr e1 sem_new, eval_type_of_expr e2 sem_new with (* need to find result type *)
                                                                    | Some ft1, Some ft2 => option_map Needtobedefined    (ftype_mux true ft1 ft2)
                                                                    | _, _ => None
                                                                    end
                    | _ => None
                    end
  end.


Fixpoint array_update_memory (n : nat) (v : hvalue) (av : array_value) : option array_value :=
  match n, av with
  | 0, Acons _ tl => Some (Acons v tl)
  | n'.+1, Acons h tl => option_map (Acons h) (array_update_memory n' v tl)
  | _, _ => None
  end.

Definition write_memory_data
  (mm : memory_map) (mem port : VarOrder.T) (value : hvalue)
  (set_regs : bool) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
  if ~~ set_regs then Some sem_new else
  match VM.find mem mm, VM.find mem sem_old with
  | Some ml, Some (Aval elt av) =>
      match find_mem_port port (ml_writers ml) with
      | Some mp =>
          match VM.find (addr mp) sem_old, VM.find (en mp) sem_old,
                VM.find (mask mp) sem_old with
          | Some (Gval (Fuint _) a), Some (Gval (Fuint _) en_v),
            Some (Gval (Fuint _) mask_v) =>
              if is_zero en_v then Some sem_new
              else if is_zero mask_v then Some sem_new
              else match adapt_hvalue_as_type value elt,
                         array_update_memory (to_nat a) value av with
                   | Some v, Some av' => Some (VM.add mem (Aval elt av') sem_new)
                   | _, _ => None
                   end
          | _, _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition unidirectional_connect_with_memory (mm : memory_map) (set_regs : bool) (r : HiF.href) (e : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match r with
    | Esubfield (Esubfield (Eid mem) port) data =>
        match eval_hfexpr_with_memory mm e sem_old sem_old with
        | Some v => write_memory_data mm mem port v set_regs sem_old sem_new
        | None => None end
    | _ => match VM.find (HiF.base_ref r) sem_new, eval_type_of_ref r sem_new, eval_hfexpr_with_memory mm e sem_old sem_old with
    | Some old_base_val, Some tor, Some new_val => match adapt_hvalue_as_type new_val tor with
                                                   | Some new_val => option_map ((VM.add (HiF.base_ref r))^~ sem_new) (repl_val_part r (fun (_ new_val : hvalue) => Some new_val) old_base_val new_val sem_old)
                                                   | None => None
                                                   end
    | _, _, _ => None
    end
    end.


Definition bidirectional_connect_with_memory (mm : memory_map) (r1 r2 : HiF.href) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match (match VM.find (HiF.base_ref r1) sem_new, eval_type_of_ref r1 sem_new, eval_href_with_memory mm r2 sem_old sem_old with
           | Some old_base_val1, Some tor1, Some new_val1 => match adapt_hvalue_as_type new_val1 tor1 with
                                                             | Some new_val1 => option_map ((VM.add (HiF.base_ref r1))^~ sem_new) (repl_val_part r1 (replace_writeable Sink) old_base_val1 new_val1 sem_old)
                                                             | None => None
                                                             end
           | _, _, _ => None
           end) with
    | Some sem_1 => match VM.find (HiF.base_ref r2) sem_1, eval_type_of_ref r2 sem_1, eval_href_with_memory mm r1 sem_old sem_old with
                    | Some old_base_val2, Some tor2, Some new_val2 => match adapt_hvalue_as_type new_val2 tor2 with
                                                                      | Some new_val2 => option_map ((VM.add (HiF.base_ref r2))^~ sem_1) (repl_val_part r2 (replace_writeable Source) old_base_val2 new_val2 sem_old)
                                                                      | None => None
                                                                      end
                    | _, _, _ => None
                    end
    | None => None
    end.

(* Sets r to an undefined value (basically a simplified version of the connect functions above)

   r = reference to be changed (may be passive or not)
   undeftype = sort of undefined value (Undefinedonpurpose or Needtobedefined)
   sem_old = values of all components in the instance before the iteration
             (used to calculate subaccess indices)
   sem_new = new values of all components in the instance, calculated from earlier statements

   Result: sem_new, updated as required: the value of the writeable parts of r is now undeftype *)
Definition undef_ref (r : HiF.href) (undeftype : ftype -> hvalue) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
    match VM.find (HiF.base_ref r) sem_new, eval_type_of_ref r sem_new with
    | Some old_base_val, Some tor => option_map ((VM.add (HiF.base_ref r))^~ sem_new) (repl_val_part r (replace_writeable Sink) old_base_val (undeftype tor) sem_old)
    | _, _ => None
    end.


Fixpoint value_iter_with_memory (mm : memory_map) (sem_old : VM.t hvalue) (set_regs : bool) (sem_new : VM.t hvalue) (ssl : HiF.hfstmt_seq) : option (VM.t hvalue) :=
    match ssl with
    | Qnil => Some sem_new
    | Qcons Sskip ssl'
    | Qcons (Sinst _ _) ssl' => value_iter_with_memory mm sem_old set_regs sem_new ssl'
    | Qcons (Swire w t) ssl' => value_iter_with_memory mm sem_old set_regs (VM.add w (Needtobedefined t) sem_new) ssl'
    | Qcons (Sreg r rt) ssl' => match VM.find r sem_old with
                                | Some old_r => value_iter_with_memory mm sem_old set_regs (VM.add r old_r sem_new) ssl'
                                | None => None
                                end
    | Qcons (Smem m fm) ssl' => match VM.find m sem_old with
                                | Some old_m => value_iter_with_memory mm sem_old set_regs (VM.add m old_m sem_new) ssl'
                                | None => None
                                end
    | Qcons (Snode n e) ssl' => match eval_hfexpr_with_memory mm e sem_old sem_old with
                                | Some hval => value_iter_with_memory mm sem_old set_regs (VM.add n hval sem_new) ssl'
                                | None => None
                                end
    | Qcons (Sfcnct r (Eref r')) ssl' => (* bidirectional connect *)
                                         match bidirectional_connect_with_memory mm r r' sem_old sem_new with
                                         | Some sem_cnct => value_iter_with_memory mm sem_old set_regs sem_cnct ssl'
                                         | None => None
                                         end
    | Qcons (Sfcnct r e) ssl' => (* unidirectional connect; must be passive *) 
                                 match unidirectional_connect_with_memory mm set_regs r e sem_old sem_new with
                                 | Some sem_cnct => value_iter_with_memory mm sem_old set_regs sem_cnct ssl'
                                 | None => None
                                 end
    | Qcons (Sinvalid r) ssl' => match undef_ref r Undefinedonpurpose sem_old sem_new with
                                 | Some sem_inv => value_iter_with_memory mm sem_old set_regs sem_inv ssl'
                                 | None => None
                                 end
    | Qcons (Swhen c ssl_true ssl_false) ssl' => match eval_hfexpr c sem_old sem_old with
                                                 | Some (Gval (Fuint _) valc) => if is_zero valc then match value_iter_with_memory mm sem_old set_regs sem_new ssl_false with
                                                                                                      | Some sem_false => value_iter_with_memory mm sem_old set_regs sem_false ssl'
                                                                                                      | None => None
                                                                                                      end
                                                                                                 else match value_iter_with_memory mm sem_old set_regs sem_new ssl_true with
                                                                                                      | Some sem_true => value_iter_with_memory mm sem_old set_regs sem_true ssl'
                                                                                                      | None => None
                                                                                                      end
                                                 | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Undefinedonpurpose sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Undefinedonpurpose sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter_with_memory mm sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | Some (Needtobedefined    (Gtyp (Fuint _)))
                                                 | Some (Uninitialized      (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Needtobedefined sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Needtobedefined sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter_with_memory mm sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | _ => None
                                                 end
    end.


(* Build memory layouts before circuit fixed-point iteration. *)
Fixpoint memory_map_of_stmts (ssl : HiF.hfstmt_seq) : memory_map :=
  match ssl with
  | Qnil => VM.empty memory_layout
  | Qcons st ssl' =>
      let tail := memory_map_of_stmts ssl' in
      match st with
      | Smem mem fm =>
          VM.add mem
            {| ml_data_type := data_type fm;
               ml_depth := depth fm;
               ml_readers := reader fm;
               ml_writers := writer fm;
               ml_read_write := read_write fm |} tail
      | Swhen _ yes no =>
          let yes_map := memory_map_of_stmts yes in
          let no_map := memory_map_of_stmts no in
          VM.fold (fun k v acc => VM.add k v acc) yes_map no_map
      | _ => tail
      end
  end.

Fixpoint memory_maps_of_modules
  (mml : seq HiF.hfmodule) : VM.t memory_map :=
  match mml with
  | [::] => VM.empty memory_map
  | FInmod mi _ ssl :: tl =>
      VM.add mi (memory_map_of_stmts ssl) (memory_maps_of_modules tl)
  | FExmod mi _ ssl :: tl =>
      VM.add mi (memory_map_of_stmts ssl) (memory_maps_of_modules tl)
  end.

Definition memory_map_for_module
  (mml : seq HiF.hfmodule) (mi : VarOrder.T) : option memory_map :=
  VM.find mi (memory_maps_of_modules mml).

Definition circuit_value_iter_with_memory
  (mml : seq HiF.hfmodule) (mi_top : VarOrder.T)
  (circuit_sem_old : SVM.t (VM.t hvalue)) (set_regs : bool)
  : option (SVM.t (VM.t hvalue)) :=
  match find_circuit_instances mml mi_top with
  | Some fci =>
      SVM.fold
        (fun (ii : SVM.key) (mi : VarOrder.T)
             (acc : option (SVM.t (VM.t hvalue))) =>
          match acc, SVM.find ii circuit_sem_old,
                (match acc with Some cs => SVM.find ii cs | None => None end),
                find_module mml mi,
                memory_map_for_module mml mi with
          | Some circuit_sem_new, Some sem_old, Some sem_new,
            Some (FInmod _ _ ssl), Some mm =>
              match value_iter_with_memory mm sem_old set_regs sem_new ssl with
              | Some sem_res => Some (SVM.add ii sem_res circuit_sem_new)
              | None => None
              end
          | _, _, _, _, _ => None
          end)
        fci (Some circuit_sem_old)
  | None => None
  end.

Fixpoint circuit_value_iterator_with_memory
  (mml : seq HiF.hfmodule) (mi_top : VarOrder.T)
  (n : nat) (states : SVM.t (VM.t hvalue))
  : option (SVM.t (VM.t hvalue)) :=
  match n with
  | 0 => Some states
  | n'.+1 =>
      match circuit_value_iter_with_memory mml mi_top states false with
      | Some states' => circuit_value_iterator_with_memory mml mi_top n' states'
      | None => None
      end
  end.

Definition circuit_value_with_memory
  (mml : seq HiF.hfmodule) (mi_top : VarOrder.T)
  (previous_cycle_register_map : option (SVM.t (VM.t hvalue)))
  (external_inputs : VM.t hvalue)
  : option (SVM.t (VM.t hvalue)) :=
  match circuit_initial_map mml mi_top previous_cycle_register_map external_inputs,
        circuit_iter_count mml Gtyp_connect_count with
  | Some initial_states, Some n =>
      match circuit_value_iterator_with_memory mml mi_top n initial_states with
      | Some stabilized => circuit_value_iter_with_memory mml mi_top stabilized true
      | None => None
      end
  | _, _ => None
  end.
