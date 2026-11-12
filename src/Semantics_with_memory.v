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
  ml_storage_id : VarOrder.T;
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

(* Port fields follow the translator schema: addr/en/clk/mask/data. *)
Definition memory_data_field : VarOrder.T := N.of_nat 4.

(* A two-level field reference also describes ordinary bundles (including
   instance ports). Classify it using the memory layout before evaluating it;
   a failure in a genuine memory access must not trigger bundle fallback. *)
Definition is_memory_data_port (writers : bool) (mm : memory_map)
  (mem port field : VarOrder.T) : bool :=
  if field == memory_data_field then
    match VM.find mem mm with
    | Some ml => match find_mem_port port (if writers then ml_writers ml else ml_readers ml) with
                 | Some _ => true | None => false end
    | None => false end
  else false.

Definition read_bundle_field (value : option hvalue) (field : VarOrder.T) : option hvalue :=
  match value with
  | Some bv => match convert_to_bundle_value bv with
    | Some fields => (fix lookup fields := match fields with
        | Bflips name _ v tail => if field == name then Some v else lookup tail
        | Bnil => None end) fields
    | None => None end
  | None => None end.

(* Field numbers are local to a port bundle, never module-level variables. *)
Definition read_memory_port_field (sem : VM.t hvalue)
  (mem port field : VarOrder.T) : option hvalue :=
  read_bundle_field (read_bundle_field (VM.find mem sem) port) field.

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
            VM.find (ml_storage_id ml) sem_old with
      | Some mp, Some (Aval elt av) =>
          (* Readers have no write mask. Pending controls must survive the
             combinational iterations just like validif and array indexing. *)
          match read_memory_port_field sem_old mem port (en mp) with
          | Some (Gval (Fuint _) en_v) =>
              if is_zero en_v then Some (Undefinedonpurpose elt)
              else match read_memory_port_field sem_old mem port (addr mp) with
                   | Some (Gval (Fuint _) a) => array_nth (to_nat a) av
                   | Some (Needtobedefined (Gtyp (Fuint _)))
                   | Some (Uninitialized (Gtyp (Fuint _))) => Some (Needtobedefined elt)
                   | Some (Undefinedonpurpose (Gtyp (Fuint _))) => Some (Undefinedonpurpose elt)
                   | _ => None end
          | Some (Needtobedefined (Gtyp (Fuint _)))
          | Some (Uninitialized (Gtyp (Fuint _))) => Some (Needtobedefined elt)
          | Some (Undefinedonpurpose (Gtyp (Fuint _))) => Some (Undefinedonpurpose elt)
          | _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Fixpoint eval_href_with_memory (mm : memory_map) (r : HiF.href) (sem_old sem_new: VM.t hvalue) : option hvalue :=
  match r with
  | Eid v => VM.find v sem_new
  | Esubfield parent field =>
      match parent with
      | Esubfield (Eid mem) port =>
          if is_memory_data_port false mm mem port field then
            eval_memory_reader_data mm mem port sem_old sem_new
          else read_bundle_field (eval_href_with_memory mm parent sem_old sem_new) field
      | _ => read_bundle_field (eval_href_with_memory mm parent sem_old sem_new) field
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
                    (* A pending guard must survive until the next iteration,
                       using the result type rather than the guard's type. *)
                    | Some (Needtobedefined (Gtyp (Fuint _)))
                    | Some (Uninitialized (Gtyp (Fuint _))) =>
                        option_map Needtobedefined (eval_type_of_expr e sem_new)
                    | Some (Undefinedonpurpose (Gtyp (Fuint _))) =>
                        option_map Undefinedonpurpose (eval_type_of_expr e sem_new)
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

Inductive memory_gate := MemoryOff | MemoryOn | MemoryPending | MemoryInvalid.

Definition classify_memory_gate (v : option hvalue) : option memory_gate :=
  match v with
  | Some (Gval (Fuint _) bits) => Some (if is_zero bits then MemoryOff else MemoryOn)
  | Some (Needtobedefined (Gtyp (Fuint _)))
  | Some (Uninitialized (Gtyp (Fuint _))) => Some MemoryPending
  | Some (Undefinedonpurpose (Gtyp (Fuint _))) => Some MemoryInvalid
  | _ => None end.

Definition memory_write_gate (sem : VM.t hvalue) (mem port : VarOrder.T)
  (mp : HiF.mem_port) : option memory_gate :=
  match classify_memory_gate (read_memory_port_field sem mem port (en mp)) with
  | Some MemoryOff => Some MemoryOff
  | Some enabled =>
      match classify_memory_gate (read_memory_port_field sem mem port (mask mp)) with
      | Some MemoryOff => Some MemoryOff
      | Some MemoryOn => Some enabled
      | Some MemoryPending => Some (match enabled with MemoryInvalid => MemoryInvalid | _ => MemoryPending end)
      | Some MemoryInvalid => Some MemoryInvalid
      | None => None end
  | None => None end.

Fixpoint unknown_memory_array (unknown : ftype -> hvalue) (elt : ftype)
  (av : array_value) : array_value :=
  match av with
  | Anil => Anil
  | Acons _ tl => Acons (unknown elt) (unknown_memory_array unknown elt tl)
  end.

(* An uncertain write must not silently leave known memory contents intact.
   A known address affects one cell; an unknown address may affect any cell. *)
Definition write_memory_address (elt : ftype) (av : array_value)
  (address : option hvalue) (value : hvalue) (unknown : ftype -> hvalue)
  : option array_value :=
  match address with
  | Some (Gval (Fuint _) a) => array_update_memory (to_nat a) value av
  | Some (Needtobedefined (Gtyp (Fuint _)))
  | Some (Uninitialized (Gtyp (Fuint _))) => Some (unknown_memory_array unknown elt av)
  | Some (Undefinedonpurpose (Gtyp (Fuint _))) =>
      Some (unknown_memory_array Undefinedonpurpose elt av)
  | _ => None end.

Definition write_memory_data
  (mm : memory_map) (mem port : VarOrder.T) (value : hvalue)
  (set_regs : bool) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
  if ~~ set_regs then Some sem_new else
  match VM.find mem mm with
  | Some ml =>
      (* Accumulate writes in sem_new; reads still observe sem_old. *)
      match find_mem_port port (ml_writers ml), VM.find (ml_storage_id ml) sem_new with
      | Some mp, Some (Aval elt av) =>
          match memory_write_gate sem_old mem port mp with
          | Some MemoryOff => Some sem_new
          | Some gate =>
              match adapt_hvalue_as_type value elt with
              | Some v =>
                  let written := match gate with
                    | MemoryPending => Needtobedefined elt
                    | MemoryInvalid => Undefinedonpurpose elt
                    | _ => v end in
                  let unknown := match gate with MemoryInvalid => Undefinedonpurpose | _ => Needtobedefined end in
                       option_map (fun av' => VM.add (ml_storage_id ml) (Aval elt av') sem_new)
                         (write_memory_address elt av
                           (read_memory_port_field sem_old mem port (addr mp)) written unknown)
              | None => None end
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition unidirectional_connect_bundle (mm : memory_map)
 (r : HiF.href) (e : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
 match VM.find (HiF.base_ref r) sem_new, eval_type_of_ref r sem_new,
       eval_hfexpr_with_memory mm e sem_old sem_old with
 | Some old_base_val, Some tor, Some new_val =>
   match adapt_hvalue_as_type new_val tor with
   | Some new_val => option_map ((VM.add (HiF.base_ref r))^~ sem_new)
       (repl_val_part r (fun (_ value : hvalue) => Some value) old_base_val new_val sem_old)
   | None => None end
 | _, _, _ => None end.

Definition unidirectional_connect_with_memory (mm : memory_map) (set_regs : bool)
 (r : HiF.href) (e : HiF.hfexpr) (sem_old sem_new : VM.t hvalue) : option (VM.t hvalue) :=
 match r with
 | Esubfield (Esubfield (Eid mem) port) field =>
   if is_memory_data_port true mm mem port field then
     match unidirectional_connect_bundle mm r e sem_old sem_new,
           eval_hfexpr_with_memory mm e sem_old sem_old with
     | Some next, Some value => write_memory_data mm mem port value set_regs sem_old next
     | _, _ => None end
   else unidirectional_connect_bundle mm r e sem_old sem_new
 | _ => unidirectional_connect_bundle mm r e sem_old sem_new
 end.

Definition is_memory_writer_ref (mm : memory_map) (r : HiF.href) : bool :=
 match r with
 | Esubfield (Esubfield (Eid mem) port) field => is_memory_data_port true mm mem port field
 | _ => false end.


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


(* Explicit invalid sources can be instantiated with quantified bit patterns.
   A statement address is [index; branch; index; ...], branch 0=true/1=false.
   A policy stays fixed for all iterations and the register commit of a cycle. *)
Definition invalid_value_policy := seq nat -> ftype -> hvalue.
Definition legacy_invalid_policy : invalid_value_policy :=
  fun _ => Undefinedonpurpose.

(* Invalidating a writer data sink is still a data assignment. As for a
   connection, update the visible port during settling and the storage only
   at the register/memory commit, using the old enable/address/mask. *)
Definition invalidate_ref_with_memory (mm : memory_map) (set_regs : bool)
  (r : HiF.href) (make_value : ftype -> hvalue) (sem_old sem_new : VM.t hvalue) :=
  match undef_ref r make_value sem_old sem_new with
  | Some next =>
      match r with
      | Esubfield (Esubfield (Eid mem) port) field =>
          if is_memory_data_port true mm mem port field then
            match eval_type_of_ref r sem_new with
            | Some t => write_memory_data mm mem port (make_value t) set_regs sem_old next
            | None => None
            end
          else Some next
      | _ => Some next
      end
  | None => None
  end.

Fixpoint input_value_of_type (contents : seq VarOrder.T -> nat -> bits)
  (t : ftype) (location : seq VarOrder.T) {struct t} : hvalue :=
  match t with
  | Gtyp g => Gval g (contents location (sizeof_fgtyp g))
  | Atyp elt n =>
      Aval elt ((fix fill (remaining index : nat) : array_value :=
        match remaining with
        | 0 => Anil
        | S rest => Acons
            (input_value_of_type contents elt (rcons location (N.of_nat index)))
            (fill rest (S index))
        end) n 0)
  | Btyp fields => Bval (input_fields_of_type contents fields location)
  end
with input_fields_of_type (contents : seq VarOrder.T -> nat -> bits)
  (fields : ffield) (location : seq VarOrder.T) {struct fields} : bundle_value :=
  match fields with
  | Fnil => Bnil
  | Fflips field flip t rest => Bflips field flip
      (input_value_of_type contents t (rcons location field))
      (input_fields_of_type contents rest location)
  end.

(* Memory initialization remains the N-valued convenience interface. *)
Definition memory_initial_value (contents : seq VarOrder.T -> N) :=
  input_value_of_type (fun location width => from_N width (contents location)).
Definition memory_initial_fields (contents : seq VarOrder.T -> N) :=
  input_fields_of_type (fun location width => from_N width (contents location)).

Fixpoint value_iter_statements_with_memory_policy
  (invalid : invalid_value_policy) (scope : seq nat) (position : nat) (mm : memory_map) (sem_old : VM.t hvalue) (set_regs : bool) (sem_new : VM.t hvalue) (ssl : HiF.hfstmt_seq) {struct ssl} : option (VM.t hvalue) :=
    match ssl with
    | Qnil => Some sem_new
    | Qcons Sskip ssl'
    | Qcons (Sinst _ _) ssl' => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_new ssl'
    | Qcons (Swire w t) ssl' => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs (VM.add w (Needtobedefined t) sem_new) ssl'
    | Qcons (Sreg r rt) ssl' => match VM.find r sem_old with
                                | Some old_r => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs (VM.add r old_r sem_new) ssl'
                                | None => None
                                end
    | Qcons (Smem m fm) ssl' => match VM.find m sem_old with
                                | Some old_m => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs (VM.add m old_m sem_new) ssl'
                                | None => None
                                end
    | Qcons (Snode n e) ssl' => match eval_hfexpr_with_memory mm e sem_old sem_old with
                                | Some hval => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs (VM.add n hval sem_new) ssl'
                                | None => None
                                end
    | Qcons (Sfcnct r (Eref r')) ssl' =>
                                         (* A writer data sink must commit even when its RHS is a reference. *)
                                         match (if is_memory_writer_ref mm r then
                                           unidirectional_connect_with_memory mm set_regs r (Eref r') sem_old sem_new
                                         else bidirectional_connect_with_memory mm r r' sem_old sem_new) with
                                         | Some sem_cnct => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_cnct ssl'
                                         | None => None
                                         end
    | Qcons (Sfcnct r e) ssl' => (* unidirectional connect; must be passive *) 
                                 match unidirectional_connect_with_memory mm set_regs r e sem_old sem_new with
                                 | Some sem_cnct => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_cnct ssl'
                                 | None => None
                                 end
    | Qcons (Sinvalid r) ssl' => match invalidate_ref_with_memory mm set_regs r (invalid (rcons scope position)) sem_old sem_new with
                                 | Some sem_inv => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_inv ssl'
                                 | None => None
                                 end
    | Qcons (Swhen c ssl_true ssl_false) ssl' => match eval_hfexpr c sem_old sem_old with
                                                 | Some (Gval (Fuint _) valc) => if is_zero valc then match value_iter_statements_with_memory_policy invalid (rcons (rcons scope position) 1) 0 mm sem_old set_regs sem_new ssl_false with
                                                                                                      | Some sem_false => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_false ssl'
                                                                                                      | None => None
                                                                                                      end
                                                                                                 else match value_iter_statements_with_memory_policy invalid (rcons (rcons scope position) 0) 0 mm sem_old set_regs sem_new ssl_true with
                                                                                                      | Some sem_true => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_true ssl'
                                                                                                      | None => None
                                                                                                      end
                                                 | Some (Undefinedonpurpose (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Undefinedonpurpose sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Undefinedonpurpose sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | Some (Needtobedefined    (Gtyp (Fuint _)))
                                                 | Some (Uninitialized      (Gtyp (Fuint _))) => match make_undefined sem_old set_regs Needtobedefined sem_new ssl_true with
                                                                                                 | Some sem_true => match make_undefined sem_old set_regs Needtobedefined sem_true ssl_false with
                                                                                                                    | Some sem_false => value_iter_statements_with_memory_policy invalid scope (S position) mm sem_old set_regs sem_false ssl'
                                                                                                                    | None => None
                                                                                                                    end
                                                                                                 | None => None
                                                                                                 end
                                                 | _ => None
                                                 end
    end.


Definition value_iter_statements_with_memory :=
  value_iter_statements_with_memory_policy legacy_invalid_policy [::] 0.

(* Apply register timing only after the full statement sequence has executed. *)
Definition value_iter_with_memory_policy (invalid : invalid_value_policy) (mm : memory_map)
  (sem_old : VM.t hvalue) (set_regs : bool) (sem_new : VM.t hvalue)
  (ssl : HiF.hfstmt_seq) : option (VM.t hvalue) :=
  match value_iter_statements_with_memory_policy invalid [::] 0 mm sem_old set_regs sem_new ssl with
  | Some proposed =>
      finish_registers (fun e => eval_hfexpr_with_memory mm e sem_old sem_old)
        sem_old set_regs proposed ssl
  | None => None
  end.

Definition value_iter_with_memory :=
  value_iter_with_memory_policy legacy_invalid_policy.

(* Build memory layouts before circuit fixed-point iteration. *)
Fixpoint memory_map_of_stmts (ssl : HiF.hfstmt_seq) : memory_map :=
  match ssl with
  | Qnil => VM.empty memory_layout
  | Qcons st ssl' =>
      let tail := memory_map_of_stmts ssl' in
      match st with
      | Smem mem fm =>
          VM.add mem
            {| ml_storage_id := storage_id fm;
               ml_data_type := data_type fm;
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

Definition circuit_value_iter_with_memory_policy
  (invalid : SVM.key -> invalid_value_policy)
  (mml : seq HiF.hfmodule) (mi_top : VarOrder.T)
  (circuit_sem_old : SVM.t (VM.t hvalue)) (set_regs : bool)
  : option (SVM.t (VM.t hvalue)) :=
  match find_circuit_instances mml mi_top with
  | Some fci =>
      match SVM.fold
        (fun (ii : SVM.key) (mi : VarOrder.T)
             (acc : option (SVM.t (VM.t hvalue))) =>
          match acc, SVM.find ii circuit_sem_old,
                (match acc with Some cs => SVM.find ii cs | None => None end),
                find_module mml mi,
                memory_map_for_module mml mi with
          | Some circuit_sem_new, Some sem_old, Some sem_new,
            Some (FInmod _ _ ssl), Some mm =>
              match value_iter_with_memory_policy (invalid ii) mm sem_old set_regs sem_new ssl with
              | Some sem_res => Some (SVM.add ii sem_res circuit_sem_new)
              | None => None
              end
          | _, _, _, _, _ => None
          end)
        fci (Some circuit_sem_old) with
      | Some evaluated => sync_circuit_ports mml fci evaluated
      | None => None
      end
  | None => None
  end.


Definition circuit_value_iter_with_memory :=
  circuit_value_iter_with_memory_policy (fun _ => legacy_invalid_policy).

Fixpoint memory_addr_width (n : nat) : nat :=
  match n with
  | 0 => 1
  | n'.+1 => if n'.+1 <= 1 then 1 else (memory_addr_width n').+1
  end.

(* The translator's synthetic port bundle orders fields as
   addr=0, en=1, clk=2, mask=3, data=4. Port [id] belongs to the
   enclosing memory bundle and must not be reused as a field id. *)

Definition memory_port_initial_value (fm : HiF.hfmem) (p : HiF.mem_port) : hvalue :=
  let aw := memory_addr_width (depth fm) in
  Bval (Bflips (addr p) Nflip (Needtobedefined (Gtyp (Fuint aw)))
    (Bflips (en p) Nflip (Needtobedefined (Gtyp (Fuint 1)))
      (Bflips (clk p) Nflip (Needtobedefined (Gtyp Fclock))
        (Bflips (mask p) Nflip (Needtobedefined (Gtyp (Fuint 1)))
          (Bflips memory_data_field Nflip (Needtobedefined (data_type fm)) Bnil))))) .

Fixpoint memory_ports_initial (ps : seq HiF.mem_port) (fm : HiF.hfmem)
  (acc : bundle_value) : bundle_value :=
  match ps with
  | [::] => acc
  | p :: tl =>
      Bflips (id p) Nflip (memory_port_initial_value fm p)
        (memory_ports_initial tl fm acc)
  end.

Definition memory_bundle_initial (fm : HiF.hfmem) : hvalue :=
  Bval (memory_ports_initial (reader fm ++ writer fm) fm Bnil).

(* Type-analysis view: a memory exposes its port bundle, not its private
   storage array. Reuse the established checker on that structural view.
   Runtime statements and register/memory state are not rewritten. *)
Fixpoint memory_type_view (stmts : HiF.hfstmt_seq) : HiF.hfstmt_seq :=
  match stmts with
  | Qnil => @Qnil VarOrder.T
  | Qcons st tl =>
      @Qcons VarOrder.T (match st with
             | Smem v fm => @Swire VarOrder.T v (type_of_val (memory_bundle_initial fm))
             | Swhen c yes no => @Swhen VarOrder.T c (memory_type_view yes) (memory_type_view no)
             | _ => st
             end) (memory_type_view tl)
  end.

Definition memory_module_type_view (m : HiF.hfmodule) : HiF.hfmodule :=
  match m with
  | FInmod mi ports stmts => @FInmod VarOrder.T mi ports (memory_type_view stmts)
  | _ => m
  end.

Definition circuit_iter_count_with_memory
  (mml : seq HiF.hfmodule) (count : ftype -> nat) : option nat :=
  circuit_iter_count (map memory_module_type_view mml) count.

Fixpoint statements_initial_map_with_memory
  (mml : seq HiF.hfmodule) (ssl : HiF.hfstmt_seq)
  (previous : option (VM.t hvalue)) (partial : VM.t hvalue)
  : option (VM.t hvalue) :=
  match ssl with
  | Qnil => Some partial
  | Qcons st tl =>
      match st with
      | Sskip => statements_initial_map_with_memory mml tl previous partial
      | Swire v t => statements_initial_map_with_memory mml tl previous (VM.add v (Needtobedefined t) partial)
      | Sreg v rt =>
          match previous with
          | None => statements_initial_map_with_memory mml tl previous (VM.add v (Uninitialized (type rt)) partial)
          | Some pm => match VM.find v pm with
                       | Some x => statements_initial_map_with_memory mml tl previous (VM.add v x partial)
                       | None => None end
          end
      | Smem v fm =>
          let ports := VM.add v (memory_bundle_initial fm) partial in
          match previous with
          | None => statements_initial_map_with_memory mml tl previous
              (VM.add (storage_id fm)
                (Aval (data_type fm) (create_undef_array_value Uninitialized (data_type fm) (depth fm))) ports)
          | Some pm => match VM.find (storage_id fm) pm with
              | Some contents => statements_initial_map_with_memory mml tl previous
                  (VM.add (storage_id fm) contents ports)
              | None => None end
          end
      | Sinst ii mi =>
          match module_type mml mi with
          | Some t => statements_initial_map_with_memory mml tl previous (VM.add ii (Needtobedefined t) partial)
          | None => None end
      | Snode v e =>
          match eval_type_of_expr e partial with
          | Some t => statements_initial_map_with_memory mml tl previous (VM.add v (Needtobedefined t) partial)
          | None => None end
      | Sfcnct _ _ | Sinvalid _ => statements_initial_map_with_memory mml tl previous partial
      | Swhen _ yes no =>
          match statements_initial_map_with_memory mml yes previous partial with
          | Some p1 => match statements_initial_map_with_memory mml no previous p1 with
                       | Some p2 => statements_initial_map_with_memory mml tl previous p2
                       | None => None end
          | None => None end
      end
  end.

Definition module_initial_map_with_memory
  (mml : seq HiF.hfmodule) (ii : seq VarOrder.T) (mi : VarOrder.T)
  (previous : option (SVM.t (VM.t hvalue)))
  (partial : SVM.t (VM.t hvalue)) : option (SVM.t (VM.t hvalue)) :=
  match find_module mml mi with
  | Some (FInmod _ ppl ssl) =>
      let base := ports_initial_map ppl in
      let prev_map := match previous with | Some pm => SVM.find ii pm | None => None end in
      match statements_initial_map_with_memory mml ssl prev_map base with
      | Some state => Some (SVM.add ii state partial)
      | None => None end
  | _ => None
  end.

Definition circuit_initial_map_with_memory
  (mml : seq HiF.hfmodule) (mi_top : VarOrder.T)
  (previous : option (SVM.t (VM.t hvalue)))
  (external_inputs : VM.t hvalue)
  : option (SVM.t (VM.t hvalue)) :=
  match find_circuit_instances mml mi_top with
  | Some fci =>
      match SVM.fold
        (fun (ii : SVM.key) (mi : VarOrder.T)
             (acc : option (SVM.t (VM.t hvalue))) =>
          match acc with
          | Some a => match module_initial_map_with_memory mml ii mi previous a with
                      | Some a' => Some a' | None => None end
          | None => None end)
        fci (Some (SVM.empty (VM.t hvalue))) with
      | Some initial =>
          match SVM.find [::] initial, find_module mml mi_top with
          | Some top, Some (FInmod _ ppl _) =>
              match update_external_ports top external_inputs ppl with
              | Some top' => Some (SVM.add [::] top' initial)
              | None => None end
          | _, _ => None end
      | None => None end
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
  match circuit_initial_map_with_memory mml mi_top previous_cycle_register_map external_inputs,
        circuit_iter_count_with_memory mml Gtyp_connect_count with
  | Some initial_states, Some n =>
      match circuit_value_iterator_with_memory mml mi_top n initial_states with
      | Some stabilized => circuit_value_iter_with_memory mml mi_top stabilized true
      | None => None
      end
  | _, _ => None
  end.

(* Reset values are evaluated in the initial input environment. *)
Fixpoint reset_zero (t : ftype) : hvalue :=
  match t with
  | Gtyp g => match g with
               | Fuint w => Gval g (zeros w)
               | Fsint w => Gval g (zeros w)
               | _ => Gval g [:: false]
               end
  | Atyp elt n => Aval elt ((fix fill n := match n with
      | 0 => Anil | S k => Acons (reset_zero elt) (fill k) end) n)
  | Btyp fs => Bval (reset_zero_fields fs)
  end
with reset_zero_fields (fs : ffield) : bundle_value :=
  match fs with
  | Fnil => Bnil
  | Fflips v f t tl => Bflips v f (reset_zero t) (reset_zero_fields tl)
  end.

Fixpoint reset_registers (mm : memory_map) (ssl : HiF.hfstmt_seq)
  (env state : VM.t hvalue) : option (VM.t hvalue) :=
  match ssl with
  | Qnil => Some state
  | Qcons st tl =>
      let next := match st with
      | Sreg v r =>
          match reset r with
          | NRst => Some (VM.add v (reset_zero (type r)) state)
          | Rst _ e => match eval_hfexpr_with_memory mm e env env with
              | Some value => option_map (fun value => VM.add v value state)
                  (adapt_hvalue_as_type value (type r))
              | None => None end
          end
      | Swhen _ yes no => match reset_registers mm yes env state with
          | Some state' => reset_registers mm no env state'
          | None => None end
      | _ => Some state end in
      match next with
      | Some state' => reset_registers mm tl env state'
      | None => None end
  end.

Definition circuit_reset_state (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (initial_inputs : VM.t hvalue) : option (SVM.t (VM.t hvalue)) :=
  match circuit_initial_map_with_memory mml top None initial_inputs,
        find_circuit_instances mml top with
  | Some initial, Some instances =>
      SVM.fold (fun path mi acc =>
        match acc, SVM.find path initial, find_module mml mi with
        | Some states, Some env, Some (FInmod _ _ stmts) =>
            match reset_registers (memory_map_of_stmts stmts) stmts env env with
            | Some state => Some (SVM.add path state states)
            | None => None end
        | _, _, _ => None end) instances (Some initial)
  | _, _ => None end.

(* k steps consume inputs 0, ..., k-1; k=0 returns the reset state. *)
Fixpoint circuit_run (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (initial : SVM.t (VM.t hvalue)) (inputs : nat -> VM.t hvalue)
  (k : nat) : option (SVM.t (VM.t hvalue)) :=
  match k with
  | 0 => Some initial
  | S n => match circuit_run mml top initial inputs n with
      | Some previous => circuit_value_with_memory mml top (Some previous) (inputs n)
      | None => None end
  end.

Definition circuit_run_from_reset (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (inputs : nat -> VM.t hvalue) (k : nat) :=
  match circuit_reset_state mml top (inputs 0) with
  | Some initial => circuit_run mml top initial inputs k
  | None => None end.

(* An initial memory value is a parameter, not an unknown hvalue.  The keys
   are the instance path, visible memory identifier, and a leaf location:
   [cell address; nested bundle fields / array indices].  Each leaf receives
   the low [sizeof_fgtyp] bits of its independently chosen natural number. *)
Definition memory_initialization :=
  seq VarOrder.T -> VarOrder.T -> seq VarOrder.T -> N.

(* Called only while constructing the initial reset state. Later cycles copy
   the previous private storage, including writes, through the existing path. *)
Fixpoint initialize_module_memories (contents : memory_initialization)
  (path : seq VarOrder.T) (stmts : HiF.hfstmt_seq) (env : VM.t hvalue)
  : VM.t hvalue :=
  match stmts with
  | Qnil => env
  | Qcons stmt rest =>
      let next := match stmt with
      | Smem mem fm => VM.add (storage_id fm)
          (memory_initial_value (contents path mem)
            (Atyp (data_type fm) (depth fm)) [::]) env
      | Swhen _ yes no => initialize_module_memories contents path no
          (initialize_module_memories contents path yes env)
      | _ => env
      end in
      initialize_module_memories contents path rest next
  end.

Definition circuit_reset_state_with_memory_init
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (contents : memory_initialization) (initial_inputs : VM.t hvalue)
  : option (SVM.t (VM.t hvalue)) :=
  match circuit_initial_map_with_memory mml top None initial_inputs,
        find_circuit_instances mml top with
  | Some initial, Some instances =>
      SVM.fold (fun path mi acc =>
        match acc, SVM.find path initial, find_module mml mi with
        | Some states, Some env, Some (FInmod _ _ stmts) =>
            let seeded := initialize_module_memories contents path stmts env in
            match reset_registers (memory_map_of_stmts stmts) stmts seeded seeded with
            | Some state => Some (SVM.add path state states)
            | None => None end
        | _, _, _ => None end) instances (Some initial)
  | _, _ => None end.

Definition circuit_run_from_reset_with_memory_init
  (mml : seq HiF.hfmodule) (top : VarOrder.T) (contents : memory_initialization)
  (inputs : nat -> VM.t hvalue) (k : nat) :=
  match circuit_reset_state_with_memory_init mml top contents (inputs 0) with
  | Some initial => circuit_run mml top initial inputs k
  | None => None end.

(* Source choices are indexed by cycle, instance path, static statement
   address, and aggregate leaf. Fanout copies the selected value; it does
   not request another choice. A caller may choose time-invariant values,
   but the universally quantified interface also permits time variation. *)
Definition invalid_choices :=
  nat -> seq VarOrder.T -> seq nat -> seq VarOrder.T -> N.

Definition chosen_invalid_policy (choices : invalid_choices) (cycle : nat)
  (instance : SVM.key) : invalid_value_policy :=
  fun site t => memory_initial_value (choices cycle instance site) t [::].

Definition circuit_value_iter_with_choices
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (choices : invalid_choices) (cycle : nat)
  (states : SVM.t (VM.t hvalue)) (set_regs : bool) :=
  circuit_value_iter_with_memory_policy (chosen_invalid_policy choices cycle)
    mml top states set_regs.

Fixpoint circuit_value_iterator_with_choices
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (choices : invalid_choices) (cycle remaining : nat)
  (states : SVM.t (VM.t hvalue)) : option (SVM.t (VM.t hvalue)) :=
  match remaining with
  | O => Some states
  | S n =>
      match circuit_value_iter_with_choices mml top choices cycle states false with
      | Some next => circuit_value_iterator_with_choices mml top choices cycle n next
      | None => None
      end
  end.

Definition circuit_value_with_choices
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (choices : invalid_choices) (cycle : nat)
  (previous : option (SVM.t (VM.t hvalue))) (inputs : VM.t hvalue) :=
  match circuit_initial_map_with_memory mml top previous inputs,
        circuit_iter_count_with_memory mml Gtyp_connect_count with
  | Some initial, Some n =>
      match circuit_value_iterator_with_choices mml top choices cycle n initial with
      | Some stable => circuit_value_iter_with_choices mml top choices cycle stable true
      | None => None
      end
  | _, _ => None
  end.

Fixpoint circuit_run_with_choices
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (choices : invalid_choices) (initial : SVM.t (VM.t hvalue))
  (inputs : nat -> VM.t hvalue) (k : nat) : option (SVM.t (VM.t hvalue)) :=
  match k with
  | O => Some initial
  | S n =>
      match circuit_run_with_choices mml top choices initial inputs n with
      | Some previous => circuit_value_with_choices mml top choices n (Some previous) (inputs n)
      | None => None
      end
  end.

Definition circuit_run_from_reset_with_choices
  (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (contents : memory_initialization) (choices : invalid_choices)
  (inputs : nat -> VM.t hvalue) (k : nat) :=
  match circuit_reset_state_with_memory_init mml top contents (inputs O) with
  | Some initial => circuit_run_with_choices mml top choices initial inputs k
  | None => None
  end.

(* ChiselTest 0.6 / FIRRTL 1.6 formal model: a DefRandom is a named
   bit-vector input, not a probability distribution or an invalid marker.
   The subtype enforces its width; design assumptions constrain the trace. *)
Definition symbolic_word (width : nat) := { value : bits | size value = width }.
Definition symbolic_inputs :=
  SVM.key -> seq nat -> seq VarOrder.T -> forall width, symbolic_word width.
Record formal_inputs := {
  formal_external_inputs : VM.t hvalue;
  formal_symbolic_inputs : symbolic_inputs
}.

Definition symbolic_word_of_N (width : nat) (value : N) : symbolic_word width :=
  exist _ (from_N width value) (size_from_N width value).

(* Adapter for existing concrete simulations; formal theorems quantify the
   bounded inputs directly, independently at every cycle. *)
Definition formal_input_of_choices (choices : invalid_choices)
  (inputs : nat -> VM.t hvalue) (cycle : nat) : formal_inputs :=
  {| formal_external_inputs := inputs cycle;
     formal_symbolic_inputs := fun path site leaf width =>
       symbolic_word_of_N width (choices cycle path site leaf) |}.

Definition formal_invalid_policy (inputs : formal_inputs) (path : SVM.key)
  : invalid_value_policy :=
  fun site t => input_value_of_type
    (fun leaf width => proj1_sig (formal_symbolic_inputs inputs path site leaf width)) t [::].

Fixpoint circuit_formal_iterations (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (inputs : formal_inputs) (n : nat) (states : SVM.t (VM.t hvalue)) :=
  match n with
  | O => Some states
  | S rest =>
    match circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
      mml top states false with
    | Some next => circuit_formal_iterations mml top inputs rest next
    | None => None
    end
  end.

Definition circuit_formal_cycle (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (previous : option (SVM.t (VM.t hvalue))) (inputs : formal_inputs) :=
  match circuit_initial_map_with_memory mml top previous (formal_external_inputs inputs),
        circuit_iter_count_with_memory mml Gtyp_connect_count with
  | Some initial, Some n =>
    match circuit_formal_iterations mml top inputs n initial with
    | Some stable => circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
        mml top stable true
    | None => None
    end
  | _, _ => None
  end.

Fixpoint circuit_formal_run (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (initial : SVM.t (VM.t hvalue)) (inputs : nat -> formal_inputs) (k : nat) :=
  match k with
  | O => Some initial
  | S n => match circuit_formal_run mml top initial inputs n with
    | Some previous => circuit_formal_cycle mml top (Some previous) (inputs n)
    | None => None
    end
  end.

Definition circuit_formal_run_from_reset (mml : seq HiF.hfmodule) (top : VarOrder.T)
  (memory_init : memory_initialization) (inputs : nat -> formal_inputs) (k : nat) :=
  match circuit_reset_state_with_memory_init mml top memory_init
    (formal_external_inputs (inputs O)) with
  | Some initial => circuit_formal_run mml top initial inputs k
  | None => None
  end.

(* Constraints apply after every consumed input cycle (states 1..k).
   State 0 is the structural reset initializer, before combinational
   evaluation, not a sampled formal step. None is a failure, not a successful
   check. No extra range or stability assumptions are invented. *)
Definition trace_satisfies {State : Type} (run : nat -> option State)
  (constraint : State -> Prop) (k : nat) : Prop :=
  forall j, (0 < j)%coq_nat -> (j <= k)%coq_nat -> exists states,
    run j = Some states /\ constraint states.

Lemma trace_satisfies_at {State : Type} (run : nat -> option State)
  constraint k j states :
  trace_satisfies run constraint k -> (0 < j)%coq_nat -> (j <= k)%coq_nat ->
  run j = Some states -> constraint states.
Proof.
 intros H Positive Bound Run. destruct (H j Positive Bound) as [actual [Eq Holds]].
 rewrite Run in Eq. inversion Eq; subst. exact Holds.
Qed.

Lemma trace_satisfies_prefix {State : Type} (run : nat -> option State)
  constraint k n :
  trace_satisfies run constraint k -> (n <= k)%coq_nat ->
  trace_satisfies run constraint n.
Proof.
 intros H Bound j Positive Earlier. apply H; [exact Positive|].
 exact (Nat.le_trans _ _ _ Earlier Bound).
Qed.
