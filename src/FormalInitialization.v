From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Local Open Scope N_scope.

(* The external formal domain consists of concrete, correctly sized bit-vectors.
   Interpreter markers (Needtobedefined, Uninitialized, Undefinedonpurpose) are
   not hardware inputs. Flip directions are followed through nested aggregates;
   output-only leaves impose no restriction on the supplied external map. *)
Definition input_direction (incoming : bool) (flip : fflip) :=
  match flip with Flipped => ~~ incoming | Nflip => incoming end.
Fixpoint type_has_input (incoming : bool) (t : ftype) : bool :=
  match t with
  | Gtyp _ => incoming
  | Atyp elt n => (n != 0%nat) && type_has_input incoming elt
  | Btyp fields => fields_have_input incoming fields
  end
with fields_have_input (incoming : bool) (fields : ffield) : bool :=
  match fields with
  | Fnil => false
  | Fflips _ flip t rest => type_has_input (input_direction incoming flip) t ||
      fields_have_input incoming rest
  end.
Fixpoint known_input_value (incoming : bool) (v : hvalue) (t : ftype) {struct v} : bool :=
  if ~~ type_has_input incoming t then true else
  match v, t with
  | Gval actual bits, Gtyp declared => (actual == declared) && (size bits == sizeof_fgtyp declared)
  | Aval actual values, Atyp declared n => (actual == declared) && known_input_array incoming values declared n
  | Bval values, Btyp fields => known_input_fields incoming values fields
  | _, _ => false
  end
with known_input_array (incoming : bool) (values : array_value) (elt : ftype) (n : nat) {struct values} : bool :=
  match values, n with
  | Anil, O => true
  | Acons v rest, S k => known_input_value incoming v elt && known_input_array incoming rest elt k
  | _, _ => false
  end
with known_input_fields (incoming : bool) (values : bundle_value) (fields : ffield) {struct values} : bool :=
  match values, fields with
  | Bnil, Fnil => true
  | Bflips actual_id actual_flip v rest, Fflips id flip t tail =>
      (actual_id == id) && (actual_flip == flip) &&
      known_input_value (input_direction incoming flip) v t &&
      known_input_fields incoming rest tail
  | _, _ => false
  end.
Definition external_port_defined (external : VM.t hvalue) (port : @hfport VarOrder.T) : bool :=
  let '(id, t, incoming) := match port with
    | Finput id t => (id, t, true) | Foutput id t => (id, t, false) end in
  if type_has_input incoming t then
    match VM.find id external with Some v => known_input_value incoming v t | None => false end
  else true.
Definition formal_external_inputs_defined (modules : seq (@hfmodule VarOrder.T))
  (top : VarOrder.T) (inputs : formal_inputs) : bool :=
  match find_module modules top with
  | Some (FInmod _ ports _) => all (external_port_defined (formal_external_inputs inputs)) ports
  | _ => false
  end.

(* Dedicated initialization namespace: [0; register-id] has even length, while
   invalid statement addresses have length 1 + 2*nesting-depth. Instance paths
   and aggregate leaf paths retain their existing independent indices. Thus
   these arbitrary register choices cannot alias any per-cycle invalid source.
   Only the first cycle's symbolic input supplies power-on values; later cycles
   copy registers via the original interpreter, never choose them again. *)
Definition symbolic_register_value (inputs : formal_inputs) (path : SVM.key)
  (id : VarOrder.T) (t : ftype) : hvalue :=
  input_value_of_type
    (fun leaf width => proj1_sig (formal_symbolic_inputs inputs path [:: 0%nat; N.to_nat id] leaf width)) t [::].
Fixpoint initialize_symbolic_registers (inputs : formal_inputs) (path : SVM.key)
  (stmts : @hfstmt_seq VarOrder.T) (state : VM.t hvalue) : VM.t hvalue :=
  match stmts with
  | Qnil => state
  | Qcons stmt rest =>
      let next := match stmt with
      | Sreg id reg => VM.add id (symbolic_register_value inputs path id (type reg)) state
      | Swhen _ yes no => initialize_symbolic_registers inputs path no
          (initialize_symbolic_registers inputs path yes state)
      | _ => state
      end in initialize_symbolic_registers inputs path rest next
  end.
Definition circuit_symbolic_initial_state (modules : seq (@hfmodule VarOrder.T))
  (top : VarOrder.T) (contents : memory_initialization) (inputs : formal_inputs)
  : option (SVM.t (VM.t hvalue)) :=
  match circuit_initial_map_with_memory modules top None (formal_external_inputs inputs),
        find_circuit_instances modules top with
  | Some initial, Some instances =>
      SVM.fold (fun path module_id acc =>
        match acc, SVM.find path initial, find_module modules module_id with
        | Some states, Some env, Some (FInmod _ _ stmts) =>
            let memories := initialize_module_memories contents path stmts env in
            Some (SVM.add path (initialize_symbolic_registers inputs path stmts memories) states)
        | _, _, _ => None end) instances (Some initial)
  | _, _ => None end.

(* reset_id/type are explicit frontend metadata for the top-level reset port.
   Low FIRRTL may encode reset in next-state muxes, so structural Sreg reset
   initialization is not used. Execute the original cycle interpreter once. *)
Definition force_formal_reset (reset_id : VarOrder.T) (reset_type : fgtyp)
  (inputs : formal_inputs) : formal_inputs :=
  {| formal_external_inputs := VM.add reset_id (Gval reset_type [:: true]) (formal_external_inputs inputs);
     formal_symbolic_inputs := formal_symbolic_inputs inputs |}.
Definition formal_state_after_reset (modules : seq (@hfmodule VarOrder.T))
  (top reset_id : VarOrder.T) (reset_type : fgtyp)
  (contents : memory_initialization) (inputs : formal_inputs) :=
  match circuit_symbolic_initial_state modules top contents inputs with
  | Some initial => circuit_formal_cycle modules top (Some initial) (force_formal_reset reset_id reset_type inputs)
  | None => None end.
(* Input 0 is used only for initialization/reset. Ordinary cycle n consumes
   input (S n), so reset and post-reset symbolic choices remain independent. *)
Definition formal_run_after_reset (modules : seq (@hfmodule VarOrder.T))
  (top reset_id : VarOrder.T) (reset_type : fgtyp)
  (contents : memory_initialization) (inputs : nat -> formal_inputs) (k : nat) :=
  match formal_state_after_reset modules top reset_id reset_type contents (inputs O) with
  | Some initial => circuit_formal_run modules top initial (fun n => inputs (S n)) k
  | None => None end.
