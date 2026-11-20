From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths LoCircuit.
Module LoVerification.
Module C := LoCircuit.
Fixpoint child_module (i : VarOrder.T) (ss : seq C.stmt) : option VarOrder.T :=
 match ss with
 | [::] => None
 | Sinst inst :: tl => if iid inst == i then Some (imid inst) else child_module i tl
 | _ :: tl => child_module i tl end.
Fixpoint module_at (ms : seq C.modul) (mi : VarOrder.T) (p : C.path) : option VarOrder.T :=
 match p with
 | [::] => Some mi
 | i :: tl => match C.find_module mi ms with
   | Some (FInmod _ _ ss) => match child_module i ss with
     | Some child => module_at ms child tl | None => None end
   | _ => None end end.
(* Reconstruct node types, including forward references, from explicit declarations. *)
Definition node_types (ss : seq C.stmt) te := List.fold_left (fun env st =>
 match st with Snode v e => TE.add v (LoFirrtl.type_of_fexpr e env) env | _ => env end) ss te.
Fixpoint complete_types n ss te := match n with
 | 0 => te | S k => complete_types k ss (node_types ss te) end.
Definition expr_true (ps : seq C.port) (ss : seq C.stmt)
 (e : fexpr VarOrder.T) (s : C.module_state) : Prop :=
 let te := complete_types (size ss) ss (C.type_env ps ss) in
 LoFirrtl.type_of_fexpr e te = Fuint 1 /\ C.value e (C.current_values s) te = [::true].
Definition local_property ps ss en predicate s : Prop :=
 expr_true ps ss en s -> expr_true ps ss predicate s.
Definition all_instances (c : C.circuit) (mi : VarOrder.T)
 (en predicate : fexpr VarOrder.T) (states : C.circuit_state) : Prop :=
 let '(Fcircuit top ms) := c in
 forall path, module_at ms top path = Some mi ->
 match C.find_module mi ms, C.state_at path states with
 | Some (FInmod _ ps ss), Some state => local_property ps ss en predicate state
 | _, _ => False end.
(* Each nonempty prefix uses the same first sample for reset as the full run.
   Failed prefix execution makes the obligation false, never vacuously true.
   The reset-only state (prefix length zero) is deliberately excluded. *)
Definition assumptions_along (c : C.circuit)
  (inputs : seq (VarOrder.T * seq bits))
  (holds : C.circuit_state -> Prop) : Prop :=
  let n := match inputs with [::] => 0 | (_, values) :: _ => size values end in
  forall j : nat, 0 < j -> j <= n ->
    match C.run_circuit c (map (fun kv => (fst kv, take j (snd kv))) inputs) with
    | Some result => holds (C.final_state result)
    | None => False
    end.
End LoVerification.
