From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths LoCircuit TestAdder.
Import LoCircuit.LoCircuit.
Local Open Scope N_scope.
Local Notation "'Finput'" := (@Finput VarOrder.T).
Local Notation "'Foutput'" := (@Foutput VarOrder.T).
Local Notation "'FInmod'" := (@FInmod VarOrder.T).
Local Notation "'Fcircuit'" := (@Fcircuit VarOrder.T).
Local Notation "'Sreg'" := (@Sreg VarOrder.T).
Local Notation "'Sinst'" := (@Sinst VarOrder.T).
Local Notation "'Sfcnct'" := (@Sfcnct VarOrder.T).
Local Notation "'Smem'" := (@Smem VarOrder.T).
Local Notation "'Econst'" := (@Econst VarOrder.T).
Local Notation "'Rst'" := (@Rst VarOrder.T).
Definition byte n := from_nat 8 n.
Definition eref (v : VarOrder.T) := @Eref VarOrder.T v.
Definition lit n := @Econst VarOrder.T (Fuint 8) (byte n).
Definition top_result c inputs :=
  match run_circuit c inputs with
  | Some result => state_at [::] (final_state result)
  | None => None end.
Definition observe c inputs v := option_map (fun st => to_nat (Store.acc v (current_values st))) (top_result c inputs).
Definition observe_next c inputs v := option_map (fun st => to_nat (Store.acc v (next_registers st))) (top_result c inputs).
Example adder_runs : observe adder_circuit [::(2,[::byte 3]); (3,[::byte 4])] 4 = Some 7%nat.
Proof. vm_compute. reflexivity. Qed.
Definition reg_ports : seq port := [:: Finput 0 Fclock; Finput 1 (Fuint 8); Foutput 3 (Fuint 8)].
Definition reg_stmts : seq stmt := [::
  Sreg (@mk_freg VarOrder.T 2 (Fuint 8) 0 (Rst (Econst (Fuint 1) [::false]) (lit 5)));
  Sfcnct 3 (eref 2); Sfcnct 2 (eref 1)].
Definition reg_circuit : circuit := Fcircuit 10 [:: FInmod 10 reg_ports reg_stmts].
Definition reg_inputs := [::(0,[::[::true];[::true]]);(1,[::byte 11;byte 22])].
Example register_current : observe reg_circuit reg_inputs 3 = Some 11%nat.
Proof. vm_compute. reflexivity. Qed.
Example register_next : observe_next reg_circuit reg_inputs 2 = Some 22%nat.
Proof. vm_compute. reflexivity. Qed.
Example reset_before_first : observe reg_circuit [::(0,[::[::true]]);(1,[::byte 11])] 3 = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.
Example empty_returns_reset : observe_next reg_circuit [::(0,[::]);(1,[::])] 2 = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.
Example invalid_width : run_circuit reg_circuit [::(0,[::[::true]]);(1,[::[::true]])] = None.
Proof. vm_compute. reflexivity. Qed.
Example unequal_lengths : run_circuit reg_circuit [::(0,[::]);(1,[::byte 1])] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_top : run_circuit (Fcircuit 99 [::FInmod 10 reg_ports reg_stmts]) reg_inputs = None.
Proof. vm_compute. reflexivity. Qed.
Definition twin_ports : seq port := [::Finput 0 Fclock; Finput 1 (Fuint 8); Finput 2 (Fuint 8); Foutput 3 (Fuint 8); Foutput 4 (Fuint 8)].
Definition twin_stmts : seq stmt := [::
  Sinst (@mk_finst VarOrder.T 20 10 [::Finput 21 Fclock; Finput 22 (Fuint 8); Foutput 23 (Fuint 8)]);
  Sinst (@mk_finst VarOrder.T 30 10 [::Finput 31 Fclock; Finput 32 (Fuint 8); Foutput 33 (Fuint 8)]);
  Sfcnct 21 (eref 0); Sfcnct 22 (eref 1); Sfcnct 31 (eref 0); Sfcnct 32 (eref 2);
  Sfcnct 3 (eref 23); Sfcnct 4 (eref 33)].
Definition twins : circuit := Fcircuit 40 [::FInmod 40 twin_ports twin_stmts; FInmod 10 reg_ports reg_stmts].
Definition twin_inputs := [::(0,[::[::true];[::true]]);(1,[::byte 11;byte 12]);(2,[::byte 21;byte 22])].
Example independent_instances : (observe twins twin_inputs 3, observe twins twin_inputs 4) = (Some 11%nat,Some 21%nat).
Proof. vm_compute. reflexivity. Qed.
Definition mem_ports : seq port := [::Finput 0 Fclock; Finput 1 (Fuint 8); Finput 2 (Fuint 1); Foutput 3 (Fuint 8)].
Definition mem_stmts : seq stmt := [::
  Smem (@mk_fmem VarOrder.T 10 (Fuint 8) 2
    [::@mk_freader_port VarOrder.T 11 12 13 14]
    [::@mk_fwriter_port VarOrder.T 15 16 17 18 19] 0 1 old);
  Sfcnct 11 (Econst (Fuint 1) [::false]); Sfcnct 13 (Econst (Fuint 1) [::true]); Sfcnct 14 (eref 0);
  Sfcnct 15 (Econst (Fuint 1) [::false]); Sfcnct 16 (eref 1); Sfcnct 17 (Econst (Fuint 1) [::true]);
  Sfcnct 18 (eref 0); Sfcnct 19 (eref 2); Sfcnct 3 (eref 12)].
Definition mem_circuit : circuit := Fcircuit 50 [::FInmod 50 mem_ports mem_stmts].
Definition mem_inputs := [::(0,[::[::true];[::true]]);(1,[::byte 7;byte 9]);(2,[::[::true];[::false]])].
Example memory_current : observe mem_circuit mem_inputs 3 = Some 7%nat.
Proof. vm_compute. reflexivity. Qed.
Example masked_write_preserves : option_map (fun st => to_nat ((get_memory 10 (next_memories st)) [::false])) (top_result mem_circuit mem_inputs) = Some 7%nat.
Proof. vm_compute. reflexivity. Qed.
Definition cycle_circuit : circuit := Fcircuit 60 [::FInmod 60 [::Foutput 1 (Fuint 8)] [::Sfcnct 1 (eref 1)]].
Example reject_comb_cycle : run_circuit cycle_circuit [::] = None.
Proof. vm_compute. reflexivity. Qed.
Example pending_memory_write : option_map (fun st =>
  (to_nat (get_memory 10 (current_memories st) [::false]),
   to_nat (get_memory 10 (next_memories st) [::false])))
  (top_result mem_circuit [::(0,[::[::true]]);(1,[::byte 7]);(2,[::[::true]])]) = Some (0%nat,7%nat).
Proof. vm_compute. reflexivity. Qed.
Definition sync_stmts : seq stmt := match mem_stmts with
  | Firrtl_with_implicit_widths.Smem m :: tl => Smem (@mk_fmem VarOrder.T 10 (Fuint 8) 2
      [::@mk_freader_port VarOrder.T 11 12 13 14]
      [::@mk_fwriter_port VarOrder.T 15 16 17 18 19] 1 1 old)::tl
  | _ => [::] end.
Definition sync_circuit : circuit := Fcircuit 50 [::FInmod 50 mem_ports sync_stmts].
Example synchronous_read_delay : observe sync_circuit mem_inputs 3 = Some 0%nat.
Proof. vm_compute. reflexivity. Qed.
Example synchronous_read_next : option_map (fun st => to_nat (Store.acc 12 (next_reads st))) (top_result sync_circuit mem_inputs) = Some 7%nat.
Proof. vm_compute. reflexivity. Qed.
Definition wrapper_ports : seq port := [::Finput 0 Fclock; Finput 1 (Fuint 8); Foutput 3 (Fuint 8)].
Definition wrapper_stmts : seq stmt := [::
  Sinst (@mk_finst VarOrder.T 5 10 [::Finput 6 Fclock; Finput 7 (Fuint 8); Foutput 8 (Fuint 8)]);
  Sfcnct 6 (eref 0); Sfcnct 7 (eref 1); Sfcnct 3 (eref 8)].
Definition nested_twins : circuit := Fcircuit 40
  [::FInmod 40 twin_ports twin_stmts; FInmod 10 wrapper_ports
    [::Sinst (@mk_finst VarOrder.T 5 11 [::Finput 6 Fclock; Finput 7 (Fuint 8); Foutput 8 (Fuint 8)]);
       Sfcnct 6 (eref 0); Sfcnct 7 (eref 1); Sfcnct 3 (eref 8)];
    FInmod 11 reg_ports reg_stmts].
Example nested_instances_independent : (observe nested_twins twin_inputs 3, observe nested_twins twin_inputs 4) = (Some 11%nat,Some 21%nat).
Proof. vm_compute. reflexivity. Qed.
Example nested_next_state :
  match run_circuit nested_twins twin_inputs with
  | Some r => option_map (fun st => to_nat (Store.acc 2 (next_registers st))) (state_at [::30;5] (final_state r))
  | None => None end = Some 22%nat.
Proof. vm_compute. reflexivity. Qed.
Definition async_circuit : circuit := Fcircuit 70 [::FInmod 70
  [::Finput 0 Fclock; Finput 1 (Fuint 8); Finput 4 Fasyncreset; Foutput 3 (Fuint 8)]
  [::Sreg (@mk_freg VarOrder.T 2 (Fuint 8) 0 (Rst (eref 4) (lit 5)));
     Sfcnct 3 (eref 2); Sfcnct 2 (eref 1)]].
Example async_reset_visible_now : observe async_circuit
  [::(0,[::[::true];[::true]]);(1,[::byte 11;byte 22]);(4,[::[::false];[::true]])] 3 = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_input_rejected : run_circuit reg_circuit [::(0,[::[::true]]);(0,[::[::true]])] = None.
Proof. vm_compute. reflexivity. Qed.
