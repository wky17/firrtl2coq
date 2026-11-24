(* Regression fixture: src/ocaml/test/fixtures/observation.lo.fir.
   Generated definitions below are retained, but no admitted theorem is imported. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_for_circuit Semantics_with_memory FormalInitialization.

Local Open Scope N_scope.

Fixpoint generated_qcat (s1 s2 : hfstmt_seq VarOrder.T) : hfstmt_seq VarOrder.T :=
  match s1 with
  | Qnil => s2
  | Qcons h t => Qcons h (generated_qcat t s2)
  end.

Definition generated_module_0_stmts_0 : hfstmt_seq VarOrder.T :=
  (@Qcons VarOrder.T (@Sreg VarOrder.T 5 (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 0)) (Rst (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false])))) (@Qcons VarOrder.T (@Sreg VarOrder.T 6 (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 0)) (Rst (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false])))) (@Qcons VarOrder.T (@Snode VarOrder.T 7 (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 6)))) (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 3) (@Econst VarOrder.T (Fuint 1) [::true])) (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Econst VarOrder.T (Fuint 1) [::true])) (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 3))) (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 4))) (@Qnil VarOrder.T)))))))).

Definition generated_module_0 : @hfmodule VarOrder.T :=
  (@FInmod VarOrder.T 0 [:: (@Finput VarOrder.T 0 (Gtyp Fclock));
(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));
(@Finput VarOrder.T 2 (Gtyp (Fuint 1)));
(@Foutput VarOrder.T 3 (Gtyp (Fuint 1)));
(@Foutput VarOrder.T 4 (Gtyp (Fuint 1)))] generated_module_0_stmts_0).

Definition generated_modules : seq (@hfmodule VarOrder.T) :=
  [:: generated_module_0].

Definition generated_top := 0.
Definition generated_circuit : @hfcircuit VarOrder.T :=
  (@Fcircuit VarOrder.T generated_top generated_modules).

(* Generated verification properties. *)
Definition generated_hvalue_true (v : Semantics_with_implicit_widths.hvalue) : Prop := match v with | Semantics_with_implicit_widths.Gval (Env_with_implicit_widths.Fuint 1) b => b != [:: false] | _ => False end.
Definition generated_expr_true (e : (@HiFirrtl_with_implicit_widths.hfexpr VarOrder.T)) (sem : Var.VM.t Semantics_with_implicit_widths.hvalue) : Prop := match Semantics_with_implicit_widths.eval_hfexpr e sem sem with | Some v => generated_hvalue_true v | None => False end.
(* Memory contents are chosen once; explicit invalid sources have universally quantified per-cycle choices. *)
(* Real reset edge after arbitrary symbolic register initialization; then k ordinary edges. *)
Definition generated_reset_id : VarOrder.T := 1.
Definition generated_reset_type : fgtyp := (Fuint 1).
Definition generated_initial_state (memory_init : memory_initialization) (inputs : formal_inputs) := formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory_init inputs.
Definition generated_run_with_choices (memory_init : memory_initialization) (choices : invalid_choices) (inputs : nat -> Var.VM.t Semantics_with_implicit_widths.hvalue) (k : nat) := formal_run_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory_init (formal_input_of_choices choices inputs) k.
Definition generated_run (memory_init : memory_initialization) (inputs : nat -> formal_inputs) (k : nat) := formal_run_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory_init inputs k.
Definition generated_observation_input (inputs : nat -> formal_inputs) (k : nat) := inputs (S k).
(* Observation k is before the next ordinary edge. Reset-bearing tops reserve input 0 for reset and use input (S k). *)
(* Both initialization and ordinary edges use the original hierarchical cycle interpreter. *)
Definition generated_observe_cycle (previous : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) (inputs : formal_inputs) := match circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs), circuit_iter_count_with_memory generated_modules generated_top Semantics_with_implicit_widths.Gtyp_connect_count with | Some initial, Some n => circuit_formal_iterations generated_modules generated_top inputs n initial | _, _ => None end.
Definition generated_observe (memory_init : memory_initialization) (inputs : nat -> formal_inputs) (k : nat) := match generated_run memory_init inputs k with | Some previous => generated_observe_cycle previous (generated_observation_input inputs k) | None => None end.
Definition generated_circuit_value (memory_init : memory_initialization) (inputs : formal_inputs) := generated_run memory_init (fun _ => inputs) 1.
Fixpoint generated_assert_instances (module_id : VarOrder.T) (p : Var.VM.t Semantics_with_implicit_widths.hvalue -> Prop) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) (xs : list (Semantics_with_implicit_widths.SVM.key * VarOrder.T)) : Prop := match xs with | [::] => True | (path, actual) :: tl => ((actual != module_id) \/ match Semantics_with_implicit_widths.SVM.find path states with | Some sem => p sem | None => False end) /\ generated_assert_instances module_id p states tl end.
Fixpoint generated_assume_instances (module_id : VarOrder.T) (p : Var.VM.t Semantics_with_implicit_widths.hvalue -> Prop) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) (xs : list (Semantics_with_implicit_widths.SVM.key * VarOrder.T)) : Prop := match xs with | [::] => True | (path, actual) :: tl => ((actual != module_id) \/ match Semantics_with_implicit_widths.SVM.find path states with | Some sem => p sem | None => False end) /\ generated_assume_instances module_id p states tl end.
Definition generated_instances (module_id : VarOrder.T) (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assert_instances module_id (fun _ => True) states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.
Definition generated_assert_m0_0_local (sem : Var.VM.t Semantics_with_implicit_widths.hvalue) : Prop := generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 5)) sem -> generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 7)) sem.
Definition generated_assume_m0_0_local (sem : Var.VM.t Semantics_with_implicit_widths.hvalue) : Prop := generated_expr_true (@Econst VarOrder.T (Fuint 1) [::true]) sem -> generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 2)) sem.
Definition generated_assert_m0_0_all (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assert_instances 0 generated_assert_m0_0_local states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.
Definition generated_assume_m0_0_all (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := match Semantics_with_implicit_widths.find_circuit_instances generated_modules generated_top with | Some im => generated_assume_instances 0 generated_assume_m0_0_local states (Semantics_with_implicit_widths.SVM.elements im) | None => False end.
Definition generated_all_assumptions (states : Semantics_with_implicit_widths.SVM.t (Var.VM.t Semantics_with_implicit_widths.hvalue)) : Prop := True /\ generated_assume_m0_0_all states.
(* Assumptions cover observations 0..k, including the same current observation as assertions. *)
Definition generated_legal_trace memory_init inputs (k : nat) : Prop := formal_external_inputs_defined generated_modules generated_top (inputs O) = true /\ forall j, (j <= k)%coq_nat -> formal_external_inputs_defined generated_modules generated_top (generated_observation_input inputs j) = true /\ exists states, generated_observe memory_init inputs j = Some states /\ generated_all_assumptions states.
Definition test_inputs (permit : bool) : formal_inputs :=
 {| formal_external_inputs := VM.add 2 (Semantics_with_implicit_widths.Gval (Fuint 1) [::permit])
     (VM.add 1 (Semantics_with_implicit_widths.Gval (Fuint 1) [::false])
     (VM.add 0 (Semantics_with_implicit_widths.Gval Fclock [::true]) (VM.empty _)));
    formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition test_memory : memory_initialization := fun _ _ _ => 0.
Definition test_state (inputs : nat -> formal_inputs) k :=
 match generated_observe test_memory inputs k with
 | Some s => s | None => Semantics_with_implicit_widths.SVM.empty _ end.
Definition legal_inputs (_ : nat) := test_inputs true.
Example initial_observation : generated_assert_m0_0_all (test_state legal_inputs 0).
Proof. vm_compute. intuition discriminate. Qed.
Example first_observation : generated_assert_m0_0_all (test_state legal_inputs 1).
Proof. vm_compute. intuition discriminate. Qed.
Example second_observation : generated_assert_m0_0_all (test_state legal_inputs 2).
Proof. vm_compute. intuition discriminate. Qed.
Example observation_registers_consistent :
 match Semantics_with_implicit_widths.SVM.find [::] (test_state legal_inputs 1) with
 | Some s => (VM.find 5 s, VM.find 6 s, VM.find 7 s)
 | None => (None,None,None) end =
 (Some (Semantics_with_implicit_widths.Gval (Fuint 1) [::true]),
  Some (Semantics_with_implicit_widths.Gval (Fuint 1) [::true]),
  Some (Semantics_with_implicit_widths.Gval (Fuint 1) [::true])).
Proof. vm_compute. reflexivity. Qed.
Definition illegal_first n := match n with S O => test_inputs false | _ => test_inputs true end.
Example initial_assumption_checked : ~ generated_legal_trace test_memory illegal_first 0.
Proof.
 intros [_ H]; destruct (H O (Nat.le_refl O)) as [_ [s [E Hs]]].
 vm_compute in E. inversion E; subst s. vm_compute in Hs. intuition discriminate.
Qed.
Example historical_assumption_checked : ~ generated_legal_trace test_memory illegal_first 1.
Proof.
 intros [_ H]; destruct (H O (Nat.le_0_l 1)) as [_ [s [E Hs]]].
 vm_compute in E. inversion E; subst s. vm_compute in Hs. intuition discriminate.
Qed.
Print Assumptions first_observation.
Print Assumptions historical_assumption_checked.
