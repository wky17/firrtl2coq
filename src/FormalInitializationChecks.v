From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory
  FormalInitialization.
Local Open Scope N_scope.

Definition init_ref id : @hfexpr VarOrder.T := @Eref VarOrder.T (@Eid VarOrder.T id).
Definition init_bit b : @hfexpr VarOrder.T := @Econst VarOrder.T (Fuint 1) [:: b].
Definition init_reg id : @hfstmt VarOrder.T := @Sreg VarOrder.T id
  (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (init_ref 0)
    (@Rst VarOrder.T (init_bit false) (init_ref id))).
(* Low FIRRTL reset is a next-state mux, not the declaration's self reset. *)
Definition init_stmts : @hfstmt_seq VarOrder.T :=
  @Qcons VarOrder.T (init_reg 3)
  (@Qcons VarOrder.T (init_reg 4)
  (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 3)
    (@Emux VarOrder.T (init_ref 1) (init_bit false) (init_ref 3)))
  (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 4)
    (@Emux VarOrder.T (init_ref 2) (init_bit false) (init_ref 4))) (@Qnil VarOrder.T)))).
Definition init_modules := [:: @FInmod VarOrder.T 0
  [:: @Finput VarOrder.T 0 (Gtyp Fclock);
      @Finput VarOrder.T 1 (Gtyp (Fuint 1));
      @Finput VarOrder.T 2 (Gtyp (Fuint 1))] init_stmts].
Definition init_inputs (seed : N) (enable : bool) : formal_inputs :=
  {| formal_external_inputs := VM.add 0 (Gval Fclock [::true])
      (VM.add 1 (Gval (Fuint 1) [::false])
      (VM.add 2 (Gval (Fuint 1) [::enable]) (VM.empty _)));
     formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width seed |}.
Definition init_read (result : option (SVM.t (VM.t hvalue))) :=
  match result with
  | Some states => match SVM.find [::] states with
    | Some state => (VM.find 3 state, VM.find 4 state)
    | None => (None,None) end
  | None => (None,None) end.
Definition init_run seed enable k :=
  formal_run_after_reset init_modules 0 1 (Fuint 1) (fun _ _ _ => 0)
    (fun _ => init_inputs seed enable) k.
Definition init_value b := Some (Gval (Fuint 1) [::b]).
Example true_reset_edge_preserves_arbitrary_unreset_register :
  init_read (init_run 1 false 0) = (init_value false, init_value true).
Proof. vm_compute. reflexivity. Qed.
Example second_initial_choice_remains_possible :
  init_read (init_run 0 false 0) = (init_value false, init_value false).
Proof. vm_compute. reflexivity. Qed.
Example ordinary_edge_copies_registers_without_resampling :
  init_read (init_run 1 false 1) = (init_value false, init_value true).
Proof. vm_compute. reflexivity. Qed.
Example reset_edge_does_not_constrain_data_enable :
  init_read (init_run 1 true 0) = (init_value false, init_value false).
Proof. vm_compute. reflexivity. Qed.
Example legitimate_input_domain :
  formal_external_inputs_defined init_modules 0 (init_inputs 1 false) = true.
Proof. vm_compute. reflexivity. Qed.
Example unknown_input_is_not_a_bitvector :
  known_input_value true (Uninitialized (Gtyp (Fuint 1))) (Gtyp (Fuint 1)) = false.
Proof. reflexivity. Qed.
Example wrong_input_width_is_rejected :
  known_input_value true (Gval (Fuint 2) [::true]) (Gtyp (Fuint 2)) = false.
Proof. reflexivity. Qed.
Definition aggregate_input_type := Btyp (Fflips 7 Nflip (Atyp (Gtyp (Fuint 2)) 1)
  (Fflips 8 Flipped (Gtyp (Fuint 1)) Fnil)).
Definition aggregate_input_value := Bval (Bflips 7 Nflip
  (Aval (Gtyp (Fuint 2)) (Acons (Gval (Fuint 2) [::true;false]) Anil))
  (Bflips 8 Flipped (Uninitialized (Gtyp (Fuint 1))) Bnil)).
Example aggregate_input_leaves_defined_output_leaves_ignored :
  known_input_value true aggregate_input_value aggregate_input_type = true.
Proof. reflexivity. Qed.
Example flipped_input_leaf_must_be_defined :
  known_input_value false aggregate_input_value aggregate_input_type = false.
Proof. reflexivity. Qed.
Print Assumptions true_reset_edge_preserves_arbitrary_unreset_register.
Print Assumptions ordinary_edge_copies_registers_without_resampling.
Print Assumptions reset_edge_does_not_constrain_data_enable.

Definition separated_symbolic_inputs : formal_inputs :=
 {| formal_external_inputs := formal_external_inputs (init_inputs 0 false);
    formal_symbolic_inputs := fun _ site _ width =>
      symbolic_word_of_N width (if size site == 2%nat then 1 else 0) |}.
Example initialization_and_invalid_namespaces_are_distinct :
  symbolic_register_value separated_symbolic_inputs [::] 4 (Gtyp (Fuint 1)) = Gval (Fuint 1) [::true] /\
  formal_invalid_policy separated_symbolic_inputs [::] [::0%nat] (Gtyp (Fuint 1)) = Gval (Fuint 1) [::false].
Proof. vm_compute. split; reflexivity. Qed.

Definition independent_reset_and_normal_inputs n :=
  match n with O => init_inputs 1 false | S _ => init_inputs 0 true end.
Example reset_and_normal_enables_are_independent :
  let run := formal_run_after_reset init_modules 0 1 (Fuint 1)
    (fun _ _ _ => 0) independent_reset_and_normal_inputs in
  (init_read (run 0), init_read (run 1)) =
    ((init_value false, init_value true), (init_value false, init_value false)).
Proof. vm_compute. reflexivity. Qed.
