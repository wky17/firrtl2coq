From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.

(* Every bit vector of the declared width is an admissible input. *)
Lemma dontcare_accepts_every_word width (word : bits) (bounded : size word = width) :
 exists inputs : formal_inputs, forall path site,
 formal_invalid_policy inputs path site (Gtyp (Fuint width)) =
 Gval (Fuint width) word.
Proof.
 exists {| formal_external_inputs := VM.empty hvalue;
           formal_symbolic_inputs := fun _ _ _ w =>
             match Nat.eq_dec w width with
             | left equal => exist _ word (Logic.eq_trans bounded (Logic.eq_sym equal))
             | right _ => symbolic_word_of_N w 0
             end |}.
 intros path site. unfold formal_invalid_policy. cbn [input_value_of_type sizeof_fgtyp formal_symbolic_inputs].
 destruct (Nat.eq_dec width width); [reflexivity|contradiction].
Qed.

(* Re-reading one source in one cycle cannot choose a new value. *)
Lemma dontcare_same_source inputs path site width :
 formal_invalid_policy inputs path site (Gtyp (Fuint width)) =
 Gval (Fuint width)
   (proj1_sig (formal_symbolic_inputs inputs path site [::] width)).
Proof. reflexivity. Qed.

Lemma dontcare_width_is_enforced inputs path site leaf width :
 size (proj1_sig (formal_symbolic_inputs inputs path site leaf width)) = width.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path site leaf width)). Qed.

Print Assumptions dontcare_accepts_every_word.

(* Identical statement positions in separate instances are independent. *)
Definition instance_check_inputs : formal_inputs :=
 {| formal_external_inputs := VM.empty hvalue;
    formal_symbolic_inputs := fun path _ _ width =>
      symbolic_word_of_N width (head (N.of_nat 0) path) |}.

Example dontcare_instance_independence :
 (formal_invalid_policy instance_check_inputs [:: N.of_nat 1] [:: 0]
    (Gtyp (Fuint 2)),
  formal_invalid_policy instance_check_inputs [:: N.of_nat 2] [:: 0]
    (Gtyp (Fuint 2))) =
 (Gval (Fuint 2) [:: true; false],
  Gval (Fuint 2) [:: false; true]).
Proof. vm_compute. reflexivity. Qed.

(* Execute real invalid statements, then copy their values through the
   snapshot-based evaluator. Sources differ by static statement position. *)
Import HiFirrtl_with_implicit_widths.
Definition check_inputs (cycle : nat) : formal_inputs :=
 {| formal_external_inputs := VM.empty hvalue;
    formal_symbolic_inputs := fun _ site _ width =>
      symbolic_word_of_N width (N.of_nat (cycle + head 0 site)) |}.
Definition check_initial :=
 VM.add (N.of_nat 2) (Needtobedefined (Gtyp (Fuint 2)))
 (VM.add (N.of_nat 1) (Needtobedefined (Gtyp (Fuint 2))) (VM.empty hvalue)).
Definition check_program : @hfstmt_seq VarOrder.T :=
 @Qcons VarOrder.T (@Sinvalid VarOrder.T (@Eid VarOrder.T (N.of_nat 1)))
 (@Qcons VarOrder.T (@Sinvalid VarOrder.T (@Eid VarOrder.T (N.of_nat 2)))
 (@Qcons VarOrder.T (@Snode VarOrder.T (N.of_nat 3) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 1))))
 (@Qcons VarOrder.T (@Snode VarOrder.T (N.of_nat 4) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 1)))) (@Qnil VarOrder.T)))).
Definition check_round cycle old :=
 value_iter_statements_with_memory_policy
   (formal_invalid_policy (check_inputs cycle) [:: (N.of_nat 0)]) [::] 0
   (VM.empty memory_layout) old false old check_program.
Definition check_observe (result : option (VM.t hvalue)) :=
 match result with
 | Some env => (VM.find (N.of_nat 1) env, VM.find (N.of_nat 2) env,
                VM.find (N.of_nat 3) env, VM.find (N.of_nat 4) env)
 | None => (None, None, None, None)
 end.
Definition check_two_rounds cycle :=
 match check_round cycle check_initial with
 | Some first => check_round cycle first
 | None => None
 end.

(* Distinct sources can differ; both readers of source 1 agree. *)
Example dontcare_execution_sharing :
 check_observe (check_two_rounds 2) =
 (Some (Gval (Fuint 2) [:: false; true]),
  Some (Gval (Fuint 2) [:: true; true]),
  Some (Gval (Fuint 2) [:: false; true]),
  Some (Gval (Fuint 2) [:: false; true])).
Proof. vm_compute. reflexivity. Qed.

(* A new cycle may supply different values for the same sources. *)
Example dontcare_execution_next_cycle :
 check_observe (check_two_rounds 1) =
 (Some (Gval (Fuint 2) [:: true; false]),
  Some (Gval (Fuint 2) [:: false; true]),
  Some (Gval (Fuint 2) [:: true; false]),
  Some (Gval (Fuint 2) [:: true; false])).
Proof. vm_compute. reflexivity. Qed.

(* A later good state cannot erase an earlier violated assumption. *)
Example formal_assumptions_are_historical :
 ~ trace_satisfies (fun n => Some n) (fun n => n <> 1) 2.
Proof.
 intro H. destruct (H 1) as [state [Run Constraint]]; try lia.
 inversion Run; subst. apply Constraint. reflexivity.
Qed.
