(* A node reads the previous iteration's environment.  A long node chain
   therefore needs settling fuel even if it has only one connect. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Local Open Scope N_scope.

Fixpoint node_chain (length : nat) (previous : N) : @hfstmt_seq VarOrder.T :=
  match length with
  | O => @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 2)
      (@Eref VarOrder.T (@Eid VarOrder.T previous))) (@Qnil VarOrder.T)
  | S rest =>
      let current := 100 + N.of_nat length in
      @Qcons VarOrder.T (@Snode VarOrder.T current
        (@Eref VarOrder.T (@Eid VarOrder.T previous)))
        (node_chain rest current)
  end.
Definition chain_statements := @Qcons VarOrder.T
  (@Sreg VarOrder.T 2 (@mk_freg VarOrder.T (Gtyp (Fuint 1))
    (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@NRst VarOrder.T)))
  (node_chain 24 0).
Definition chain_modules := [:: @FInmod VarOrder.T 0
  [:: @Finput VarOrder.T 0 (Gtyp (Fuint 1));
      @Finput VarOrder.T 1 (Gtyp Fclock)] chain_statements].
Definition chain_inputs (_ : nat) : VM.t hvalue :=
  VM.add 0 (Gval (Fuint 1) [:: true])
    (VM.add 1 (Gval Fclock [:: true]) (VM.empty hvalue)).
Example chain_bound_counts_nodes :
  circuit_iter_count_with_memory chain_modules 0 Gtyp_connect_count = Some 25%nat.
Proof. vm_compute. reflexivity. Qed.
Definition read_chain_register (states : option (SVM.t (VM.t hvalue))) :=
  match states with
  | Some states => match SVM.find [::] states with
    | Some state => VM.find 2 state | None => None end
  | None => None end.
Example chain_settles_before_commit :
  read_chain_register (circuit_run_from_reset chain_modules 0 chain_inputs 1)
  = Some (Gval (Fuint 1) [:: true]).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions chain_bound_counts_nodes.
Print Assumptions chain_settles_before_commit.

(* Repeated instances in series must each contribute their node budget. *)
Definition repeated_child := @FInmod VarOrder.T 1
 [:: @Finput VarOrder.T 0 (Gtyp (Fuint 1)); @Foutput VarOrder.T 2 (Gtyp (Fuint 1))]
 (node_chain 24 0).
Definition repeated_stmts : @hfstmt_seq VarOrder.T :=
 @Qcons VarOrder.T (@Sreg VarOrder.T 3 (@mk_freg VarOrder.T (Gtyp (Fuint 1))
   (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@NRst VarOrder.T)))
 (@Qcons VarOrder.T (@Sinst VarOrder.T 4 1)
 (@Qcons VarOrder.T (@Sinst VarOrder.T 5 1)
 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 4) 0)
   (@Eref VarOrder.T (@Eid VarOrder.T 0)))
 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 5) 0)
   (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 4) 2)))
 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 3)
   (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 5) 2))) (@Qnil VarOrder.T)))))).
Definition repeated_modules := [:: @FInmod VarOrder.T 0
 [:: @Finput VarOrder.T 0 (Gtyp (Fuint 1)); @Finput VarOrder.T 1 (Gtyp Fclock)]
 repeated_stmts; repeated_child].
Definition repeated_inputs (_ : nat) : VM.t hvalue :=
 VM.add 0 (Gval (Fuint 1) [::true]) (VM.add 1 (Gval Fclock [::true]) (VM.empty _)).
Definition repeated_result :=
 match circuit_run_from_reset repeated_modules 0 repeated_inputs 1 with
 | Some states => match SVM.find [::] states with
   | Some state => VM.find 3 state | None => None end
 | None => None end.
Example repeated_instance_bound :
  circuit_iter_count_with_memory repeated_modules 0 Gtyp_connect_count = Some 57%nat.
Proof. vm_compute. reflexivity. Qed.
Example repeated_instances_settle_before_commit :
  repeated_result = Some (Gval (Fuint 1) [::true]).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions repeated_instances_settle_before_commit.
