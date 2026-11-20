(* Symbolic invalid assignments must receive a propagation iteration. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
Local Open Scope N_scope.
Definition invalid_tmap : VM.t (ftype * fcomponent) :=
  VM.add 0 (Gtyp (Fuint 1), Wire) (VM.empty (ftype * fcomponent)).
Example invalid_assignment_has_fuel :
  max_iter_count_stmt' Gtyp_connect_count invalid_tmap
    (@Sinvalid VarOrder.T (@Eid VarOrder.T 0)) = Some 1%nat.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions invalid_assignment_has_fuel.
