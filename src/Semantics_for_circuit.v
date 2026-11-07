(* Explicit entry points for the section-parametrized circuit semantics. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var FMaps FSets.
Require Import firrtl.HiFirrtl_with_implicit_widths.
Require Import firrtl.Semantics_with_implicit_widths.

Set Implicit Arguments.

Module ExplicitCircuitSemantics.

(* These aliases use exactly the ordered-map implementations used by the
   semantics file.  They make the result type usable by generated programs. *)
Module VM := Var.VM.
Module SeqVarOrder := MakeSeqOrder Var.VarOrder.
Module SVM := FMaps.MakeTreeMap SeqVarOrder.

Definition circuit_value_for
  (mml : seq (HiF.hfmodule))
  (mi_top : Var.VarOrder.T)
  (external_inputs : VM.t hvalue)
  : option (Semantics_with_implicit_widths.SVM.t (Var.VM.t hvalue)) :=
  @circuit_value mml mi_top None external_inputs.

Definition circuit_value_for_previous
  (mml : seq (HiF.hfmodule))
  (mi_top : Var.VarOrder.T)
  (previous : option (Semantics_with_implicit_widths.SVM.t (Var.VM.t hvalue)))
  (external_inputs : VM.t hvalue)
  : option (Semantics_with_implicit_widths.SVM.t (Var.VM.t hvalue)) :=
  @circuit_value mml mi_top previous external_inputs.

End ExplicitCircuitSemantics.
