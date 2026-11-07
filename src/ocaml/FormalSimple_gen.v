From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.

Local Open Scope N_scope.

Definition generated_circuit : @hfcircuit VarOrder.T :=
  (@Fcircuit VarOrder.T 0 [:: (@FInmod VarOrder.T 0 [:: (@Finput VarOrder.T 0 (Gtyp Fclock));
(@Finput VarOrder.T 1 (Gtyp (Fuint 1)));
(@Foutput VarOrder.T 2 (Btyp (Fflips 0 Flipped (Gtyp (Fuint 10)) (Fflips 1 Flipped (Gtyp (Fuint 10)) (Fflips 2 Nflip (Gtyp (Fuint 10)) Fnil)))))] (@Qcons VarOrder.T (@Snode VarOrder.T 3 (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 2) 0)) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 2) 1)))) (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 2) 2) (@Eref VarOrder.T (@Eid VarOrder.T 3))) (@Qnil VarOrder.T))))]).
