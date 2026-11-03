From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths.

(*
  对应的 FIRRTL 文本：

  circuit Adder :
    module Adder :
      input a : UInt<8>
      input b : UInt<8>
      output s : UInt<8>
      s <= add(a, b)
*)

Local Open Scope N_scope.

Definition adder_module : @fmodule VarOrder.T :=
  @FInmod VarOrder.T 1
    [:: @Finput  VarOrder.T 2 (Fuint 8);
        @Finput  VarOrder.T 3 (Fuint 8);
        @Foutput VarOrder.T 4 (Fuint 8) ]
    [:: @Sfcnct VarOrder.T 4
          (@Eprim_binop VarOrder.T Badd
             (@Eref VarOrder.T 2)
             (@Eref VarOrder.T 3)) ].

Definition adder_circuit : @fcircuit VarOrder.T :=
  @Fcircuit VarOrder.T 0 [:: adder_module].
