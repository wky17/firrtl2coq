From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
  Semantics_with_implicit_widths.
Local Open Scope N_scope.

(* The divider's skip-count subtraction mixes seven- and six-bit UInts. *)
Example unsigned_mixed_width_subtraction :
  eval_binop_basic Bsub (Gval (Fuint 7) (from_N 7 64))
    (Gval (Fuint 6) (from_N 6 32)) =
  Some (Gval (Fuint 8) (from_N 8 32)).
Proof. vm_compute. reflexivity. Qed.

(* Widen before subtracting: the top operand bit is not a sign bit. *)
Example unsigned_top_bit_subtraction :
  eval_binop_basic Bsub (Gval (Fuint 4) (from_N 4 8))
    (Gval (Fuint 4) (from_N 4 1)) =
  Some (Gval (Fuint 5) (from_N 5 7)).
Proof. vm_compute. reflexivity. Qed.

(* Negative differences wrap in the declared result width. *)
Example unsigned_negative_difference :
  eval_binop_basic Bsub (Gval (Fuint 4) (from_N 4 1))
    (Gval (Fuint 4) (from_N 4 8)) =
  Some (Gval (Fuint 5) (from_N 5 25)).
Proof. vm_compute. reflexivity. Qed.

(* The signed branch still interprets 4'b1000 as -8. *)
Example signed_subtraction_unchanged :
  eval_binop_basic Bsub (Gval (Fsint 4) (from_N 4 8))
    (Gval (Fsint 4) (from_N 4 1)) =
  Some (Gval (Fsint 5) (from_N 5 23)).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions unsigned_mixed_width_subtraction.
