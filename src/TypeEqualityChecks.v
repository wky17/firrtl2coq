From Coq Require Import NArith.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths.

Definition clock_field name direction := Fflips name direction (Gtyp Fclock) Fnil.

Example nflip_different_names :
  ffield_eqn (clock_field 0%N Nflip) (clock_field 1%N Nflip) = false.
Proof. reflexivity. Qed.

Example flipped_different_names :
  ffield_eqn (clock_field 0%N Flipped) (clock_field 1%N Flipped) = false.
Proof. reflexivity. Qed.

Example different_directions :
  ffield_eqn (clock_field 0%N Nflip) (clock_field 0%N Flipped) = false.
Proof. reflexivity. Qed.

Example identical_fields :
  ffield_eqn (clock_field 0%N Nflip) (clock_field 0%N Nflip) = true.
Proof. reflexivity. Qed.

Example bundle_different_names :
  ftype_eqn (Btyp (clock_field 0%N Nflip))
            (Btyp (clock_field 1%N Nflip)) = false.
Proof. reflexivity. Qed.

Example array_bundle_different_names :
  ftype_eqn (Atyp (Btyp (clock_field 0%N Nflip)) 2)
            (Atyp (Btyp (clock_field 1%N Nflip)) 2) = false.
Proof. reflexivity. Qed.

(* The former counterexample must no longer yield an equality. *)
Fail Definition ignored_name_equality :
  clock_field 0%N Nflip = clock_field 1%N Nflip :=
  proj1 (@ffield_eqn_eq (clock_field 0%N Nflip) (clock_field 1%N Nflip)) eq_refl.

Print Assumptions ftype_eqn_eq.
Print Assumptions ffield_eqn_eq.
Print Assumptions ftype_eqP.
Print Assumptions ffield_eqP.
