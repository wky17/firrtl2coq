From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.




(****** Aggregate type ******)

Section Ftype.

(* Variable var : eqType. *)

(* flipped direction for subfields *)
Inductive fflip : Type := Flipped | Nflip.

(* flipped direction type equality is decidable *)
Lemma fflip_eq_dec (x y : fflip) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* Boolean equality of flipped direction type *)
Definition fflip_eqn (x y : fflip) : bool :=
  match x, y with
  | Flipped, Flipped | Nflip, Nflip => true
  | _, _ => false
  end.

(* reflection predicate for flipped direction type *)
Lemma fflip_eqP : forall (x y : fflip), reflect (x = y) (fflip_eqn x y).
  Proof.
    destruct x, y ; simpl fflip_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
  Qed.

(* eqType for flipped direction type *)
Definition fflip_eqMixin := EqMixin fflip_eqP.
Canonical fflip_eqType := Eval hnf in EqType fflip fflip_eqMixin.

Inductive ftype : Type :=
| Gtyp : fgtyp -> ftype
| Atyp : ftype -> nat -> ftype
| Btyp : ffield -> ftype

with ffield : Type :=
| Fnil : ffield
| Fflips : var -> fflip -> ftype -> ffield -> ffield
.

Scheme ftype_ffield_ind := Induction for ftype Sort Prop
with ffield_ftype_ind := Induction for ffield Sort Prop.

(* is passive type *)
Fixpoint is_passive (t : ftype) : bool :=
  match t with
  | Gtyp t => true
  | Atyp t _ => is_passive t
  | Btyp fs => is_passive_fields fs
  end
with is_passive_fields (fs : ffield) : bool :=
       match fs with
       | Fnil => true
       | Fflips _ Nflip t fs => is_passive t && (is_passive_fields fs)
       | Fflips _ Flipped t fs => false
       end.

(* Equality of types *)

Lemma ftype_eq_dec (x y : ftype) : {x = y} + {x <> y}
with ffield_eq_dec (fx fy : ffield) : {fx = fy} + {fx <> fy}.
Proof.
  decide equality. apply fgtyp_eq_dec. apply Nat.eq_dec.
  decide equality.
  decide equality. apply N.eq_dec.
Qed.

Fixpoint ftype_eqn (x y : ftype) : bool :=
  match x, y with
  | Gtyp tx, Gtyp ty => fgtyp_eqn tx ty
  | Atyp tx nx, Atyp ty ny => ftype_eqn tx ty && (nx == ny)
  | Btyp fx, Btyp fy => ffield_eqn fx fy
  | _, _ => false
  end
with ffield_eqn (f1 f2 : ffield) : bool :=
       match  f1, f2 with
       | Fnil, Fnil => true
       | Fflips _ Nflip t1 fs1, Fflips _ Nflip t2 fs2
         => ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2
         => (v1 == v2) && ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | _, _ => false
       end.

Notation "x =? y" := (ftype_eqn x y).

Lemma ftype_eqn_refl (x : ftype) : x =? x
with ffield_eqn_refl (fx : ffield) : ffield_eqn fx fx.
Proof.
Admitted.

Lemma ftype_eqn_eq (x y : ftype) : x =? y <-> x = y
with ffield_eqn_eq (fx fy : ffield) : ffield_eqn fx fy <-> fx = fy.
Proof.
Admitted.

Lemma ftype_eqn_sym (x y : ftype) : x =? y -> y =? x
with ffield_eqn_sym (fx fy : ffield) : ffield_eqn fx fy -> ffield_eqn fy fx.
Proof.
Admitted.

Lemma ftype_eqn_trans (x y z : ftype) : x =? y -> y =? z -> x =? z
with ffield_eqn_trans (fx fy fz : ffield) : ffield_eqn fx fy -> ffield_eqn fy fz -> ffield_eqn fx fz.
Proof.
Admitted.

Instance ftype_eqn_Reflexive : Reflexive (@ftype_eqn) := @ftype_eqn_refl.
Instance ftype_eqn_Symmetric : Symmetric (@ftype_eqn) := @ftype_eqn_sym.
Instance ftype_eqn_Transitive : Transitive (@ftype_eqn) := @ftype_eqn_trans.
Instance ftype_eqn_Equivalence : Equivalence (@ftype_eqn) :=
  { Equivalence_Reflexive := ftype_eqn_Reflexive;
    Equivalence_Symmetric := ftype_eqn_Symmetric;
    Equivalence_Transitive := ftype_eqn_Transitive }.
Instance ffield_eqn_Reflexive : Reflexive (@ffield_eqn) := @ffield_eqn_refl.
Instance ffield_eqn_Symmetric : Symmetric (@ffield_eqn) := @ffield_eqn_sym.
Instance ffield_eqn_Transitive : Transitive (@ffield_eqn) := @ffield_eqn_trans.
Instance ffield_eqn_Equivalence : Equivalence (@ffield_eqn) :=
  { Equivalence_Reflexive := ffield_eqn_Reflexive;
    Equivalence_Symmetric := ffield_eqn_Symmetric;
    Equivalence_Transitive := ffield_eqn_Transitive }.

Lemma ftype_eqP : forall (x y : ftype), reflect (x = y) (x =? y)
with ffield_eqP : forall (fx fy : ffield), reflect (fx = fy) (ffield_eqn fx fy).
Proof.
- move=> x y. case H : (ftype_eqn x y).
  - apply ReflectT. exact: (proj1 (ftype_eqn_eq x y) H).
  - apply ReflectF. move=> Hxy.
    have Htrue : ftype_eqn x y := proj2 (ftype_eqn_eq x y) Hxy.
    by rewrite Htrue in H.
- move=> fx fy. case H : (ffield_eqn fx fy).
  - apply ReflectT. exact: (proj1 (ffield_eqn_eq fx fy) H).
  - apply ReflectF. move=> Hxy.
    have Htrue : ffield_eqn fx fy := proj2 (ffield_eqn_eq fx fy) Hxy.
    by rewrite Htrue in H.
Qed.

Definition ftype_eqMixin := EqMixin ftype_eqP.
Definition ffield_eqMixin := EqMixin ffield_eqP.
Canonical ftype_eqType := Eval hnf in EqType ftype ftype_eqMixin.
Canonical ffield_eqType := Eval hnf in EqType ffield ffield_eqMixin.

End Ftype.

Inductive fcomponent : Set :=
| In_port
| Instanceof
| Memory
| Node
| Out_port
| Register
| Wire
| Fmodule
.

(** eq dec *)
Lemma fcomponent_eq_dec (x y : fcomponent) : {x = y} + {x <> y}.
Proof.  decide equality.  Qed.

Definition fcomponent_eqn (x y : fcomponent) : bool :=
  match x, y with
  | In_port, In_port
  | Instanceof, Instanceof
  | Memory, Memory
  | Node, Node
  | Out_port, Out_port
  | Register, Register
  | Wire, Wire
  | Fmodule, Fmodule => true
  | _, _ => false
  end.

Lemma fcomponent_eqP : Equality.axiom fcomponent_eqn.
Proof. unfold Equality.axiom, fcomponent_eqn. intros.
destruct x, y ; try (apply ReflectF ; discriminate).
all : (apply ReflectT ; reflexivity).
Qed.
Canonical fcomponent_eqMixin := EqMixin fcomponent_eqP.
Canonical fcomponent_eqType := Eval hnf in EqType fcomponent fcomponent_eqMixin.
