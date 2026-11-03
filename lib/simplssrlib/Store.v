
(** * Stores of variable values *)

From Coq Require Import Program Program.Tactics FMaps ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From simplssrlib Require Import Types SsrOrder HList FMaps ZAriths Env Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Stores as total maps from variables to values of a single type.
    The type t of stores is a dependent type. *)

Module Type DTStore (V : SsrOrder).

  Local Notation var := V.t.

  Section DTStore.

    Variable value : Type.

    Parameter t : Type -> Type.

    Parameter acc : var -> t value -> value.

    Parameter upd : var -> value -> t value -> t value.

    Parameter upd2 : var -> value -> var -> value -> t value -> t value.

    Parameter acc_upd_eq :
      forall x y v s,
        x == y ->
        acc x (upd y v s) = v.

    Parameter acc_upd_neq :
      forall x y v s,
        x != y ->
        acc x (upd y v s) = acc x s.

    Parameter acc_upd2_eq1 :
      forall x y1 v1 y2 v2 (s : t value),
        x == y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v1.

    Parameter acc_upd2_eq2 :
      forall x y1 v1 y2 v2 (s : t value),
        x == y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v2.

    Parameter acc_upd2_neq :
      forall x y1 v1 y2 v2 s,
        x != y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = acc x s.

    Parameter Upd : var -> value -> t value -> t value -> Prop.

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t value) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Parameter Equal : t value -> t value -> Prop.

    Parameter Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).

    Parameter Upd2_upd :
      forall x1 v1 x2 v2 s,
        Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).

    Parameter Upd2_upd2 :
      forall x1 v1 x2 v2 s,
        Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).

    Parameter acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.

    Parameter acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.

    Parameter acc_Upd2_eq1 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v1.

    Parameter acc_Upd2_eq2 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v2.

    Parameter acc_Upd2_neq :
      forall x y1 v1 y2 v2 s1 s2,
        x != y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = acc x s1.

    Parameter Equal_def :
      forall s1 s2, Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).

    Parameter Equal_refl : forall s, Equal s s.

    Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.

    Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.

    Parameter Equal_ST : RelationClasses.Equivalence Equal.

    Parameter Equal_upd_Equal : forall v e s1 s2,
        Equal s1 s2 ->
        Equal (upd v e s1) (upd v e s2).

    Parameter Equal_Upd_Equal : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Upd v e s3 s4 ->
        Equal s1 s3 -> Equal s2 s4.

    Parameter Equal_upd2_Equal : forall v1 e1 v2 e2 s1 s2,
        Equal s1 s2 ->
        Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).

    Parameter Equal_Upd2_Equal : forall v1 e1 v2 e2 s1 s2 s3 s4,
        Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 ->
        Equal s1 s3 -> Equal s2 s4.

    Parameter Upd_pred_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.

    Parameter Upd_succ_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.

    Parameter Upd_Equal_Upd : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.

    Parameter Upd2_pred_Equal : forall v1 e1 v2 e2 s1 s2 s,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.

    Parameter Upd2_succ_Equal : forall v1 e1 v2 e2 s1 s2 s,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.

    Parameter Upd2_Equal_Upd2 : forall v1 e1 v2 e2 s1 s2 s3 s4,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.

    Parameter upd_acc_idem : forall v s, Equal (upd v (acc v s) s) s.

    Parameter upd_idem : forall v e s, Equal (upd v e (upd v e s)) (upd v e s).

    Parameter Upd_idem : forall v e s1 s2 s3,
        Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.

    Parameter upd2_idem : forall v1 e1 v2 e2 s,
        Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).

    Parameter Upd2_idem : forall v1 e1 v2 e2 s1 s2 s3,
        Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.

  End DTStore.

End DTStore.


(** An implementation of DTStore. The type t of stores is a function. *)
Module MakeDTStore (X : SsrOrder) <: DTStore X.

  Section DTStore.

    Variable value : Type.

    Definition var := X.T.

    Definition t : Type := var -> value.

    Parameter empty : var -> value.

    Definition acc (x : var) (s : t) := s x.

    Definition upd (x : var) (v : value) (s : t) :=
      fun (y : var) => if y == x then v else acc y s.

    Definition upd2 x1 v1 x2 v2 (s : t) : t :=
      upd x2 v2 (upd x1 v1 s).

    Lemma acc_upd_eq {x y v s} :
      x == y ->
      acc x (upd y v s) = v.
    Proof. rewrite /acc /upd => Hxy. rewrite Hxy. reflexivity. Qed.

    Lemma acc_upd_neq {x y v s} :
      x != y ->
      acc x (upd y v s) = acc x s.
    Proof. rewrite {1}/acc /upd => Hxy. rewrite (negPf Hxy). reflexivity. Qed.

    Lemma acc_upd2_eq1 {x y1 v1 y2 v2 s} :
      x == y1 -> x != y2 ->
      acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_eq Hx1). Qed.

    Lemma acc_upd2_eq2 {x y1 v1 y2 v2 s} :
      x == y2 ->
      acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof. move=> Hx2. rewrite /upd2 (acc_upd_eq Hx2). reflexivity. Qed.

    Lemma acc_upd2_neq {x y1 v1 y2 v2 s} :
      x != y1 -> x != y2 ->
      acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_neq Hx1). Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Definition Equal (s1 s2 : t) : Prop :=
      forall v, acc v s1 = acc v s2.

    Lemma Upd_upd x v s : Upd x v s (upd x v s).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd x1 v1 x2 v2 s :
      Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd2 x1 v1 x2 v2 s :
      Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
    Proof. exact: Upd2_upd. Qed.

    Lemma acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = v.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx.
      rewrite (acc_upd_eq Hxy) in Hx. assumption.
    Qed.

    Lemma acc_Upd_neq x y v s1 s2 : x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx.
      rewrite (acc_upd_neq Hxy) in Hx. assumption.
    Qed.

    Lemma acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
    Proof. move=> Heq Hne Hupd. rewrite (Hupd x). exact: acc_upd2_eq1. Qed.

    Lemma acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
      x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
    Proof. move=> Heq Hupd. rewrite (Hupd x). exact: acc_upd2_eq2. Qed.

    Lemma acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
    Proof. move=> Hne1 Hne2 Hupd. rewrite (Hupd x). exact: acc_upd2_neq. Qed.

    Lemma Equal_def s1 s2 :
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
    Proof. done. Qed.

    Lemma Equal_refl s : Equal s s.
    Proof. done. Qed.

    Lemma Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1.
    Proof. move=> H v; rewrite (H v); reflexivity. Qed.

    Lemma Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
    Proof. move=> H1 H2 v. rewrite (H1 v) (H2 v). reflexivity. Qed.

    Instance Equal_ST : RelationClasses.Equivalence Equal :=
      { Equivalence_Reflexive := Equal_refl;
        Equivalence_Symmetric := Equal_sym;
        Equivalence_Transitive := Equal_trans }.

    Lemma Equal_upd_Equal v e s1 s2 : Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
    Proof.
      move=> H x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite !(acc_upd_neq Hxv). exact: (H x).
    Qed.

    Lemma Equal_Upd_Equal v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hupd1 Hupd2 Heq x. rewrite (Hupd1 x) (Hupd2 x). exact: Equal_upd_Equal.
    Qed.

    Lemma Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
      Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).
    Proof.
      move=> Heq. rewrite /upd2. move: (Equal_upd_Equal v1 e1 Heq) => {Heq} Heq.
      exact: (Equal_upd_Equal v2 e2 Heq).
    Qed.

    Lemma Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hup12 Hup34 Heq13 x. rewrite (Hup12 x) (Hup34 x).
      exact: (Equal_upd2_Equal _ _ _ _ Heq13).
    Qed.

    Lemma Upd_pred_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd_succ_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
    Proof. move=> H H2s x. rewrite -(H2s x) (H x). reflexivity. Qed.

    Lemma Upd_Equal_Upd v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.
    Proof. move=> H Hs2 x. rewrite -(Hs2 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma upd_acc_idem v s : Equal (upd v (acc v s) s) s.
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). by rewrite (eqP Hxv).
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s).
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x). case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). rewrite (H12 x)  (acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd2_idem v1 e1 v2 e2 s :
      Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).
    Proof.
      rewrite /upd2 => x. case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

    Lemma Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x) (H12 x). case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1). rewrite (H12 x).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

  End DTStore.

End MakeDTStore.



Module DTStoreAdapter (X : SsrOrder) (V : Equalities.Typ).

  Module S := MakeDTStore X.
  Definition value := V.t.
  Definition var := S.var.
  Definition t := S.t value.
  Definition empty : t := S.empty value.
  Definition acc x (s : t) := S.acc x s.
  Definition upd x v (s : t) := S.upd x v s.
  Definition upd2 x1 v1 x2 v2 (s : t) := S.upd2 x1 v1 x2 v2 s.
  Definition acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = v :=
    @S.acc_upd_eq value x y v s.
  Definition acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s :=
    @S.acc_upd_neq value x y v s.
  Definition acc_upd2_eq1 {x y1 v1 y2 v2 s} :
    x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1 :=
    @S.acc_upd2_eq1 value x y1 v1 y2 v2 s.
  Definition acc_upd2_eq2 {x y1 v1 y2 v2 s} :
    x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2 :=
    @S.acc_upd2_eq2 value x y1 v1 y2 v2 s.
  Definition acc_upd2_neq {x y1 v1 y2 v2 s} :
    x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s :=
    @S.acc_upd2_neq value x y1 v1 y2 v2 s.
  Definition Upd x v (s1 s2 : t) := S.Upd x v s1 s2.
  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) := S.Upd2 x1 v1 x2 v2 s1 s2.
  Definition Equal (s1 s2 : t) := S.Equal s1 s2.
  Definition Upd_upd x v s : Upd x v s (upd x v s) := @S.Upd_upd value x v s.
  Definition Upd2_upd x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)) :=
    @S.Upd2_upd value x1 v1 x2 v2 s.
  Definition Upd2_upd2 x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s) :=
    @S.Upd2_upd2 value x1 v1 x2 v2 s.
  Definition acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = v :=
    @S.acc_Upd_eq value x y v s1 s2.
  Definition acc_Upd_neq x y v s1 s2 :
    x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1 := @S.acc_Upd_neq value x y v s1 s2.
  Definition acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
    x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1 :=
    @S.acc_Upd2_eq1 value x y1 v1 y2 v2 s1 s2.
  Definition acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
    x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2 :=
    @S.acc_Upd2_eq2 value x y1 v1 y2 v2 s1 s2.
  Definition acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
    x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1 :=
    @S.acc_Upd2_neq value x y1 v1 y2 v2 s1 s2.
  Definition Equal_def s1 s2 :
    Equal s1 s2 <-> (forall v, acc v s1 = acc v s2) :=
    @S.Equal_def value s1 s2.
  Definition Equal_refl s : Equal s s := @S.Equal_refl value s.
  Definition Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1 := @S.Equal_sym value s1 s2.
  Definition Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3 :=
    @S.Equal_trans value s1 s2 s3.
  Instance Equal_ST : RelationClasses.Equivalence Equal := S.Equal_ST value.
  Definition Equal_upd_Equal v e s1 s2 :
    Equal s1 s2 -> Equal (upd v e s1) (upd v e s2) :=
    @S.Equal_upd_Equal value v e s1 s2.
  Definition Equal_Upd_Equal v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4 :=
    @S.Equal_Upd_Equal value v e s1 s2 s3 s4.
  Definition Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
    Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2) :=
    @S.Equal_upd2_Equal value v1 e1 v2 e2 s1 s2.
  Definition Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4 :=
    @S.Equal_Upd2_Equal value v1 e1 v2 e2 s1 s2 s3 s4.
  Definition Upd_pred_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2 := @S.Upd_pred_Equal value v e s1 s2 s.
  Definition Upd_succ_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s := @S.Upd_succ_Equal value v e s1 s2 s.
  Definition Upd_Equal_Upd v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4 :=
    @S.Upd_Equal_Upd value v e s1 s2 s3 s4.
  Definition Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2 :=
    @S.Upd2_pred_Equal value v1 e1 v2 e2 s1 s2 s.
  Definition Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s :=
    @S.Upd2_succ_Equal value v1 e1 v2 e2 s1 s2 s.
  Definition Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4 :=
    @S.Upd2_Equal_Upd2 value v1 e1 v2 e2 s1 s2 s3 s4.
  Definition upd_acc_idem v s : Equal (upd v (acc v s) s) s :=
    @S.upd_acc_idem value v s.
  Definition upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s) :=
    @S.upd_idem value v e s.
  Definition Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3 :=
    @S.Upd_idem value v e s1 s2 s3.
  Definition upd2_idem v1 e1 v2 e2 s :
    Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s) :=
    @S.upd2_idem value v1 e1 v2 e2 s.
  Definition Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3 :=
    @S.Upd2_idem value v1 e1 v2 e2 s1 s2 s3.

End DTStoreAdapter.



(** An implementation of DTStore. The type t of stores is a function. *)
Module MakeRealizableDTStore (X : SsrOrder) <: DTStore X.

  Section DTStore.

    Variable value : Type.

    Definition var := X.T.

    Definition t : Type := var -> value.

    Definition empty (d : value) : var -> value := fun _ => d.

    Definition acc (x : var) (s : t) := s x.

    Definition upd (x : var) (v : value) (s : t) :=
      fun (y : var) => if y == x then v else acc y s.

    Definition upd2 x1 v1 x2 v2 (s : t) : t :=
      upd x2 v2 (upd x1 v1 s).

    Lemma acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = v.
    Proof. rewrite /acc /upd => Hxy. rewrite Hxy. reflexivity. Qed.

    Lemma acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s.
    Proof. rewrite {1}/acc /upd => Hxy. by rewrite (negPf Hxy). Qed.

    Lemma acc_upd2_eq1 {x y1 v1 y2 v2 s} :
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_eq Hx1). Qed.

    Lemma acc_upd2_eq2 {x y1 v1 y2 v2 s} :
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof. move=> Hx2. by rewrite /upd2 (acc_upd_eq Hx2). Qed.

    Lemma acc_upd2_neq {x y1 v1 y2 v2 s} :
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_neq Hx1). Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Definition Equal (s1 s2 : t) : Prop :=
      forall v, acc v s1 = acc v s2.

    Lemma Upd_upd x v s : Upd x v s (upd x v s).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd2 x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
    Proof. exact: Upd2_upd. Qed.

    Lemma acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = v.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_eq Hxy) in Hx.
    Qed.

    Lemma acc_Upd_neq x y v s1 s2 : x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_neq Hxy) in Hx.
    Qed.

    Lemma acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
    Proof. move=> Heq Hne Hupd. rewrite (Hupd x). exact: acc_upd2_eq1. Qed.

    Lemma acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
      x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
    Proof. move=> Heq Hupd. rewrite (Hupd x). exact: acc_upd2_eq2. Qed.

    Lemma acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
    Proof. move=> Hne1 Hne2 Hupd. rewrite (Hupd x). exact: acc_upd2_neq. Qed.

    Lemma Equal_def s1 s2 :
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
    Proof. done. Qed.

    Lemma Equal_refl s : Equal s s.
    Proof. done. Qed.

    Lemma Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1.
    Proof. move=> H v; rewrite (H v); reflexivity. Qed.

    Lemma Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
    Proof. move=> H1 H2 v. rewrite (H1 v) (H2 v). reflexivity. Qed.

    Instance Equal_ST : RelationClasses.Equivalence Equal :=
      { Equivalence_Reflexive := Equal_refl;
        Equivalence_Symmetric := Equal_sym;
        Equivalence_Transitive := Equal_trans }.

    Lemma Equal_upd_Equal v e s1 s2 : Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
    Proof.
      move=> H x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite !(acc_upd_neq Hxv). exact: (H x).
    Qed.

    Lemma Equal_Upd_Equal v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hupd1 Hupd2 Heq x. rewrite (Hupd1 x) (Hupd2 x). exact: Equal_upd_Equal.
    Qed.

    Lemma Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
      Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).
    Proof.
      move=> Heq. rewrite /upd2. move: (Equal_upd_Equal v1 e1 Heq) => {Heq} Heq.
      exact: (Equal_upd_Equal v2 e2 Heq).
    Qed.

    Lemma Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hup12 Hup34 Heq13 x. rewrite (Hup12 x) (Hup34 x).
      exact: (Equal_upd2_Equal _ _ _ _ Heq13).
    Qed.

    Lemma Upd_pred_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd_succ_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
    Proof. move=> H H2s x. rewrite -(H2s x) (H x). reflexivity. Qed.

    Lemma Upd_Equal_Upd v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.
    Proof. move=> H Hs2 x. rewrite -(Hs2 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma upd_acc_idem v s : Equal (upd v (acc v s) s) s.
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). by rewrite (eqP Hxv).
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s).
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x). case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). rewrite (H12 x)  (acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd2_idem v1 e1 v2 e2 s :
      Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).
    Proof.
      rewrite /upd2 => x. case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

    Lemma Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x) (H12 x). case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1). rewrite (H12 x).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

  End DTStore.

End MakeRealizableDTStore.



Module RealizableDTStoreAdapter (X : SsrOrder) (V : HasDefaultTyp).
  Module S := MakeRealizableDTStore X.
  Definition value := V.t.
  Definition var := S.var.
  Definition t := S.t value.
  Definition empty : t := S.empty V.default.
  Definition acc x (s : t) := S.acc x s.
  Definition upd x v (s : t) := S.upd x v s.
  Definition upd2 x1 v1 x2 v2 (s : t) := S.upd2 x1 v1 x2 v2 s.
  Definition acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = v :=
    @S.acc_upd_eq value x y v s.
  Definition acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s :=
    @S.acc_upd_neq value x y v s.
  Definition acc_upd2_eq1 {x y1 v1 y2 v2 s} :
    x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1 :=
    @S.acc_upd2_eq1 value x y1 v1 y2 v2 s.
  Definition acc_upd2_eq2 {x y1 v1 y2 v2 s} :
    x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2 :=
    @S.acc_upd2_eq2 value x y1 v1 y2 v2 s.
  Definition acc_upd2_neq {x y1 v1 y2 v2 s} :
    x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s :=
    @S.acc_upd2_neq value x y1 v1 y2 v2 s.
  Definition Upd x v (s1 s2 : t) := S.Upd x v s1 s2.
  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) := S.Upd2 x1 v1 x2 v2 s1 s2.
  Definition Equal (s1 s2 : t) := S.Equal s1 s2.
  Definition Upd_upd x v s : Upd x v s (upd x v s) := @S.Upd_upd value x v s.
  Definition Upd2_upd x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)) :=
    @S.Upd2_upd value x1 v1 x2 v2 s.
  Definition Upd2_upd2 x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s) :=
    @S.Upd2_upd2 value x1 v1 x2 v2 s.
  Definition acc_Upd_eq x y v s1 s2 :
    x == y -> Upd y v s1 s2 -> acc x s2 = v := @S.acc_Upd_eq value x y v s1 s2.
  Definition acc_Upd_neq x y v s1 s2 :
    x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1 :=
    @S.acc_Upd_neq value x y v s1 s2.
  Definition acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
    x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1 :=
    @S.acc_Upd2_eq1 value x y1 v1 y2 v2 s1 s2.
  Definition acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
    x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2 :=
    @S.acc_Upd2_eq2 value x y1 v1 y2 v2 s1 s2.
  Definition acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
    x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1 :=
    @S.acc_Upd2_neq value x y1 v1 y2 v2 s1 s2.
  Definition Equal_def s1 s2 :
    Equal s1 s2 <-> (forall v, acc v s1 = acc v s2) :=
    @S.Equal_def value s1 s2.
  Definition Equal_refl s : Equal s s := @S.Equal_refl value s.
  Definition Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1 := @S.Equal_sym value s1 s2.
  Definition Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3 :=
    @S.Equal_trans value s1 s2 s3.
  Instance Equal_ST : RelationClasses.Equivalence Equal := S.Equal_ST value.
  Definition Equal_upd_Equal v e s1 s2 :
    Equal s1 s2 -> Equal (upd v e s1) (upd v e s2) :=
    @S.Equal_upd_Equal value v e s1 s2.
  Definition Equal_Upd_Equal v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4 :=
    @S.Equal_Upd_Equal value v e s1 s2 s3 s4.
  Definition Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
    Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2) :=
    @S.Equal_upd2_Equal value v1 e1 v2 e2 s1 s2.
  Definition Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4 :=
    @S.Equal_Upd2_Equal value v1 e1 v2 e2 s1 s2 s3 s4.
  Definition Upd_pred_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2 :=
    @S.Upd_pred_Equal value v e s1 s2 s.
  Definition Upd_succ_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s :=
    @S.Upd_succ_Equal value v e s1 s2 s.
  Definition Upd_Equal_Upd v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4 :=
    @S.Upd_Equal_Upd value v e s1 s2 s3 s4.
  Definition Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2 :=
    @S.Upd2_pred_Equal value v1 e1 v2 e2 s1 s2 s.
  Definition Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s :=
    @S.Upd2_succ_Equal value v1 e1 v2 e2 s1 s2 s.
  Definition Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4 :=
    @S.Upd2_Equal_Upd2 value v1 e1 v2 e2 s1 s2 s3 s4.
  Definition upd_acc_idem v s : Equal (upd v (acc v s) s) s :=
    @S.upd_acc_idem value v s.
  Definition upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s) :=
    @S.upd_idem value v e s.
  Definition Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3 :=
    @S.Upd_idem value v e s1 s2 s3.
  Definition upd2_idem v1 e1 v2 e2 s :
    Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s) :=
    @S.upd2_idem value v1 e1 v2 e2 s.
  Definition Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
    Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3 :=
    @S.Upd2_idem value v1 e1 v2 e2 s1 s2 s3.
End RealizableDTStoreAdapter.



(** Stores as total maps from variables to values of a single type.
    The type of values is fixed in a store module. *)
Module Type TStore (X : SsrOrder) (V : Equalities.Typ).

  Local Notation var := X.t.

  Local Notation value := V.t.

  Section TStore.

    Parameter t : Type.

    Parameter acc : var -> t -> value.

    Parameter upd : var -> value -> t -> t.

    Parameter upd2 : var -> value -> var -> value -> t -> t.

    Parameter acc_upd_eq :
      forall x y v s,
        x == y ->
        acc x (upd y v s) = v.

    Parameter acc_upd_neq :
      forall x y v s,
        x != y ->
        acc x (upd y v s) = acc x s.

    Parameter acc_upd2_eq1 :
      forall x y1 v1 y2 v2 (s : t),
        x == y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v1.

    Parameter acc_upd2_eq2 :
      forall x y1 v1 y2 v2 (s : t),
        x == y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = v2.

    Parameter acc_upd2_neq :
      forall x y1 v1 y2 v2 s,
        x != y1 ->
        x != y2 ->
        acc x (upd2 y1 v1 y2 v2 s) = acc x s.

    Parameter Upd : var -> value -> t -> t -> Prop.

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Parameter Equal : t -> t -> Prop.

    Parameter Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).

    Parameter Upd2_upd :
      forall x1 v1 x2 v2 s,
        Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).

    Parameter Upd2_upd2 :
      forall x1 v1 x2 v2 s,
        Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).

    Parameter acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.

    Parameter acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.

    Parameter acc_Upd2_eq1 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v1.

    Parameter acc_Upd2_eq2 :
      forall x y1 v1 y2 v2 s1 s2,
        x == y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = v2.

    Parameter acc_Upd2_neq :
      forall x y1 v1 y2 v2 s1 s2,
        x != y1 ->
        x != y2 ->
        Upd2 y1 v1 y2 v2 s1 s2 ->
        acc x s2 = acc x s1.

    Parameter Equal_def :
      forall s1 s2, Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).

    Parameter Equal_refl : forall s, Equal s s.

    Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.

    Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.

    Parameter Equal_ST : RelationClasses.Equivalence Equal.

    Parameter Equal_upd_Equal : forall v e s1 s2,
        Equal s1 s2 ->
        Equal (upd v e s1) (upd v e s2).

    Parameter Equal_Upd_Equal : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Upd v e s3 s4 ->
        Equal s1 s3 -> Equal s2 s4.

    Parameter Equal_upd2_Equal : forall v1 e1 v2 e2 s1 s2,
        Equal s1 s2 ->
        Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).

    Parameter Equal_Upd2_Equal : forall v1 e1 v2 e2 s1 s2 s3 s4,
        Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 ->
        Equal s1 s3 -> Equal s2 s4.

    Parameter Upd_pred_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.

    Parameter Upd_succ_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.

    Parameter Upd_Equal_Upd : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.

    Parameter Upd2_pred_Equal : forall v1 e1 v2 e2 s1 s2 s,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.

    Parameter Upd2_succ_Equal : forall v1 e1 v2 e2 s1 s2 s,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.

    Parameter Upd2_Equal_Upd2 : forall v1 e1 v2 e2 s1 s2 s3 s4,
        Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.

    Parameter upd_acc_idem : forall v s, Equal (upd v (acc v s) s) s.

    Parameter upd_idem : forall v e s, Equal (upd v e (upd v e s)) (upd v e s).

    Parameter Upd_idem : forall v e s1 s2 s3,
        Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.

    Parameter upd2_idem : forall v1 e1 v2 e2 s,
        Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).

    Parameter Upd2_idem : forall v1 e1 v2 e2 s1 s2 s3,
        Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.

  End TStore.

End TStore.

(* Implementation of TStore using functions *)
Module MakeTStoreFun (X : SsrOrder) (V : HasDefaultTyp) <: TStore X V.

  Local Notation var := X.t.

  Local Notation value := V.t.

  Local Notation d := V.default.

  Section TStore.

    Definition t : Type := var -> value.

    Definition empty : var -> value := fun _ => d.

    Definition acc (x : var) (s : t) := s x.

    Definition upd (x : var) (v : value) (s : t) :=
      fun (y : var) => if y == x then v else acc y s.

    Definition upd2 x1 v1 x2 v2 (s : t) : t :=
      upd x2 v2 (upd x1 v1 s).

    Lemma acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = v.
    Proof. rewrite /acc /upd => Hxy. rewrite Hxy. reflexivity. Qed.

    Lemma acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s.
    Proof. rewrite {1}/acc /upd => Hxy. by rewrite (negPf Hxy). Qed.

    Lemma acc_upd2_eq1 {x y1 v1 y2 v2 s} :
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_eq Hx1). Qed.

    Lemma acc_upd2_eq2 {x y1 v1 y2 v2 s} :
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof. move=> Hx2. by rewrite /upd2 (acc_upd_eq Hx2). Qed.

    Lemma acc_upd2_neq {x y1 v1 y2 v2 s} :
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_neq Hx1). Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Definition Equal (s1 s2 : t) : Prop :=
      forall v, acc v s1 = acc v s2.

    Lemma Upd_upd x v s : Upd x v s (upd x v s).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd2 x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
    Proof. exact: Upd2_upd. Qed.

    Lemma acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = v.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_eq Hxy) in Hx.
    Qed.

    Lemma acc_Upd_neq x y v s1 s2 : x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_neq Hxy) in Hx.
    Qed.

    Lemma acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
    Proof. move=> Heq Hne Hupd. rewrite (Hupd x). exact: acc_upd2_eq1. Qed.

    Lemma acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
      x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
    Proof. move=> Heq Hupd. rewrite (Hupd x). exact: acc_upd2_eq2. Qed.

    Lemma acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
    Proof. move=> Hne1 Hne2 Hupd. rewrite (Hupd x). exact: acc_upd2_neq. Qed.

    Lemma Equal_def s1 s2 :
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
    Proof. done. Qed.

    Lemma Equal_refl s : Equal s s.
    Proof. done. Qed.

    Lemma Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1.
    Proof. move=> H v; rewrite (H v); reflexivity. Qed.

    Lemma Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
    Proof. move=> H1 H2 v. rewrite (H1 v) (H2 v). reflexivity. Qed.

    Instance Equal_ST : RelationClasses.Equivalence Equal :=
      { Equivalence_Reflexive := Equal_refl;
        Equivalence_Symmetric := Equal_sym;
        Equivalence_Transitive := Equal_trans }.

    Lemma Equal_upd_Equal v e s1 s2 : Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
    Proof.
      move=> H x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite !(acc_upd_neq Hxv). exact: (H x).
    Qed.

    Lemma Equal_Upd_Equal v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hupd1 Hupd2 Heq x. rewrite (Hupd1 x) (Hupd2 x). exact: Equal_upd_Equal.
    Qed.

    Lemma Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
      Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).
    Proof.
      move=> Heq. rewrite /upd2. move: (Equal_upd_Equal v1 e1 Heq) => {Heq} Heq.
      exact: (Equal_upd_Equal v2 e2 Heq).
    Qed.

    Lemma Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hup12 Hup34 Heq13 x. rewrite (Hup12 x) (Hup34 x).
      exact: (Equal_upd2_Equal _ _ _ _ Heq13).
    Qed.

    Lemma Upd_pred_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd_succ_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
    Proof. move=> H H2s x. rewrite -(H2s x) (H x). reflexivity. Qed.

    Lemma Upd_Equal_Upd v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.
    Proof. move=> H Hs2 x. rewrite -(Hs2 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma upd_acc_idem v s : Equal (upd v (acc v s) s) s.
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). by rewrite (eqP Hxv).
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s).
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x). case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). rewrite (H12 x)  (acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd2_idem v1 e1 v2 e2 s :
      Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).
    Proof.
      rewrite /upd2 => x. case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

    Lemma Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x) (H12 x). case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1). rewrite (H12 x).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

  End TStore.

End MakeTStoreFun.


(* Implementation of TStore using maps *)
Module MakeTStoreMap (X : SsrOrder) (V : HasDefaultTyp) <: TStore X V.

  Module M := FMaps.MakeTreeMap X.

  Local Notation var := X.T.
  Local Notation value := V.t.
  Local Notation d := V.default.

  Section TStore.

    Definition t : Type := M.t value.

    Definition empty : t := M.empty value.

    Definition acc (x : var) (s : t) :=
      match M.find x s with
      | None => d
      | Some v => v
      end.

    Definition upd (x : var) (v : value) (s : t) := M.add x v s.

    Definition upd2 x1 v1 x2 v2 (s : t) : t :=
      upd x2 v2 (upd x1 v1 s).

    Lemma acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = v.
    Proof.
      rewrite /acc /upd => Hxy. rewrite (M.Lemmas.find_add_eq Hxy). reflexivity.
    Qed.

    Lemma acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s.
    Proof.
      rewrite {1}/acc /upd => Hxy. move/idP/negP: Hxy => Hxy.
      rewrite (M.Lemmas.find_add_neq Hxy). reflexivity.
    Qed.

    Lemma acc_upd2_eq1 {x y1 v1 y2 v2 s} :
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_eq Hx1). Qed.

    Lemma acc_upd2_eq2 {x y1 v1 y2 v2 s} :
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
    Proof. move=> Hx2. by rewrite /upd2 (acc_upd_eq Hx2). Qed.

    Lemma acc_upd2_neq {x y1 v1 y2 v2 s} :
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
    Proof. move=> Hx1 Hx2. by rewrite /upd2 (acc_upd_neq Hx2) (acc_upd_neq Hx1). Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).

    Definition Equal (s1 s2 : t) : Prop :=
      forall v, acc v s1 = acc v s2.

    Lemma Upd_upd x v s : Upd x v s (upd x v s).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
    Proof. move=> y. reflexivity. Qed.

    Lemma Upd2_upd2 x1 v1 x2 v2 s : Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
    Proof. exact: Upd2_upd. Qed.

    Lemma acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = v.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_eq Hxy) in Hx.
    Qed.

    Lemma acc_Upd_neq x y v s1 s2 : x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hupd. move: (Hupd x) => Hx. by rewrite (acc_upd_neq Hxy) in Hx.
    Qed.

    Lemma acc_Upd2_eq1 x y1 v1 y2 v2 s1 s2 :
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
    Proof. move=> Heq Hne Hupd. rewrite (Hupd x). exact: acc_upd2_eq1. Qed.

    Lemma acc_Upd2_eq2 x y1 v1 y2 v2 s1 s2 :
      x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
    Proof. move=> Heq Hupd. rewrite (Hupd x). exact: acc_upd2_eq2. Qed.

    Lemma acc_Upd2_neq x y1 v1 y2 v2 s1 s2 :
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
    Proof. move=> Hne1 Hne2 Hupd. rewrite (Hupd x). exact: acc_upd2_neq. Qed.

    Lemma Equal_def s1 s2 :
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
    Proof. done. Qed.

    Lemma Equal_refl s : Equal s s.
    Proof. done. Qed.

    Lemma Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1.
    Proof. move=> H v; rewrite (H v); reflexivity. Qed.

    Lemma Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
    Proof. move=> H1 H2 v. rewrite (H1 v) (H2 v). reflexivity. Qed.

    Instance Equal_ST : RelationClasses.Equivalence Equal :=
      { Equivalence_Reflexive := Equal_refl;
        Equivalence_Symmetric := Equal_sym;
        Equivalence_Transitive := Equal_trans }.

    Lemma Equal_upd_Equal v e s1 s2 : Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
    Proof.
      move=> H x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite !(acc_upd_neq Hxv). exact: (H x).
    Qed.

    Lemma Equal_Upd_Equal v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hupd1 Hupd2 Heq x. rewrite (Hupd1 x) (Hupd2 x). exact: Equal_upd_Equal.
    Qed.

    Lemma Equal_upd2_Equal v1 e1 v2 e2 s1 s2 :
      Equal s1 s2 -> Equal (upd2 v1 e1 v2 e2 s1) (upd2 v1 e1 v2 e2 s2).
    Proof.
      move=> Heq. rewrite /upd2. move: (Equal_upd_Equal v1 e1 Heq) => {} Heq.
      exact: (Equal_upd_Equal v2 e2 Heq).
    Qed.

    Lemma Equal_Upd2_Equal v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hup12 Hup34 Heq13 x. rewrite (Hup12 x) (Hup34 x).
      exact: (Equal_upd2_Equal _ _ _ _ Heq13).
    Qed.

    Lemma Upd_pred_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd_succ_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
    Proof. move=> H H2s x. rewrite -(H2s x) (H x). reflexivity. Qed.

    Lemma Upd_Equal_Upd v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd2_pred_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s -> Upd2 v1 e1 v2 e2 s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_succ_Equal v1 e1 v2 e2 s1 s2 s :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s2 s -> Upd2 v1 e1 v2 e2 s1 s.
    Proof. move=> H Hs2 x. rewrite -(Hs2 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma Upd2_Equal_Upd2 v1 e1 v2 e2 s1 s2 s3 s4 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd2 v1 e1 v2 e2 s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd2_Equal. Qed.

    Lemma upd_acc_idem v s : Equal (upd v (acc v s) s) s.
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). by rewrite (eqP Hxv).
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s).
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x). case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). rewrite (H12 x)  (acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd2_idem v1 e1 v2 e2 s :
      Equal (upd2 v1 e1 v2 e2 (upd2 v1 e1 v2 e2 s)) (upd2 v1 e1 v2 e2 s).
    Proof.
      rewrite /upd2 => x. case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

    Lemma Upd2_idem v1 e1 v2 e2 s1 s2 s3 :
      Upd2 v1 e1 v2 e2 s1 s2 -> Upd2 v1 e1 v2 e2 s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x) (H12 x). case Hxv2: (x == v2).
      - rewrite !(acc_upd_eq Hxv2). reflexivity.
      - move/idP/negP: Hxv2 => Hxv2. rewrite !(acc_upd_neq Hxv2).
        case Hxv1: (x == v1).
        + rewrite !(acc_upd_eq Hxv1). reflexivity.
        + move/idP/negP: Hxv1 => Hxv1. rewrite !(acc_upd_neq Hxv1). rewrite (H12 x).
          rewrite (acc_upd_neq Hxv2) (acc_upd_neq Hxv1). reflexivity.
    Qed.

  End TStore.

End MakeTStoreMap.



(** Stores as partial maps from variables to values of a single type. *)

Module Type PStore (V : SsrOrder).

  Local Notation var := V.t.

  Section PStore.

    Variable value : Type.

    Parameter t : Type -> Type.

    Parameter empty : t value.

    Parameter acc : var -> t value -> option value.

    Parameter upd : var -> value -> t value -> t value.

    Parameter unset : var -> t value -> t value.

    Parameter acc_upd_eq :
      forall x y v s,
        x == y ->
        acc x (upd y v s) = Some v.

    Parameter acc_upd_neq :
      forall x y v s,
        x != y ->
        acc x (upd y v s) = acc x s.

    Parameter acc_empty :
      forall x, acc x empty = None.

    Parameter acc_unset_eq :
      forall x y s,
        x == y ->
        acc x (unset y s) = None.

    Parameter acc_unset_neq :
      forall x y s,
        x != y ->
        acc x (unset y s) = acc x s.

    Parameter Empty : t value -> Prop.

    Parameter Upd : var -> value -> t value -> t value -> Prop.

    Parameter Unset : var -> t value -> t value -> Prop.

    Parameter Equal : t value -> t value -> Prop.

    Parameter Empty_acc :
      forall x s,
        Empty s ->
        acc x s = None.

    Parameter Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).

    Parameter Unset_unset :
      forall x s,
        Unset x s (unset x s).

    Parameter acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = Some v.

    Parameter acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.

    Parameter acc_Unset_eq :
      forall x y s1 s2,
        x == y ->
        Unset y s1 s2 ->
        acc x s2 = None.

    Parameter acc_Unset_neq :
      forall x y s1 s2,
        x != y ->
        Unset y s1 s2 ->
        acc x s2 = acc x s1.

    Parameter Equal_def :
      forall s1 s2,
        Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).

    Parameter Equal_refl : forall s, Equal s s.

    Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.

    Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.

    Parameter Equal_ST : RelationClasses.Equivalence Equal.

    Parameter Equal_upd_Equal : forall v e s1 s2,
        Equal s1 s2 ->
        Equal (upd v e s1) (upd v e s2).

    Parameter Equal_Upd_Equal : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Upd v e s3 s4 ->
        Equal s1 s3 -> Equal s2 s4.

    Parameter Upd_pred_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.

    Parameter Upd_succ_Equal : forall v e s1 s2 s,
        Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.

    Parameter Upd_Equal_Upd : forall v e s1 s2 s3 s4,
        Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.

    Parameter upd_acc_idem : forall v e s, acc v s = Some e -> Equal (upd v e s) s.

    Parameter upd_idem : forall v e s, Equal (upd v e (upd v e s)) (upd v e s).

    Parameter Upd_idem : forall v e s1 s2 s3,
        Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.

  End PStore.

End PStore.



Module MakePStore (X : SsrOrder) <: PStore X.

  Module M := FMapList.Make(X).
  Module L := FMapLemmas(M).

  Section PStore.

    Definition var : eqType := X.T.

    Variable value : Type.

    Definition t : Type := M.t value.

    Definition empty : t := M.empty value.

    Definition acc (x : var) (s : t) := M.find x s.

    Definition upd (x : var) (v : value) (s : t) := M.add x v s.

    Definition unset (x : var) (s : t) := M.remove x s.

    Lemma acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = Some v.
    Proof.
      rewrite /acc /upd => Hxy. rewrite (eqP Hxy) => {Hxy x}.
      apply: L.find_add_eq. reflexivity.
    Qed.

    Lemma acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s.
    Proof. rewrite /acc /upd => Hxy. apply: L.find_add_neq. exact: (negP Hxy). Qed.

    Lemma acc_empty {x} : acc x empty = None.
    Proof. exact: L.empty_o. Qed.

    Lemma acc_unset_eq {x y s} : x == y -> acc x (unset y s) = None.
    Proof. move=> Heq. apply: L.remove_eq_o. rewrite eq_sym. exact: Heq. Qed.

    Lemma acc_unset_neq {x y s} : x != y -> acc x (unset y s) = acc x s.
    Proof.
      move=> Hne. apply: L.remove_neq_o. move=> Heq.
      move/eqP: Hne; apply. by rewrite (eqP Heq).
    Qed.

    Definition Empty (s : t) : Prop := M.Empty s.

    Definition Upd x v s1 s2 : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Unset x s1 s2 : Prop :=
      forall y, acc y s2 = acc y (unset x s1).

    Definition Equal (s1 s2 : t) : Prop :=
      forall v, acc v s1 = acc v s2.

    Lemma Empty_acc {x s} : Empty s -> acc x s = None.
    Proof. move=> Hemp. exact: (L.Empty_find _ Hemp). Qed.

    Lemma Upd_upd x v s : Upd x v s (upd x v s).
    Proof. move=> y. reflexivity. Qed.

    Lemma Unset_unset x s : Unset x s (unset x s).
    Proof. move=> y. reflexivity. Qed.

    Lemma acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = Some v.
    Proof.
      move=> Hxy Hupd. move: (Hupd x). rewrite (acc_upd_eq Hxy). by apply.
    Qed.

    Lemma acc_Upd_neq x y v s1 s2 : x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hupd. move: (Hupd x). rewrite (acc_upd_neq Hxy). by apply.
    Qed.

    Lemma acc_Unset_eq x y s1 s2 : x == y -> Unset y s1 s2 -> acc x s2 = None.
    Proof.
      move=> Hxy Hunset. move: (Hunset x). rewrite (acc_unset_eq Hxy). by apply.
    Qed.

    Lemma acc_Unset_neq x y s1 s2 : x != y -> Unset y s1 s2 -> acc x s2 = acc x s1.
    Proof.
      move=> Hxy Hunset. move: (Hunset x). rewrite (acc_unset_neq Hxy). by apply.
    Qed.

    Lemma Equal_def s1 s2 :
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
    Proof. done. Qed.

    Lemma Equal_refl s : Equal s s.
    Proof. done. Qed.

    Lemma Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1.
    Proof. move=> H v; rewrite (H v); reflexivity. Qed.

    Lemma Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
    Proof. move=> H1 H2 v. rewrite (H1 v) (H2 v). reflexivity. Qed.

    Instance Equal_ST : RelationClasses.Equivalence Equal :=
      { Equivalence_Reflexive := Equal_refl;
        Equivalence_Symmetric := Equal_sym;
        Equivalence_Transitive := Equal_trans }.

    Lemma Equal_upd_Equal v e s1 s2 : Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
    Proof.
      move=> H x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite !(acc_upd_neq Hxv). exact: (H x).
    Qed.

    Lemma Equal_Upd_Equal v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
    Proof.
      move=> Hupd1 Hupd2 Heq x. rewrite (Hupd1 x) (Hupd2 x). exact: Equal_upd_Equal.
    Qed.

    Lemma Upd_pred_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
    Proof. move=> H H1s x. rewrite (H x). exact: Equal_upd_Equal. Qed.

    Lemma Upd_succ_Equal v e s1 s2 s : Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
    Proof. move=> H H2s x. rewrite -(H2s x) (H x). reflexivity. Qed.

    Lemma Upd_Equal_Upd v e s1 s2 s3 s4 :
      Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4.
    Proof. move=> H H13 H24 x. rewrite -(H24 x) (H x). exact: Equal_upd_Equal. Qed.

    Lemma upd_acc_idem v e s : acc v s = Some e -> Equal (upd v e s) s.
    Proof.
      move=> Hacc x. case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv) (eqP Hxv) Hacc. reflexivity.
      - move/idP/negP: Hxv=> Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s).
    Proof.
      move=> x. case Hxv: (x == v).
      - rewrite !(acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

    Lemma Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3.
    Proof.
      move=> H12 H23 x. rewrite (H23 x). case Hxv: (x == v).
      - rewrite (acc_upd_eq Hxv). rewrite (H12 x)  (acc_upd_eq Hxv). reflexivity.
      - move/idP/negP: Hxv => Hxv. rewrite (acc_upd_neq Hxv). reflexivity.
    Qed.

  End PStore.

End MakePStore.



Module PStoreAdapter (X : SsrOrder) (V : Equalities.Typ).
  Module S := MakePStore X.
  Definition var := S.var.
  Definition value := V.t.
  Definition t := S.t value.
  Definition empty := S.empty value.
  Definition acc x (s : t) := S.acc x s.
  Definition upd x v (s : t) := S.upd x v s.
  Definition unset x (s : t) := S.unset x s.
  Definition acc_upd_eq {x y v s} : x == y -> acc x (upd y v s) = Some v :=
    @S.acc_upd_eq value x y v s.
  Definition acc_upd_neq {x y v s} : x != y -> acc x (upd y v s) = acc x s :=
    @S.acc_upd_neq value x y v s.
  Definition acc_empty x : acc x empty = None := @S.acc_empty value x.
  Definition acc_unset_eq {x y s} : x == y -> acc x (unset y s) = None :=
    @S.acc_unset_eq value x y s.
  Definition acc_unset_neq {x y s} : x != y -> acc x (unset y s) = acc x s :=
    @S.acc_unset_neq value x y s.
  Definition Empty (s : t) : Prop := S.Empty s.
  Definition Upd x v (s1 s2 : t) : Prop := S.Upd x v s1 s2.
  Definition Unset x (s1 s2 : t) : Prop := S.Unset x s1 s2.
  Definition Equal (s1 s2 : t) := S.Equal s1 s2.
  Definition Empty_acc {x s} : Empty s -> acc x s = None := @S.Empty_acc value x s.
  Definition Upd_upd x v s : Upd x v s (upd x v s) := @S.Upd_upd value x v s.
  Definition Unset_unset x s : Unset x s (unset x s) := @S.Unset_unset value x s.
  Definition acc_Upd_eq x y v s1 s2 : x == y -> Upd y v s1 s2 -> acc x s2 = Some v :=
    @S.acc_Upd_eq value x y v s1 s2.
  Definition acc_Upd_neq x y v s1 s2 :
    x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1 :=
    @S.acc_Upd_neq value x y v s1 s2.
  Definition acc_Unset_eq x y s1 s2 : x == y -> Unset y s1 s2 -> acc x s2 = None :=
    @S.acc_Unset_eq value x y s1 s2.
  Definition acc_Unset_neq x y s1 s2 :
    x != y -> Unset y s1 s2 -> acc x s2 = acc x s1 :=
    @S.acc_Unset_neq value x y s1 s2.
  Definition Equal_def s1 s2 :
    Equal s1 s2 <-> (forall v, acc v s1 = acc v s2) :=
    @S.Equal_def value s1 s2.
  Definition Equal_refl s : Equal s s := @S.Equal_refl value s.
  Definition Equal_sym s1 s2 : Equal s1 s2 -> Equal s2 s1 := @S.Equal_sym value s1 s2.
  Definition Equal_trans s1 s2 s3 : Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3 :=
    @S.Equal_trans value s1 s2 s3.
  Instance Equal_ST : RelationClasses.Equivalence Equal := S.Equal_ST value.
  Definition Equal_upd_Equal v e s1 s2 :
    Equal s1 s2 -> Equal (upd v e s1) (upd v e s2) :=
    @S.Equal_upd_Equal value v e s1 s2.
  Definition Equal_Upd_Equal v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4 :=
    @S.Equal_Upd_Equal value v e s1 s2 s3 s4.
  Definition Upd_pred_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2 :=
    @S.Upd_pred_Equal value v e s1 s2 s.
  Definition Upd_succ_Equal v e s1 s2 s :
    Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s :=
    @S.Upd_succ_Equal value v e s1 s2 s.
  Definition Upd_Equal_Upd v e s1 s2 s3 s4 :
    Upd v e s1 s2 -> Equal s1 s3 -> Equal s2 s4 -> Upd v e s3 s4 :=
    @S.Upd_Equal_Upd value v e s1 s2 s3 s4.
  Definition upd_idem v e s : Equal (upd v e (upd v e s)) (upd v e s) :=
    @S.upd_idem value v e s.
  Definition Upd_idem v e s1 s2 s3 : Upd v e s1 s2 -> Upd v e s2 s3 -> Equal s2 s3 :=
    @S.Upd_idem value v e s1 s2 s3.
End PStoreAdapter.



(** Stores with heterogeneous values. The environment is pre-defined. *)

Module Type HStorePreDefined.

  Declare Module V : SsrOrder.
  Declare Module HE : HEnv with Module V := V.

  Local Open Scope hlist_scope.

  Parameter T : Set.

  Parameter V : T -> Set.

  Parameter t : HE.t T -> Type.

  Parameter empty : forall E : HE.t T, t E.

  Parameter upd :
    forall (E : HE.t T) (ty : T),
      HE.pvar E ty -> V ty -> t E -> t E.

  Parameter acc :
    forall (E : HE.t T) (ty : T),
      HE.pvar E ty -> t E -> V ty.

  Parameter bisim : forall (E : HE.t T), t E -> t E -> Prop.

  Axiom acc_upd_heq :
    forall (E : HE.t T) (tyx tyy : T) (x : HE.pvar E tyx) (y : HE.pvar E tyy)
           (e : V tyy) (s : t E),
      HE.pvar_var x == HE.pvar_var y ->
      acc x (upd y e s) =v e.

  Axiom acc_upd_eq :
    forall (E : HE.t T) (ty : T) (x : HE.pvar E ty) (y : HE.pvar E ty)
           (e : V ty) (s : t E),
      HE.pvar_var x == HE.pvar_var y ->
      acc x (upd y e s) = e.

  Axiom acc_upd_neq :
    forall (E : HE.t T) (tyx tyy : T) (x : HE.pvar E tyx) (y : HE.pvar E tyy)
           (e : V tyy) (s : t E),
      HE.pvar_var x != HE.pvar_var y ->
      acc x (upd y e s) = acc x s.

  Axiom bisim_refl : forall (E : HE.t T) (s : t E), bisim s s.

  Axiom bisim_pvar_inv :
    forall (E : HE.t T) (s1 s2 : t E) (ty : T) (x : HE.pvar E ty),
      bisim s1 s2 -> acc x s1 = acc x s2.

End HStorePreDefined.



Module Type HETEROGENEOUS.
  Parameter T : Set.
  Parameter V : T -> Set.
  Parameter default : forall (x : T), V x.
  Axiom ty_dec : forall (x y : T), {x = y} + {x <> y}.
End HETEROGENEOUS.

Module MakeHStorePreDefined (IV : SsrOrder) (H : HETEROGENEOUS) (IHE : HEnv with Module V := IV) <: HStorePreDefined with Module V := IV with Module HE := IHE.

  Module V := IV.
  Module HE := IHE.

  Local Open Scope hlist_scope.

  Definition T : Set := H.T.

  Definition V : T -> Set := H.V.

  Definition t (E : HE.t T) : Type := hlist V (HE.vtypes E).

  Program Fixpoint defaults (types : list T) : hlist V types :=
    match types with
    | nil => hnil V
    | cons hd tl => Hcons (H.default hd) (defaults tl)
    end.

  Definition empty (E : HE.t T) : t E := defaults (HE.vtypes E).

  Definition upd E ty (x : HE.pvar E ty) (v : V ty) (st : t E) : t E :=
    updlidx (HE.pvar_lidx x) v st.

  Definition acc E ty (x : HE.pvar E ty) (st : t E) : V ty :=
    acclidx (HE.pvar_lidx x) st.

  Definition bisim E (s1 s2 : t E) : Prop :=
    forall ty (x : HE.pvar E ty), acc x s1 = acc x s2.

  Lemma acc_upd_heq E tyx tyy (x : HE.pvar E tyx) (y : HE.pvar E tyy)
        (e : V tyy) (s : t E) :
    HE.pvar_var x == HE.pvar_var y ->
    (acc x (upd y e s) =v e).
  Proof.
    rewrite /acc /upd /= => Hxy.
    rewrite acclidx_updlidx_heq.
    - reflexivity.
    - apply: HE.pvar_lidx_heq.
      assumption.
  Qed.

  Lemma acc_upd_eq E ty (x y : HE.pvar E ty) (e : V ty) (s : t E) :
    HE.pvar_var x == HE.pvar_var y ->
    acc x (upd y e s) = e.
  Proof.
    move=> Hxy.
    apply: value_eq_eq.
    apply: acc_upd_heq.
    assumption.
  Qed.

  Lemma acc_upd_neq E tyx tyy (x : HE.pvar E tyx) (y : HE.pvar E tyy)
        (e : V tyy) (s : t E) :
    HE.pvar_var x != HE.pvar_var y ->
    acc x (upd y e s) = acc x s.
  Proof.
    rewrite /acc /upd /= => Hne.
    rewrite acclidx_updlidx_hneq.
    - reflexivity.
    - apply: HE.pvar_lidx_hneq.
      assumption.
  Qed.

  Lemma bisim_refl E (s : t E) : bisim s s.
  Proof.
    move=> ty x; reflexivity.
  Qed.

  Lemma bisim_pvar_inv E (s1 s2 : t E) ty (x : HE.pvar E ty) :
    bisim s1 s2 -> acc x s1 = acc x s2.
  Proof.
    move=> Hs.
    exact: Hs.
  Qed.

End MakeHStorePreDefined.



(** Stores with heterogeneous values. The environment is updated with store. *)

Module Type HStore.

  Declare Module V : SsrOrder.
  Declare Module HE : HEnv with Module V := V.

  Local Open Scope hlist_scope.

  (* Syntax of types *)
  Parameter T : Set.

  (* Semantics of types *)
  Parameter V : T -> Set.

  (* Stores *)
  Parameter t : HE.t T -> Type.

  (* An empty store *)
  Parameter empty : t (HE.empty T).

  (* Update a variable that is already in the environment *)
  Parameter upd :
    forall (E : HE.t T) (ty : T) (x : HE.pvar E ty), V ty -> t E -> t E.

  (* Add a new variable or change the type of a variable *)
  Parameter add :
    forall (E : HE.t T) (x : V.t) (ty : T), V ty -> t E -> t (HE.add x ty E).

  (* Access a variable known to be in the environment *)
  Parameter accp : forall (E : HE.t T) (ty : T), HE.pvar E ty -> t E -> V ty.

  (* Access a variable *)
  Parameter acc : forall (E : HE.t T), V.t -> forall (ty : T), t E -> option (V ty).

  Axiom accp_upd_heq :
    forall E s tyx (x : HE.pvar E tyx) tyy (y : HE.pvar E tyy) (v : V tyy),
      HE.pvar_var x == HE.pvar_var y ->
      accp x (upd y v s) =v v.

  Axiom accp_upd_eq :
    forall E s ty (x y : HE.pvar E ty) (v : V ty),
      HE.pvar_var x == HE.pvar_var y ->
      accp x (upd y v s) = v.

  Axiom accp_upd_neq :
    forall E s tyx (x : HE.pvar E tyx) tyy (y : HE.pvar E tyy) (v : V tyy),
      HE.pvar_var x != HE.pvar_var y ->
      accp x (upd y v s) = accp x s.

  (* Bi-simulation *)

  Parameter bisim : forall (E : HE.t T), t E -> t E -> Prop.

  Axiom bisim_refl : forall (E : HE.t T) (s : t E), bisim s s.

  Axiom bisim_pvar_inv :
    forall (E : HE.t T) (s1 s2 : t E)(ty : T) (x : HE.pvar E ty),
      bisim s1 s2 -> accp x s1 = accp x s2.

End HStore.



Module MakeHStore (IV : SsrOrder) (H : HETEROGENEOUS) (IHE : HEnv with Module V := IV) <: HStore with Module V := IV with Module HE := IHE.

  Module V := IV.
  Module HE := IHE.

  Local Open Scope hlist_scope.
  Local Notation var := V.t.

  Definition T := H.T.

  Definition V := H.V.

  Definition t (E : HE.t T) : Type := hlist V (HE.vtypes E).

  Fixpoint defaults (types : list T) : hlist V types :=
    match types with
    | nil => hnil V
    | cons hd tl => Hcons (H.default hd) (defaults tl)
    end.

  Definition empty : t (HE.empty T) := defaults (HE.vtypes (HE.empty T)).

  (* Update a variable that is already in the environment *)
  Definition upd E (ty : T) (x : HE.pvar E ty) (v : V ty) (s : t E) : t E :=
    updlidx (HE.pvar_lidx x) v s.

  (* Add a new variable or change the type of a variable *)
  Definition add E (x : var) (ty : T) (v : V ty) (s : t E) : t (HE.add x ty E) :=
    eq_rect (ty::HE.vtypes E) (fun tys => hlist V tys) (Hcons v s)
            (HE.vtypes (HE.add x ty E))
            (Logic.eq_sym (HE.vtypes_add E x ty)).

  (* Access a variable known to be in the environment *)
  Definition accp (E : HE.t T) (ty : T) (x : HE.pvar E ty) (s : t E) : V ty :=
    acclidx (HE.pvar_lidx x) s.

  (* Access a variable *)
  Definition acc (E : HE.t T) (x : var) (ty : T) (s : t E) : option (V ty) :=
    match HE.find x E with
    | None => None
    | Some e =>
      match H.ty_dec ty (HE.vty e) with
      | left pf => Some (eq_rect (HE.vty e) (fun ty => V ty) (acclidx (HE.vidx e) s)
                                 ty (Logic.eq_sym pf))
      | right _ => None
      end
    end.

  Lemma accp_upd_heq
        E (s : t E) tyx (x : HE.pvar E tyx) tyy (y : HE.pvar E tyy) (v : V tyy) :
      HE.pvar_var x == HE.pvar_var y ->
      accp x (upd y v s) =v v.
  Proof.
    rewrite /accp /upd /= => Hxy. rewrite acclidx_updlidx_heq; first by reflexivity.
    apply: HE.pvar_lidx_heq. assumption.
  Qed.

  Lemma accp_upd_eq E (s : t E) ty (x y : HE.pvar E ty) (v : V ty) :
    HE.pvar_var x == HE.pvar_var y ->
    accp x (upd y v s) = v.
  Proof.
    move=> Hxy. apply: value_eq_eq. apply: accp_upd_heq. assumption.
  Qed.

  Lemma accp_upd_neq
        E (s : t E) tyx (x : HE.pvar E tyx) tyy (y : HE.pvar E tyy) (v : V tyy) :
    HE.pvar_var x != HE.pvar_var y ->
    accp x (upd y v s) = accp x s.
  Proof.
    rewrite /accp /upd /= => Hne. rewrite acclidx_updlidx_hneq; first by reflexivity.
    apply: HE.pvar_lidx_hneq. assumption.
  Qed.

  Lemma acc_add_eq E (s : t E) (x y : V.t) (ty : T) (v : V ty) :
    x == y ->
    acc x ty (add y v s) = Some v.
  Proof.
    move=> Hxy. rewrite /acc /add /=.
    move: (HE.find_add_eq E x ty) => [e [Hfind [Hty Hidx]]].
    move/eqP: Hxy => Hxy; subst. rewrite {}Hfind. case: (H.ty_dec ty (HE.vty e)).
    - move: e Hty Hidx. simplify_eqs.
    -
    (* Does not know how to proceed *)
  Abort.

  Lemma acc_upd_neq E (s : t E) (x : V.t) (ty : T) (y : HE.pvar E ty) (v : V ty) :
    x != HE.pvar_var y ->
    acc x ty (upd y v s) = acc x ty s.
  Proof.
    move=> Hne. rewrite /upd. rewrite /acc.
  Abort.

  (* Bi-simulation*)

  Definition bisim E (s1 s2 : t E) : Prop :=
    forall ty (x : HE.pvar E ty), accp x s1 = accp x s2.

  Lemma bisim_refl E (s : t E) : bisim s s.
  Proof.
    move=> ty x; reflexivity.
  Qed.

  Lemma bisim_pvar_inv (E : HE.t T) (s1 s2 : t E)(ty : T) (x : HE.pvar E ty) :
    bisim s1 s2 -> accp x s1 = accp x s2.
  Proof.
    move=> Hs. exact: Hs.
  Qed.

End MakeHStore.



(** State equality modulo values of a set of variables *)

From simplssrlib Require Import FSets.

Module TStateEqmod
       (X : SsrOrder)
       (Store : DTStore X) (VS : SsrFSet with Module SE := X).

  Section SEQM1.

    Variable vs : VS.t.

    Variable value : Type.

    Definition state_eqmod (s1 s2 : Store.t value) : Prop :=
      forall v, VS.mem v vs -> Store.acc v s1 = Store.acc v s2.

    Lemma state_eqmod_refl (s : Store.t value) : state_eqmod s s.
    Proof.
      move=> v Hmem; reflexivity.
    Qed.

    Lemma state_eqmod_sym (s1 s2 : Store.t value) :
      state_eqmod s1 s2 -> state_eqmod s2 s1.
    Proof.
      move=> Heqm v Hmem. rewrite (Heqm v Hmem). reflexivity.
    Qed.

    Lemma state_eqmod_trans (s1 s2 s3 : Store.t value) :
      state_eqmod s1 s2 -> state_eqmod s2 s3 -> state_eqmod s1 s3.
    Proof.
      move=> Heqm12 Heqm23 v Hmem. rewrite (Heqm12 v Hmem) (Heqm23 v Hmem).
      reflexivity.
    Qed.

    Global Instance state_eqmod_equiv : RelationClasses.Equivalence state_eqmod.
    Proof.
      split.
      - exact: state_eqmod_refl.
      - exact: state_eqmod_sym.
      - exact: state_eqmod_trans.
    Defined.

  End SEQM1.

  Module VSLemmas := FSetLemmas VS.

  Section SEQM2.

    Variable value : Type.

    Lemma state_eqmod_subset (vs1 vs2 : VS.t) (s1 s2 : Store.t value) :
      state_eqmod vs1 s1 s2 ->
      VS.subset vs2 vs1 ->
      state_eqmod vs2 s1 s2.
    Proof.
      move=> Heqm Hsub v Hmem. exact: (Heqm v (VSLemmas.mem_subset Hmem Hsub)).
    Qed.

    Lemma state_eqmod_add1 v (vs : VS.t) (s1 s2 : Store.t value) :
      state_eqmod (VS.add v vs) s1 s2 ->
      Store.acc v s1 = Store.acc v s2 /\ state_eqmod vs s1 s2.
    Proof.
      move=> Heqm; split.
      - apply: Heqm. apply: VSLemmas.mem_add2. exact: VS.E.eq_refl.
      - move=> x Hmem; apply: Heqm. apply: VSLemmas.mem_add3. assumption.
    Qed.

    Lemma state_eqmod_add2 v (vs : VS.t) (s1 s2 : Store.t value) :
      state_eqmod vs s1 s2 ->
      Store.acc v s1 = Store.acc v s2 ->
      state_eqmod (VS.add v vs) s1 s2.
    Proof.
      move=> Heqm Hv x Hmem. case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem.
      - by rewrite (eqP Hmem).
      - exact: (Heqm x Hmem).
    Qed.

    Lemma state_eqmod_union1 (vs1 vs2 : VS.t) (s1 s2 : Store.t value) :
      state_eqmod (VS.union vs1 vs2) s1 s2 ->
      state_eqmod vs1 s1 s2 /\ state_eqmod vs2 s1 s2.
    Proof.
      move=> Heqm; split; move=> v Hmem; apply: Heqm.
      - apply: VSLemmas.mem_union2. assumption.
      - apply: VSLemmas.mem_union3. assumption.
    Qed.

    Lemma state_eqmod_union2 (vs1 vs2 : VS.t) (s1 s2 : Store.t value) :
      state_eqmod vs1 s1 s2 ->
      state_eqmod vs2 s1 s2 ->
      state_eqmod (VS.union vs1 vs2) s1 s2.
    Proof.
      move=> Heqm1 Heqm2 v Hmem. case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
      - exact: (Heqm1 v Hmem).
      - exact: (Heqm2 v Hmem).
    Qed.

  End SEQM2.

End TStateEqmod.
