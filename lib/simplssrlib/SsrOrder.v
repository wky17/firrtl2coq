
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From simplssrlib Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Coq OrderedType with Boolean equality. *)

Module Type SsrOrderMinimal.
  Parameter t : eqType.
  Definition eqn : t -> t -> bool := fun x y => x == y.
  Parameter ltn : t -> t -> bool.
  Axiom ltn_trans : forall x y z : t, ltn x y -> ltn y z -> ltn x z.
  Axiom ltn_not_eqn : forall x y : t, ltn x y -> x != y.
  Parameter compare : forall x y : t, Compare ltn eqn x y.
End SsrOrderMinimal.

Module Type SsrOrder <: OrderedType.
  Parameter T : eqType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Parameter ltn : t -> t -> bool.
  Definition lt : t -> t -> Prop := fun x y => ltn x y.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.

  (* Derived facts *)
  Axiom ltn_trans : forall x y z : t, ltn x y -> ltn y z -> ltn x z.
  Axiom ltn_eqF : forall (x y : t), ltn x y -> (x == y) = false.
  Axiom ltnn : forall (x : t), ltn x x = false.
  Axiom nltn_eqVlt : forall (x y : t), (~~ ltn x y) = ((x == y) || ltn y x).
  Axiom ltn_neqAlt : forall (x y : t), ltn x y = (x != y) && ~~ (ltn y x).
  Axiom neq_ltn : forall (x y : t), (x != y) = (ltn x y) || (ltn y x).
End SsrOrder.

Module MakeSsrOrder (M : SsrOrderMinimal) <: SsrOrder.

  Definition T : eqType := M.t.

  Definition t : Type := T.

  Definition eq : t -> t -> Prop := fun x y => x == y.

  Definition ltn : t -> t -> bool := M.ltn.

  Definition lt : t -> t -> Prop := fun x y => ltn x y.

  Lemma eq_refl (x : t) : eq x x.
  Proof. exact: eqxx. Qed.

  Lemma eq_sym (x y : t) : eq x y -> eq y x.
  Proof. by rewrite /eq eq_sym. Qed.

  Lemma eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. move=> Hxy Hyz. rewrite (eqP Hxy). exact: Hyz. Qed.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z :=
    M.ltn_trans.

  Lemma lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof. move=> Hlt Heq. by move/negP: (M.ltn_not_eqn Hlt). Qed.

  Definition compare : forall x y : t, Compare lt eq x y := M.compare.
  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof. exact: lt_trans. Qed.

  Lemma ltn_eqF (x y : t) : ltn x y -> (x == y) = false.
  Proof. move=> H. apply/negP. exact: lt_not_eq. Qed.

  Lemma ltnn (x : t) : ltn x x = false.
  Proof. case H: (ltn x x) => //=. move: (ltn_eqF H). by rewrite eqxx. Qed.

  Lemma nltn_eqVlt (x y : t) : (~~ ltn x y) = ((x == y) || ltn y x).
  Proof.
    case Heq: (x == y) => /=.
    - by rewrite (eqP Heq) ltnn.
    - case Hlt: (ltn x y) => /=; symmetry.
      + apply/negP => Hyx. move: (ltn_trans Hlt Hyx). by rewrite ltnn.
      + move: Heq Hlt. case: (compare x y); by move=> ->.
  Qed.

  Lemma ltn_neqAlt (x y : t) : ltn x y = (x != y) && ~~ (ltn y x).
  Proof.
    rewrite nltn_eqVlt. case H: ((x != y) && ((y == x) || ltn x y)).
    - move/andP: H=> [H1 H2]. case/orP: H2 => H2.
      + by rewrite (eqP H2) eqxx in H1.
      + assumption.
    - apply/negP=> H2. move/negP: H; apply. rewrite (ltn_eqF H2) H2.
      by rewrite orbT.
  Qed.

  Lemma neq_ltn (x y : t) : (x != y) = (ltn x y) || (ltn y x).
  Proof.
    case: (compare x y) => H.
    - by rewrite (ltn_eqF H) H.
    - by rewrite H (eqP H) !ltnn.
    - by rewrite H eqtype.eq_sym (ltn_eqF H) orbT.
  Qed.

End MakeSsrOrder.



(* OrderedType with a default value and a successor function,
   useful for generating new values *)

Module Type HasSucc (Import T : SsrOrder).
  Parameter succ : t -> t.
End HasSucc.

Module Type HasLtn (Import T : SsrOrder).
  Parameter ltn : t -> t -> bool.
End HasLtn.

Module Type HasLtnSucc (Import T : SsrOrder) (Import L : HasLtn T) (Import S : HasSucc T).
  Parameter ltn_succ : forall (x : t), ltn x (succ x).
End HasLtnSucc.

Module Type SsrOrderWithDefaultSucc <: SsrOrder :=
  SsrOrder <+ HasDefault <+ HasSucc <+ HasLtnSucc.



(** Product of ordered types. *)

Module MakeProdOrderMinimal (O1 O2 : SsrOrder) <: SsrOrderMinimal with Definition t := prod_eqType O1.T O2.T.

  Definition t : eqType := prod_eqType O1.T O2.T.

  Definition eqn (x y : t) : bool := x == y.

  Definition ltn (x y : t) : bool :=
    O1.ltn (fst x) (fst y) || (fst x == fst y) && O2.ltn (snd x) (snd y).

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    case: x => x1 x2; case: y => y1 y2; case: z => z1 z2. rewrite /ltn /=.
    case/orP=> [Hxy1 | /andP [Hxy1 Hxy2]]; (case/orP=> [Hyz1 | /andP [Hyz1 Hyz2]]).
    - by rewrite (O1.lt_trans Hxy1 Hyz1).
    - by rewrite -(eqP Hyz1) Hxy1.
    - by rewrite (eqP Hxy1) Hyz1.
    - by rewrite (eqP Hxy1) (eqP Hyz1) eqxx (O2.lt_trans Hxy2 Hyz2) orbT.
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    case: x => x1 x2; case: y => y1 y2. rewrite /ltn /=.
    case/orP=> [Hxy1 | /andP [Hxy1 Hxy2]].
    - apply/eqP=> H. case: H => H1 H2. apply: (O1.lt_not_eq Hxy1). by apply/eqP.
    - apply/eqP=> H. case: H => H1 H2. apply: (O2.lt_not_eq Hxy2). by apply/eqP.
  Qed.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case: x => x1 x2; case: y => y1 y2. rewrite /ltn /eqn.
    case: (O1.compare x1 y1) => H1.
    - apply: LT => /=. by rewrite H1.
    - case: (O2.compare x2 y2) => H2.
      + apply: LT => /=. by rewrite H1 H2 orbT.
      + apply: EQ => /=. by rewrite (eqP H1) (eqP H2).
      + apply: GT => /=. by rewrite (eqP H1) eqxx H2 orbT.
    - apply: GT => /=. by rewrite H1.
  Defined.

End MakeProdOrderMinimal.

Module MakeProdOrder (O1 O2 : SsrOrder) <: SsrOrder
    with Definition T := prod_eqType O1.T O2.T.
  Module M := MakeProdOrderMinimal O1 O2.
  Module P := MakeSsrOrder M.
  Include P.
End MakeProdOrder.

Module MakeProdOrderWithDefaultSucc (O1 O2 : SsrOrderWithDefaultSucc) <: SsrOrderWithDefaultSucc
    with Definition T := prod_eqType O1.T O2.T.
  Module M := MakeProdOrderMinimal O1 O2.
  Module P := MakeSsrOrder M.
  Include P.
  Definition default : t := (O1.default, O2.default).
  Definition succ (x : t) : t := (O1.succ (fst x), O2.default).
  Lemma ltn_succ (x : t) : ltn x (succ x).
  Proof.
    case: x => x y. rewrite /ltn /succ /=. rewrite /M.ltn /=.
    by rewrite O1.ltn_succ /=.
  Qed.
End MakeProdOrderWithDefaultSucc.



(** Union of ordered types. *)

Module MakeUnionOrderMinimal
       (V1 : SsrOrder) (V2 : SsrOrder) <: SsrOrderMinimal.

  Inductive ut : Type :=
  | C1 : V1.t -> ut
  | C2 : V2.t -> ut.

  Definition uo_eqb (x y : ut) : bool :=
    match x, y with
    | C1 x, C1 y => x == y
    | C2 x, C2 y => x == y
    | _, _ => false
    end.

  Lemma uo_eqP : Equality.axiom uo_eqb.
  Proof.
    move=> x y.
    case H: (uo_eqb x y).
    - apply: ReflectT.
      move: H; case: y; case: x => //=.
      + move=> x y H.
        rewrite (eqP H).
        reflexivity.
      + move=> x y H.
        rewrite (eqP H).
        reflexivity.
    - apply: ReflectF.
      move: H; case: y; case: x => //=.
      + move=> x y H1 [] H2.
        apply/negPf: H1.
        rewrite H2; exact: eqxx.
      + move=> x y H1 [] H2.
        apply/negPf: H1.
        rewrite H2; exact: eqxx.
  Qed.

  Canonical uo_eqMixin := EqMixin uo_eqP.
  Canonical uo_eqType := Eval hnf in EqType ut uo_eqMixin.

  Definition t : eqType := uo_eqType.

  Definition eqn : t -> t -> bool := uo_eqb.

  Definition ltn (x y : t) : bool :=
    match x, y with
    | C1 x, C1 y => V1.ltn x y
    | C1 _, C2 _ => true
    | C2 _, C1 _ => false
    | C2 x, C2 y => V2.ltn x y
    end.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    case: z; case: y; case: x => //=.
    - exact: V1.lt_trans.
    - exact: V2.lt_trans.
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    case: y; case: x => //=.
    - move=> x y H. apply/negP. exact: V1.lt_not_eq.
    - move=> x y H. apply/negP. exact: V2.lt_not_eq.
  Qed.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case: y; case: x.
    - move=> x y.
      case H: (V1.compare x y).
      + apply: LT; assumption.
      + apply: EQ; assumption.
      + apply: GT; assumption.
    - move=> x y.
      by apply: GT.
    - move=> x y.
      by apply: LT.
    - move=> x y.
      case H: (V2.compare x y).
      + apply: LT; assumption.
      + apply: EQ; assumption.
      + apply: GT; assumption.
  Defined.

End MakeUnionOrderMinimal.

Module MakeUnionOrder
       (V1 : SsrOrder) (V2 : SsrOrder) <: SsrOrder.
  Module M := MakeUnionOrderMinimal V1 V2.
  Module O := MakeSsrOrder M.
  Include O.
  Definition c1 (x : V1.t) : t := M.C1 x.
  Definition c2 (x : V2.t) : t := M.C2 x.
End MakeUnionOrder.



(** A singleton ordered type. *)

Module UnitOrderMinimal <: SsrOrderMinimal.

  Definition t : eqType := unit_eqType.

  Definition eqn (x y : t) : bool := x == y.

  Definition ltn (x y : t) : bool := false.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof. done. Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof. done. Qed.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof. by apply: EQ. Defined.

End UnitOrderMinimal.

Module UnitOrder <: SsrOrder.
  Module O := MakeSsrOrder UnitOrderMinimal.
  Include O.
End UnitOrder.

