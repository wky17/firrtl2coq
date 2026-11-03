
From Coq Require Import Arith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat div eqtype.
From simplssrlib Require Import Types SsrOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section NatLemmas.

  Theorem nat_strong_ind (P : nat -> Prop) :
    (forall n : nat, (forall k : nat, k < n -> P k) -> P n) ->
    forall n : nat, P n.
  Proof.
    move=> IH. have H0: P 0.
    { apply: IH. move=> k H; by inversion H. }
    have H: forall n m, m <= n -> P m.
    { move=> n; elim: n.
      - move=> m Hm. rewrite leqn0 in Hm. rewrite (eqP Hm); exact: H0.
      - move=> n H m Hmn. apply: IH. move=> k Hkm.
        apply: H. exact: (leq_trans Hkm Hmn). }
    move=> n. apply: IH. move=> k Hkn. exact: (H _ _ (ltnW Hkn)).
  Qed.

  Lemma addn_add n m :
    n + m = (n + m)%coq_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma subn_sub n m :
    n - m = (n - m)%coq_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma muln_mul n m :
    n * m = (n * m)%coq_nat.
  Proof.
    reflexivity.
  Qed.

  Lemma leq_le_iff n m : n <= m <-> (n <= m)%coq_nat.
  Proof.
    elim: m n => /=.
    - move=> n; split => H.
      + rewrite /leq subn0 in H. rewrite (eqP H). done.
      + inversion_clear H. done.
    - move=> m IH n; split => H.
      + apply: (proj1 (Nat.le_pred_le_succ n m)). apply: (proj1 (IH (n.-1))).
        rewrite -subn1 leq_subLR addnC addn1. exact: H.
      + rewrite -addn1 addnC -leq_subLR subn1. apply: (proj2 (IH (n.-1))).
        apply: (proj2 (Nat.le_pred_le_succ n m)). exact: H.
  Qed.

  Lemma leq_le n m : n <= m -> (n <= m)%coq_nat.
  Proof.
    exact: (proj1 (leq_le_iff n m)).
  Qed.

  Lemma le_leq n m : (n <= m)%coq_nat -> n <= m.
  Proof.
    exact: (proj2 (leq_le_iff n m)).
  Qed.

  Lemma ltn_lt_iff n m : n < m <-> (n < m)%coq_nat.
  Proof.
    split => H.
    - apply: (proj1 (Nat.le_succ_l n m)). apply: leq_le. exact: H.
    - apply: le_leq. apply: (proj2 (Nat.le_succ_l n m)). exact: H.
  Qed.

  Lemma ltn_lt n m : n < m -> (n < m)%coq_nat.
  Proof.
    exact: (proj1 (ltn_lt_iff n m)).
  Qed.

  Lemma lt_ltn n m : (n < m)%coq_nat -> n < m.
  Proof.
    exact: (proj2 (ltn_lt_iff n m)).
  Qed.

  Lemma geq_ge_iff n m : n >= m <-> (n >= m)%coq_nat.
  Proof.
    split => H.
    - exact: (leq_le H).
    - exact: (le_leq H).
  Qed.

  Lemma geq_ge n m : n >= m -> (n >= m)%coq_nat.
  Proof.
    exact: (proj1 (geq_ge_iff n m)).
  Qed.

  Lemma ge_geq n m : (n >= m)%coq_nat -> n >= m.
  Proof.
    exact: (proj2 (geq_ge_iff n m)).
  Qed.

  Lemma gtn_gt_iff n m : n > m <-> (n > m)%coq_nat.
  Proof.
    split => H.
    - exact: (ltn_lt H).
    - exact: (lt_ltn H).
  Qed.

  Lemma gtn_gt n m : n > m -> (n > m)%coq_nat.
  Proof.
    exact: (proj1 (gtn_gt_iff n m)).
  Qed.

  Lemma gt_gtn n m : (n > m)%coq_nat -> n > m.
  Proof.
    exact: (proj2 (gtn_gt_iff n m)).
  Qed.

  Lemma ltn_leq_sub n m :
    n < m -> n <= m - 1.
  Proof.
    rewrite leq_eqVlt. move=> /orP. case => H.
    - rewrite -(eqP H). rewrite subn1 Nat.pred_succ. exact: leqnn.
    - move: (leq_sub2r 1 H). rewrite subn1 Nat.pred_succ. exact: ltnW.
  Qed.

  Lemma subn_gtn : forall n m r, n < m - r -> r < m.
  Proof.
    move=> n m r H.
    have: r < m.
    - rewrite -(subn_gt0 r m).
      induction n.
      + assumption.
      + by auto.
    - exact.
  Qed.

  Lemma lt_subr_addl : forall n m r : nat, (n < m - r) == (n + r < m).
  Proof.
    move=> n m r.
    case Hrm: (r < m).
    - rewrite -(ltn_add2r r n (m - r)).
      rewrite (subnK (ltnW Hrm)).
      exact: eqxx.
    - (* left is false *)
      move/negP/negP: (Hrm) => Hle.
      rewrite -leqNgt in Hle.
      move: (subn_eq0 m r) => Hsub.
      rewrite Hle in Hsub.
      move/idP/eqP: Hsub => Hsub.
      rewrite Hsub => {Hsub}.
      rewrite ltn0.
      (* right is false *)
      rewrite -(leq_add2l n m r) in Hle.
      move: (leq_trans (leq_addl n m) Hle) => {Hle} Hle.
      rewrite (leqNgt m (n + r)) in Hle.
      move/negPf: Hle => Hle.
      rewrite Hle.
      exact: eqxx.
  Qed.

  Lemma lt_sub1r_add1l : forall n m : nat, (n < m.-1) == (n.+1 < m).
  Proof.
    move=> n m.
    rewrite -{2}addn1 -subn1.
    exact: (lt_subr_addl n m 1).
  Qed.

  Lemma lt_sub1l_le (n m : nat) : (n.-1 < m) -> (n <= m).
  Proof.
    move=> H. move: (ltn_lt H) => {H} H.
    move: (Nat.lt_pred_le _ _ H) => {H} /le_leq H. exact: H.
  Qed.

  Lemma gt0_sub1F :
    forall n : nat, n > 0 -> n = n - 1 -> False.
  Proof.
    move=> n; elim: n.
    - done.
    - move=> n IH Hgt Heq.
      rewrite -add1n addKn add1n in Heq.
      apply: IH.
      + rewrite -Heq.
        assumption.
      + rewrite -{2}Heq -add1n addKn.
        reflexivity.
  Qed.

  Lemma ltn_leq_trans n m p :
    m < n -> n <= p -> m < p.
  Proof.
    move=> Hmn Hnp.
    move/ltP: Hmn => Hmn.
    move/leP: Hnp => Hnp.
    apply/ltP.
    exact: (Lt.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma ltn_addn m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
  Proof.
    move=> /ltP H1 /ltP H2. apply/ltP. exact: (Nat.add_lt_mono _ _ _ _ H1 H2).
  Qed.

  Lemma ltn_leq_addn x y a b : x < a -> y <= b -> x + y < a + b.
  Proof.
    move => /ltP H1 /leP H2. apply/ltP. exact: (Nat.add_lt_le_mono _ _ _ _ H1 H2).
  Qed.

  Lemma leq_ltn_addn x y a b : x <= a -> y < b -> x + y < a + b.
  Proof.
    move=> H1 H2. rewrite (addnC x) (addnC a). exact: ltn_leq_addn.
  Qed.

  Lemma ltb_leq n m : (n <? m) = true -> n <= m.
  Proof.
    move=> H. apply/leP. move: (Nat.ltb_lt n m) => [H1 _]. move: (H1 H) => {H1 H} H.
    auto with arith.
  Qed.

  Lemma eqn_ltn_gtn_cases :
    forall (m n : nat), (m == n) || (m < n) || (n < m).
  Proof.
    move=> m n. case Heq: (m == n) => /=; first done.
    move/idP/negP: Heq. rewrite neq_ltn. by apply.
  Qed.

  Lemma ltn_leq_mul_ltn m1 m2 n1 n2 :
    0 < m2 ->
    m1 < n1 -> m2 <= n2 -> m1 * m2 < n1 * n2.
  Proof.
    move=> H H1 H2. rewrite leq_eqVlt in H2. move/orP: H2; case => H2.
    - rewrite -(eqP H2) => {H2}.
      + rewrite ltn_mul2r H H1. done.
      + exact: ltn_mul.
  Qed.

  Lemma ltn_leq_mul_leq m1 m2 n1 n2 :
    m1 < n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
  Proof.
    move=> H1 H2. move: (ltnW H1) => {H1} H1. exact: leq_mul.
  Qed.

  Lemma leq_ltn_mul_ltn m1 m2 n1 n2 :
    0 < m1 ->
    m1 <= n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
  Proof.
    move=> H H1 H2. rewrite (mulnC m1 m2) (mulnC n1 n2). exact: ltn_leq_mul_ltn.
  Qed.

  Lemma leq_ltn_mul_leq m1 m2 n1 n2 :
    m1 <= n1 -> m2 < n2 -> m1 * m2 <= n1 * n2.
  Proof.
    move=> H1 H2. move: (ltnW H2) => {H2} H2. exact: leq_mul.
  Qed.

  Lemma addr_ltn n m : 0 < m -> n < n + m.
  Proof.
    move=> Hm. rewrite -{1}(addn0 n) ltn_add2l. assumption.
  Qed.

  Lemma addl_ltn n m : 0 < m -> n < m + n.
  Proof.
    rewrite addnC. exact: addr_ltn.
  Qed.

  Lemma div2_succ n :
    Nat.div2 (S n) = Nat.odd n + Nat.div2 n.
  Proof.
    case H: (Nat.odd n).
    - move: (proj1 (Nat.odd_spec n) H) => {H} [m H].
      rewrite {n}H.
      have: (((2 * m) + 1).+1 = 2 * (1 + m)) by ring.
      move=> ->. rewrite Nat.div2_double (plus_comm (2 * m) 1)
                         Nat.div2_succ_double.
      reflexivity.
    - move/negPn: H => H. move: (proj1 (Nat.even_spec n) H) => {H} [m H].
      rewrite {n}H Nat.div2_double Nat.div2_succ_double.
      reflexivity.
  Qed.

  Lemma expn_pow n m : n ^ m = Nat.pow n m.
  Proof.
    elim: m.
    - reflexivity.
    - move=> m IH. rewrite expnS (Nat.pow_succ_r _ _ (Nat.le_0_l m)) IH.
      reflexivity.
  Qed.

  Lemma ssrodd_odd n :
    odd n = Nat.odd n.
  Proof.
    elim: n => /=.
    - reflexivity.
    - move=> n IH. rewrite {}IH Nat.odd_succ Nat.negb_odd. reflexivity.
  Qed.

  Lemma addn_subn a b c :
    b <= c ->
    (a + b == c) = (a == c - b).
  Proof.
    move=> Hbc. case H: (a == c - b).
    - move: H. rewrite -(eqn_add2r b) (subnK Hbc). by apply.
    - move/negP: H => Hne. apply/negP => H. apply: Hne.
      rewrite -(eqn_add2r b) (subnK Hbc). exact: H.
  Qed.

  Lemma sub_diff_add_rdiff m n : n - (n - m) + (m - n) = m.
  Proof.
    case/orP: (leq_total n m) => H.
    - rewrite -subn_eq0 in H. rewrite (eqP H) subn0. rewrite subn_eq0 in H.
      exact: (subnKC H).
    - rewrite -subn_eq0 in H. rewrite (eqP H) addn0. rewrite subn_eq0 in H.
      exact: (subKn H).
  Qed.

  Lemma ssrdiv2_succ n :
    (n.+1)./2 = odd n + n./2.
  Proof.
    rewrite /half -/uphalf -/half uphalf_half.
    reflexivity.
  Qed.

  Lemma ssrdiv2_div2 n :
    n./2 = Nat.div2 n.
  Proof.
    elim: n.
    - reflexivity.
    - move=> n IH.
      rewrite div2_succ ssrdiv2_succ ssrodd_odd IH.
      reflexivity.
  Qed.

  Lemma modn_muln2_subn1 n : 0 < n -> (n.*2 - 1) %% n = n - 1.
  Proof.
    move=> Hn. rewrite -addnn -(addnBA _ Hn) modnDl.
    apply: modn_small. rewrite subn1 (prednK Hn).
    exact: leqnn.
  Qed.

  Lemma divn_muln2_subn1 n : 0 < n -> (n.*2 - 1) %/ n = 1.
  Proof.
    move=> Hn. move: (divn_eq (n.*2-1) n).
    rewrite (modn_muln2_subn1 Hn) -addnn -{1}(addnBA _ Hn).
    move/eqP => H. rewrite eqn_add2r -{1}(mul1n n) (eqn_pmul2r Hn) in H.
    apply/eqP. rewrite eq_sym. assumption.
  Qed.

  Lemma divn01 x n :
    x < n.*2 -> x %/ n = 0 \/ x %/ n = 1.
  Proof.
    move=> Hx.
    have Hn: n > 0.
    { case: n Hx; first by move=> H; inversion H. move=> n _.
      exact: ltn0Sn. }
    case Hxn: (x < n).
    - rewrite (divn_small Hxn). left; reflexivity.
    - rewrite ltnNge in Hxn. move/negPn: Hxn => Hxn. right.
      rewrite -add1n in Hx. move: (leq_sub2r 1 Hx).
      rewrite addKn => {Hx} Hx.
      move: (leq_div2r n Hx) (leq_div2r n Hxn).
      rewrite divnn Hn /= (divn_muln2_subn1 Hn) => {Hx Hxn} Hx Hxn.
      apply/eqP; rewrite eqn_leq. by rewrite Hx Hxn.
  Qed.

  Lemma odd_divn x n :
    x < n.*2 -> nat_of_bool (odd (x %/ n)) = x %/ n.
  Proof.
    move=> Hx. by case: (divn01 Hx) => ->.
  Qed.

  Lemma odd_divn_eucl x n :
    x < n.*2 ->
    x = odd (x %/ n) * n + x %% n.
  Proof.
    move=> H. rewrite (odd_divn H) -(divn_eq x n). reflexivity.
  Qed.

  Lemma ltn_ltn_addn_divn x y n :
    x < n -> y < n -> (x + y) %/ n = 0 \/ (x + y) %/ n = 1.
  Proof.
    move=> Hx Hy. apply: divn01. rewrite -addnn. exact: (ltn_addn Hx Hy).
  Qed.

  Lemma divn_eq0 n m :
    n %/ m = 0 -> m = 0 \/ n < m.
  Proof.
    move=> Hdivn. move: (divn_eq n m).
    rewrite Hdivn mul0n add0n. move=> Hmodn. case Hm0: (m == 0).
    - left; by rewrite (eqP Hm0).
    - right; rewrite ltnNge. apply/negP => Hmn. rewrite -divn_gt0 in Hmn.
      + rewrite Hdivn in Hmn; by inversion Hmn.
      + rewrite ltn_neqAle eq_sym. move/idP/negP: Hm0.
        move=> H; rewrite H /=. done.
  Qed.

  Lemma divn_gt0_eq0 n m :
    n %/ m = 0 -> m > 0 -> n < m.
  Proof.
    move=> Hdivn Hm.
    case: (divn_eq0 Hdivn).
    - move=> H; rewrite {}H in Hm *. by inversion Hm.
    - by apply.
  Qed.

  Lemma ltn_1_2expnS n :
    1 < 2 ^ n.+1.
  Proof.
    rewrite expnS. apply: leq_pmulr. rewrite expn_gt0. done.
  Qed.

  Lemma modn_muln_modn_l n x y :
    (n %% (x * y)) %% x = n %% x.
  Proof.
    have: (n %% x) = (n %/ (x * y) * (x * y) + n %% (x * y)) %% x.
    { rewrite -(divn_eq n (x * y)). reflexivity. }
    rewrite -modnDm.
    have: (n %/ (x * y) * (x * y)) %% x = 0.
    { rewrite (mulnC x y) mulnA modnMl. reflexivity. }
    move=> ->. rewrite add0n. rewrite modn_mod. move=> <-. reflexivity.
  Qed.

  Lemma modn_muln_modn_r n x y :
    (n %% (x * y)) %% y = n %% y.
  Proof.
    rewrite (mulnC x y). exact: modn_muln_modn_l.
  Qed.

  Lemma expn2_gt0 n : 0 < 2^n.
  Proof.
    by rewrite expn_gt0.
  Qed.

  Lemma expn2_gt1 n : 1 < 2^n.+1.
  Proof.
    rewrite expnS. apply: leq_pmulr. by rewrite expn_gt0.
  Qed.

  Lemma modn_subn n m : m <= n -> n %% m = (n - m) %% m.
  Proof.
    move=> H. apply/eqP. rewrite -(eqn_modDl m).
    rewrite addnC modnDr. rewrite addnC (subnK H). exact: eqxx.
  Qed.

  Lemma mod_sub n m :
    (m <> 0)%coq_nat ->
    (m <= n)%coq_nat -> ((n mod m) = (n - m) mod m)%coq_nat.
  Proof.
    move=> Hm Hmn. rewrite -(Nat.mod_add (n - m) 1 _ Hm).
    rewrite Nat.mul_1_l (Nat.sub_add _ _ Hmn).
    reflexivity.
  Qed.

  Lemma modn_modulo (n m : nat) : m != 0 -> n %% m = Nat.modulo n m.
  Proof.
    move=> Hm0. case H: (n < m)%N.
    - rewrite (modn_small H) Nat.mod_small; first reflexivity.
      exact: (ltn_lt H).
    - move/negP/idP: H; rewrite -leqNgt => H.
      move: m H Hm0. induction n using nat_strong_ind.
      move=> m Hmn Hm0. have Hne: m <> 0 by move/eqP: Hm0; apply.
      rewrite (modn_subn Hmn) (mod_sub Hne (leq_le Hmn)).
      case Hsub: ((n - m) < m)%N.
      + rewrite (modn_small Hsub) (Nat.mod_small _ _ (ltn_lt Hsub)).
        reflexivity.
      + move/negP/idP: Hsub; rewrite -leqNgt => Hsub.
        apply: H.
        * rewrite -lt0n in Hm0. rewrite -{2}(subn0 n). apply: ltn_sub2l.
          -- exact: (ltn_leq_trans Hm0 Hmn).
          -- exact: Hm0.
        * exact: Hsub.
        * exact: Hm0.
  Qed.

  Lemma divn_div (n m : nat) : n %/ m = Nat.div n m.
  Proof.
    case Hm: (m == 0).
    - rewrite (eqP Hm) divn0 /=. reflexivity.
    - move/negP/idP: Hm => Hm. have Hne: (m <> 0) by move/eqP: Hm; apply.
      move: (eq_refl n). rewrite {1}(divn_eq n m).
      rewrite {3}(Nat.div_mod n m Hne).
      rewrite -(modn_modulo _ Hm) -addn_add. rewrite eqn_add2r.
      rewrite -muln_mul mulnC. rewrite -lt0n in Hm. rewrite (eqn_pmul2l Hm).
      move/eqP=> H. exact: H.
  Qed.

End NatLemmas.



(** EQTYPE modules. *)

Module NatEqtype <: EQTYPE.
  Definition t := nat_eqType.
End NatEqtype.

Module OptionNatEqtype <: EQTYPE.
  Module OptionNat := MakeOptionReflectable(NatEqtype).
  Definition t := OptionNat.option_eqType.
End OptionNatEqtype.



(** An ordered type for nat with a Boolean equality in mathcomp. *)

Module NatOrderMinimal <: SsrOrderMinimal.

  Definition t : eqType := nat_eqType.

  Definition eqn : t -> t -> bool := fun x y : t => x == y.

  Definition ltn : t -> t -> bool := fun x y => x < y.

  Hint Unfold eqn ltn.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof. exact: ltn_trans. Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof. move=> H. by rewrite (ltn_eqF H). Qed.

  Lemma compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case H: (Nat.compare x y).
    - apply: EQ. move: (PeanoNat.Nat.compare_eq_iff x y) => [Hc _].
      apply/eqP. exact: (Hc H).
    - apply: LT. move: (PeanoNat.Nat.compare_lt_iff x y) => [Hc _].
      apply/ltP. exact: (Hc H).
    - apply: GT. move: (PeanoNat.Nat.compare_gt_iff x y) => [Hc _].
      apply/ltP. exact: (Hc H).
  Defined.

End NatOrderMinimal.

Module NatOrder <: SsrOrder := MakeSsrOrder NatOrderMinimal.



Ltac deduce_compare_cases H :=
  match type of H with
  | is_true (_ < _)%N =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    let H5 := fresh in
    (move: (H) => H1; rewrite ltnNge in H1);
    (move: (H1) => H2; rewrite leq_eqVlt negb_or in H2; case/andP: H2=> H2 H3);
    (move/negPf: H3; move/negPf: H2; move/negPf: H1; move=> H1 H2 H3);
    (move: (ltnW H) => H4);
    (move: (ltnW H) => /eqP H5)
  | is_true (_ <= _)%N =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    (move: (H) => H1; rewrite leqNgt in H1; move/negPf: H1 => H1);
    (move: (H); move/eqP=> H2);
    (move: (H) => H3; rewrite leq_eqVlt in H3)
  | (?n = ?m)%N =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    (move: (ltnn n) => H1; rewrite {2}H in H1);
    (move: (ltnn m) => H2; rewrite -{2}H in H2);
    (move: (leqnn n) => H3; rewrite {2}H in H3);
    (move: (leqnn m) => H4; rewrite -{2}H in H4)
  end.
