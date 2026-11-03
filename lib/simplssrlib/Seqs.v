
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.
From simplssrlib Require Import SsrOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SeqLemmas.

  Variable A : Type.

  Variable B : Type.

  Variable default : A.

  Lemma singleton_seq (l : seq A) :
    size l = 1%N -> exists x : A, l = x :: nil.
  Proof.
    elim: l => //=.
    move=> hd tl; elim tl => //=.
    move=> _ _; exists hd.
    reflexivity.
  Qed.

  Lemma last_decomp (l : seq A) (n : nat) :
    size l = (n + 1)%N -> exists s x, l = rcons s x.
  Proof.
    move: l n. apply: last_ind => /=.
    - by case.
    - move=> l x IH n H. exists l; exists x; reflexivity.
  Qed.

  Lemma last_default_irrelevant (l : seq A) (n : nat) b1 b2 :
    size l = (n + 1)%N -> last b1 l = last b2 l.
  Proof.
    move: l n b1 b2. apply: last_ind => /=.
    - move=> n b1 b2; by case n.
    - move=> l lst IH n b1 b2 H. rewrite !last_rcons. reflexivity.
  Qed.

  Lemma nth_cons (x : A) (l : list A) (n : nat) :
    0 < n -> nth default (x::l) n = nth default l (n - 1).
  Proof. case: n => //=. move=> n _. by rewrite subn1 -pred_Sn. Qed.

  Lemma nth_tl (l : list A) (n : nat) : nth default (tl l) n = nth default l (n + 1).
  Proof.
    case: l => [| x l] //=.
    - by rewrite 2!nth_nil.
    - rewrite nth_cons; last by rewrite addn_gt0 orbT. by rewrite addn1 subn1 -pred_Sn.
  Qed.

  Lemma drop_take (s : seq A) n m :
    n <= m -> m < size s -> drop (m - n) (take m s) = take n (drop (m - n) s).
  Proof.
    elim: s n m => [| x s IH] n m Hnm Hms //. rewrite /= in Hms.
    case: m Hnm Hms.
    - rewrite leqn0 => /eqP ->. rewrite subnn drop0 take0. reflexivity.
    - move=> m Hnm Hms. rewrite -(addn1 m) -(addn1 (size s)) ltn_add2r in Hms.
      rewrite leq_eqVlt in Hnm. case/orP: Hnm => Hnm.
      + rewrite (eqP Hnm) subnn !drop0. reflexivity.
      + rewrite ltnS in Hnm. rewrite take_cons. rewrite !(subSn Hnm) !drop_cons.
        exact: (IH _ _ Hnm Hms).
  Qed.

  Lemma take_take (s : seq A) (n m : nat) : take n (take m s) = take (minn n m) s.
  Proof.
    elim: s n m => [| x s IH] n m //.
    case: m => [| m] //. case: n => [| n] //. rewrite minnSS.
    rewrite !take_cons. rewrite IH. reflexivity.
  Qed.

  Lemma nseq_addn (x : A) n m : nseq (n + m) x = nseq n x ++ nseq m x.
  Proof.
    elim: n m => [| n IHn] m //=. rewrite IHn. reflexivity.
  Qed.

  Lemma drop_nseq (x : A) n m : drop n (nseq m x) = nseq (m - n) x.
  Proof.
    case Hnm: (m <= n).
    - rewrite -{1}(subnK Hnm). rewrite -drop_drop.
      have Hm: m = size (nseq m x) by rewrite size_nseq.
      rewrite {2}Hm. rewrite drop_size /=. rewrite -subn_eq0 in Hnm.
      rewrite (eqP Hnm) /=. reflexivity.
    - move/idP/negP: Hnm. rewrite -ltnNge => Hnm. move: (subnK (ltnW Hnm)) => H.
      rewrite -{1}H. rewrite addnC nseq_addn.
      rewrite drop_size_cat; last by rewrite size_nseq. reflexivity.
  Qed.

  Lemma take_nseq (x : A) n m : take n (nseq m x) = nseq (minn n m) x.
  Proof.
    case Hnm: (n <= m).
    - move/minn_idPl: (Hnm) => ->. move: (subnK Hnm) => <-.
      rewrite addnC nseq_addn. rewrite take_size_cat; last by rewrite size_nseq.
      reflexivity.
    - move/idP/negP: Hnm. rewrite -ltnNge => Hnm.
      move/minn_idPr: (ltnW Hnm) => ->. rewrite take_oversize; first by reflexivity.
      rewrite size_nseq. exact: (ltnW Hnm).
  Qed.

  Lemma drop_nseq_more (s : seq A) (x : A) n m :
    n <= m -> drop n s = nseq (size s - n) x -> drop m s = nseq (size s - m) x.
  Proof.
    move=> Hmn Hdn. move: (subnK Hmn) => H. rewrite -{1}H.
    rewrite -drop_drop. rewrite Hdn. rewrite drop_nseq. rewrite -subnDA.
    rewrite addnC H. reflexivity.
  Qed.

  Lemma take_nseq_less_minn (s : seq A) (x : A) n m :
    m <= n -> take n s = nseq (minn n (size s)) x ->
    take m s = nseq (minn m (size s)) x.
  Proof.
    move=> Hmn. case Hns: (n <= size s).
    - move/minn_idPl: (Hns) => ->. move/minn_idPl: (leq_trans Hmn Hns) => ->.
      elim: s n m Hmn Hns => [| e s IH] n m Hmn Hns.
      + rewrite leqn0 in Hns. rewrite (eqP Hns) in Hmn.
        rewrite leqn0 in Hmn. rewrite (eqP Hmn). reflexivity.
      + case: n Hmn Hns => [| n] Hmn Hns.
        * rewrite leqn0 in Hmn. rewrite (eqP Hmn). reflexivity.
        * case: m Hmn => [| m] Hmn.
          -- reflexivity.
          -- rewrite /= !ltnS in Hmn Hns. rewrite !take_cons.
             rewrite -(addn1 n) -(addn1 m). rewrite (addnC n) (addnC m).
             rewrite !nseq_addn /=. case => -> H.
             rewrite (IH _ _ Hmn Hns H). reflexivity.
    - move/idP/negP: Hns. rewrite -ltnNge => Hsn. move/minn_idPr: (ltnW Hsn) => ->.
      rewrite (take_oversize (ltnW Hsn)). move=> ->. rewrite size_nseq.
      case Hms: (m <= size s).
      + rewrite take_nseq. move/minn_idPl: (Hms) => ->. reflexivity.
      + move/idP/negP: Hms. rewrite -ltnNge => Hsm. move/minn_idPr: (ltnW Hsm) => ->.
        rewrite take_oversize; first reflexivity.
        rewrite size_nseq. exact: (ltnW Hsm).
  Qed.

  Lemma take_nseq_less (s : seq A) (x : A) n m :
    m <= n -> n <= size s -> take n s = nseq n x -> take m s = nseq m x.
  Proof.
    move=> Hmn Hns. move/minn_idPl: (leq_trans Hmn Hns) => {2}<-.
    move/minn_idPl: (Hns) => {2}<-. exact: (take_nseq_less_minn Hmn).
  Qed.

  Lemma catsl_inj (s1 s2 s3 : seq A) : s1 ++ s2 = s1 ++ s3 -> s2 = s3.
  Proof. elim: s1 s2 s3 => [| hd tl IH] s2 s3 //=. case. exact: IH. Qed.

  Lemma catsr_inj (s1 s2 s3 : seq A) : s2 ++ s1 = s3 ++ s1 -> s2 = s3.
  Proof.
    elim: s1 s2 s3 => [| hd tl IH] s2 s3 /=.
    - rewrite !cats0. by apply.
    - rewrite -!cat_rcons. move=> H. move: (IH _ _ H) => {H} H.
      move: (rcons_inj H). case. by apply.
  Qed.

  Lemma In_rcons x (s : seq A) l :
    List.In x (rcons s l) <-> List.In x s \/ x = l.
  Proof.
    elim: s => [| hd tl IH] /=.
    - split; case=> H //=.
      + right. symmetry. assumption.
      + left; symmetry. assumption.
    - move: IH=> [IH1 IH2]. split; case => H /=.
      + left; left. assumption.
      + case: (IH1 H) => {H} H.
        * left; right; assumption.
        * right; assumption.
      + case: H => H.
        * left; assumption.
        * right. exact: (IH2 (or_introl H)).
      + right. exact: (IH2 (or_intror H)).
  Qed.

  Lemma incl_consl (a : A) (l m : seq A) :
    incl (a :: l) m -> In a m /\ incl l m.
  Proof.
    move=> H. split.
    - apply: (H a). exact: in_eq.
    - move=> x Hinx. apply: (H x). apply: List.in_cons. assumption.
  Qed.

  Lemma incl_empty (s : seq A) :
    incl s [::] -> s = [::].
  Proof.
    elim: s => [| x s IH] //=. move=> H. move: (incl_consl H) => [H1 H2].
    apply: False_ind. exact: (List.in_nil H1).
  Qed.

  (* Tail-recursive flatten *)

  Fixpoint tflatten_rec res (ss : seq (seq A)) :=
    match ss with
    | [::] => res
    | hd::tl => tflatten_rec (catrev hd res) tl
    end.

  Definition tflatten ss := tflatten_rec [::] ss.

  Lemma tflatten_rec_rcons pre ss s :
    tflatten_rec pre (rcons ss s) = rev s ++ tflatten_rec pre ss.
  Proof.
    elim: ss pre => [| hd tl IH] //=. exact: catrevE.
  Qed.

  Lemma tflatten_rcons ss s :
    tflatten (rcons ss s) = rev s ++ tflatten ss.
  Proof. exact: tflatten_rec_rcons. Qed.

  Lemma tflatten_rec_flatten pre ss :
    tflatten_rec pre ss = rev (flatten ss) ++ pre.
  Proof.
    move: ss. apply: last_ind => //=. move=> ss s IH.
    rewrite flatten_rcons. rewrite rev_cat. rewrite -catA. rewrite -IH.
    exact: tflatten_rec_rcons.
  Qed.

  Lemma tflatten_flatten ss :
    tflatten ss = rev (flatten ss).
  Proof.
    rewrite /tflatten. rewrite tflatten_rec_flatten. rewrite cats0. reflexivity.
  Qed.

  Lemma tflatten_rec_expand pre ss :
    tflatten_rec pre ss = tflatten_rec [::] ss ++ pre.
  Proof.
    move: ss pre. apply: last_ind => //=.
    move=> ss s IH pre. rewrite tflatten_rec_rcons. rewrite IH.
    rewrite tflatten_rec_rcons. rewrite catA. reflexivity.
  Qed.

  Lemma tflatten_rec_cons pre s ss :
    tflatten_rec pre (s::ss) = tflatten_rec (catrev s pre) ss.
  Proof. reflexivity. Qed.

  Lemma tflatten_cons s ss :
    tflatten (s::ss) = tflatten ss ++ (rev s).
  Proof.
    rewrite /tflatten tflatten_rec_cons. rewrite tflatten_rec_expand.
    reflexivity.
  Qed.

  Lemma tflatten_rec_cat pre ss1 ss2 :
    tflatten_rec pre (ss1 ++ ss2) = tflatten_rec (tflatten_rec pre ss1) ss2.
  Proof.
    rewrite tflatten_rec_flatten. rewrite flatten_cat. rewrite rev_cat.
    rewrite -catA. rewrite -tflatten_rec_flatten. rewrite -tflatten_rec_flatten.
    reflexivity.
  Qed.

  Lemma tflattens_cat ss1 ss2 :
    tflatten (ss1 ++ ss2) = tflatten ss2 ++ tflatten ss1.
  Proof.
    rewrite /tflatten. rewrite tflatten_rec_cat. rewrite tflatten_rec_expand.
    reflexivity.
  Qed.

  Lemma filter_tflatten ss (p : pred A) :
    filter p (tflatten ss) = tflatten [seq filter p i | i <- ss].
  Proof.
    rewrite (tflatten_flatten [seq filter p i | i <- ss]).
    rewrite -filter_flatten. rewrite -filter_rev. rewrite -tflatten_flatten.
    reflexivity.
  Qed.

  Lemma split_cons (x : A * B) (s : seq (A * B)) :
    split (x::s) = (x.1::(split s).1, x.2::(split s).2).
  Proof.
    rewrite /=. case Hs: (split s) => [sa sb] /=. case: x => [xa xb] /=.
    reflexivity.
  Qed.

  Lemma split_cat (s1 s2 : seq (A * B)) :
    split (s1 ++ s2) = ((split s1).1 ++ (split s2).1, (split s1).2 ++ (split s2).2).
  Proof.
    elim: s1 => [| [hd1a hd1b] tl1 IH] //=.
    - by case: (split s2).
    - move: IH. case: (split (tl1 ++ s2)) => [cs1 cs2].
      case: (split tl1) => [tl11 tl12]. case: (split s2) => [tl21 tl22] /=.
      case=> ? ?; subst. reflexivity.
  Qed.

  Lemma split_rcons (s : seq (A * B)) (x : A * B) :
    split (rcons s x) = (rcons (split s).1 x.1, rcons (split s).2 x.2).
  Proof.
    move: s x. apply: last_ind.
    - move=> [xa xb] /=. reflexivity.
    - move=> s [ya yb] IH [xa xb] /=. rewrite IH /=.
      rewrite -(cats1 s) rcons_cat. rewrite split_cat /=.
      rewrite -cats1 cat_rcons. rewrite -cats1 cat_rcons. reflexivity.
  Qed.

  Lemma split_rev (s : seq (A * B)) :
    split (rev s) = (rev (split s).1, rev (split s).2).
  Proof.
    elim: s => [| [hda hdb] tl IH] //=. rewrite rev_cons.
    rewrite split_rcons. rewrite IH /=. case: (split tl) => [s1 s2] /=.
    rewrite !rev_cons. reflexivity.
  Qed.

  (* Tail-recursive map *)

  Section MapRev.

    Variable f : A -> B.

    Fixpoint mapr_rec res es :=
      match es with
      | [::] => res
      | hd::tl => mapr_rec (f hd::res) tl
      end.

    Definition mapr es := mapr_rec [::] es.

    Lemma mapr_rec_cons res e es : mapr_rec res (e::es) = mapr_rec (f e::res) es.
    Proof. reflexivity. Qed.

    Lemma mapr_rec_split res es : mapr_rec res es = mapr_rec [::] es ++ res.
    Proof.
      elim: es res => [| e es IH] //= res. rewrite (IH (f e::res)).
      rewrite (IH [:: f e]). rewrite -cat_rcons. rewrite -cats1. reflexivity.
    Qed.

    Lemma mapr_cons e es : mapr (e::es) = rcons (mapr es) (f e).
    Proof.
      rewrite /mapr. rewrite mapr_rec_cons. rewrite mapr_rec_split. rewrite -cats1.
      reflexivity.
    Qed.

    Lemma mapr_rec_rcons res es e :
      mapr_rec res (rcons es e) = f e :: mapr_rec res es.
    Proof. by elim: es res e => [| e1 es IH] //=. Qed.

    Lemma mapr_rcons es e : mapr (rcons es e) = f e :: mapr es.
    Proof. exact: mapr_rec_rcons. Qed.

    Lemma mapr_rec_cat res es1 es2 :
      mapr_rec res (es1 ++ es2) = mapr_rec (mapr_rec res es1) es2.
    Proof. by elim: es1 res es2 => [| e1 es1 IH] res es2 //=. Qed.

    Lemma mapr_cat es1 es2 : mapr (es1 ++ es2) = mapr es2 ++ mapr es1.
    Proof.
      rewrite /mapr. rewrite mapr_rec_cat. rewrite mapr_rec_split.
      reflexivity.
    Qed.

    Lemma size_mapr es : size (mapr es) = size es.
    Proof.
      elim: es => [| e es IH] //=. rewrite mapr_cons. rewrite size_rcons. by rewrite IH.
    Qed.

    Lemma mapr_rec_rev_map res es : mapr_rec res es = rev (map f es) ++ res.
    Proof.
      elim: es res => [| e es IH] res //=. rewrite IH. rewrite rev_cons.
      rewrite cat_rcons. reflexivity.
    Qed.

    Lemma mapr_rev_map es : mapr es = rev (map f es).
    Proof. rewrite /mapr. rewrite mapr_rec_rev_map. by rewrite cats0. Qed.

    Lemma mapr_map_rev es : mapr es = map f (rev es).
    Proof. rewrite map_rev. exact: mapr_rev_map. Qed.

  End MapRev.

End SeqLemmas.

Lemma map_tflatten {A B : Type} (f : A -> B) ss :
  map f (tflatten ss) = tflatten (map (map f) ss).
Proof.
  rewrite (tflatten_flatten (map (map f) ss)). rewrite -map_flatten.
  rewrite -map_rev. rewrite -tflatten_flatten. reflexivity.
Qed.

Section EqSeqLemmas.

  Variable A : eqType.

  Variable B : eqType.

  Lemma singleton_eq (x y : A) : ([::x] == [::y]) = (x == y).
  Proof.
    case H: (x == y).
    - by rewrite (eqP H) eqxx.
    - apply/negP => /eqP [] Heq. by rewrite Heq eqxx in H.
  Qed.

  Lemma in_In (x : A) (s : seq A) : x \in s <-> In x s.
  Proof.
    elim: s => [| y ys IH] //=. rewrite in_cons. case H: (x == y) => /=.
    - split.
      + move=> _. left. rewrite (eqP H). reflexivity.
      + done.
    - split.
      + move=> Hin. right. apply/IH. exact: Hin.
      + case.
        * move=> Hyx; rewrite Hyx eqxx in H; discriminate.
        * move/IH. by apply.
  Qed.

  Lemma map_l_nil (f : A -> B) (l : seq A) :
    (map f l == [::]) = (l == [::]).
  Proof. by case: l. Qed.

  Lemma seq_neq_split (x y : A) (xs ys : seq A) :
    (x::xs != y::ys) = ((x != y) || (xs != ys)).
  Proof.
    rewrite negb_and -/eqseq. case Hxy: (x == y) => /=; by trivial.
  Qed.

  Lemma has_catrev p (l1 l2 : seq A) : has p (catrev l1 l2) = has p l1 || has p l2.
  Proof.
    elim: l1 l2 => [| hd tl IH] l2 //=. rewrite -cat1s catrev_catr has_cat IH /=.
    rewrite orbF (Bool.orb_comm (has p tl)). reflexivity.
  Qed.

  Lemma all_catrev p (l1 l2 : seq A) : all p (catrev l1 l2) = all p l1 && all p l2.
  Proof.
    elim: l1 l2 => [| hd tl IH] l2 //=. rewrite -cat1s catrev_catr all_cat IH /=.
    rewrite andbT (Bool.andb_comm (all p tl)). reflexivity.
  Qed.

  Lemma cat_nseql (x : A) s1 s2 n :
    s1 ++ s2 = nseq n x -> s1 = nseq (size s1) x.
  Proof.
    move=> H. have: size (s1 ++ s2) = size (nseq n x) by rewrite H.
    rewrite size_cat size_nseq => Hn. rewrite -Hn in H.
    rewrite nseq_addn in H. move/eqP: H. rewrite eqseq_cat; last by rewrite size_nseq.
    move/andP=> [/eqP <- _]. reflexivity.
  Qed.

  Lemma cat_nseqr (x : A) s1 s2 n :
    s1 ++ s2 = nseq n x -> s2 = nseq (size s2) x.
  Proof.
    move=> H. have: size (s1 ++ s2) = size (nseq n x) by rewrite H.
    rewrite size_cat size_nseq => Hn. rewrite -Hn in H.
    rewrite nseq_addn in H. move/eqP: H. rewrite eqseq_cat; last by rewrite size_nseq.
    move/andP=> [_ /eqP <-]. reflexivity.
  Qed.

  Lemma in_rcons (x : A) s (y : A) :
    x \in rcons s y = (x \in s) || (x == y).
  Proof.
    elim: s => [| hd tl IH] /=.
    - rewrite mem_seq1. reflexivity.
    - rewrite !in_cons. rewrite IH. rewrite orbA. reflexivity.
  Qed.

  Lemma in_split_rev_l {C : Type} (x : A) (s : seq (A * C)) :
    (x \in (split (rev s)).1) = (x \in (split s).1).
  Proof.
    rewrite split_rev /=. rewrite mem_rev. reflexivity.
  Qed.

  Lemma in_split_rev_r {C : Type} (x : B) (s : seq (C * B)) :
    (x \in (split (rev s)).2) = (x \in (split s).2).
  Proof.
    rewrite split_rev /=. rewrite mem_rev. reflexivity.
  Qed.


  (* Tail recursive filter function *)

  Variable p : pred A.

  Fixpoint tfilter_rec (res es : seq A) :=
    match es with
    | [::] => res
    | hd::tl => if p hd
                then tfilter_rec (hd::res) tl
                else tfilter_rec res tl
    end.

  Definition tfilter es := tfilter_rec [::] es.

  Lemma tfilter_rec_filter res es :
    tfilter_rec res es = filter p (rev es) ++ res.
  Proof.
    rewrite filter_rev. elim: es res => [| e es IH] res //=. case: (p e).
    - rewrite rev_cons. rewrite cat_rcons. rewrite -IH. reflexivity.
    - exact: IH.
  Qed.

  Lemma tfilter_filter es : tfilter es = filter p (rev es).
  Proof.
    rewrite /tfilter. rewrite tfilter_rec_filter. rewrite cats0. reflexivity.
  Qed.

  Lemma tfilter_rec_expand res es :
    tfilter_rec res es = tfilter_rec [::] es ++ res.
  Proof.
    rewrite !tfilter_rec_filter. rewrite !filter_rev. rewrite cats0.
    reflexivity.
  Qed.

  Lemma tfilter_rec_cat res es1 es2 :
    tfilter_rec res (es1 ++ es2) =
    tfilter_rec (tfilter_rec res es1) es2.
  Proof.
    rewrite !tfilter_rec_filter. rewrite !filter_rev.
    rewrite filter_cat. rewrite rev_cat. rewrite catA. reflexivity.
  Qed.

  Lemma tfilter_cat es1 es2 :
    tfilter (es1 ++ es2) = tfilter es2 ++ tfilter es1.
  Proof.
    rewrite /tfilter. rewrite tfilter_rec_cat. rewrite tfilter_rec_expand.
    reflexivity.
  Qed.

  Lemma tfilter_rec_rcons res es e :
    tfilter_rec res (rcons es e) = if p e
                                   then e::(tfilter_rec res es)
                                   else tfilter_rec res es.
  Proof.
    rewrite !tfilter_rec_filter. rewrite !filter_rev filter_rcons. case: (p e).
    - rewrite rev_rcons. rewrite cat_cons. reflexivity.
    - reflexivity.
  Qed.

  Lemma tfilter_rcons es e :
    tfilter (rcons es e) = if p e
                           then e::(tfilter es)
                           else tfilter es.
  Proof.
    rewrite /tfilter. rewrite tfilter_rec_rcons. reflexivity.
  Qed.

  Lemma tfilter_rec_cons res e es :
    tfilter_rec res (e::es) = if p e
                              then tfilter_rec (e::res) es
                              else tfilter_rec res es.
  Proof. reflexivity. Qed.

  Lemma tfilter_cons e es :
    tfilter (e::es) = if p e
                      then rcons (tfilter es) e
                      else tfilter es.
  Proof.
    rewrite /tfilter. rewrite tfilter_rec_cons. rewrite tfilter_rec_expand.
    rewrite cats1. reflexivity.
  Qed.

  Lemma tfilter_nil : tfilter [::] = [::].
  Proof. reflexivity. Qed.

End EqSeqLemmas.

Section UnzipLemmas.

  Variable A : eqType.

  Variable B : eqType.

  Lemma unzip1_l_nil (pairs : seq (A * B)) :
    (unzip1 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip1 map_l_nil. Qed.

  Lemma unzip2_l_nil (pairs : seq (A * B)) :
    (unzip2 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip2 map_l_nil. Qed.

End UnzipLemmas.

Section PrefixOf.

  Variable A : eqType.

  Implicit Type s : seq A.

  Fixpoint prefix_of (s1 s2 : seq A) : bool :=
    match s1 with
    | [::] => true
    | x1::s1 => match s2 with
                | [::] => false
                | x2::s2 => (x1 == x2) && (prefix_of s1 s2)
                end
    end.

  Lemma prefix_of_nil s : prefix_of nil s.
  Proof. done. Qed.

  Lemma prefix_of_is_nil s : prefix_of s nil = (s == nil).
  Proof. by case: s. Qed.

  Lemma prefix_of_take s1 s2 :
    prefix_of s1 s2 = (s1 == take (size s1) s2).
  Proof.
    elim: s1 s2 => [|x1 s1 IH1] /=.
    - by move=> ?; rewrite take0 eqxx.
    - case => //=. move=> x2 s2. rewrite eqseq_cons IH1. reflexivity.
  Qed.

  Lemma prefix_of_size s1 s2 : prefix_of s1 s2 -> size s1 <= size s2.
  Proof.
    rewrite prefix_of_take. move=> /eqP ->. rewrite size_take.
    case H: (size s1 < size s2) => //=. by apply: ltnW.
  Qed.

  Lemma prefix_of_cons x1 s1 x2 s2 :
    prefix_of (x1::s1) (x2::s2) = ((x1 == x2) && prefix_of s1 s2).
  Proof. reflexivity. Qed.

  Lemma prefix_of_rcons s1 s2 x :
    prefix_of s1 s2 -> prefix_of s1 (rcons s2 x).
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 tl2] x //=.
    move=> /andP [/eqP -> Htl]. by rewrite eqxx (IH1 _ _ Htl).
  Qed.

  Lemma prefix_of_belast x s1 s2 :
    prefix_of (x::s1) s2 -> prefix_of (belast x s1) s2.
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 [| tl2_hd tl2_tl]] x //=.
    - by rewrite andbF.
    - move=> /andP [/eqP -> /andP [/eqP -> H]]. rewrite eqxx andTb. apply: IH1.
      by rewrite prefix_of_cons eqxx H.
  Qed.

  Lemma prefix_of_refl s : prefix_of s s.
  Proof. elim: s => //=. move=> ? ? ->; by rewrite eqxx. Qed.

  Lemma prefix_of_antisym s1 s2 : (prefix_of s1 s2 && prefix_of s2 s1) = (s1 == s2).
  Proof.
    elim: s1 s2 => [| hd1 tl1 IH1] /=.
    - move=> s2. rewrite prefix_of_is_nil eq_sym. reflexivity.
    - case=> [|hd2 tl2] => //=. rewrite (andbA ((hd1 == hd2) && prefix_of tl1 tl2)).
      rewrite -(andbA (hd1 == hd2)). rewrite (andbC (prefix_of tl1 tl2)).
      rewrite andbA. rewrite (eq_sym hd2). rewrite Bool.andb_diag. rewrite -andbA.
      rewrite IH1. reflexivity.
  Qed.

  Lemma prefix_of_trans s1 s2 s3 :
    prefix_of s1 s2 -> prefix_of s2 s3 -> prefix_of s1 s3.
  Proof.
    elim: s1 s2 s3 => [| hd1 tl1 IH1] [| hd2 tl2] [| hd3 tl3] //=.
    move=> /andP [/eqP -> H12] /andP [/eqP -> H23].
      by rewrite eqxx (IH1 _ _ H12 H23).
  Qed.

  Lemma prefix_of_cons_ident x s1 s2 :
    prefix_of (x::s1) s2 -> prefix_of s1 s2 -> constant (x::s1).
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 [| tl2_hd tl2_tl]] x //=.
    - by rewrite andbF.
    - move=> /andP [/eqP <- /andP [/eqP <- H1]]. move=> /andP [/eqP -> H2].
      rewrite eqxx andTb. apply: (IH1 _ _ _ H2).
      by rewrite prefix_of_cons eqxx andTb H1.
  Qed.

  Variable default : A.

  Lemma prefix_of_nth s1 s2 i :
    prefix_of s1 s2 -> i < size s1 -> nth default s1 i = nth default s2 i.
  Proof.
    rewrite prefix_of_take. move=> /eqP Hs Hi. rewrite Hs (nth_take _ Hi).
    reflexivity.
  Qed.

End PrefixOf.

Section Fold.

  Context {A : Type} {B : Type} {R : relation B} {E : Equivalence R}.

  Context {f : B -> A -> B}.

  Context {Rf_swap : forall (a1 a2 : A) (b : B),
              R (f (f b a1) a2) (f (f b a2) a1)}.

  Context {R_foldl : forall (b1 b2 : B) (ls : seq A),
              R b1 b2 -> R (foldl f b1 ls) (foldl f b2 ls)}.

  Lemma foldl_cons (hd : A) (tl : seq A) (r : B) :
    R (foldl f r (hd::tl)) (f (foldl f r tl) hd).
  Proof.
    elim: tl hd r => /=.
    - move=> hd r. reflexivity.
    - move=> tl_hd tl_tl IH hd r. rewrite -(IH hd (f r tl_hd)).
      move: (Rf_swap tl_hd hd r) => H. rewrite (R_foldl _ H). reflexivity.
  Qed.

End Fold.

Module SeqOrderMinimal (X : SsrOrder) <: SsrOrderMinimal.
  Definition t := seq_eqType X.T.
  Definition eqn (x y : t) : bool := x == y.
  Fixpoint ltn (x y : t) : bool :=
    match x, y with
    | _, [::] => false
    | [::], hd::_ => true
    | hd1::tl1, hd2::tl2 => (X.ltn hd1 hd2) || ((hd1 == hd2) && (ltn tl1 tl2))
    end.
  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    elim: x y z.
    - case; first by trivial.
      move=> hdy tly. elim; by trivial.
    - move=> hdx tlx IHx. case; first by trivial.
      move=> hdy tly. case; first by trivial.
      move=> hdz tlz /= /orP H1 /orP H2. case: H1; case: H2.
      + move=> Hyz Hxy. by rewrite (X.lt_trans Hxy Hyz).
      + move=> /andP [Hyz_hd Hyz_tl] Hxy_hd. by rewrite -(eqP Hyz_hd) Hxy_hd.
      + move=> Hyz_hd /andP [Hxy_hd Hxy_tl]. by rewrite (eqP Hxy_hd) Hyz_hd.
      + move=> /andP [Hyz_hd Hyz_tl] /andP [Hxy_hd Hxy_tl].
        by rewrite (eqP Hxy_hd) (eqP Hyz_hd) eqxx (IHx _ _ Hxy_tl Hyz_tl) orbT.
  Qed.
  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    elim: x y.
    - case; by trivial.
    - move=> hdx tlx IHx. case; first by trivial.
      move=> hdy tly /=. rewrite seq_neq_split. case/orP.
      + move=> Hhd. move/negP: (X.lt_not_eq Hhd). by move=> ->.
      + move/andP=> [Hhd Htl]. by rewrite (IHx _ Htl) orbT.
  Qed.
  Definition compare (x y : t) : Compare ltn eqn x y.
    elim: x y.
    - case.
      + by apply: EQ.
      + move=> hdy tly. by apply: LT.
    - move=> hdx tlx IHx. case.
      + by apply: GT.
      + move=> hdy tly. case (X.compare hdx hdy) => Hhd.
        * apply: LT. by rewrite /= Hhd.
        * case: (IHx tly) => Htl.
          -- apply: LT. by rewrite /= Hhd Htl orbT.
          -- apply: EQ. apply/andP; rewrite -/eqseq. split; first assumption.
             rewrite /eq in Htl. apply/eqP. exact: (eqP Htl).
          -- apply: GT. by rewrite /= eq_sym Hhd Htl orbT.
        * apply: GT. by rewrite /= Hhd.
  Defined.
End SeqOrderMinimal.

Module SeqOrder (X : SsrOrder) <: SsrOrder.
  Module Y := SeqOrderMinimal X.
  Module M := MakeSsrOrder Y.
  Include M.
End SeqOrder.
