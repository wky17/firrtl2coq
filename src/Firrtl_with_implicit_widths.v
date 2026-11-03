From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope firrtl with firrtl.

Section LoFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt (*| AsFixed*) | AsClock | AsAsync .

  Lemma ucast_eq_dec : forall {x y : ucast}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition ucast_eqn (x y : ucast) : bool :=
  match x, y with
  | AsUInt, AsUInt | AsSInt, AsSInt | AsClock, AsClock
  | AsAsync, AsAsync => true
  | _, _ => false
  end.
  Lemma ucast_eqP : Equality.axiom ucast_eqn.
  Proof.
  unfold Equality.axiom, ucast_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical ucast_eqMixin := EqMixin ucast_eqP.
  Canonical ucast_eqType := Eval hnf in EqType ucast ucast_eqMixin.

  Inductive eunop : Set :=
  | Upad : nat -> eunop
  | Ushl : nat -> eunop
  | Ushr : nat -> eunop
  | Ucvt
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr : nat -> nat -> eunop
  | Uhead : nat -> eunop
  | Utail : nat -> eunop.

  Lemma eunop_eq_dec : forall {x y : eunop}, {x = y} + {x <> y}.
  Proof.  decide equality ; apply Nat.eq_dec.  Qed.
  Definition eunop_eqn (x y : eunop) : bool :=
  match x, y with
  | Upad n, Upad m | Ushl n, Ushl m | Ushr n, Ushr m | Uhead n, Uhead m | Utail n, Utail m =>
        n == m
  | Ucvt, Ucvt | Uneg, Uneg | Unot, Unot | Uandr, Uandr | Uorr, Uorr | Uxorr, Uxorr => true
  | Uextr n n0, Uextr m m0 => (n == m) && (n0 == m0)
  | _, _ => false
  end.
  Lemma eunop_eqP : Equality.axiom eunop_eqn.
  Proof.
  unfold Equality.axiom, eunop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  1,2,3,5,6: destruct (n == n0) eqn: Hn ; move /eqP : Hn => Hn ;
        first (by rewrite Hn ; apply ReflectT ; reflexivity) ;
        last  (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  destruct (n == n1) eqn: Hn ; move /eqP : Hn => Hn ;
        last (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  rewrite Hn andTb.
  destruct (n0 == n2) eqn: Hn0 ; move /eqP : Hn0 => Hn0 ;
        last (by apply ReflectF ; contradict Hn0 ; injection Hn0 ; done).
  rewrite Hn0 ; apply ReflectT ; reflexivity.
  Qed.
  Canonical eunop_eqMixin := EqMixin eunop_eqP.
  Canonical eunop_eqType := Eval hnf in EqType eunop eunop_eqMixin.

  Inductive bcmp : Set :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

  Lemma bcmp_eq_dec : forall {x y : bcmp}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition bcmp_eqn (x y : bcmp) : bool :=
  match x, y with
  | Blt, Blt | Bleq, Bleq | Bgt, Bgt | Bgeq, Bgeq | Beq, Beq | Bneq, Bneq => true
  | _, _ => false
  end.
  Lemma bcmp_eqP : Equality.axiom bcmp_eqn.
  Proof.
  unfold Equality.axiom, bcmp_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical bcmp_eqMixin := EqMixin bcmp_eqP.
  Canonical bcmp_eqType := Eval hnf in EqType bcmp bcmp_eqMixin.

  Inductive ebinop : Set :=
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Brem
  (* | Bsdiv *)
  (* | Bsrem *)
  | Bcomp: bcmp -> ebinop
  | Bdshl
  | Bdshr
  | Band
  | Bor
  | Bxor
  | Bcat .

  Lemma ebinop_eq_dec : forall {x y : ebinop}, {x = y} + {x <> y}.
  Proof.  decide equality ; apply bcmp_eq_dec.  Qed.
  Definition ebinop_eqn (x y : ebinop) : bool :=
  match x, y with
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bdiv, Bdiv | Brem, Brem
  | Bdshl, Bdshl | Bdshr, Bdshr | Band, Band | Bor, Bor | Bxor, Bxor | Bcat, Bcat => true
  | Bcomp b, Bcomp c => b == c
  | _, _ => false
  end.
  Lemma ebinop_eqP : Equality.axiom ebinop_eqn.
  Proof.
  unfold Equality.axiom, ebinop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
        first (by apply ReflectT ; rewrite Hb ; reflexivity) ;
        last  (by apply ReflectF ; injection ; done).
  Qed.
  Canonical ebinop_eqMixin := EqMixin ebinop_eqP.
  Canonical ebinop_eqType := Eval hnf in EqType ebinop ebinop_eqMixin.

  Variable var : eqType.

  (* mux, valid, sub-xxx, TBD *)
  Inductive fexpr : Type :=
  | Econst : fgtyp -> bits -> fexpr
  | Ecast : ucast -> fexpr -> fexpr
  | Eprim_unop : eunop -> fexpr -> fexpr
  | Eprim_binop : ebinop -> fexpr -> fexpr -> fexpr
  | Emux : fexpr -> fexpr -> fexpr -> fexpr
  | Evalidif : fexpr -> fexpr -> fexpr
  | Eref : var -> fexpr
  .

  Lemma fexpr_eq_dec : forall {x y : fexpr}, {x = y} + {x <> y}.
  Proof.  decide equality ; try apply fgtyp_eq_dec ; try apply ucast_eq_dec ;
  try apply eunop_eq_dec ; try apply ebinop_eq_dec.
  destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
        first (by left  ; exact Hb) ;
        last  (by right ; exact Hb).
  destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
        first (by left  ; exact Hs) ;
        last  (by right ; exact Hs).
  Qed.
  Fixpoint fexpr_eqn (x y : fexpr) : bool :=
  match x, y with
  | Econst tx sx, Econst ty sy => (tx == ty) && (sx == sy)
  | Ecast  cx ex, Ecast  cy ey => (cx == cy) && fexpr_eqn ex ey
  | Eprim_unop ux ex, Eprim_unop uy ey => (ux == uy) && fexpr_eqn ex ey
  | Eprim_binop ox ex fx, Eprim_binop oy ey fy => (ox == oy) && fexpr_eqn ex ey && fexpr_eqn fx fy
  | Emux ex fx gx, Emux ey fy gy => fexpr_eqn ex ey && fexpr_eqn fx fy && fexpr_eqn gx gy
  | Evalidif ex fx, Evalidif ey fy => fexpr_eqn ex ey && fexpr_eqn fx fy
  | Eref vx, Eref vy => vx == vy
  | _, _ => false
  end.
  Lemma fexpr_eqP : Equality.axiom fexpr_eqn.
  Proof.
  unfold Equality.axiom, fexpr_eqn.
  induction x, y ;
        try (by apply ReflectF ; discriminate).
  * destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
          last by (apply ReflectF ; contradict Hf ; injection Hf ; done).
    rewrite Hf andTb.
    destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
          last by (apply ReflectF ; contradict Hb ; injection Hb ; done).
    rewrite Hb ; apply ReflectT ; reflexivity.
  * fold fexpr_eqn in IHx ; fold fexpr_eqn.
    destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
          last by (apply ReflectF ; contradict Hu ; injection Hu ; done).
    rewrite Hu andTb.
    specialize (IHx y) ; apply reflect_iff in IHx.
    destruct (fexpr_eqn x y) eqn: Hx.
    + apply ReflectT.
      destruct IHx as [_ IHx] ; specialize (IHx Logic.eq_refl).
      rewrite IHx ; reflexivity.
    + apply ReflectF ; injection ; intro.
      destruct IHx as [IHx _].
      apply IHx in H0 ; done.
  * fold fexpr_eqn in IHx ; fold fexpr_eqn.
    destruct (e == e0) eqn: He ; move /eqP : He => He ;
          last by (apply ReflectF ; contradict He ; injection He ; done).
    rewrite He andTb.
    specialize (IHx y) ; apply reflect_iff in IHx.
    destruct (fexpr_eqn x y).
    + apply ReflectT.
      destruct IHx as [_ IHx] ; specialize (IHx Logic.eq_refl).
      rewrite IHx ; reflexivity.
    + apply ReflectF ; injection ; intro.
      destruct IHx as [IHx _].
      apply IHx in H0 ; done.
  * fold fexpr_eqn in IHx1 ; fold fexpr_eqn in IHx2 ; fold fexpr_eqn.
    destruct (e == e0) eqn: He ; move /eqP : He => He ;
          last by (apply ReflectF ; contradict He ; injection He ; done).
    rewrite He andTb.
    specialize (IHx1 y1) ; apply reflect_iff in IHx1.
    destruct (fexpr_eqn x1 y1) ;
          last by (apply ReflectF ; injection ; intros _ H0 ;
                   destruct IHx1 as [IHx1 _] ;
                   apply IHx1 in H0 ; done).
    destruct IHx1 as [_ IHx1] ; specialize (IHx1 Logic.eq_refl).
    rewrite IHx1 andTb.
    specialize (IHx2 y2) ; apply reflect_iff in IHx2.
    destruct (fexpr_eqn x2 y2) ;
          last by (apply ReflectF ; injection ; intros H0 ;
                   destruct IHx2 as [IHx2 _] ;
                   apply IHx2 in H0 ; done).
    destruct IHx2 as [_ IHx2] ; specialize (IHx2 Logic.eq_refl).
    rewrite IHx2.
    apply ReflectT ; reflexivity.
  * fold fexpr_eqn in IHx1 ; fold fexpr_eqn in IHx2 ; fold fexpr_eqn in IHx3 ; fold fexpr_eqn.
    specialize (IHx1 y1) ; apply reflect_iff in IHx1.
    destruct (fexpr_eqn x1 y1) ;
          last by (apply ReflectF ; injection ; intros _ _ H0 ;
                   destruct IHx1 as [IHx1 _] ;
                   apply IHx1 in H0 ; done).
    destruct IHx1 as [_ IHx1] ; specialize (IHx1 Logic.eq_refl).
    rewrite IHx1 andTb.
    specialize (IHx2 y2) ; apply reflect_iff in IHx2.
    destruct (fexpr_eqn x2 y2) ;
          last by (apply ReflectF ; injection ; intros _ H0 ;
                   destruct IHx2 as [IHx2 _] ;
                   apply IHx2 in H0 ; done).
    destruct IHx2 as [_ IHx2] ; specialize (IHx2 Logic.eq_refl).
    rewrite IHx2 andTb.
    specialize (IHx3 y3) ; apply reflect_iff in IHx3.
    destruct (fexpr_eqn x3 y3) ;
          last by (apply ReflectF ; injection ; intros H0 ;
                   destruct IHx3 as [IHx3 _] ;
                   apply IHx3 in H0 ; done).
    destruct IHx3 as [_ IHx3] ; specialize (IHx3 Logic.eq_refl).
    rewrite IHx3.
    apply ReflectT ; reflexivity.
  * fold fexpr_eqn in IHx1 ; fold fexpr_eqn in IHx2 ; fold fexpr_eqn.
    specialize (IHx1 y1) ; apply reflect_iff in IHx1.
    destruct (fexpr_eqn x1 y1) ;
          last by (apply ReflectF ; injection ; intros _ H0 ;
                   destruct IHx1 as [IHx1 _] ;
                   apply IHx1 in H0 ; done).
    destruct IHx1 as [_ IHx1] ; specialize (IHx1 Logic.eq_refl).
    rewrite IHx1 andTb.
    specialize (IHx2 y2) ; apply reflect_iff in IHx2.
    destruct (fexpr_eqn x2 y2) ;
          last by (apply ReflectF ; injection ; intros H0 ;
                   destruct IHx2 as [IHx2 _] ;
                   apply IHx2 in H0 ; done).
    destruct IHx2 as [_ IHx2] ; specialize (IHx2 Logic.eq_refl).
    rewrite IHx2.
    apply ReflectT ; reflexivity.
  * destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
          last by (apply ReflectF ; contradict Hs ; injection Hs ; done).
    rewrite Hs.
    apply ReflectT ; reflexivity.
  Qed.
  Canonical fexpr_eqMixin := EqMixin fexpr_eqP.
  Canonical fexpr_eqType := Eval hnf in EqType fexpr fexpr_eqMixin.

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Lemma ruw_eq_dec : forall {x y : ruw}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition ruw_eqn (x y : ruw) : bool :=
  match x, y with
  | old, old | new, new | undefined, undefined => true
  | _, _ => false
  end.
  Lemma ruw_eqP : Equality.axiom ruw_eqn.
  Proof.
  unfold Equality.axiom, ruw_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical ruw_eqMixin := EqMixin ruw_eqP.
  Canonical ruw_eqType := Eval hnf in EqType ruw ruw_eqMixin.

  Record freader_port : Type :=
    mk_freader_port
      {
        addr : var;
        data : var;
        en : var;
        clk : var
      }.

Record fwriter_port : Type :=
    mk_fwriter_port
      {
        addr0 : var;
        data0 : var;
        en0 : var;
        clk0 : var;
        mask : var
      }.

  Record fmem : Type :=
    mk_fmem
      {
        mid : var;
        data_type : fgtyp;
        depth : nat;
        reader : seq freader_port;
        writer : seq fwriter_port;
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : fexpr -> fexpr -> rst.
  
  Record freg : Type :=
    mk_freg
      {
        rid : var;
        type : fgtyp;
        clock : var;
        reset : rst
      }.

  Inductive fport : Type :=
  | Finput : var -> fgtyp -> fport
  | Foutput : var -> fgtyp -> fport
  .

  Record finst : Type :=
    mk_finst
      {
        iid : var;
        imid : var;
        iports : seq fport
      }.

  Inductive fstmt : Type :=
  | Sskip
  | Swire : var -> fgtyp -> fstmt
  | Sreg : freg -> fstmt
  | Smem : fmem -> fstmt
  | Sinst : finst -> fstmt
  | Snode : var -> fexpr -> fstmt
  | Sfcnct : var -> fexpr -> fstmt
  (*| Spcnct : fexpr -> fexpr -> fstmt*)
  | Sinvalid : var -> fstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : fexpr -> fstmt -> fstmt -> fstmt
  | Sstop : fexpr -> fexpr -> nat -> fstmt
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  .

  (* TBD *)
  Inductive fmodule : Type :=
  | FInmod : var -> seq fport -> seq fstmt -> fmodule
  | FExmod : var -> seq fport -> seq fstmt -> fmodule
  .

  Inductive fcircuit : Type := Fcircuit : var -> seq fmodule -> fcircuit.

End LoFirrtl.

(* Commented from here by David N. Jansen because there were errors.

(************************************************************)
(* Parallel semantics model *)


Module Type ExprStore (V : SsrOrder) (TE : TypEnv with Module SE := V).
  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := (option (fexpr V.T)).

  Parameter t : Type.
  Parameter empty : t.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.

End ExprStore.

Module ExprType (V:SsrOrder)<: HasDefaultTyp.
  Definition t : Type := option (fexpr V.T).
  Definition default : t := None. (* Econst V.T (Fuint 0) [::]. *)
End ExprType.

Module MakeExprStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <:
  ExprStore V TE.
  Module ExprTypeV := ExprType V.
  Include MakeTStoreMap V ExprTypeV.
  Module Lemmas := FMapLemmas TE.
End MakeExprStore.

Module EStore := MakeExprStore VarOrder TE.

Module MakeFirrtl
       (V : SsrOrder)
       (TE : TypEnv with Module SE := V)
       (SV : ValStore V TE).
  Local Open Scope firrtl.
  Local Open Scope bits.
  
  Module VSLemmas := SsrFSetLemmas VS.

  Local Notation var := V.t.

  Local Notation vstate := SV.t.

(****** Semantics ******)

  (* Small-step *) 

  Definition fexpr := fexpr V.T.
  Definition econst c := @Econst V.T c.
  Definition eref v := @Eref V.T v.
  Definition ecast u e := @Ecast V.T u e.
  Definition eprim_unop u e := @Eprim_unop V.T u e.
  Definition eprim_binop b e1 e2 := @Eprim_binop V.T b e1 e2.
  Definition emux c e1 e2 := @Emux V.T c e1 e2.
  Definition evalidif c e := @Evalidif V.T c e.

  Definition fstmt := fstmt V.T.
  Definition sskip := @Sskip V.T.
  Definition swire v t := @Swire V.T v t.  
  Definition sreg r := @Sreg V.T r.
  Definition smem m := @Smem V.T m.
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.

  Definition freg := @freg V.T.
  Definition mk_freg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
  Definition fmem := @fmem V.T.
  Definition mk_fmem := @mk_fmem V.T.
  Definition mk_fwriter_port := @mk_fwriter_port V.T.
  Definition mk_freader_port := @mk_freader_port V.T.
  Definition fwriter_port := @fwriter_port V.T.
  Definition freader_port := @freader_port V.T.
  Definition fport := @fport V.T.
  Definition mk_finst := @mk_finst V.T.
  Definition fmodule := @fmodule V.T.
  Definition fcircuit := @fcircuit V.T.

  Definition memory_map := bits -> bits.
  Definition memfind (key : bits) (map : memory_map) : bits := map key.
  Definition memupd (key : bits) (v : bits) (memmap : memory_map) : memory_map :=
    fun (y : bits) => if y == key then v else memfind y memmap.
  Definition memempty : memory_map := (fun _ => [::]).

  Definition mapls := TE.t (seq var).
  Definition mapioin := TE.t (seq bits).
  Definition mapdata2etc := TE.t (var * var * var * var * var).
  Definition map2etc := TE.t (mapdata2etc).

  Definition mapmem := TE.t memory_map. 

  Fixpoint mylListIn (a:var) (l:list var) : bool :=
      match l with
        | nil => b0
        | b :: m => if b == a then b1 else (mylListIn a m)
      end.

  Definition maptuple := TE.t (var * var).
  Definition mmaptuple := TE.t maptuple.
  Definition mapfstmt := TE.t (seq fstmt).
  Definition mapterss := TE.t (TE.env * vstate * vstate * mapmem).
  Definition mapvar := TE.t var.
  Definition mvar := TE.t mapvar.
  Definition mmapvar := TE.t (mvar * mapvar).
  Definition mmvar := TE.t (mapvar * mapvar).

  Fixpoint bitsIn (a: bits) (l:list bits) : bool :=
      match l with
        | nil => b0
        | b :: m => if ((to_nat b) == (to_nat a)) then b1 else (bitsIn a m)
      end.
  Fixpoint varIn (a: var) (l:seq var) : bool :=
      match l with
        | nil => b0
        | b :: m => if (b == a) then b1 else (varIn a m)
      end.

  Definition g := var -> seq var.
  Definition mapg := TE.t g.
  Definition emptyg : g := (fun _ => [::]).
  Definition findg (key : var) (map : g) : seq var := map key.
  Definition updg (key : var) (v : seq var) (map : g) : g :=
    fun (y : var) => if y == key then v else findg y map.

  Definition var2stmtmap := TE.t fstmt.
  Definition allvar2stmtmap := TE.t var2stmtmap.
  Definition fmap := TE.t nat.
  Definition boolmap := TE.t bool.
  Definition allboolmap := TE.t boolmap.

  Fixpoint upd_inner s s0 (a2 : seq var) (finstinmap : mapvar) : vstate :=
      match a2 with
      | [::] => s0
      | h::t => let s1 := match TE.find h finstinmap with
                            | None => s0
                            | Some a => SV.upd h (SV.acc a s) s0
                            end in
      upd_inner s s1 t finstinmap
      end.
  
  (* From Coq Require Import ZArith. *)
  
  Definition ftcast (bs : bits) (fty : fgtyp) (tty : fgtyp) : bits :=
    match fty with
    | Fuint w => ucastB bs (sizeof_fgtyp tty)
    | Fsint w => scastB bs (sizeof_fgtyp tty)
    | _ => ucastB bs 1
    end.
  
  Definition to_Clock bs := Z.b2z (lsb bs).
  Definition to_Reset bs := Z.b2z (lsb bs).

  (* Casting operations *)
  Definition eunop_ucast (o : ucast) : bits -> Z :=
    match o with
    | AsUInt => to_Zpos
    | AsSInt => to_Z
    | AsClock => to_Clock
    | AsAsync => to_Reset
    end.

  (* Unary operations *)
  Definition eunop_op (o : eunop) (t : fgtyp) : bits -> bits :=
    match o with
    | Upad n => fun b => if (n < size b) then b else
                 (match t with
                  | Fuint w => zext (n - w) b
                  | Fsint w => sext (n - w) b
                  | _ => b
                  end)
    | Ushl n => fun b => cat (zeros n) b
    | Ushr n => fun b => if (n < size b) then high (size b - n) b else [::msb b]
    | Ucvt =>  fun b =>
                 (match t with
                  | Fuint w => sext 1 b
                  | _ => b
                  end)
    | Uneg => fun b => (match t with
                    | Fuint _ => negB (zext 1 b)
                    | Fsint _ => negB (sext 1 b)
                    | _ => b
                    end)
    | Unot => invB
    | Uandr => fun b => [::foldr andb b1 b]
    | Uorr => fun b => [::foldr orb b0 b]
    | Uxorr => fun b => [::foldr xorb b0 b]
    | Uextr n1 n2 => extract n1 n2
    | Uhead n => high n
    | Utail n => fun b => low (size b - n) b
    end.  

  (*Compute (eunop_op Uneg (Fuint 2) [:: true; false; false; true]).
  Compute (to_Z [:: false; true; false; true]).*)

  (* Comparison operations *)
  Definition binop_bcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::ltB bs1 bs2]
    | Bleq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::leB bs1 bs2]
    | Bgt => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::gtB bs1 bs2]
    | Bgeq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::geB bs1 bs2]
    | Beq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::bs1 == bs2]
    | Bneq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                           let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::(~~ (bs1 == bs2))]
    end.
    (*Compute (binop_bcmp Bgeq [::true;false;true] [::true;false;true]).
    Compute (binop_bcmp Bgeq [::true;false;true] [::true;false;true;false]).*)

  Definition binop_sbcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sltB bs1 bs2]
    | Bleq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sleB bs1 bs2]
    | Bgt => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sgtB bs1 bs2]
    | Bgeq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sgeB bs1 bs2]
    | Beq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::bs1 == bs2]
    | Bneq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                           let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                           [::(~~ (bs1 == bs2))]
    end.

  (* Binary operations *)

  (* addition with zero extended bits *)
  Definition full_adder_ext c bs1 bs2 : bool * bits := full_adder_zip c (extzip0 bs1 bs2).
  Definition adcB_ext c bs1 bs2 := full_adder_ext c bs1 bs2.
  Definition addB_ext bs1 bs2 : bits := let (c, r) := (adcB_ext false bs1 bs2) in rcons r c.

  (*Compute (extzip0 [::false;false;false] [::true;true;true;true]).*)

  Lemma size_full_adder_ext c bs1 bs2 : size (snd (full_adder_ext c bs1 bs2)) = maxn (size bs1) (size bs2).
  Proof.
    rewrite /full_adder_ext.
    dcase (extzip0 bs1 bs2) => [zp Hzp].
    rewrite -(size_extzip b0 b0 bs1 bs2) -/extzip0 Hzp.
    elim : zp bs1 bs2 Hzp c => [|zh zt IH] bs1 bs2 Hzp c. rewrite //.
    dcase zh => [[hd1 hd2] Hz]. rewrite Hz in Hzp => {Hz zh}.
    dcase (bool_adder c hd1 hd2) => [[c0 hd] Hadder].
    dcase (full_adder_zip c0 zt) => [[c1 tl] Hfull].
    move: Hzp.
    case: bs1; case: bs2 => //.
    - move=> b bs Hzs. case: Hzs => H1 H2.
      have ->: zip (copy (size bs) b0) bs = extzip0 [::] bs by rewrite /extzip0/=; elim bs =>//.
      move => H3.
      move: (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move=> ->.
    - move => b bs Hzs. case : Hzs => H1 H2.
      have ->: zip bs (copy (size bs) b0) = extzip0 bs [::] by rewrite /extzip0/=; elim bs =>//.
      move => H3.
      move: (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move=> ->.
    - move => b11 bs1 b21 bs2 Hzs. case: Hzs => H1 H2 H3.
      move : (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move => ->.
  Qed.
      
  Lemma size_adcB_ext bs1 bs2: size (snd (adcB_ext false bs1 bs2)) = maxn (size bs1) (size bs2).
  Proof.
    rewrite /adcB_ext size_full_adder_ext //.
  Qed.

  Lemma size_addB_ext bs1 bs2 : size (addB_ext bs1 bs2) = (maxn (size bs1) (size bs2)).+1.
  Proof.
    rewrite /addB_ext. case Hadc : (adcB_ext false bs1 bs2) => [c r].
    rewrite /=-size_adcB_ext Hadc size_rcons //.
  Qed.

  Lemma extzip0_zext bs1 bs2 :
    extzip0 bs1 bs2 = zip (zext (size bs2 - size bs1) bs1) (zext ((size bs1) - size bs2) bs2) .
  Proof.
    rewrite /extzip0. rewrite /zext /zeros extzip_zip //.
  Qed.
  
  Lemma to_Zpos_addB_ext bs1 bs2 :
    to_Zpos (addB_ext bs1 bs2) = Z.add (to_Zpos bs1) (to_Zpos bs2).
  Proof.
    rewrite /addB_ext /adcB_ext /full_adder_ext.
    rewrite extzip0_zext.
    case Hadc : (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) => [c r].
    have ->: r = snd (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) by rewrite Hadc//.
    have ->: c = fst (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) by rewrite Hadc//.
    rewrite -/(full_adder false (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(adcB false (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(addB (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(carry_addB (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite to_Zpos_rcons. rewrite size_addB 2!size_zext. rewrite -2!maxnE maxnC minnn maxnC maxnE.
    have ->: ((size bs1 + (size bs2 - size bs1)) = size (zext (size bs2 - size bs1) bs1)).
    rewrite size_zext//.
    rewrite to_Zpos_addB. rewrite 2!to_Zpos_zext//.
    rewrite 2!size_zext. rewrite -2!maxnE maxnC//.
  Qed.

  (* subtraction with extended bits *)
  Definition sbbB_ext b bs1 bs2 : bool * bits := adcB_ext (~~ b) bs1 (~~# bs2).
  Definition subB_ext bs1 bs2 := let newl := (maxn (size bs1) (size bs2))+1 in
                                  let nbs1 := zext (newl-(size bs1)) bs1 in
                                  let nbs2 := zext (newl-(size bs2)) bs2 in
                                  snd (sbbB false nbs1 nbs2).

  Compute (sbbB_ext false [::false;false] [::false;false]).
  Compute (subB_ext [::false;false] [::false;false]).

  Lemma size_subB_ext bs1 bs2 : size (subB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  rewrite /subB_ext.
  rewrite size_sbbB 2!size_zext addn1 subnKC.
  rewrite subnKC.
  rewrite /minn ltnn //.
  apply leqW.
  rewrite leq_maxr //.
  apply leqW.
  rewrite leq_maxl //.
Qed.

  Lemma to_Zpos_subB_ext bs1 bs2 : ~~(bs1 <# bs2) -> to_Zpos (subB_ext bs1 bs2) = Z.sub (to_Zpos bs1) (to_Zpos bs2).
  Proof.
    intros.
    rewrite /subB_ext.
    rewrite -/(subB (zext (maxn (size bs1) (size bs2) + 1 - size bs1) bs1) (zext (maxn (size bs1) (size bs2) + 1 - size bs2) bs2)).
    assert (size (zext (maxn (size bs1) (size bs2) + 1 - size bs1) bs1) = size (zext (maxn (size bs1) (size bs2) + 1 - size bs2) bs2)).
    rewrite addn1 2!size_zext subnKC.
    rewrite subnKC //.
    move : (leq_maxl (size bs2) (size bs1)) => Hbd2.
    rewrite maxnC in Hbd2.
    move : (leqnSn (maxn (size bs1) (size bs2))) => Hmax1.
    rewrite (leq_trans Hbd2 Hmax1) //.
    move : (leq_maxl (size bs1) (size bs2)) => Hbd1.
    move : (leqnSn (maxn (size bs1) (size bs2))) => Hmax1.
    rewrite (leq_trans Hbd1 Hmax1) //.
    assert (~~ borrow_subB (zext (maxn (size bs1) (size bs2) + 1 - size bs1) bs1) (zext (maxn (size bs1) (size bs2) + 1 - size bs2) bs2)).
    rewrite -(ltB_equiv_borrow_subB H0) ltB_zext H //.
    rewrite bv2z_sub_unsigned.
    rewrite (to_Zpos_zext bs1 (maxn (size bs1) (size bs2) + 1 - size bs1)) (to_Zpos_zext bs2 (maxn (size bs1) (size bs2) + 1 - size bs2)) //.
    apply H0.
    apply H1.
  Qed.

  Definition SadcB_ext ea eb := let (c, r) := adcB false ea eb in 
            (if (msb ea) == (msb eb) then (rcons r c) else (rcons r (~~c))).

  Lemma size_SadcB_ext bs1 bs2 : size bs1 = size bs2 -> size (SadcB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  Proof. 
    rewrite /SadcB_ext.
    move=> Heql.
    rewrite Heql.
    case Hmsb : (msb bs1 == msb bs2).
    case Hadc : (adcB false bs1 bs2) => [c r].
    rewrite /adcB in Hadc. 
    rewrite size_rcons /maxn ltnn addn1.
    move : (size_full_adder bs1 bs2 false) => Hbd1.
    rewrite Hadc in Hbd1.
    rewrite Heql /minn ltnn in Hbd1.
    rewrite Hbd1 //.

    case Hadc : (adcB false bs1 bs2) => [c r].
    rewrite /adcB in Hadc. 
    rewrite size_rcons /maxn ltnn addn1.
    move : (size_full_adder bs1 bs2 false) => Hbd1.
    rewrite Hadc in Hbd1.
    rewrite Heql /minn ltnn in Hbd1.
    rewrite Hbd1 //.
  Qed.

  Lemma to_Z_SadcB_ext bs1 bs2 : size bs1 = size bs2 -> to_Z (SadcB_ext bs1 bs2) = Z.add (to_Z bs1) (to_Z bs2).
  Proof.
    intro.
    rewrite /SadcB_ext.
    case Hadc : (adcB false bs1 bs2) => [c r].
    have ->: r = snd (adcB false bs1 bs2) by rewrite Hadc//.
    have ->: c = fst (adcB false bs1 bs2) by rewrite Hadc//.
    rewrite -/(addB bs1 bs2).
    rewrite -/(carry_addB bs1 bs2).
    case Hmsb : (msb bs1 == msb bs2).
      - rewrite to_Z_rcons 2!to_Z_to_Zpos Z.add_sub_assoc.
      move /eqP : Hmsb => Hmsb.
      case Hcarry : (carry_addB bs1 bs2 == true).
        - move /eqP : Hcarry => Hcarry.
        rewrite Hcarry.
        rewrite -Z.add_sub_swap -to_Zpos_addB.
        rewrite Hcarry Z.opp_succ -Z.sub_1_r.
        case Hmsb1 : (msb bs1 == true).
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1.
          rewrite -Z.add_sub_assoc Z.sub_diag Z.add_0_r.
          rewrite -(Z.add_cancel_l (Z.opp (to_Zneg (bs1 +# bs2)) - 1) (to_Zpos (bs1 +# bs2) - msb bs2 * 2 ^ Z.of_nat (size bs2)) (to_Zneg (bs1 +# bs2))).
          rewrite Z.add_sub_assoc Z.add_opp_diag_r Z.add_sub_assoc Z.add_comm to_Zpos_add_to_Zneg.
          rewrite size_addB  H /minn ltnn.
          rewrite Hmsb in Hmsb1.
          rewrite Hmsb1 Z.mul_1_l.
          rewrite -(Z.add_opp_r (2 ^ Z.of_nat (size bs2)) 1) Z.add_simpl_l Z.sub_0_l //.
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite carry_addB_eq_msbs in Hcarry.
          apply not_true_is_false in Hmsb1.
          rewrite -Hmsb andb_diag andbN andNb andb_false_l Hmsb1 in Hcarry.
          discriminate.
          rewrite H //.
          apply H.
        - move /eqP : Hcarry => Hcarry.
        apply not_true_is_false in Hcarry.
        rewrite Hcarry.
        rewrite -Z.add_sub_swap -to_Zpos_addB.
        rewrite Hcarry Z.mul_0_l Z.add_0_r. 
        rewrite carry_addB_eq_msbs in Hcarry.
        rewrite -Hmsb andb_diag andbN andNb andb_false_l orb_false_l orb_false_l in Hcarry.
        rewrite Hmsb in Hcarry.
        rewrite Hmsb Hcarry Z.mul_0_l Z.sub_0_r Z.mul_0_l Z.sub_0_r //.
        apply H.
        apply H.
      - rewrite to_Z_rcons 2!to_Z_to_Zpos Z.add_sub_assoc.
      move /eqP : Hmsb => Hmsb.
      case Hcarry : (~~ carry_addB bs1 bs2 == true).
        - move /eqP : Hcarry => Hcarry.
        rewrite Hcarry.
        rewrite -Z.add_sub_swap -to_Zpos_addB.
        apply negbTE in Hcarry.
        rewrite Hcarry Z.opp_succ -Z.sub_1_r Z.mul_0_l Z.add_0_r -Z.sub_add_distr.
        rewrite -(Z.add_cancel_l (Z.opp (to_Zneg (bs1 +# bs2)) - 1) (to_Zpos (bs1 +# bs2) -
        (msb bs1 * 2 ^ Z.of_nat (size bs1) +
        msb bs2 * 2 ^ Z.of_nat (size bs2))) (to_Zneg (bs1 +# bs2))).
        rewrite Z.add_sub_assoc Z.add_opp_diag_r Z.add_sub_assoc Z.add_comm to_Zpos_add_to_Zneg.
        case Hmsb1 : (msb bs1 == true).
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply not_true_is_false in Hmsb.
          rewrite Hmsb Z.mul_1_l Z.mul_0_l Z.add_0_r size_addB H /minn ltnn.
          rewrite -(Z.add_opp_r (2 ^ Z.of_nat (size bs2)) 1) Z.add_simpl_l Z.sub_0_l //.
          - move /eqP : Hmsb1 => Hmsb1.
          apply not_true_is_false in Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply Bool.not_false_is_true in Hmsb.
          rewrite Hmsb Hmsb1 Z.mul_1_l Z.mul_0_l Z.add_0_l size_addB H /minn ltnn.
          rewrite -(Z.add_opp_r (2 ^ Z.of_nat (size bs2)) 1) Z.add_simpl_l Z.sub_0_l //.
          apply H.
        - move /eqP : Hcarry => Hcarry.
        apply not_true_is_false in Hcarry.
        rewrite Hcarry.
        apply negbFE in Hcarry. (*?*)
        rewrite -Z.add_sub_swap -to_Zpos_addB.
        rewrite Hcarry.
        case Hmsb1 : (msb bs1 == true).
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1.
          rewrite -Z.add_sub_assoc Z.sub_diag Z.add_0_r.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply not_true_is_false in Hmsb.
          rewrite Hmsb Z.mul_0_l Z.sub_0_r //.
          - move /eqP : Hmsb1 => Hmsb1.
          apply not_true_is_false in Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply Bool.not_false_is_true in Hmsb.
          rewrite Hmsb Hmsb1 2!Z.mul_1_l Z.mul_0_l Z.sub_0_r H -Z.add_sub_assoc Z.sub_diag Z.add_0_r //.
          apply H. 
Qed.

  Definition SsbbB_ext ea eb := let (b, r) := sbbB false ea eb in 
            (if (msb ea) == (msb eb) then (rcons r b) else (rcons r (~~b))).

  Lemma size_SsbbB_ext bs1 bs2 : size bs1 = size bs2 -> size (SsbbB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  Proof. 
    rewrite /SsbbB_ext.
    move=> Heql.
    rewrite Heql.
    case Hmsb : (msb bs1 == msb bs2).
    case Hsbb : (sbbB false bs1 bs2) => [c r].
    move : (size_sbbB false bs1 bs2) => Hbd1.
    rewrite Hsbb in Hbd1.
    rewrite Heql /minn ltnn in Hbd1.
    rewrite size_rcons /maxn ltnn addn1 Hbd1 //.
    
    case Hsbb : (sbbB false bs1 bs2) => [c r].
    move : (size_sbbB false bs1 bs2) => Hbd1.
    rewrite Hsbb in Hbd1.
    rewrite Heql /minn ltnn in Hbd1.
    rewrite size_rcons /maxn ltnn addn1 Hbd1 //.
  Qed.

  Lemma to_Z_SsbbB_ext bs1 bs2 : size bs1 = size bs2 -> to_Z (SsbbB_ext bs1 bs2) = Z.sub (to_Z bs1) (to_Z bs2).
  Proof.
    intro.  
    rewrite /SsbbB_ext.
    case Hadc : (sbbB false bs1 bs2) => [c r].
    have ->: r = snd (sbbB false bs1 bs2) by rewrite Hadc//.
    have ->: c = fst (sbbB false bs1 bs2) by rewrite Hadc//.
    rewrite -/(subB bs1 bs2).
    rewrite -/(borrow_subB bs1 bs2).
    case Hmsb : (msb bs1 == msb bs2).
      - rewrite to_Z_rcons 2!to_Z_to_Zpos Z.sub_sub_distr.
      move /eqP : Hmsb => Hmsb.
      case Hcarry : (borrow_subB bs1 bs2 == true).
        - move /eqP : Hcarry => Hcarry.
        rewrite Hcarry Z.opp_succ -Z.sub_1_r.
        rewrite -(Z.add_opp_r (to_Zpos bs1) (msb bs1 * 2 ^ Z.of_nat (size bs1))) Z.add_sub_swap.
        rewrite -(Z.add_cancel_l (- to_Zneg (bs1 -# bs2) - 1) (to_Zpos bs1 - to_Zpos bs2 + - (msb bs1 * 2 ^ Z.of_nat (size bs1)) +
        msb bs2 * 2 ^ Z.of_nat (size bs2)) ((to_Zpos (bs1 -# bs2) + to_Zneg (bs1 -# bs2)))).
        rewrite Z.add_sub_assoc -Z.add_assoc Z.add_opp_diag_r Z.add_0_r to_Zpos_add_to_Zneg to_Zpos_subB.
        rewrite Hcarry Z.mul_1_l size_subB H /minn ltnn.
        case Hmsb1 : (msb bs1 == true).
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1.
          rewrite Hmsb in Hmsb1.
          rewrite Hmsb1 Zplus_assoc_reverse Z.add_opp_diag_l Z.add_0_r -Z.add_sub_swap Z.add_sub_assoc //. 
          - rewrite Hmsb Zplus_assoc_reverse Z.add_opp_diag_l Z.add_0_r -Z.add_sub_swap Z.add_sub_assoc //.
          apply H.
        - move /eqP : Hcarry => Hcarry.
        apply not_true_is_false in Hcarry.
        rewrite Hcarry.
        rewrite -(Z.add_opp_r (to_Zpos bs1) (msb bs1 * 2 ^ Z.of_nat (size bs1))) Z.add_sub_swap.
        rewrite to_Zpos_subB.
        rewrite Hcarry Z.mul_0_l Z.add_0_l Hmsb H Zplus_assoc_reverse Z.add_opp_diag_l Z.add_0_r //.
        apply H.

      - rewrite to_Z_rcons 2!to_Z_to_Zpos Z.sub_sub_distr.
      move /eqP : Hmsb => Hmsb.
      case Hcarry : (~~ borrow_subB bs1 bs2 == true).
        - move /eqP : Hcarry => Hcarry.
        rewrite Hcarry Z.opp_succ -Z.sub_1_r.
        rewrite -(Z.add_opp_r (to_Zpos bs1) (msb bs1 * 2 ^ Z.of_nat (size bs1))) Z.add_sub_swap.
        rewrite -(Z.add_cancel_l (- to_Zneg (bs1 -# bs2) - 1) (to_Zpos bs1 - to_Zpos bs2 + - (msb bs1 * 2 ^ Z.of_nat (size bs1)) +
        msb bs2 * 2 ^ Z.of_nat (size bs2)) ((to_Zpos (bs1 -# bs2) + to_Zneg (bs1 -# bs2)))).
        rewrite Z.add_sub_assoc -Z.add_assoc Z.add_opp_diag_r Z.add_0_r to_Zpos_add_to_Zneg to_Zpos_subB.
        apply negbTE in Hcarry.
        rewrite Hcarry Z.mul_0_l Z.add_0_l size_subB H /minn ltnn.
        case Hmsb1 : (msb bs1 == true).
          - move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply not_true_is_false in Hmsb.
          rewrite Hmsb1 Hmsb Z.mul_0_l Z.mul_1_l Z.add_0_r.
          rewrite (Z.add_assoc (2 ^ Z.of_nat (size bs2) - 1) (to_Zpos bs1 - to_Zpos bs2) (- 2 ^ Z.of_nat (size bs2))).
          rewrite -Z.add_sub_swap -Z.add_sub_assoc Z.add_comm Z.add_assoc Z.add_opp_diag_l Z.add_0_l //.
          - rewrite borrow_subB_eq_msbs in Hcarry.
          move /eqP : Hmsb1 => Hmsb1.
          apply not_true_is_false in Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply Bool.not_false_is_true in Hmsb.
          rewrite Hmsb Hmsb1 in Hcarry.
          discriminate.
          apply H.
          apply H.

        - move /eqP : Hcarry => Hcarry.
        apply not_true_is_false in Hcarry.
        rewrite Hcarry.
        rewrite -(Z.add_opp_r (to_Zpos bs1) (msb bs1 * 2 ^ Z.of_nat (size bs1))) Z.add_sub_swap.
        rewrite to_Zpos_subB.
        apply negbFE in Hcarry.
        rewrite Hcarry Z.mul_1_l. 

        case Hmsb1 : (msb bs1 == true).
          - rewrite borrow_subB_eq_msbs in Hcarry.
          move /eqP : Hmsb1 => Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply not_true_is_false in Hmsb.
          rewrite Hmsb1 Hmsb in Hcarry.
          discriminate.
          apply H.
          - move /eqP : Hmsb1 => Hmsb1.
          apply not_true_is_false in Hmsb1.
          rewrite Hmsb1 in Hmsb.
          apply not_eq_sym in Hmsb.
          apply Bool.not_false_is_true in Hmsb.
          rewrite Hmsb Hmsb1 Z.mul_1_l Z.mul_0_l Z.add_0_r H.
          rewrite (Z.add_comm (to_Zpos bs1 - to_Zpos bs2) (2 ^ Z.of_nat (size bs2))) Z.add_sub_assoc //.
          apply H.
  Qed.

Lemma to_Z_negB bs : to_Z (negB (sext 1 bs)) = Z.opp (to_Z bs).
Proof.
  case H0 : (bs == zeros (size bs)).
  apply sext_neq_zeros in H0.
  move /eqP : H0 => H0.
  rewrite H0.
  rewrite (eqP (@negB_zeros (size bs + 1))).
  move /eqP : H0 => H0.
  apply sext_neq_zeros in H0.
  move /eqP : H0 => H0.
  rewrite H0.
  rewrite 2!to_Z_zeros.
  rewrite Z.opp_0 //.
  rewrite -(to_Z_sext bs 1).
  apply to_Z_negB.
  rewrite negb_andb.
  case Hmsb1 : (msb bs == false).
  move /eqP : Hmsb1 => Hmsb1.
  rewrite msb_sext Hmsb1.
  trivial.
  move /eqP : Hmsb1 => Hmsb1.
  apply Bool.not_false_is_true in Hmsb1.
  rewrite msb_sext Hmsb1.
  simpl.  
  have ->: dropmsb (sext 1 bs) = bs.
  rewrite /sext Hmsb1.
  have ->: copy 1 true = [:: true] by rewrite /copy //.
  rewrite dropmsb_cat //. 
  have ->: dropmsb [::true] = [::] by rewrite /dropmsb //.
  rewrite cats0 //.
  rewrite size_sext -addnBA //.
  rewrite subnn addn0.
  apply contraFneq with (b:=(bs == zeros (size bs))).
  intro.
  move /eqP : H =>H.
  apply H.
  exact H0.
Qed.

  Definition Sfull_mul (bs1 bs2 : bits) : bits :=
    if (((size bs1) == 0) || ((size bs2) == 0))
    then zeros (size bs1 + size bs2)
    else if ((bs1 == [::b0]) || (bs2 == [::b0]))
    then zeros (size bs1 + size bs2)
    else if (bs1 == rcons (zeros (size bs1 -1)) b1)
    then negB (sext 1 ((zeros (size bs1 -1)) ++ bs2))
    else if (bs2 == rcons (zeros (size bs2 -1)) b1)
    then negB (sext 1 ((zeros (size bs2 -1)) ++ bs1))
    else
    let msb1 := msb bs1 in 
    let msb2 := msb bs2 in 
    if ((msb1 == b0) && (msb2 == b0))
    then zext 2 (full_mul (dropmsb bs1) (dropmsb bs2))
    else if ((msb1 == b1) && (msb2 == b1))
    then (full_mul (negB bs1) (negB bs2)) 
    else if ((msb1 == b0) && (msb2 == b1))
    then negB (sext 1 (full_mul (dropmsb bs1) (negB bs2)))
    else negB (sext 1 (full_mul (negB bs1) (dropmsb bs2))).
    
Lemma size_Sfull_mul bs1 bs2: size (Sfull_mul bs1 bs2) = (size bs1) + (size bs2).
  Proof.
    rewrite /Sfull_mul.
    case Hlen1 : (size bs1 == 0).
    simpl.
    rewrite size_zeros //.
    case Hlen2 : (size bs2 == 0).
    simpl.
    rewrite size_zeros //.
    simpl.
    case H10 : (bs1 == [:: b0]).
    simpl.
    rewrite size_zeros //.
    case H20 : (bs2 == [:: b0]).
    simpl.
    rewrite size_zeros //.
    simpl.
    apply negbT in Hlen1 ; rewrite -lt0n in Hlen1.
    apply negbT in Hlen2 ; rewrite -lt0n in Hlen2.
    case Hbs11 : (bs1 == rcons (zeros (size bs1 - 1)) b1).
    rewrite size_negB size_sext size_cat addnACl size_zeros addnBA.
    rewrite add1n subn1 Nat.pred_succ addnC //.
    exact Hlen1.
    case Hbs21 : (bs2 == rcons (zeros (size bs2 - 1)) b1).
    rewrite size_negB size_sext size_cat addnACl size_zeros addnBA.
    rewrite add1n subn1 Nat.pred_succ addnC //.
    exact Hlen2.
    case Hmsb00 : ((msb bs1 == b0) && (msb bs2 == b0)).
    rewrite size_zext size_full_mul 2!size_dropmsb.
    rewrite {1}subn1 addnCAC addnABC.
    have -> : 2-1=1 by simpl.
    rewrite addnACl.
    rewrite -subn1 subnK.
    rewrite addnC //.
    exact Hlen1.
    trivial.
    exact Hlen2.
    case Hmsb11 : ((msb bs1 == b1) && (msb bs2 == b1)).
    rewrite size_full_mul 2!size_negB //.
    case Hmsb01 : ((msb bs1 == b0) && (msb bs2 == b1)).
    rewrite size_negB size_sext size_full_mul size_dropmsb size_negB.
    rewrite subn1 addnACl -subn1 addnBA.
    rewrite add1n subn1 Nat.pred_succ addnC //.
    exact Hlen1.
    rewrite size_negB size_sext size_full_mul size_dropmsb size_negB.
    rewrite addnCAC addnBA.
    rewrite add1n subn1 Nat.pred_succ addnC //.
    exact Hlen2.
Qed.

Lemma rconsmsb bs : size bs > 0 -> bs = rcons (dropmsb bs) (msb bs).
  Proof.
    intro.
    have ->: (dropmsb bs) = fst (splitmsb bs) by rewrite /dropmsb.
    have ->: (msb bs) = snd (splitmsb bs) by rewrite /dropmsb.
    symmetry.
    apply joinmsb_splitmsb.
    exact H.
Qed.

Lemma zext_full_mul bs1 bs2 : to_Zpos (full_mul (joinmsb bs1 false) bs2) = to_Zpos (full_mul bs1 bs2).
Proof.
  rewrite 2!to_Zpos_full_mul to_Zpos_joinmsb Z.mul_0_l Z.add_0_l //.
Qed.

Lemma msb0_full_mul bs1 bs2 : msb (full_mul (rcons bs1 false) bs2) = false.
Proof.
  assert (H : Z.lt (to_Zpos (full_mul (rcons bs1 false) bs2)) (2 ^ Z.of_nat (size (full_mul (rcons bs1 false) bs2) - 1))).
  rewrite size_full_mul size_rcons -addnBAC.
  rewrite subn1 Nat.pred_succ.
  rewrite to_Zpos_full_mul to_Zpos_rcons Z.mul_0_l Z.add_0_r -to_Zpos_full_mul -size_full_mul.
  apply to_Zpos_bounded.
  rewrite ltn0Sn //.
  apply /negbTE. 
  rewrite -> msb0_to_Zpos_bounded.
  exact H.
  rewrite size_full_mul size_rcons ltn0Sn //.
Qed.

Lemma msb_0full_mul bs1 bs2 : msb (full_mul bs1 (rcons bs2 false)) = false.
Proof.
  rewrite full_mulBC msb0_full_mul //.
Qed.

Lemma to_Z_Sfull_mul bs1 bs2: to_Z (Sfull_mul bs1 bs2) = (Z.mul (to_Z bs1) (to_Z bs2)).
  Proof.
    rewrite /Sfull_mul.
    case Hlen1 : (size bs1 == 0).
    move /eqP : Hlen1 => Hlen1.
    apply size0nil in Hlen1.
    simpl.
    rewrite Hlen1 to_Z_nil to_Z_zeros Z.mul_0_l //.
    case Hlen2 : (size bs2 == 0).
    move /eqP : Hlen2 => Hlen2.
    apply size0nil in Hlen2.
    simpl.
    rewrite Hlen2 to_Z_nil to_Z_zeros Z.mul_0_r //.
    case Hbs10 : (bs1 == [::b0]).
    simpl.
    move /eqP : Hbs10 => Hbs10.
    rewrite Hbs10.
    rewrite Z.mul_0_l to_Z_zeros //.
    case Hbs20 : (bs2 == [::b0]).
    simpl.
    move /eqP : Hbs20 => Hbs20.
    rewrite Hbs20.
    rewrite Z.mul_0_r to_Z_zeros //.
    simpl.
    case Hbs11 : (bs1 == rcons (zeros (size bs1 - 1)) b1).
    move /eqP : Hbs11 => Hbs11.
    rewrite {2}Hbs11 to_Z_rcons.
    simpl.
    rewrite to_Zneg_zeros - Z.add_1_r Z.sub_add to_Z_negB to_Z_cat.
    rewrite to_Zpos_zeros Z.add_0_l size_zeros Z.mul_comm Z.mul_opp_l //.
    rewrite lt0n Hlen2 //.
    case Hbs21 : (bs2 == rcons (zeros (size bs2 - 1)) b1).
    move /eqP : Hbs21 => Hbs21.
    rewrite {2}Hbs21 to_Z_rcons.
    simpl.
    rewrite to_Zneg_zeros - Z.add_1_r Z.sub_add to_Z_negB to_Z_cat.
    rewrite to_Zpos_zeros Z.add_0_l size_zeros Z.mul_opp_r //.
    rewrite lt0n Hlen1 //.

    case Hmsb00 : ((msb bs1 == b0) && (msb bs2 == b0)).
    move /andP : Hmsb00 => [H10 H20]. 
    rewrite to_Z_zext.
    rewrite to_Zpos_full_mul 2!to_Z_to_Zpos.
    move /eqP : H10 => H10.
    move /eqP : H20 => H20.
    rewrite H10 H20 2!Z.mul_0_l 2!Z.sub_0_r.
    have {2}-> : (bs1 = rcons (dropmsb bs1) (msb bs1)).
    apply rconsmsb.
    rewrite lt0n Hlen1 //.
    have {2}-> : (bs2 = rcons (dropmsb bs2) (msb bs2)).
    apply rconsmsb.
    rewrite lt0n Hlen2 //.
    rewrite 2!to_Zpos_rcons H10 H20 2!Z.mul_0_l 2!Z.add_0_r //.
    trivial.

    assert (Hrcons1 : bs1 = rcons (dropmsb bs1) (msb bs1)).
    apply rconsmsb.
    rewrite lt0n Hlen1 //.
    assert (Hrcons2 : bs2 = rcons (dropmsb bs2) (msb bs2)).
    apply rconsmsb.
    rewrite lt0n Hlen2 //.
    assert (Hrconsn1 : -# bs1 = rcons (dropmsb (-# bs1)) (msb (-# bs1))).
    apply rconsmsb.
    rewrite size_negB.
    rewrite lt0n Hlen1 //.
    assert (Hrconsn2 : -# bs2 = rcons (dropmsb (-# bs2)) (msb (-# bs2))).
    apply rconsmsb.
    rewrite size_negB.
    rewrite lt0n Hlen2 //.

    case Hmsb11 : ((msb bs1 == b1) && (msb bs2 == b1)).
    move /andP : Hmsb11 => [H11 H21]. 
    move /eqP : H11 => H11.
    move /eqP : H21 => H21.
    rewrite full_mul_mulB_zext. 

    case Hdrop2 : (dropmsb bs2 == zeros (size bs2 - 1)).
    move /eqP : Hdrop2 => Hdrop2.
    rewrite {1}Hrcons2 Hdrop2 H21 in Hbs21.
    rewrite eq_refl in Hbs21.
    discriminate.
    case Hdrop1 : (dropmsb bs1 == zeros (size bs1 - 1)).
    move /eqP : Hdrop1 => Hdrop1.
    rewrite {1}Hrcons1 Hdrop1 H11 in Hbs11.
    rewrite eq_refl in Hbs11.
    discriminate.
    
    assert (Ht1 : zext (size (-# bs2)) (-# bs1) = sext (size (-# bs2)) (-# bs1)).
    rewrite /zext /sext.
    rewrite -msb_negB.
    rewrite H11 //.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    assert (Ht2 : zext (size (-# bs1)) (-# bs2) = sext (size (-# bs1)) (-# bs2)).
    rewrite /zext /sext.
    rewrite -msb_negB.
    rewrite H21 //.
    apply contraFneq with (b:=(dropmsb bs2 == zeros (size bs2 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop2.

    rewrite Ht1 Ht2.
    rewrite bv2z_mul_signed.
    rewrite 2!to_Z_sext.
    rewrite NBitsOp.to_Z_negB.
    rewrite NBitsOp.to_Z_negB.
    rewrite Z.mul_opp_opp //.
    rewrite H21 andb_true_l.
    apply contraFneq with (b:=(dropmsb bs2 == zeros (size bs2 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop2.
    rewrite H11 andb_true_l.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    rewrite size_sext.
    rewrite 2!size_negB addn_gt0 lt0n Hlen1 //.
    rewrite 2!size_sext addnC //.
    apply smulo_sext.

    case Hmsb01 : ((msb bs1 == b0) && (msb bs2 == b1)).
    move /andP : Hmsb01 => [H10 H21]. 
    move /eqP : H10 => H10.
    move /eqP : H21 => H21.

    case Hdrop2 : (dropmsb bs2 == zeros (size bs2 - 1)).
    move /eqP : Hdrop2 => Hdrop2.
    rewrite {1}Hrcons2 Hdrop2 H21 in Hbs21.
    rewrite eq_refl in Hbs21.
    discriminate.

    rewrite to_Z_negB {1}to_Z_to_Zpos.
    rewrite {2}Hrconsn2.
    rewrite -msb_negB.
    rewrite H21.
    simpl.
    rewrite msb_0full_mul Z.mul_0_l Z.sub_0_r.
    have -> : to_Zpos (full_mul (dropmsb bs1) (-# bs2)) = to_Zpos (full_mul bs1 (-# bs2)).
    rewrite {2}Hrcons1.
    rewrite H10.
    rewrite zext_full_mul //.
    have -> : to_Zpos (full_mul bs1 (-# bs2)) = to_Z (full_mul bs1 (-# bs2)).
    rewrite to_Z_to_Zpos {3}Hrcons1 H10 msb0_full_mul Z.mul_0_l Z.sub_0_r //.
    rewrite full_mul_mulB_zext.
    
    have -> : (zext (size (-# bs2)) bs1 = sext (size (-# bs2)) bs1).
    rewrite /zext /sext.
    rewrite H10 //.
    have -> : (zext (size bs1) (-# bs2) = sext (size bs1) (-# bs2)).
    rewrite /zext /sext.
    rewrite -msb_negB.
    rewrite H21 //.
    apply contraFneq with (b:=(dropmsb bs2 == zeros (size bs2 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop2.
    
    rewrite bv2z_mul_signed.
    rewrite 2!to_Z_sext.
    rewrite NBitsOp.to_Z_negB.
    rewrite Z.mul_opp_r Z.opp_involutive //.
    rewrite H21 andb_true_l.
    apply contraFneq with (b:=(dropmsb bs2 == zeros (size bs2 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop2.
    rewrite size_sext.
    rewrite addn_gt0 lt0n Hlen1 //.
    rewrite 2!size_sext addnC //.
    apply smulo_sext.
    apply contraFneq with (b:=(dropmsb bs2 == zeros (size bs2 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop2.

    assert (Hmsb10 : (msb bs1 == b1) && (msb bs2 == b0)).
    apply /andP.
    split. 
    elim H11 : (msb bs1).
    trivial.
    rewrite H11 in Hmsb00.
    rewrite H11 in Hmsb01.
    simpl in Hmsb00.
    simpl in Hmsb01.
    move /eqP : Hmsb00 => Hmsb00.
    move /eqP : Hmsb01 => Hmsb01.
    apply not_true_is_false in Hmsb01.
    apply Bool.not_false_is_true in Hmsb00.
    rewrite Hmsb00 in Hmsb01.
    discriminate.
    elim H20 : (msb bs2).
    rewrite H20 andbC in Hmsb11.
    rewrite H20 andbC in Hmsb01.
    simpl in Hmsb11.
    simpl in Hmsb01.
    move /eqP : Hmsb11 => Hmsb11.
    move /eqP : Hmsb01 => Hmsb01.
    apply not_true_is_false in Hmsb11.
    apply Bool.not_false_is_true in Hmsb01.
    rewrite Hmsb11 in Hmsb01.
    discriminate.
    trivial.
    move /andP : Hmsb10 => [H11 H20]. 
    move /eqP : H11 => H11.
    move /eqP : H20 => H20.

    case Hdrop1 : (dropmsb bs1 == zeros (size bs1 - 1)).
    move /eqP : Hdrop1 => Hdrop1.
    rewrite {1}Hrcons1 Hdrop1 H11 in Hbs11.
    rewrite eq_refl in Hbs11.
    discriminate.

    rewrite to_Z_negB {1}to_Z_to_Zpos.
    rewrite {2}Hrconsn1.
    rewrite -msb_negB.
    rewrite H11.
    simpl.
    rewrite msb0_full_mul Z.mul_0_l Z.sub_0_r.
    have -> : to_Zpos (full_mul (-# bs1) (dropmsb bs2)) = to_Zpos (full_mul (-# bs1) bs2).
    rewrite {2}Hrcons2.
    rewrite H20.
    symmetry.
    rewrite full_mulBC zext_full_mul full_mulBC //.
    have -> : to_Zpos (full_mul (-# bs1) bs2) = to_Z (full_mul (-# bs1) bs2).
    rewrite to_Z_to_Zpos {3}Hrcons2 H20 msb_0full_mul Z.mul_0_l Z.sub_0_r //.
    rewrite full_mul_mulB_zext.
    
    have -> : (zext (size (-# bs1)) bs2 = sext (size (-# bs1)) bs2).
    rewrite /zext /sext.
    rewrite H20 //.
    have -> : (zext (size bs2) (-# bs1) = sext (size bs2) (-# bs1)).
    rewrite /zext /sext.
    rewrite -msb_negB.
    rewrite H11 //.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    
    rewrite bv2z_mul_signed.
    rewrite 2!to_Z_sext.
    rewrite NBitsOp.to_Z_negB.
    rewrite Z.mul_opp_l Z.opp_involutive //.
    rewrite H11 andb_true_l.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    rewrite size_sext size_negB.
    rewrite addn_gt0 lt0n Hlen1 //.
    rewrite 2!size_sext addnC //.
    apply smulo_sext.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
Qed.

  Definition ebinop_op (o : ebinop) (t1 t2 : fgtyp) : bits -> bits -> bits :=
    match t1, t2 with
    | Fuint w1, Fuint w2 =>
      fun a b =>
        let w := maxn w1 w2 in
        let ea := zext (w-w1) a in
        let eb := zext (w-w2) b in
      match o with
      | Badd => addB_ext a b
      | Bsub => subB_ext a b
      | Bdiv => udivB' a b
      | Brem => low (minn w1 w2) (uremB a b)
      (* | Bsdiv => sdivB *)
      (* | Bsrem => sremB *)
      | Bmul => full_mul a b
      | Bcomp c => binop_bcmp c a b
      | Band => andB ea eb
      | Bor => orB ea eb
      | Bxor => xorB ea eb
      | Bcat => cat b a
      | Bdshl => zext ((Nat.pow 2 (size b) - 1) - (to_nat b)) (cat (zeros (to_nat b)) a)
      | Bdshr => (shrB (to_nat b) a)
      end
    | Fsint w1, Fsint w2 =>
      fun a b =>
        let w := maxn w1 w2 in
        let ea := sext (w-w1) a in
        let eb := sext (w-w2) b in
      match o with
      | Badd => SadcB_ext ea eb
      | Bsub => SsbbB_ext ea eb
      | Bdiv => sext 1 (sdivB a b)
      | Brem => low (minn w1 w2) (sremB a b)
      | Bmul => Sfull_mul a b
      | Bcomp c => binop_sbcmp c ea eb
      | Band => andB ea eb
      | Bor => orB ea eb
      | Bxor => xorB ea eb
      | Bcat => cat b a
      | _ => a
      end
    | Fsint _, Fuint _ =>
      fun a b =>
      match o with
      | Bdshl => sext ((Nat.pow 2 (size b) - 1) - (to_nat b)) (cat (zeros (to_nat b)) a)
      | Bdshr => (sarB (to_nat b) a)
      | _ => a
      end
    | _, _ => fun a b => a
    end.
    
  Fixpoint type_of_fexpr (e : fexpr) (te : TE.env) : fgtyp :=
    match e with
    | Econst t c => t
    | Eref v => TE.vtyp v te
    | Ecast AsUInt e => Fuint (sizeof_fgtyp (type_of_fexpr e te))
    | Ecast AsSInt e => Fsint (sizeof_fgtyp (type_of_fexpr e te))
    | Ecast AsClock e => Fclock
    | Ecast AsAsync e => Fasyncreset
    | Eprim_unop u e => match u with
                        | Upad n => if (n < (sizeof_fgtyp (type_of_fexpr e te))) then (type_of_fexpr e te)
                                    else match (type_of_fexpr e te) with
                                    | Fuint _ => Fuint n
                                    | Fsint _ => Fsint n
                                    | _ => TE.deftyp
                                    end
                        | Uandr | Uorr | Uxorr => Fuint 1
                        | Uextr n1 n2 => Fuint (n1 - n2 + 1)
                        | Uhead n => Fuint n
                        | Utail n => Fuint ((sizeof_fgtyp (type_of_fexpr e te)) - n)
                        | Ushl n => match (type_of_fexpr e te) with
                                    | Fuint w => Fuint (w + n)
                                    | Fsint w => Fsint (w + n)
                                    | _ => TE.deftyp
                                    end
                        | Ushr n => match (type_of_fexpr e te) with
                                    | Fuint w => if n < w then Fuint (w - n) else Fuint 1
                                    | Fsint w => if n < w then Fsint (w - n) else Fsint 1
                                    | _ => TE.deftyp
                                    end
                        | Ucvt => match (type_of_fexpr e te) with
                                  | Fuint w => Fsint (w + 1)
                                  | Fsint w => Fsint w
                                  | _ => TE.deftyp
                                  end
                        | Uneg => match (type_of_fexpr e te) with
                                  | Fuint w => Fsint (w + 1)
                                  | Fsint w => Fsint (w + 1)
                                  | _ => TE.deftyp
                                  end
                        | Unot => match (type_of_fexpr e te) with
                                  | Fuint w => Fuint w
                                  | Fsint w => Fuint w
                                  | _ => TE.deftyp
                                  end
                        end
    | Eprim_binop b e1 e2 => match b with
                             | Bdshl => match (type_of_fexpr e1 te) with
                                                | Fuint n => Fuint (n + (Nat.pow 2 (sizeof_fgtyp (type_of_fexpr e2 te))) - 1)
                                                | Fsint n => Fsint (n + (Nat.pow 2 (sizeof_fgtyp (type_of_fexpr e2 te))) - 1)
                                                | _ => TE.deftyp
                                                end
                             | Bdshr => match (type_of_fexpr e1 te) with
                                                | Fuint n => Fuint n
                                                | Fsint n => Fsint n
                                                | _ => TE.deftyp
                                                end
                             | Badd | Bsub => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                              | Fuint s1, Fuint s2 => Fuint ((maxn s1 s2)+1)
                                              | Fsint s1, Fsint s2 => Fsint ((maxn s1 s2)+1)
                                              | _, _ => TE.deftyp
                                              end
                             | Bmul => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                              | Fuint s1, Fuint s2 => Fuint (s1 + s2)
                                              | Fsint s1, Fsint s2 => Fsint (s1 + s2)
                                              | _, _ => TE.deftyp
                                       end
                             | Bcomp c => Fuint 1
                             | Band | Bor | Bxor => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                                    | Fuint s1, Fuint s2 => Fuint (maxn s1 s2)
                                                    | Fsint s1, Fsint s2 => Fsint (maxn s1 s2)
                                                    | _, _ => TE.deftyp
                                                    end
                             | Bdiv => match type_of_fexpr e1 te with
                                       | Fuint n => Fuint n
                                       | Fsint n => Fsint (n+1)
                                       | _ => TE.deftyp
                                       end
                             | Brem => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                       | Fuint s1, Fuint s2 => Fuint (minn s1 s2)
                                       | Fsint s1, Fsint s2 => Fsint (minn s1 s2)
                                       | _, _ => TE.deftyp
                                       end
                             | Bcat => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                      | Fuint s1, Fuint s2 => Fuint (s1 + s2)
                                      | Fsint s1, Fsint s2 => Fuint (s1 + s2)
                                      | _, _ => TE.deftyp
                                      end
                             end
    | Emux c e1 e2 => let t1 := (type_of_fexpr e1 te) in
                      let t2 := (type_of_fexpr e2 te) in
                      match t1, t2 with
                      | Fuint w1, Fuint w2 => Fuint (maxn w1 w2)
                      | Fsint w1, Fsint w2 => Fsint (maxn w1 w2)
                      | _, _ => TE.deftyp
                      end
    | Evalidif c e => (* if (Z.ltb 0 (to_Z (eval_fexpr c s))) then *)
                      (type_of_fexpr e te)
    end.

  (* Expression evaluation, value *)
  Fixpoint eval_fexpr (e : fexpr) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap) : vstate * bits :=
    match e with
    | Econst t c => let val := match t with
                    | Fuint w1 => zext (w1 - size c) c
                    | Fsint w2 => sext (w2 - size c) c
                    | _ => c
                    end in (rs, val)
    | Eref v => (* SV.acc v s*)
    if mylListIn v readerls (* reader ports *)
    then match TE.find v data2etc with
        | None => (rs, [::b0])
        | Some a => 
          let '(addrvar, envar, midvar, flagvar, clkvar) := a in 
          match TE.find midvar read_la with(* 没有找到m是同步或异步 *)
          | None => (rs, [::b0])
          | Some thisread_la =>
          let addrval := SV.acc addrvar s in
          let enval := SV.acc envar s in
          let clk0val := SV.acc clkvar s in
          let clkval := SV.acc clkvar rs in
          let readv := 
          (if enval == [:: b0]
            then [::b0]
          else 
          (match TE.find midvar memmap with
          | None => [::b0]
          | Some b => memfind addrval b
          end)) in 
          if thisread_la == false
          then (*if (((clk0val == [:: b0]) && (clkval == [:: b1])) || (flagval == [::b1]))
              then*) (rs, readv)
              (*else (rs, [:: b0])*)
          else if (((clk0val == [:: b0]) && (clkval == [:: b1])) )
              then (*(SV.upd v readv rs, SV.acc v s)*)(rs, readv)
              else ((*SV.upd v readv *)rs, [::b0])
          end
        end
    else (rs, SV.acc v s) (* inst ports & others *)
    | Eprim_binop b e1 e2 =>
      let (rs0, ve1) := (eval_fexpr e1 rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, ve2) := (eval_fexpr e2 rs0 s te readerls writerls data2etc memmap read_la) in
      let te1 := type_of_fexpr e1 te in
      let te2 := type_of_fexpr e2 te in
      let val := (ebinop_op b te1 te2) ve1 ve2 in
      (rs1, val)
    | Eprim_unop u e =>
      let t := type_of_fexpr e te in
      let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
      let val := (eunop_op u t) val1 in
      (rs0, val)
    | Emux c e1 e2 =>
      let t1 := (type_of_fexpr e1 te) in
      let t2 := (type_of_fexpr e2 te) in
      let (rs0, valc) := (eval_fexpr c rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, val1) := (eval_fexpr e1 rs0 s te readerls writerls data2etc memmap read_la) in
      let (rs2, val2) := (eval_fexpr e2 rs1 s te readerls writerls data2etc memmap read_la) in
      let val := match t1, t2 with
      | Fuint w1, Fuint w2 => if ~~ (is_zero valc) 
      then (zext ((max w1 w2) - w1) val1) 
      else (zext ((max w1 w2) - w2) val2)
      | Fsint w1, Fsint w2 => if ~~ (is_zero valc) 
      then (sext ((max w1 w2) - w1) val1)
      else (sext ((max w1 w2) - w2) val2)
      | _, _ => [::]
      end in (rs2, val)
    | Evalidif c e => 
      let (rs0, valc) := (eval_fexpr c rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, val1) := (eval_fexpr e rs0 s te readerls writerls data2etc memmap read_la) in
      let val := if ~~ (is_zero valc) then val1 else [::] in
      (rs1, val)
    (* | Edeclare v t => zeros (sizeof_fgtyp t) *)
    | Ecast AsUInt e => 
      let (rs0, val) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in (rs0, val)
    | Ecast AsSInt e => let (rs0, val) := eval_fexpr e rs s te readerls writerls data2etc memmap read_la in (rs0, val)
    | Ecast AsClock e => let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
                         let val := [::lsb val1] in (rs0, val)
    | Ecast AsAsync e => let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
                         let val := [::lsb val1] in (rs0, val)
    end.
  
  (*Compute (ebinop_op Bcat (Fuint 4) (Fuint 4) [::true; true;true; true] [:: true]).
  Compute (ebinop_op Bsub (Fuint 16) (Fuint 16) [:: false] [:: false]).*)

  Definition upd_typenv_fport (p : fport) (te : TE.env) : TE.env :=
    match p with
    | Finput v t => TE.add v t te
    | Foutput v t => TE.add v t te
    end.

  Fixpoint upd_typenv_fports (ps : seq fport) (te : TE.env) : TE.env :=
    match ps with
    | [::] => te
    | h :: tl => upd_typenv_fports tl (upd_typenv_fport h te)
    end.

  (* Expression statement, type env *)
  Definition upd_typenv_fstmt (s : fstmt) (te : TE.env) (st : vstate) : TE.env :=
    match s with
    | Swire v t  => TE.add v t te
    | Sreg r => TE.add (rid r) (type r) te
    | Snode v e => TE.add v (type_of_fexpr e te) te
    | Smem m => let te1 := List.fold_left (fun tt tr => let tt0 := TE.add (addr tr) (Fuint ((Nat.log2 (depth m)) )) tt in
                                             let tt1 := TE.add (data tr) (data_type m) tt0 in
                                             let tt2 := TE.add (en tr) (Fuint 1) tt1 in
                                             TE.add (clk tr) Fclock tt2 
                               ) (reader m) te in
                            List.fold_left (fun tt tr => let tt0 := TE.add (addr0 tr) (Fuint ((Nat.log2 (depth m)) )) tt in
                               let tt1 := TE.add (data0 tr) (data_type m) tt0 in
                               let tt2 := TE.add (en0 tr) (Fuint 1) tt1 in
                               let tt3 := TE.add (clk0 tr) Fclock tt2 in
                               TE.add (mask tr) (Fuint 1) tt3
                               ) (writer m) (TE.add (mid m) Fclock te1) (* mid不代表任何值 *)
    | Sinst inst => upd_typenv_fports (iports inst) te
    | Sfcnct v e2 => TE.add v (type_of_fexpr e2 te) te
    | Sinvalid v => TE.add v (TE.vtyp v te) te
    | _ => te
    end.

  Fixpoint upd_typenv_fstmts (ss : seq fstmt) (te : TE.env) (s : vstate) : TE.env :=
    match ss with
    | [::] => te
    | h :: tl => upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s
    end.

  Definition eval_noninst_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
 : vstate * vstate * mapmem :=
    match st with
        | Sskip => (rs, s, memmap)
        | Swire v t => (rs, SV.upd v (zeros (sizeof_fgtyp t)) s, memmap)
        | Sreg r =>
          let (rs0, s0) := if SV.acc (rid r) rs == [::]
                          then (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) rs,
                                SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s)
                          else (rs, SV.upd (rid r) (SV.acc (rid r) rs) s) in
                    match reset r with
                    | NRst => (rs0, s0, memmap)
                    | Rst e1 e2 =>
                        let te1 := type_of_fexpr e1 te in
                        let (_, ve1) := eval_fexpr e1 rs s0 te readerls writerls data2etc memmap read_la in
                        let (_, ve2) := eval_fexpr e2 rs s0 te readerls writerls data2etc memmap read_la in
                        if (is_zero ve1) then (rs0, s0, memmap)
                        else
                          match te1 with
                          | Fuint 1 => (SV.upd (rid r) ve2 rs0, s0, memmap)
                          | Fasyncreset => (SV.upd (rid r) ve2 rs0, SV.upd (rid r) ve2 s0, memmap)
                          | _ => (rs0, s0, memmap)
                          end
                    end
        | Smem m => (rs, s, memmap)
        | Sinst inst => (rs, s, memmap) (* 在拓扑排序时始终放在每个mod的最后，用来对所有的inst更新rs/s/memory *)
        | Snode v e => let (rs0, ve) := eval_fexpr e rs s te readerls writerls data2etc memmap read_la in
                      (rs0, SV.upd v ve s, memmap)
        | Sfcnct v e2 => let (rs0, newv) := eval_fexpr e2 rs s te readerls writerls data2etc memmap read_la in 
                                let memmap0 := 
                                (if mylListIn v writerls (* writer ports *)
                                then match TE.find v data2etc with
                                      | None => memmap
                                      | Some a => (let '(addrvar,envar, midvar, maskvar, clkvar) := a in 
                                        match TE.find midvar memmap with
                                        | None => memmap (* parse ast时已生成所有mem的map TE.add midvar (memupd (from_nat 4 10) (from_nat 4 11) memempty) memmap*)
                                        | Some b => let maskval := SV.acc maskvar s in
                                                    let addrval := SV.acc addrvar s in 
                                                    let enval := SV.acc envar s in
                                                    let clkval := SV.acc clkvar rs in
                                                    let clk0val := SV.acc clkvar s in 
                                                    if ((enval == [:: b1]) && (clk0val == [:: b0]) && (clkval == [:: b1]))
                                                      then (if maskval == [:: b1]
                                                        then TE.add midvar (memupd addrval (SV.acc v s) b) memmap
                                                        else TE.add midvar (memupd addrval [:: b0] b) memmap
                                                      )
                                                      else
                                                      memmap
                                                    end
                                )
                                end
                                else memmap)
                                in
                                if SV.acc v rs0 == [::]
                                  then (rs0, SV.upd v newv s, memmap0)
                                else (SV.upd v newv rs0, s, memmap0) (* regs *)
        | Sinvalid v =>
          let tv := TE.vtyp v te in
          (rs, SV.upd v (zeros (sizeof_fgtyp tv)) s, memmap)
        | _ => (rs, s, memmap)
        end.

  Fixpoint eval_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
  (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss :=
  let te1 := upd_typenv_fstmt st te s in 
  match iternum with
  | 0 => let '(rs0,s0,memmap0) := eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap read_la in (rs0,s0,memmap0,fterss)
  | S iternum0 =>
    (match st with
        | Sfcnct v e2 => let (newrs, newv) := (match e2 with 
                            | Eref v1 => if mylListIn v1 finstoutl
                                        then let v0 := (match TE.find v1 finstoutm with (* outport -> (mod name a4, inst name a0) *)
                                        | None => [::b1] (* 不知道inst.output对应的fmodule*)
                                        | Some (a4,a0) => (match TE.find a4 ffmodsmap with (* mod name -> fstmt seq mst *) 
                                                    | None => [::b1;b1]
                                                    | Some mst => (match TE.find a0 fterss with
                                                                | None => [::b1;b1;b1]
                                                                | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find a4 finstin with (* mod name -> inport name list *)
                                                                                                        | None => [::b1;b1;b1;b1]
                                                                                                        | Some a2 => (match TE.find a0 finstinmap with
                                                                                                                    | None => [::b1;b1;b1;b1]
                                                                                                                    | Some a5 => (let updfinstin := a5 in
                                                                                                        (let s1 := upd_inner s s0 a2 updfinstin in 
                                                                                                          (* evaluate inner module *)
                                                                                                          let s2 := (let readerls0 := (match TE.find a4 rl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              let writerls0 := (match TE.find a4 wl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              let finstoutl0 := (match TE.find a4 allfinstoutl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              match TE.find a4 alldata2etc with
                                                                                                                              | None => s
                                                                                                                              | Some a => let data2etc0 := a in 
                                                                                                                              match TE.find a4 fread_la with
                                                                                                                              | None => s
                                                                                                                              | Some a => let read_la0 := a in
                                                                                                                                match TE.find a4 allfinstoutm with
                                                                                                                                | None =>  s
                                                                                                                                | Some a => let finstoutm0 := a in
                                                                                                                                  match TE.find a4 allfinstportmap with
                                                                                                                                  | None =>  s
                                                                                                                                  | Some a => let (finstinmap0,finstoutmap0) := a in
                                                                                                                                      let '(_, s2, _, _) := 
                                                                                                                                      List.fold_left (fun '(trs, ts, tmemmap, tfterss) tempst => eval_fstmt tempst trs ts te0 readerls0 writerls0 data2etc0 mem0 read_la0 finstoutl0 finstoutm0 ffmodsmap tfterss fread_la finstin finstinmap0 finstoutmap0 rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, mem0, fterss) in
                                                                                                                                      s2   
                                                                                                                                  end
                                                                                                                                end
                                                                                                                                end
                                                                                                                              end) in
                                                                                                          (match TE.find v1 finstoutmap with
                                                                                                          | None => nil
                                                                                                          | Some a3 => SV.acc a3 s2
                                                                                                          end)))
                                                                                                          end)
                                                                                                        end)
                                                                end)
                                                    end)
                                        end) in (rs, v0)                                 
                                        else (eval_fexpr e2 rs s te1 readerls writerls data2etc memmap read_la)
                            | _ => (eval_fexpr e2 rs s te1 readerls writerls data2etc memmap read_la)
                            end) in 
                            let memmap0 := 
                            (if mylListIn v writerls (* writer ports *)
                            then match TE.find v data2etc with
                                  | None => memmap
                                  | Some a => (let '(addrvar,envar, midvar, maskvar, clkvar) := a in 
                                    match TE.find midvar memmap with
                                    | None => memmap 
                                    | Some b => let maskval := SV.acc maskvar s in
                                                let addrval := SV.acc addrvar s in 
                                                let clkval := SV.acc clkvar rs in
                                                let clk0val := SV.acc clkvar s in 
                                                let enval := SV.acc envar s in
                                                if ((enval == [:: b1]) && (clk0val == [:: b0]) && (clkval == [:: b1]))
                                                  then (if maskval == [:: b1]
                                                    then TE.add midvar (memupd addrval (SV.acc v s) b) memmap
                                                    else TE.add midvar (memupd addrval [:: b0] b) memmap
                                                  )
                                                  else memmap
                                                end
                            )
                            end
                            else memmap)in
                            if SV.acc v newrs == [::]
                              then (newrs, SV.upd v newv s, memmap0, fterss)
                            else (SV.upd v newv newrs, s, memmap0, fterss) (* regs *)
    | Sinst inst => let v := iid inst in
                  match TE.find (imid inst) ffmodsmap with (* mod name -> fstmt seq mst *) 
                  | None => (SV.upd v [:: b1] rs,s,memmap,fterss)
                  | Some mst => (match TE.find (iid inst) fterss with
                              | None => (SV.upd v [:: b1;b1] rs,s,memmap,fterss)
                              | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find (imid inst) finstin with (* mod name -> inport name list *)
                                                                          | None => (SV.upd v [:: b1;b1;b1] rs,s,memmap,fterss)
                                                                          | Some a2 => (match TE.find v finstinmap with
                                                                                      | None => (rs,s,memmap,fterss)
                                                                                      | Some a3 => (let updfinstin := a3 in
                                                                          (let s1 := upd_inner s s0 a2 updfinstin in
                                                                           (* evaluate inner module *)
                                                                           let readerls0 := (match TE.find (imid inst) rl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  let writerls0 := (match TE.find (imid inst) wl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  let finstoutl0 := (match TE.find (imid inst) allfinstoutl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  match TE.find (imid inst) alldata2etc with
                                                                                  | None => (SV.upd v [:: b1;b1;b1] rs,s,memmap,fterss)
                                                                                  | Some a => let data2etc0 := a in 
                                                                                    match TE.find (imid inst) allfinstoutm with
                                                                                    | None =>  (SV.upd v [:: b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                    | Some a => let finstoutm0 := a in
                                                                                      match TE.find (imid inst) allfinstportmap with
                                                                                      | None =>  (SV.upd v [:: b1;b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                      | Some a => let (finstinmap0,finstoutmap0) := a in
                                                                                        match TE.find (imid inst) fread_la with
                                                                                        | None => (SV.upd v [:: b1;b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                        | Some a => let read_la0 := a in
                                                                                          let '(rs2, s2, memmap2, fterss2) := 
                                                                                          List.fold_left (fun '(trs, ts, tmemmap, tfterss) tempst => eval_fstmt tempst trs ts te0 readerls0 writerls0 data2etc0 mem0 read_la0 finstoutl0 finstoutm0 ffmodsmap tfterss fread_la finstin finstinmap0 finstoutmap0 rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, mem0, fterss) in
                                                                                          (rs, s, memmap, TE.add v (te0,rs2,s2,memmap2) fterss2)
                                                                                      end
                                                                                    end
                                                                                    end
                                                                                  end))
                                                                                  end)
                                                                          end)
                              end)
                  end
    | _ => let '(rs0,s0,memmap0) := eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap read_la in (rs0,s0,memmap0,fterss)
    end)
    end.  

  Fixpoint eval_fstmts st rs s te (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
  (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss :=
    match st with
    | [::] => (rs, s, memmap, fterss) (* 对所有inst更新 terss、memory *)
    | h :: tl => let te1 := upd_typenv_fstmt h te s in 
      let '(rs1, s1, memmap0, fterss0) := eval_fstmt h rs s te1 readerls writerls data2etc memmap read_la finstoutl finstoutm ffmodsmap fterss fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum in
      eval_fstmts tl rs1 s1 te1 readerls writerls data2etc memmap0 read_la finstoutl finstoutm ffmodsmap fterss0 fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum
    end.

  Fixpoint upd_argulist s (io_in : mapioin) name ind : vstate :=
    match name with
     | [:: ] => s
     | h::t => let tin := match TE.find h io_in with
                          | None => nil
                          | Some a => a
                          end in
     upd_argulist (SV.upd h (List.nth ind tin [::b0]) s) io_in t ind
    end.

  Definition myupdateo s2 omap l := 
  let newv := SV.acc l s2 in
  let newl := match (TE.find l omap) with
  | Some a => (List.rev (List.cons newv (List.rev a)))
  | None => [:: [::b1]]
  end in
  TE.add l newl omap.

  Definition eval_module (v : var) rs s (te : TE.env) (io_in : mapioin) ols (readerls : mapls) (writerls : mapls) (data2etc : map2etc) (memmap : mapmem)
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstportmap : mmapvar) (iternum : nat) : vstate * vstate * mapmem * mapterss * mapioin :=
    match (TE.find v ffmodsmap) with
    | Some st => (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
                        let readerls0 := (match TE.find v readerls with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        let writerls0 := (match TE.find v writerls with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        let finstoutl0 := (match TE.find v finstoutl with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        match TE.find v data2etc with
                        | None => (rs,s, memmap, fterss, io_in)
                        | Some a => let data2etc0 := a in 
                        match TE.find v fread_la with
                        | None => (rs,s, memmap, fterss, io_in)
                        | Some read_la =>
                          match TE.find v finstoutm with
                          | None =>  (rs,s, memmap, fterss, io_in)
                          | Some a => let finstoutm0 := a in
                            match TE.find v finstportmap with
                            | None =>  (rs,s, memmap, fterss, io_in)
                            | Some a => let (finstinmap0,finstoutmap0) := a in
                            let '(rs2,s2, memmap2, fterss2) := eval_fstmts (rev st) rs s te readerls0 writerls0 data2etc0 memmap read_la finstoutl0 finstoutm0 ffmodsmap fterss fread_la finstin finstinmap0 finstoutmap0 readerls writerls data2etc finstoutl finstoutm finstportmap iternum in
                            let io_in2 := List.fold_left (myupdateo s2) ols io_in in
                            (rs2,s2, memmap2, fterss2, io_in2)
                            end
                            end
                          end
                        end
    | None => (rs,s, memmap, fterss, io_in)
    end.

Fixpoint run_module0 (mainmod : var) rs s te (io_in : mapioin) name ols readerls writerls data2etc memmap clk_num len 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss * mapioin :=
  match clk_num with
    | 0 => (rs,s,memmap,fterss,io_in)
    | S m => let n := len - S m in
             let s1 := upd_argulist s io_in name n in
             (*let te1 := upd_typenv_fstmts st te s1 in*) (* 放在和upd fports同时？ *)
             let '(rs2, s2, memmap0, fterss0, io_in0) := eval_module mainmod rs s1 te io_in ols readerls writerls data2etc memmap finstoutl finstoutm ffmodsmap fterss fread_la finstin finstportmap iternum in (* 每个clk后 fterss 需要更新*)
             run_module0 mainmod rs2 s2 te io_in0 name ols readerls writerls data2etc memmap0 m len finstoutl finstoutm ffmodsmap fterss0 fread_la finstin finstportmap iternum
    end.
    

Fixpoint expr2varlist (expr : fexpr) (ls : seq var) : seq var := 
  match expr with
  | Econst _ _ => ls
  | Eref v => List.cons v ls
  | Eprim_unop _ e1 => expr2varlist e1 ls
  | Eprim_binop _ e1 e2 => expr2varlist e2 (expr2varlist e1 ls)
  | Emux e1 e2 e3 => expr2varlist e3 (expr2varlist e2 (expr2varlist e1 ls))
  | Evalidif e1 e2 => expr2varlist e2 (expr2varlist e1 ls)
  | Ecast _ e => expr2varlist e ls
  end.

Definition findreg (ls roots : seq var) (st : fstmt) : seq var * seq var :=
  match st with
  | Sreg r => (List.cons (rid r) ls, List.cons (rid r) roots)
  | Snode v e => if (expr2varlist e [::] == [::]) then (ls, List.cons v roots)
                  else (ls, roots)
  | Sfcnct v1 e2 => if (expr2varlist e2 [::] == [::]) then (ls, List.cons v1 roots)
                    else (ls, roots)
  | Sinvalid v => (ls, List.cons v roots)
  | _ => (ls, roots)
  end.

  Definition findallvar (ls : seq var) (st : fstmt) : seq var :=
  match st with
  | Sreg r => List.cons (rid r) ls
  | Snode v _ => List.cons v ls
  | Swire v _ => List.cons v ls
  | Smem m => let ls0 := List.fold_left (fun tl tr => List.cons (addr tr) ls) (reader m) ls in
              List.fold_left (fun tl tr => List.cons (addr0 tr) ls) (writer m) ls0
  | Sinst inst => List.fold_left (fun tl tp => match tp with
                                  | Finput v _ => List.cons v tl
                                  | Foutput v _ => List.cons v tl
                                  end) (iports inst) ls
  | Sinvalid v => List.cons v ls
  | _ => ls
  end.

Definition def_known_reg_order (regls : seq var) (defls : seq fstmt) (knownls : seq fstmt) (regstmtls : seq fstmt) (st : fstmt) : seq fstmt * seq fstmt * seq fstmt :=
  match st with
  | Sskip => (defls, cons st knownls, regstmtls)
  | Swire _ _ => (cons st defls, knownls, regstmtls)
  | Sreg _ => (cons st defls, knownls, regstmtls)
  | Smem m => (cons st defls, knownls, regstmtls) 
  | Sinst _ => (defls, knownls, cons st regstmtls) (*TBD*)
  | Snode v e => if (expr2varlist e [::] == [::]) then (defls, cons st knownls, regstmtls)
                else (defls, knownls, regstmtls)
  | Sfcnct v1 e2 => if (expr2varlist e2 [::] == [::]) then (defls, cons st knownls, regstmtls)
                                 else (if (varIn v1 regls) then (defls, knownls, cons st regstmtls)
                                                          else (defls, knownls, regstmtls))
  | Sinvalid _ => (defls, cons st knownls, regstmtls)
  | _ => (defls, knownls, regstmtls) (*Swhen\Sstop*)
  end.

Definition known_reg_orders (oldstmts : seq fstmt) : seq fstmt * seq fstmt * seq fstmt := 
  let (regls, _) := List.fold_left (fun '(ls1, ls2) tst => findreg ls1 ls2 tst) oldstmts ([::], [::]) in
  let '(revdefls, revknownls, revregstmtls) := List.fold_left (fun '(templ1, templ2, templ3) st => def_known_reg_order regls templ1 templ2 templ3 st) oldstmts ([::],[::],[::]) in
  let knownls := List.rev revknownls in 
  let regstmtls := List.rev revregstmtls in
  let defls := List.rev revdefls in
  (defls, knownls, regstmtls).

Definition addreader2g (tempg : g) (tempr : freader_port) : g :=
  let g0 := updg (addr tempr) (cons (data tempr) (findg (addr tempr) tempg)) tempg in
  let g1 := updg (en tempr) (cons (data tempr) (findg (en tempr) g0)) g0 in
  updg (clk tempr) (cons (data tempr) (findg (clk tempr) g1)) g1.

Definition addwriter2g (tempg : g) (tempw : fwriter_port) : g :=
  let g0 := updg (addr0 tempw) (cons (data0 tempw) (findg (addr0 tempw) tempg)) tempg in
  let g1 := updg (en0 tempw) (cons (data0 tempw) (findg (en0 tempw) g0)) g0 in
  let g2 := updg (clk0 tempw) (cons (data0 tempw) (findg (clk0 tempw) g1)) g1 in
  updg (mask tempw) (cons (data0 tempw) (findg (mask tempw) g2)) g2.

Definition addnewruw2g0 (temprl : seq freader_port) (tempg : g) (tempw : fwriter_port) : g :=
  List.fold_left (fun tg tempr => updg (data0 tempw) (cons (data tempr) (findg (data0 tempw) tg)) tg) temprl tempg.

Definition addnewruw2g1 (temprl : seq freader_port) (tempg : g) (tempw : fwriter_port) : g :=
  List.fold_left (fun tg tempr => updg (data tempr) (cons (data0 tempw) (findg (data tempr) tg)) tg) temprl tempg.

Definition inst_inoutlist (pl : seq fport) : seq var * seq var :=
  List.fold_left (fun '(il, ol) tempp => match tempp with
                                        | Finput v _ => (List.cons v il, ol)
                                        | Foutput v _ => (il, List.cons v ol)
                                        end) pl ([::],[::]).

Fixpoint dfs (fing : g) (n : nat) (v : seq var) (x : var) : seq var :=
  if (varIn x v) then v else (
    match n with 
    | S n' => foldl (dfs fing n') (x :: v) (fing x)
    | 0 => v
    end).

(* y是否依赖于x *)
Definition dfs_path (fing : g) (n : nat) (x : var) (y : var) : bool :=
  let xchildren := dfs fing n [::] x in
  varIn y xchildren.

Definition add_regedge (regls : seq var) (fing : g) (st : fstmt) 
  : g :=
  match st with
  | Sfcnct v1 e2 => (match e2 with
                                | Econst _ _ => fing
                                | _ => (if (varIn v1 regls) then (let preset := expr2varlist e2 [::] in
                                              List.fold_left (fun tempg tempv => updg tempv (cons v1 (findg tempv tempg)) tempg) preset fing) else fing)
                                end)
  | _ => fing
  end.

Definition buildg (regls : seq var) (flagmap : fmap) (inportsmap : mapvar) (outportsmap : mapvar) (knowng : mapg) (fing : g) (var2stmt : var2stmtmap) (st : fstmt) 
  : g * var2stmtmap :=
  match st with
  | Sskip => (fing, var2stmt)
  | Swire _ _ => (fing, var2stmt)
  | Sreg _ => (fing, var2stmt)
  | Smem m => let readerls := reader m in
              let newg0 := List.fold_left addreader2g readerls fing in
              let writerls := writer m in
              let newg1 := List.fold_left addwriter2g writerls newg0 in
              let newg := (match (read_write m) with
              | old => List.fold_left (addnewruw2g1 readerls) writerls newg1  (* reader的后继是writer *)
              | new => List.fold_left (addnewruw2g0 readerls) writerls newg1  (* writer后继是reader *)
              | undefined => newg1
              end) in
              (newg, var2stmt) 
  | Sinst inst => let instmod := imid inst in
                  let instg := (match (TE.find instmod knowng) with
                              | None => emptyg
                              | Some tempg => tempg
                              end) in
                  let (inports, outports) := inst_inoutlist (iports inst) in
                  let instlen := (match (TE.find instmod flagmap) with
                              | None => 0
                              | Some tempg => tempg
                              end) in
                  let newg := List.fold_left (fun tempg inp => (match (TE.find inp inportsmap) with
                                                              | Some ininp => List.fold_left (fun tempg0 outp => (match (TE.find outp outportsmap) with
                                                                                                                | Some inoutp => (if (dfs_path instg instlen ininp inoutp) 
                                                                                                                  then (updg inp (cons outp (findg inp tempg0)) tempg0) else tempg0)
                                                                                                                | None => tempg0
                                                                                                                end)) outports tempg
                                                              | None => tempg
                                                              end)) inports fing in
                    (newg, var2stmt) (*TBD*)
  | Snode v e =>let preset := expr2varlist e [::] in
                if (preset == [::]) then (fing, var2stmt)
                else let newg := List.fold_left (fun tempg tempv => updg tempv (cons v (findg tempv tempg)) tempg) preset fing in
                              (newg, TE.add v st var2stmt)
  | Sfcnct v1 e2 => let preset := expr2varlist e2 [::] in
                                if (preset == [::]) then (fing, var2stmt)
                                else (if (varIn v1 regls) then (fing, var2stmt) 
                                        else (let newg := List.fold_left (fun tempg tempv => updg tempv (cons v1 (findg tempv tempg)) tempg) preset fing in
                                              (newg, TE.add v1 st var2stmt)))
  | Sinvalid _ => (fing, var2stmt)
  | _ => (fing, var2stmt) (*Swhen\Sstop*)
  end.

Definition findkinstps (kpsmap : mapls) (finsti2e_outmap : mvar) (ls : seq var) (st : fstmt) : seq var :=
match st with
| Sinst inst => let mv := imid inst in
                let iv := iid inst in
                match (TE.find mv kpsmap) with
                | None => ls
                | Some kps => 
                match (TE.find iv finsti2e_outmap) with
                              | None => ls
                              | Some outmap =>
                              (let exkps := List.fold_left (fun tls p => match (TE.find p outmap) with
                                                                        | None => tls
                                                                        | Some exp => (exp :: tls)
                                                                        end) kps [::] in
                              ls ++ exkps)
                              end
                end
| _ => ls
end.

Fixpoint topo_tree (fing : g) (n : nat) (gray_nodes : seq var) (already_found : option (seq var)) (root : var) : option (seq var) :=
match already_found, n with
| None, _ => already_found (* propagate earlier error *)
| _, 0 => None 
| Some already_found', S n' => 
(if (root \in gray_nodes) then (Some (root :: gray_nodes)) (*None cycle *)
else if (root \in already_found') then already_found
else match (foldl (topo_tree fing n' (root :: gray_nodes)) already_found (fing root)) with
  | Some result => Some (root :: result)
  | None => None
  end)
end.

Definition topo_sort (fing : g) (n : nat) (vertices : seq var) : option (seq var) :=
foldl (topo_tree fing n [::]) (Some [::]) vertices.

(* 有module依赖关系的list: [C,B,C] C->B->A, A中有B的inst, B中有C的inst. mapg为mod name->mod graph *)

Fixpoint modname2g (modorder : seq var) (flagmap : fmap) (oldstmtsmap : mapfstmt) (instportsmap : mmvar) (finsti2e_outmap : mvar) (inpsmap : mapls) (outpsmap : mapls) (instoutl : mapls) (fingmap : mapg) (newstmtsmap : mapfstmt) (newvarmap : mapls) (kpsmap : mapls) : mapg * mapfstmt * mapls * mapls :=
  match modorder with
  | [::] => (fingmap, newstmtsmap, newvarmap, kpsmap)
  | h :: t => let tempstmts := (match (TE.find h oldstmtsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let '(inportsmap, outportsmap) := (match (TE.find h instportsmap) with
                                | Some tempm => tempm 
                                | None => (TE.empty var, TE.empty var)
                                end) in 
              let inps := (match (TE.find h inpsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let outps := (match (TE.find h outpsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let instoutps := (match (TE.find h instoutl) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let len := (match (TE.find h flagmap) with
                                | Some n => n 
                                | None => 0
                                end) in 

              let '(regls, roots) := List.fold_left (fun '(ls1, ls2) tst => findreg ls1 ls2 tst) tempstmts ([::], [::]) in
              let kinstps := List.fold_left (fun ls tst => findkinstps kpsmap finsti2e_outmap ls tst) tempstmts [::] in
              
              let '(newg, var2stmt) := List.fold_left (fun '(tempg, tempm) tempst => buildg regls flagmap inportsmap outportsmap fingmap tempg tempm tempst) tempstmts (emptyg, TE.empty fstmt) in
              let kps := (match (topo_sort newg len roots) with
              | None => [::]
              | Some tseq => List.fold_left (fun ls op => if (varIn op tseq) then (op :: ls) else ls) outps [::]
              end) in
              
              let allvar := List.fold_left (fun ls tst => findallvar ls tst) tempstmts [::] in
              (* 起点 : fcnct到常数、reg、node到常数、所有input、invalid 、inst中的reg、const*)
              match (topo_sort newg len (inps ++ roots ++ kinstps)(*allvar*)) with
              | None => (TE.add h newg fingmap, TE.add h [::] newstmtsmap, TE.add h [::] newvarmap, TE.add h [::] kpsmap)
              | Some tseq => let newvarorder := tseq in
              let newstorder := List.map (fun tv => match (TE.find tv var2stmt) with 
                                                    | None => if varIn tv instoutps then Sfcnct tv (Eref tv)
                                                    else sskip
                                                    | Some tempst => tempst
                                                    end) newvarorder in
              let '(fingmap0, newstmtsmap0, newvarmap0, kpsmap0) := (TE.add h newg fingmap, TE.add h newstorder newstmtsmap, TE.add h newvarorder newvarmap, TE.add h kps kpsmap) in
              modname2g t flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl fingmap0 newstmtsmap0 newvarmap0 kpsmap0 
              end
  end.

Definition reorder (modorder : seq var) (flagmap : fmap) (oldstmtsmap : mapfstmt) (instportsmap : mmvar) (finsti2e_outmap : mvar) (inpsmap : mapls) (outpsmap : mapls) (instoutl : mapls) : mapfstmt * mapls :=
  let '(defmap, knownmap, regstmtmap) := List.fold_left (fun '(tempm0, tempm1, tempm2) modname => let tempstmts := (match (TE.find modname oldstmtsmap) with
                                                        | None => [::]
                                                        | Some tstmts => tstmts 
                                                        end) in 
                                                        let '(newdefls, newknown, newreg) := known_reg_orders tempstmts in
                                                        (TE.add modname newdefls tempm0, TE.add modname newknown tempm1, TE.add modname newreg tempm2)) modorder (TE.empty (seq fstmt),TE.empty (seq fstmt), TE.empty (seq fstmt)) in
  let '(a, orderedmap, varmap, b) := modname2g modorder flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl (TE.empty g) (TE.empty (seq fstmt)) (TE.empty (seq var)) (TE.empty (seq var)) in
  let newstmtsmap := List.fold_left (fun tmap modname => match (TE.find modname defmap) with
                                                        | None => tmap 
                                                        | Some tdefs => match (TE.find modname regstmtmap) with
                                                        | None => tmap 
                                                        | Some tregs => match (TE.find modname orderedmap) with
                                                                        | None => tmap
                                                                        | Some tordered => match (TE.find modname knownmap) with
                                                                                          | None => tmap
                                                                                          | Some tknown => let allordered := tdefs ++ (tknown ++ (tordered ++ tregs)) in TE.add modname (rev allordered) tmap
                                                                                          end
                                                                        end
                                                        end
                                                        end) modorder (TE.empty (seq fstmt)) in
  (newstmtsmap, varmap)
  .

Definition run_module (modorder : seq var) (flagmap : fmap) (newinstportsmap : mmvar) (finsti2e_outmap : mvar) (mainmod : var) rs s te (io_in : mapioin) name ols readerls writerls data2etc memmap clk_num len 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstout : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss * mapioin :=
  let '(newffmodsmap, varmap) := reorder modorder flagmap ffmodsmap newinstportsmap finsti2e_outmap finstin finstout finstoutl in
  run_module0 mainmod rs s te io_in name ols readerls writerls data2etc memmap clk_num len finstoutl finstoutm newffmodsmap fterss fread_la finstin finstportmap iternum.

  (********************************************************************************)

  (* Parallel evaluation *)
  
  Definition eval_fport_init (p : fport) (s : vstate) : vstate :=
    match p with
    | Finput v t => if SV.acc v s == [::] then SV.upd v (from_Z (sizeof_fgtyp t) 0) s else s
    | Foutput v t => if SV.acc v s == [::] then SV.upd v (from_Z (sizeof_fgtyp t) 0) s else s
    end.

  Fixpoint eval_fports_init (ps : seq fport) (s : vstate) : vstate :=
    match ps with
    | [::] => s
    | h :: tl => eval_fports_init tl (eval_fport_init h s)
    end.
(*
  Fixpoint eval_fmodule (m : fmodule) (s : vstate) (te : TE.env) : vstate :=
    match m with
    | FInmod v ps st => let (_, s) := eval_fstmts st (SV.empty) ((eval_fports_init ps s)) te in s
    | _ => s
    end.
*)
  Definition upd_typenv_fmodule (m : fmodule) (te : TE.env) (s : vstate) : TE.env :=
    match m with
    | FInmod v ps ss => upd_typenv_fstmts ss (upd_typenv_fports ps te) s
    | _ => te
    end.
  
  (* fexpr eqn , TBD *)

  (* Well-typed *)

  (* well typed expr *)
  
  Fixpoint well_typed_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst t c => (sizeof_fgtyp t) == (size c)
    | Eref v => 0 < sizeof_fgtyp (TE.vtyp v te)
    (* | Edeclare v t => 0 < sizeof_fgtyp t *)
    | Ecast _ e1 => well_typed_fexpr e1 te
    | Eprim_unop o e1 => match o with 
                        | Upad _ => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | Ushl _ => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | Ushr _ => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | Ucvt => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | Uneg => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | Unot => match (type_of_fexpr e1 te) with
                                    | Fuint _ => well_typed_fexpr e1 te
                                    | Fsint _ => well_typed_fexpr e1 te
                                    | _ => false
                                    end
                        | _ => well_typed_fexpr e1 te
                        end
    | Eprim_binop b e1 e2 => match b with
                        | Bdshl => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Bdshr => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Badd | Bsub => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Bmul => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Band | Bor | Bxor => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Bdiv => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Brem => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        | Bcat => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                end
                        | Bcomp _ => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                  | Fuint _, Fuint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | Fsint _, Fsint _ => well_typed_fexpr e1 te && (well_typed_fexpr e2 te)
                                  | _, _ => false
                                  end
                        end
    | Emux c e1 e2 => let t1 := (type_of_fexpr e1 te) in
                      let t2 := (type_of_fexpr e2 te) in
                      match t1, t2 with
                      | Fuint _, Fuint _ => (well_typed_fexpr c te) && (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
                      | Fsint _, Fsint _ => (well_typed_fexpr c te) && (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
                      | _, _ => false
                      end
    | Evalidif c e1 => (well_typed_fexpr c te) && (well_typed_fexpr e1 te)
    end.

  (* no mem evaluation *)

  Fixpoint no_mem_eval_fexpr (e : fexpr) (s : vstate) (te : TE.env) : bits :=
    match e with
    | Econst t c => match t with
                  | Fuint w1 => zext (sizeof_fgtyp t - size c) c
                  | Fsint w2 => sext (sizeof_fgtyp t - size c) c
                  | _ => c
                  end
    | Eref v => SV.acc v s
    (* | Efield *)
    (* | Esubfield  *)
    | Eprim_binop b e1 e2 =>
      let ve1 := (no_mem_eval_fexpr e1 s te) in
      let ve2 := (no_mem_eval_fexpr e2 s te) in
      let te1 := type_of_fexpr e1 te in
      let te2 := type_of_fexpr e2 te in
      (ebinop_op b te1 te2) ve1 ve2
    | Eprim_unop u e =>
      let t := type_of_fexpr e te in
      (eunop_op u t) (no_mem_eval_fexpr e s te)
    | Emux c e1 e2 =>
      let t1 := (type_of_fexpr e1 te) in
      let t2 := (type_of_fexpr e2 te) in
      match t1, t2 with
      | Fuint w1, Fuint w2 => if ~~ (is_zero (no_mem_eval_fexpr c s te)) 
      then (zext ((maxn w1 w2) - w1) (no_mem_eval_fexpr e1 s te)) else(zext ((maxn w1 w2) - w2) (no_mem_eval_fexpr e2 s te))
      | Fsint w1, Fsint w2 => if ~~ (is_zero (no_mem_eval_fexpr c s te)) 
      then (sext ((maxn w1 w2) - w1) (no_mem_eval_fexpr e1 s te)) else(sext ((maxn w1 w2) - w2) (no_mem_eval_fexpr e2 s te))
      | _, _ => [::]
      end       
    | Evalidif c e => (* if ~~ (is_zero (no_mem_eval_fexpr c s te)) then*) (no_mem_eval_fexpr e s te) (* else [::]*)
    (* | Edeclare v t => zeros (sizeof_fgtyp t) *)
    | Ecast AsUInt e => no_mem_eval_fexpr e s te
    | Ecast AsSInt e => no_mem_eval_fexpr e s te
    | Ecast AsClock e => [::lsb (no_mem_eval_fexpr e s te)]
    | Ecast AsAsync e => [::lsb (no_mem_eval_fexpr e s te)]
    end.

  Definition no_mem_eval_noninst_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) : vstate * vstate :=
    match st with
    (*| Sskip => (rs, s)*)
    | Swire v t => (rs, SV.upd v (zeros (sizeof_fgtyp t)) s)
    | Sreg r =>
      let (rs0, s0) := if SV.acc (rid r) rs == [::]
                       then (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) rs,
                             SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s)
                       else (rs, SV.upd (rid r) (SV.acc (rid r) rs) s) in
                match reset r with
                | NRst => (rs0, s0)
                | Rst e1 e2 =>
                    let te1 := type_of_fexpr e1 te in
                    let ve1 := no_mem_eval_fexpr e1 s0 te in
                    let ve2 := no_mem_eval_fexpr e2 s0 te in
                    if (is_zero ve1) then (rs0, s0)
                    else
                      match te1 with
                      | Fuint 1 => (SV.upd (rid r) ve2 rs0, s0)
                      | Fasyncreset => (SV.upd (rid r) ve2 rs0, SV.upd (rid r) ve2 s0)
                      | _ => (rs0, s0)
                      end
                end
    (*| Smem m => (rs, s) 
    | Sinst _ => (rs, s) *)
    | Snode v e => (rs, SV.upd v (no_mem_eval_fexpr e s te) s)
    | Sfcnct v e2 => let newv := no_mem_eval_fexpr e2 s te in
                            let len0 := size newv in
                            match (TE.vtyp v te) with
                            | Fuint w => 
                                      if SV.acc v rs == [::]
                                      then (rs, SV.upd v (zext (w - len0) newv) s)
                                      else (SV.upd v (zext (w - len0) newv) rs, s)
                            | Fsint w => 
                                      if SV.acc v rs == [::]
                                      then (rs, SV.upd v (sext (w - len0) newv) s)
                                      else (SV.upd v (sext (w - len0) newv) rs, s)
                            | _ => (rs,s)
                            end
    | Sinvalid v =>
      let tv := TE.vtyp v te in
      (rs, SV.upd v (zeros (sizeof_fgtyp tv)) s)
    | _ => (rs, s)
    end.  

  
  Definition no_mem_upd_typenv_fstmt (s : fstmt) (te : TE.env) : TE.env :=
    match s with
    | Swire v t  => TE.add v t te
    | Sreg r => TE.add (rid r) (type r) te
    | Snode v e => TE.add v (type_of_fexpr e te) te
    | Sinst inst => upd_typenv_fports (iports inst) te
    | Sinvalid v => TE.add v (TE.vtyp v te) te
    | _ => te
    end.

  Fixpoint no_mem_upd_typenv_fstmts (ss : seq fstmt) (te : TE.env): TE.env :=
    match ss with
    | [::] => te
    | h :: tl => no_mem_upd_typenv_fstmts tl (no_mem_upd_typenv_fstmt h te)
    end.
  
  Fixpoint no_mem_eval_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) 
    (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
    (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapterss :=
    match iternum with
    | 0 => let '(rs0,s0) := no_mem_eval_noninst_fstmt st rs s te in (rs0,s0,fterss)
    | S iternum0 =>
      (match st with
          | Sfcnct v e2 => match e2 with 
                              | Eref v1 => if mylListIn v1 finstoutl
                                          then let newv := ((match TE.find v1 finstoutm with (* outport -> (mod name a4, inst name a0) *)
                                          | None => nil (* 不知道inst.output对应的fmodule*)
                                          | Some (a4,a0) => (match TE.find a4 ffmodsmap with (* mod name -> fstmt seq mst *) 
                                                      | None => nil
                                                      | Some mst => (match TE.find a0 fterss with
                                                                  | None => nil
                                                                  | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find a4 finstin with (* mod name -> inport name list *)
                                                                                                          | None => nil
                                                                                                          | Some a2 => (match TE.find a0 finstinmap with
                                                                                                                      | None => nil
                                                                                                                      | Some updfinstin => match TE.find a4 allfinstoutl with
                                                                                                                                          | None => nil
                                                                                                                                          | Some finstoutl0 =>
                                                                                                          (let s1 := upd_inner s s0 a2 updfinstin in 
                                                                                                            (* evaluate inner module *)
                                                                                                            let s2 := (match TE.find a4 allfinstoutm with
                                                                                                              | None =>  s
                                                                                                              | Some finstoutm0 =>
                                                                                                                match TE.find a4 allfinstportmap with
                                                                                                                | None =>  s
                                                                                                                | Some (finstinmap0,finstoutmap0) =>
                                                                                                                let te1 := no_mem_upd_typenv_fstmts (rev mst) te0 in
                                                                                                                snd (fst (List.fold_left (fun '(trs, ts, tfterss) tempst => no_mem_eval_fstmt tempst trs ts te1 finstoutl0 finstoutm0 ffmodsmap tfterss finstin finstinmap0 finstoutmap0 allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, fterss)))
                                                                                                                end
                                                                                                              end) in
                                                                                                            (match TE.find v1 finstoutmap with
                                                                                                            | None => nil
                                                                                                            | Some a3 => SV.acc a3 s2
                                                                                                            end))end end)
                                                                                                            end)
                                                                                                          end)
                                                                  end)
                                                      end)) in
                                                      if SV.acc v rs == [::]
                                                        then (rs, SV.upd v newv s, fterss)
                                                      else (SV.upd v newv rs, s, fterss) (* regs *)
                                          else let '(rs0,s0) := no_mem_eval_noninst_fstmt st rs s te in (rs0,s0,fterss)
                              | _ => let '(rs0,s0) := no_mem_eval_noninst_fstmt st rs s te in (rs0,s0,fterss)
                              end
          | Sinst inst => let v := iid inst in
                              match TE.find (imid inst) ffmodsmap with (* mod name -> fstmt seq mst *) 
                              | None => (rs, s, fterss)
                              | Some mst => (match TE.find (iid inst) fterss with
                                          | None => (rs,s,fterss)
                                          | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find (imid inst) finstin with (* mod name -> inport name list *)
                                                                                      | None => (rs,s,fterss)
                                                                                      | Some a2 => (match TE.find v finstinmap with
                                                                                                  | None => (rs,s,fterss)
                                                                                                  | Some updfinstin =>
                                                                                      (let s1 := upd_inner s s0 a2 updfinstin in
                                                                                       (* evaluate inner module *)
                                                                                              match TE.find (imid inst) allfinstoutl with
                                                                                              | None => (rs,s,fterss)
                                                                                              | Some finstoutl0 => 
                                                                                                match TE.find (imid inst) allfinstoutm with
                                                                                                | None =>  (rs,s,fterss)
                                                                                                | Some a => let finstoutm0 := a in
                                                                                                  match TE.find (imid inst) allfinstportmap with
                                                                                                  | None =>  (rs,s,fterss)
                                                                                                  | Some a => let (finstinmap0,finstoutmap0) := a in
                                                                                                      let '(rs2, s2, fterss2) := 
                                                                                                      List.fold_left (fun '(trs, ts, tfterss) tempst => no_mem_eval_fstmt tempst trs ts te0 finstoutl0 finstoutm0 ffmodsmap tfterss finstin finstinmap0 finstoutmap0 allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, fterss) in
                                                                                                      (rs, s, TE.add v (te0,rs2,s2,mem0) fterss2)
                                                                                                  end
                                                                                                end
                                                                                              end)
                                                                                                  end)
                                                                                      end)
                                          end)
                              end
          | _ => let '(rs0,s0) := no_mem_eval_noninst_fstmt st rs s te in (rs0,s0,fterss)
      end)
      end.  

  Fixpoint no_mem_eval_fstmts st rs s te (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
  (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapterss :=
  match st with
  | [::] => (rs, s, fterss)
  | hd :: tl => let te0 := no_mem_upd_typenv_fstmt hd te in
                let '(rs0, s0, _) := no_mem_eval_fstmt hd rs s te0 finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap iternum in
                no_mem_eval_fstmts tl rs0 s0 te0 finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap iternum
  end.

  (*List.fold_left (fun '(trs, ts, tfterss) tempst => no_mem_eval_fstmt tempst trs ts te finstoutl finstoutm ffmodsmap tfterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap iternum) st (rs, s, fterss).
*)
  Definition no_mem_eval_module (v : var) rs s (te : TE.env) (io_in : mapioin) ols
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (finstin : mapls) (finstportmap : mmapvar) (iternum : nat) : vstate * vstate * mapterss * mapioin :=
    match (TE.find v ffmodsmap) with
    | Some st => (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
                        let finstoutl0 := (match TE.find v finstoutl with
                        | None =>  nil
                        | Some a => a 
                        end) in
                          match TE.find v finstoutm with
                          | None =>  (rs,s, fterss, io_in)
                          | Some a => let finstoutm0 := a in
                            match TE.find v finstportmap with
                            | None =>  (rs,s, fterss, io_in)
                            | Some a => let (finstinmap0,finstoutmap0) := a in
                            let '(rs2,s2, fterss2) := no_mem_eval_fstmts (rev st) rs s te finstoutl0 finstoutm0 ffmodsmap fterss finstin finstinmap0 finstoutmap0 finstoutl finstoutm finstportmap iternum in
                            let io_in2 := List.fold_left (myupdateo s2) ols io_in in
                            (rs2,s2, fterss2, io_in2)
                          end
                        end
    | None => (rs,s,fterss, io_in)
    end.

  Fixpoint no_mem_run_module0 (mainmod : var) rs s te (io_in : mapioin) name ols clk_num len 
    (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (finstin : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapterss * mapioin :=
    match clk_num with
      | 0 => (rs,s,fterss,io_in)
      | S m => let n := len - S m in
              let s1 := upd_argulist s io_in name n in
              (*let te1 := upd_typenv_fstmts st te s1 in*) (* 放在和upd fports同时？ *)
              let '(rs2, s2, fterss0, io_in0) := no_mem_eval_module mainmod rs s1 te io_in ols finstoutl finstoutm ffmodsmap fterss finstin finstportmap iternum in (* 每个clk后 fterss 需要更新*)
              no_mem_run_module0 mainmod rs2 s2 te io_in0 name ols m len finstoutl finstoutm ffmodsmap fterss0 finstin finstportmap iternum
      end.

  Definition no_mem_run_module (modorder : seq var) (flagmap : fmap) (newinstportsmap : mmvar) (finsti2e_outmap : mvar) (mainmod : var) rs s te (io_in : mapioin) name ols clk_num len 
    (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (finstin : mapls) (finstout : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapterss * mapioin :=
    let '(newffmodsmap, varmap) := reorder modorder flagmap ffmodsmap newinstportsmap finsti2e_outmap finstin finstout finstoutl in
    no_mem_run_module0 mainmod rs s te io_in name ols clk_num len finstoutl finstoutm newffmodsmap fterss finstin finstportmap iternum.

  Fixpoint no_mem_eval_fstmts_inline st rs s te : vstate * vstate :=
    match st with
    | [::] => (rs, s)
    | hd :: tl => let te0 := no_mem_upd_typenv_fstmt hd te in
                  let (rs0, s0) := no_mem_eval_noninst_fstmt hd rs s te0 in
                  no_mem_eval_fstmts_inline tl rs0 s0 te0
    end.
    
  Definition no_mem_eval_module_inline sl rs s (te : TE.env) (io_in : mapioin) ols : vstate * vstate * mapioin :=
    (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
    let '(rs2,s2) := no_mem_eval_fstmts_inline (rev sl) rs s te in
    let io_in2 := List.fold_left (myupdateo s2) ols io_in in
    (rs2,s2, io_in2).

  Fixpoint no_mem_run_module0_inline sl rs s te (io_in : mapioin) name ols clk_num len : vstate * vstate * mapioin :=
    match clk_num with
      | 0 => (rs,s,io_in)
      | S m => let n := len - S m in
              let s1 := upd_argulist s io_in name n in
              (*let te1 := upd_typenv_fstmts st te s1 in*) (* 放在和upd fports同时？ *)
              let '(rs2, s2, io_in0) := no_mem_eval_module_inline sl rs s1 te io_in ols in 
              no_mem_run_module0_inline sl rs2 s2 te io_in0 name ols m len
      end.

  Definition reorder_inline fmain : seq fstmt * g :=
  match fmain with
  | FInmod _ pl sl => 
    let '(def, known, regstmt) := known_reg_orders sl in
    let '(regls, roots) := List.fold_left (fun '(ls1, ls2) tst => findreg ls1 ls2 tst) sl ([::], [::]) in
    let inps := List.fold_left (fun ls p => match p with
                                            | Finput v _ => List.cons v ls
                                            | Foutput v _ => ls
                                            end) pl [::] in
    let '(newg, var2stmt) := List.fold_left (fun '(tempg, tempm) tempst => match tempst with
                                            |  Snode v e => 
                                              let preset := expr2varlist e [::] in
                                                if (preset == [::]) then (tempg, tempm)
                                                else let newg0 := List.fold_left (fun tempg0 tempv => updg tempv (cons v (findg tempv tempg0)) tempg0) preset tempg in
                                                              (newg0, TE.add v tempst tempm)
                                            | Sfcnct v1 e2 => let preset := expr2varlist e2 [::] in
                                                            if (preset == [::]) then (tempg, tempm)
                                                            else (if (varIn v1 regls) then (tempg, tempm)
                                                                    else (let newg0 := List.fold_left (fun tempg0 tempv => updg tempv (cons v1 (findg tempv tempg0)) tempg0) preset tempg in
                                                                          (newg0, TE.add v1 tempst tempm)))
                                            | _ => (tempg, tempm)
                                            end) sl (emptyg, TE.empty fstmt) in
    match (topo_sort newg (List.length pl + List.length sl) (inps ++ roots)) with
    | None => ([::], emptyg)
    | Some varorder =>
    let ordered := List.map (fun tv => match (TE.find tv var2stmt) with 
                  | None => sskip
                  | Some tempst => tempst
                  end) varorder in
    (def ++ known ++ ordered ++ regstmt, newg)
    end
  | _ => ([::], emptyg)
  end.

  Definition no_mem_run_module_inline fmain rs s te (io_in : mapioin) name ols clk_num len : vstate * vstate * mapioin :=
    let (reordersl, _) := reorder_inline fmain in
    no_mem_run_module0_inline (rev reordersl) rs s te io_in name ols clk_num len.

  (* conform lemmas *)

  Definition is_defined (v : var) (te : TE.env) : bool :=
    TE.mem v te.

  Fixpoint is_defined_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst _ _ => true
    | Eref v => is_defined v te
    (* | Edeclare v t => true *)
    | Ecast _ e1 => is_defined_fexpr e1 te
    | Eprim_unop _ e1 => is_defined_fexpr e1 te
    | Eprim_binop _ e1 e2 => (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Emux c e1 e2 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Evalidif c e1 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te)
    end.

  Definition is_defined_fstmt (s : fstmt) (te : TE.env) : bool :=
    match s with
    | Sskip => true
    | Swire v t => true
    | Sreg r => is_defined (rid r) te
    | Snode v e => is_defined_fexpr e te
    | Sfcnct v e => is_defined v te && is_defined_fexpr e te
    | _ => true
    end.

  (************************************************************)
  
  (* inline *)
  (* well formed expression *)
  Definition well_formed_fexpr e te := well_typed_fexpr e te && is_defined_fexpr e te.
  
  Definition well_typed_fstmt_inline (s : fstmt) (te : TE.env) s1 rs1 : bool :=
    match s with
    | Sskip => true
    | Swire v t => 0 < sizeof_fgtyp t
    | Sreg r => (*0 < sizeof_fgtyp (type r)*)(TE.vtyp (rid r) te == (type r)) &&
                (match (reset r) with
                 | NRst => true
                 | Rst e1 e2 => (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te) && 
                 (size (no_mem_eval_fexpr e2 (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s1) (TE.add (rid r) (type r) te)) == (sizeof_fgtyp (type r)))
                 && (size (no_mem_eval_fexpr e2 (SV.upd (rid r) (SV.acc (rid r) rs1) s1) (TE.add (rid r) (type r) te)) == (sizeof_fgtyp (type r)))
                 end)
    | Snode v e => well_typed_fexpr e te
    | Sfcnct v e => match (TE.vtyp v te) with
                                | Fuint w => well_typed_fexpr e te && (w >= (sizeof_fgtyp (type_of_fexpr e te)))
                                | Fsint w => well_typed_fexpr e te && (w >= (sizeof_fgtyp (type_of_fexpr e te)))
                                | _ => false
                                end
    | Sinst _ => false
    | _ => true
    end.
    
  (* well formed statement *)
  Definition well_formed_fstmt_inline s te s1 rs1 := well_typed_fstmt_inline s te s1 rs1 && is_defined_fstmt s te.

  Lemma conform_eval_swire_upd_env_inline rs1 s1 te v t :
    SV.conform s1 te ->
    well_formed_fstmt_inline (Swire v t) te s1 rs1 ->
    SV.conform (snd (no_mem_eval_noninst_fstmt (Swire v t) rs1 s1 (no_mem_upd_typenv_fstmt (Swire v t) te))) (no_mem_upd_typenv_fstmt (Swire v t) te).
  Proof.
    rewrite /= => Hcf1 Hwf.
    apply SV.conform_Upd with (zeros (sizeof_fgtyp t)) s1.
    rewrite size_zeros//.
    apply SV.Upd_upd.
    exact Hcf1.
  Qed.

  (*Lemma conform_eval_reg_upd_env_inline rs1 s1 te r : 
    SV.conform s1 te ->
    SV.conformr rs1 te ->
    well_formed_fstmt_inline (Sreg r) te s1 rs1 ->
    (SV.conform (snd (no_mem_eval_noninst_fstmt (Sreg r) rs1 s1 (no_mem_upd_typenv_fstmt (Sreg r) te))) (no_mem_upd_typenv_fstmt (Sreg r) te)) 
    /\ (SV.conformr (fst (no_mem_eval_noninst_fstmt (Sreg r) rs1 s1 (no_mem_upd_typenv_fstmt (Sreg r) te))) (no_mem_upd_typenv_fstmt (Sreg r) te)).
  Proof.*)

  Lemma conform_eval_reg_upd_env_inline rs1 s1 te r : 
    SV.conform s1 te ->
    SV.conform rs1 te ->
    well_formed_fstmt_inline (Sreg r) te s1 rs1 ->
    (SV.conform (snd (no_mem_eval_noninst_fstmt (Sreg r) rs1 s1 (no_mem_upd_typenv_fstmt (Sreg r) te))) (no_mem_upd_typenv_fstmt (Sreg r) te)) 
    /\ (SV.conform (fst (no_mem_eval_noninst_fstmt (Sreg r) rs1 s1 (no_mem_upd_typenv_fstmt (Sreg r) te))) (no_mem_upd_typenv_fstmt (Sreg r) te)).
  Proof.
    rewrite /= => Hcf1 Hcfr1 Hwf.
    rewrite /well_formed_fstmt_inline in Hwf.
    move /andP : Hwf => [Hwf Hmem].
    rewrite /is_defined_fstmt /is_defined in Hmem.
    simpl in Hwf. 
    move /andP : Hwf => [Htypr He2].
    move /eqP : Htypr => Htypr.

    assert (Haddsame : TE.Equal (TE.add (rid r) (type r) te) te).
    rewrite SV.Lemmas.add_same.
    apply SV.Lemmas.Equal_refl.
    rewrite -Htypr.
    case H: (TE.find (rid r) te).
    rewrite (TE.find_some_vtyp H) //.
    apply SV.Lemmas.find_none_not_mem in H.
    rewrite Hmem in H.
    discriminate.

    assert (Hzeros : SV.conform (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) rs1) (TE.add (rid r) (type r) te)).
    apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
    rewrite size_zeros//.
    apply SV.Upd_upd.
    done.

    assert (Hzeros1 : SV.conform (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s1) (TE.add (rid r) (type r) te)).
    apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
    rewrite size_zeros//.
    apply SV.Upd_upd.
    done.

    elim Hreset : (reset r) => [| e1 e2].
    - case Hinit : (SV.acc (rid r) rs1 == [::]).
      - split.
      simpl.
      apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
      rewrite size_zeros//.
      apply SV.Upd_upd.
      done.
      simpl.
      apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
      rewrite size_zeros//.
      apply SV.Upd_upd.
      done.
      - split.
      simpl.
      apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
      rewrite -(SV.conform_mem Hcfr1)//.
      rewrite (TE.vtyp_vsize Htypr) //.
      apply SV.Upd_upd.
      done.
      simpl.
      move : Hcfr1.
      apply SV.conform_equal.
      exact Haddsame.
    - case Hinit : (SV.acc (rid r) rs1 == [::]).
      - case Hzero : (is_zero (no_mem_eval_fexpr e1 (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s1)
      (TE.add (rid r) (type r) te))).
      split.
      simpl.
      apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
      rewrite size_zeros//.
      apply SV.Upd_upd.
      done.
      simpl.
      apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
      rewrite size_zeros//.
      apply SV.Upd_upd.
      done.
      case Htypee1 : (type_of_fexpr e1 (TE.add (rid r) (type r) te)) => [n||||].
      - (* Fuint n *)
        case Hn : n => [|n'].
          - split.
          simpl.
          apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
          rewrite size_zeros//.
          apply SV.Upd_upd.
          done.
          simpl.
          apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
          rewrite size_zeros//.
          apply SV.Upd_upd.
          done.
          - case Hn' : n'.
          split.
          simpl.
          apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
          rewrite size_zeros//.
          apply SV.Upd_upd.
          done.
          rewrite Hreset in He2.
          move /andP : He2 => [He2 He22].
          move /andP : He2 => [He2 He21].
          move /eqP : He21 => He21.
          move /eqP : He22 => He22.
          move /andP : He2 => [Hwf1 Hwf2].
          simpl.
          apply SV.conform_upd.
          symmetry.
          exact He21.
          move : Hzeros.
          apply SV.conform_equal.
          exact (SV.Lemmas.Equal_sym Haddsame).
          split.
          simpl.
          apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
          rewrite size_zeros//.
          apply SV.Upd_upd.
          done.
          simpl.
          apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
          rewrite size_zeros//.
          apply SV.Upd_upd.
          done.
        - 1,2,3: split.
        1,2,3,4,5,6,7,8: simpl.
        1,3,5: apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) s1.
        1,4,7: rewrite size_zeros//.
        1,3,5: apply SV.Upd_upd.
        1,2,3: done.
        1,2,3: apply SV.conform_Upd with (zeros (sizeof_fgtyp (type r))) rs1.
        1,4,7: rewrite size_zeros//.
        1,3,5: apply SV.Upd_upd.
        1,2,3: done.
        - (* Fasyncreset *)
        split.
        1,2: apply SV.conform_upd.
        1,2,3,4: rewrite Hreset in He2.
        1,2,3,4: move /andP : He2 => [He2 He22].
        1,2,3,4: move /andP : He2 => [He2 He21].
        1,2,3,4: move /eqP : He21 => He21.
        1,2,3,4: move /eqP : He22 => He22.
        1,2,3,4: move /andP : He2 => [Hwf1 Hwf2].
        1,3: symmetry.
        1,2: exact He21.
        move : Hzeros1.
        apply SV.conform_equal.
        exact (SV.Lemmas.Equal_sym Haddsame).
        move : Hzeros.
        apply SV.conform_equal.
        exact (SV.Lemmas.Equal_sym Haddsame).
      - case Hzero : (is_zero (no_mem_eval_fexpr e1 (SV.upd (rid r) (SV.acc (rid r) rs1) s1)
      (TE.add (rid r) (type r) te))).
      split.
      simpl.
      apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
      rewrite -(SV.conform_mem Hcfr1)//.
      rewrite (TE.vtyp_vsize Htypr) //.
      apply SV.Upd_upd.
      done.
      simpl.
      move : Hcfr1.
      apply SV.conform_equal.
      exact Haddsame.
      case Htypee1 : (type_of_fexpr e1 (TE.add (rid r) (type r) te)) => [n||||].
      - (* Fuint n *)
        case Hn : n => [|n'].
          - split.
          simpl.
          apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
          rewrite -(SV.conform_mem Hcfr1)//.
          rewrite (TE.vtyp_vsize Htypr) //.
          apply SV.Upd_upd.
          done.
          simpl.
          move : Hcfr1.
          apply SV.conform_equal.
          exact Haddsame.
          - case Hn' : n'.
          split.
          simpl.
          apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
          rewrite -(SV.conform_mem Hcfr1)//.
          rewrite (TE.vtyp_vsize Htypr) //.
          apply SV.Upd_upd.
          done.
          simpl.
          apply SV.conform_Upd with (no_mem_eval_fexpr e2
          (SV.upd (rid r) (SV.acc (rid r) rs1) s1)
          (TE.add (rid r) (type r) te)) rs1.
          rewrite Hreset in He2.
          move /andP : He2 => [He2 He22].
          move /andP : He2 => [He2 He21].
          move /eqP : He21 => He21.
          move /eqP : He22 => He22.
          move /andP : He2 => [Hwf1 Hwf2].
          symmetry.
          exact He22.
          apply SV.Upd_upd.
          done.
          split.
          simpl.
          apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
          rewrite -(SV.conform_mem Hcfr1)//.
          rewrite (TE.vtyp_vsize Htypr) //.
          apply SV.Upd_upd.
          done.
          simpl.
          move : Hcfr1.
          apply SV.conform_equal.
          exact Haddsame.
        - 1,2,3: split.
        1,2,3,4,5,6: simpl.
        1,3,5: apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
        1,4,7: rewrite -(SV.conform_mem Hcfr1)//.
        1,2,3: rewrite (TE.vtyp_vsize Htypr) //.
        1,3,5: apply SV.Upd_upd.
        1,2,3: done.
        1,2,3: move : Hcfr1.
        1,2,3: apply SV.conform_equal.
        1,2,3: exact Haddsame.
        - (* Fasyncreset *)
        split.
        simpl.
        apply SV.conform_upd.
        rewrite Hreset in He2.
        move /andP : He2 => [He2 He22].
        move /andP : He2 => [He2 He21].
        move /eqP : He21 => He21.
        move /eqP : He22 => He22.
        move /andP : He2 => [Hwf1 Hwf2].
        symmetry.
        exact He22.
        assert (Haccs1 : SV.conform (SV.upd (rid r) (SV.acc (rid r) rs1) s1) (TE.add (rid r) (type r) te)).
        apply SV.conform_Upd with (SV.acc (rid r) rs1) s1.
        rewrite -(SV.conform_mem Hcfr1)//.
        rewrite (TE.vtyp_vsize Htypr) //.
        apply SV.Upd_upd.
        done.
        move : Haccs1.
        apply SV.conform_equal.
        exact (SV.Lemmas.Equal_sym Haddsame).
        simpl.
        apply SV.conform_upd.
        rewrite Hreset in He2.
        move /andP : He2 => [He2 He22].
        move /andP : He2 => [He2 He21].
        move /eqP : He21 => He21.
        move /eqP : He22 => He22.
        move /andP : He2 => [Hwf1 Hwf2].
        symmetry.
        exact He22.
        exact Hcfr1.
  Qed.

  Lemma conform_eval_invalid_upd_env_inline rs1 s1 te v :
    SV.conform s1 te ->
    well_formed_fstmt_inline (Sinvalid v) te s1 rs1 ->
    SV.conform (snd (no_mem_eval_noninst_fstmt (Sinvalid v) rs1 s1 (no_mem_upd_typenv_fstmt (Sinvalid v) te))) (no_mem_upd_typenv_fstmt (Sinvalid v) te).
  Proof.
    rewrite /= => Hcf1 Hwf.
    apply SV.conform_Upd with (zeros (sizeof_fgtyp (TE.vtyp v (TE.add v (TE.vtyp v te) te)))) s1.
    rewrite size_zeros//.
    rewrite TE.vtyp_add_eq //.
    apply SV.Upd_upd.
    done.
  Qed.

  Lemma typeof_eval_fexpr e : forall s1 te,
    SV.conform s1 te ->
    well_formed_fexpr e te ->
    size (no_mem_eval_fexpr e s1 te) = sizeof_fgtyp (type_of_fexpr e te) .
  Proof.
    induction e.
    - (* const *)
      move => s1 te Hcf.
      simpl.
      case f;try by done.
      move => n Hb.
      rewrite /well_formed_fexpr in Hb.
      move : Hb => /andP [/eqP Hb _].
      rewrite size_zext Hb subnn addn0 //.
      move => n Hb.
      rewrite /well_formed_fexpr in Hb.
      move : Hb => /andP [/eqP Hb _].
      rewrite size_sext Hb subnn addn0 //.
      move => /andP [/eqP Hb _].
      symmetry.
      exact Hb.
      move => /andP [/eqP Hb _].
      symmetry.
      exact Hb.
      move => /andP [/eqP Hb _].
      symmetry.
      exact Hb.
    - (* cast *)
      case Hu:u.
      - (* asuint *)
        move => s1 te Hcf Hwt.
        simpl.
        simpl in Hwt.
        apply IHe with (s1:=s1) in Hwt.
        exact Hwt.
        exact Hcf.
      - (* assint *)
        move => s1 te Hcf Hwt.
        simpl.
        simpl in Hwt.
        apply IHe with (s1:=s1) in Hwt.
        exact Hwt.
        exact Hcf.
      - simpl.
        reflexivity.
        simpl.
        reflexivity.
    - (* unop *)
      move => s1 te Hcf.
      case e.
        (* pad *)
      - move => n Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        case Hn:(n < size (no_mem_eval_fexpr e0 s1 te)).
        rewrite Ht.
        apply IHe in Hcf.
        rewrite Hcf in Hn.
        rewrite Ht in Hn.
        rewrite Hn -Ht //.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht.
        apply IHe in Hcf.
        rewrite Hcf in Hn.
        rewrite Ht in Hn.
        rewrite Hn size_zext Hcf Ht subnKC //.
        apply contraFleq with (b:=(n < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        case Hn:(n < size (no_mem_eval_fexpr e0 s1 te)).
        rewrite Ht.
        apply IHe in Hcf.
        rewrite Hcf in Hn.
        rewrite Ht in Hn.
        rewrite Hn -Ht //.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht.
        apply IHe in Hcf.
        rewrite Hcf in Hn.
        rewrite Ht in Hn.
        rewrite Hn size_sext Hcf Ht subnKC //.
        apply contraFleq with (b:=(n < sizeof_fgtyp (Fsint n0))).
        trivial.
        exact Hn.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* shl *)
        move => n Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht size_cat size_zeros.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        rewrite addnC //.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht size_cat size_zeros.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        rewrite addnC //.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* shr *)
        move => n Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        case Hn : (n < size (no_mem_eval_fexpr e0 s1 te)).
        rewrite size_high.
        apply IHe in Hcf.
        rewrite Hcf Ht in Hn.
        simpl in Hn.
        rewrite Hn.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        apply IHe in Hcf.
        rewrite Hcf Ht in Hn.
        simpl in Hn.
        rewrite Hn.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        case Hn : (n < size (no_mem_eval_fexpr e0 s1 te)).
        rewrite size_high.
        apply IHe in Hcf.
        rewrite Hcf Ht in Hn.
        simpl in Hn.
        rewrite Hn.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        apply IHe in Hcf.
        rewrite Hcf Ht in Hn.
        simpl in Hn.
        rewrite Hn.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* cvt *)
        move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        rewrite size_sext.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* neg *)
        move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        rewrite size_negB size_zext.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        rewrite size_negB size_sext.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* not *)
        move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        case Ht:(type_of_fexpr e0 te) => [n0|n0|||].
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        rewrite size_invB.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        simpl.
        rewrite Ht.
        rewrite size_invB.
        apply IHe in Hcf.
        rewrite Hcf Ht.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
        rewrite Ht in Hwt.
        discriminate.
      - (* andr *)
        move => Hwf.
        simpl.
        reflexivity.
      - (* orr *)
        move => Hwf.
        simpl.
        reflexivity.
      - (* xorr *)
        move => Hwf.
        simpl.
        reflexivity.
      - (* extr *)
        move => n n0 Hwf.
        simpl.
        rewrite size_extract.
        reflexivity.
      - (* head *)
        move => n Hwf.
        simpl.
        rewrite size_high.
        reflexivity.
      - (* tail *)
        move => n Hwf.
        simpl.
        rewrite size_low.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        apply IHe in Hcf.
        rewrite Hcf.
        reflexivity.
        rewrite /well_formed_fexpr Hwt Hid //.
    - (* binop *)
    move => s1 te Hcf.
      case e1.
        (* add *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_addB_ext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite addn1 //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_SadcB_ext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite 2!size_sext Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite 2!size_sext Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* sub *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_subB_ext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite addn1 //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_SsbbB_ext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite 2!size_sext Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite 2!size_sext Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* mul *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_full_mul.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_Sfull_mul.
        generalize Hcf.
        apply IHe1 in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite Hcf Ht1.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* div *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_udivB.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_sext size_sdivB.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* rem *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_low //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_low //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* cmp *)
      - move => b Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case b.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        simpl.
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* dshl *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_zext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_sext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* dshr *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_shrB.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_sarB.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        reflexivity.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* and *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_andB 2!size_zext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_andB 2!size_sext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* or *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_orB 2!size_zext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_orB 2!size_sext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* xor *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_xorB 2!size_zext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_xorB 2!size_sext.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
      (* cat *)
      - move => Hwf.
        rewrite /well_formed_fexpr in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hid.
        simpl in Hwt.
        move : Hid => /andP [Hid1 Hid2].
        case Ht1:(type_of_fexpr e2 te) => [n0|n0|||].
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_cat.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite addnC //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        case Ht2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        simpl.
        rewrite Ht1 Ht2.
        simpl.
        rewrite size_cat.
        generalize Hcf.
        apply IHe1 in Hcf.
        rewrite Hcf Ht1.
        simpl.
        move => Hcf0.
        apply IHe2 in Hcf0.
        rewrite Hcf0 Ht2.
        simpl.
        rewrite addnC //.
        rewrite /well_formed_fexpr Hwt2 Hid2 //.
        rewrite /well_formed_fexpr Hwt1 Hid1 //.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 Ht2 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        rewrite Ht1 in Hwt.
        discriminate.
        - (* mux *)
      move => s1 te Hcf Hwf.
      rewrite /well_formed_fexpr in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl.
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      move : Hid2 => /andP [Hid1 Hid2].
      case H2:(type_of_fexpr e2 te) =>[n0|n0|||].
      case H3:(type_of_fexpr e3 te) =>[n1|n1|||].
      case H1:(is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [Hwt1 Hwt2].
      assert (Hwf2:well_formed_fexpr e2 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3:well_formed_fexpr e3 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt3 Hid3 //.
      apply IHe3 with (s1:=s1) in Hwf3.
      rewrite Hwf3 H3.
      simpl.
      rewrite subnKC //.
      rewrite leq_maxr //.
      exact Hcf.
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [Hwt1 Hwt2].
      assert (Hwf2:well_formed_fexpr e2 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3:well_formed_fexpr e3 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt3 Hid3 //.
      apply IHe2 with (s1:=s1) in Hwf2.
      rewrite Hwf2 H2.
      simpl.
      rewrite subnKC //.
      rewrite leq_maxl //.
      exact Hcf.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      case H3:(type_of_fexpr e3 te) =>[n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      case H1:(is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [Hwt1 Hwt2].
      assert (Hwf2:well_formed_fexpr e2 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3:well_formed_fexpr e3 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt3 Hid3 //.
      apply IHe3 with (s1:=s1) in Hwf3.
      rewrite Hwf3 H3.
      simpl.
      rewrite subnKC //.
      rewrite leq_maxr //.
      exact Hcf.
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [Hwt1 Hwt2].
      assert (Hwf2:well_formed_fexpr e2 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3:well_formed_fexpr e3 te).
      rewrite /well_formed_fexpr.
      rewrite Hwt3 Hid3 //.
      apply IHe2 with (s1:=s1) in Hwf2.
      rewrite Hwf2 H2.
      simpl.
      rewrite subnKC //.
      rewrite leq_maxl //.
      exact Hcf.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
    - (* validif *)
      move => s1 te Hcf Hwf.
      simpl.
      rewrite /well_formed_fexpr in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid1 Hid2].
      move : Hwt => /andP [Hwt1 Hwt2].
      apply IHe2 in Hcf.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
    - (* ref *)
      move => s1 te Hcf Hwt.
      simpl.
      simpl in Hwt.
      rewrite /well_formed_fexpr in Hwt.
      move : Hwt => /andP [_ Hid].
      simpl in Hid.
      rewrite /is_defined in Hid.
      apply SV.conform_mem with (v:=s) in Hcf.
      rewrite -Hcf.
      rewrite (TE.vtyp_vsize (eqP(eqxx (TE.vtyp s te))))//.
      exact Hid.
  Qed.

  Lemma acyclic_eval_expr_node : forall v e te s1 rs1 ty,
  well_formed_fstmt_inline (Snode v e) te s1 rs1 -> no_mem_eval_fexpr e s1 (TE.add v ty te) = no_mem_eval_fexpr e s1 te.
  Admitted.

  Lemma acyclic_eval_stmt_node : forall v e te s1 rs1,
  no_mem_eval_noninst_fstmt (Snode v e) rs1 s1 (TE.add v (type_of_fexpr e te) te) = no_mem_eval_noninst_fstmt (Snode v e) rs1 s1 te.
  Admitted.

  Lemma acyclic_typ_expr_node : forall v e te s1 rs1 ty,
  well_formed_fstmt_inline (Snode v e) te s1 rs1 -> type_of_fexpr e (TE.add v ty te) = type_of_fexpr e te.
  Admitted.

  Lemma conform_eval_node_upd_env_inline e : forall rs1 s1 te v ,
    SV.conform s1 te ->
    well_formed_fstmt_inline (Snode v e) te s1 rs1 ->
    SV.conform (snd (no_mem_eval_noninst_fstmt (Snode v e) rs1 s1 (no_mem_upd_typenv_fstmt (Snode v e) te))) (no_mem_upd_typenv_fstmt (Snode v e) te).
  Proof.
    rewrite {1}/no_mem_upd_typenv_fstmt.
    move => rs1 s1 te v Hcf Hwf.
    rewrite acyclic_eval_stmt_node.
    move : rs1 s1 te v Hcf Hwf.
    induction e.
    (* cosnt *)
    - rewrite /upd_typenv_fstmt.
    move => rs1 s1 te v Hcf Hwf.
    apply SV.conform_upd.
    rewrite /well_formed_fstmt_inline /= in Hwf.
    move : Hwf => /andP [/eqP H _].
    simpl.
    rewrite H subnn zext0 sext0.
    case f ;done.
    exact Hcf.
    (* cast *)
    - case u; try by done.
      (* uint *)
      - move => rs1 s1 te v Hcf Hwf.
      apply SV.conform_upd.
      simpl.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      assert (Hwf : well_formed_fstmt_inline (Snode v e) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt Hid //.
      specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe.
      apply IHe in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      exact Hcf.
      try reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf.
      exact Hcf.
      (* sint *)
      - move => rs1 s1 te v Hcf Hwf.
      apply SV.conform_upd.
      simpl.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      assert (Hwf : well_formed_fstmt_inline (Snode v e) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt Hid //.
      specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe.
      apply IHe in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      exact Hcf.
      try reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf.
      exact Hcf.
      - move => rs1 s1 te v Hcf Hwf.
      apply SV.conform_upd.
      simpl.
      reflexivity.
      exact Hcf.
      - move => rs1 s1 te v Hcf Hwf.
      apply SV.conform_upd.
      simpl.
      reflexivity.
      exact Hcf.
    (* enoup *)
    - case e; try by done.
    (* upad *)
      - move => n rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Hn:(n < sizeof_fgtyp (type_of_fexpr e0 te)).
        - case Htyp:(type_of_fexpr e0 te) => [n0|n0|||] ; rewrite Htyp in Hwt ; try discriminate.
          - assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            exact Hcf.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            exact Hcf.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
        - case Htyp:(type_of_fexpr e0 te) => [n0|n0|||] ; rewrite Htyp in Hwt ; try discriminate.
          - assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            rewrite size_zext -Hcf.
            simpl.
            rewrite subnKC //.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            apply contraFleq with (b:=(n < n0)).
            trivial.
            exact Hn.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            rewrite size_sext -Hcf.
            simpl.
            rewrite subnKC //.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            apply contraFleq with (b:=(n < n0)).
            trivial.
            exact Hn.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          exact Hcf.
      - (* shl *)
      move => n rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_cat -Hcf Htyp size_zeros.
        simpl.
        rewrite addnC //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_cat -Hcf Htyp size_zeros.
        simpl.
        rewrite addnC //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        exact Hcf.
      - (* shr *)
      move => n rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Hn:(n < sizeof_fgtyp (type_of_fexpr e0 te)).
        - case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
          - rewrite Htyp in Hwt.
            assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            rewrite Hn -Hcf size_high.
            simpl.
            reflexivity.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - rewrite Htyp in Hwt.
            assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            rewrite Hn -Hcf size_high.
            simpl.
            reflexivity.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - rewrite Htyp in Hwt.
            discriminate.
          - rewrite Htyp in Hwt.
            discriminate.
          - rewrite Htyp in Hwt.
            discriminate.
        - case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
          - rewrite Htyp in Hwt.
            assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            rewrite Hn.
            simpl.
            reflexivity.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - rewrite Htyp in Hwt.
            assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
            rewrite /well_formed_fstmt_inline.
            simpl.
            rewrite Hwt Hid //.
            specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
            simpl in IHe.
            apply IHe in Hcf.
            apply SV.conform_mem with (v:=v) in Hcf.
            rewrite TE.vsize_add_eq in Hcf.
            rewrite SV.acc_upd_eq in Hcf.
            rewrite Hcf in Hn.
            rewrite Hn.
            rewrite Htyp in Hcf.
            simpl in Hcf.
            rewrite -Hcf in Hn.
            rewrite Hn.
            simpl.
            reflexivity.
            reflexivity.
            reflexivity.
            apply SV.Lemmas.mem_add_eq.
            apply TE.SE.eq_refl.
            exact Hwf.
          - rewrite Htyp in Hwt.
            discriminate.
          - rewrite Htyp in Hwt.
            discriminate.
          - rewrite Htyp in Hwt.
            discriminate.
          exact Hcf.
      - (* cvt *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_sext -Hcf Htyp.
        simpl. 
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite Htyp in Hcf.
        exact Hcf.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        exact Hcf.
      - (* neg *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_negB size_zext -Hcf Htyp.
        simpl. 
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_negB size_sext -Hcf Htyp.
        simpl. 
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        exact Hcf.
      - (* not *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_invB.
        rewrite Htyp in Hcf.
        exact Hcf.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt Hid //.
        specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe.
        apply IHe in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite size_invB.
        rewrite Htyp in Hcf.
        exact Hcf.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        exact Hcf.
      - (* and *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      simpl.
      reflexivity.
      exact Hcf.
      - (* orr *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      simpl.
      reflexivity.
      exact Hcf.
      - (* xorr *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      simpl.
      reflexivity.
      exact Hcf.
      - (* extr *)
      move => n n0 rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd. 
      rewrite size_extract.
      simpl.
      reflexivity.
      exact Hcf.
      - (* head *)
      move => n rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd. 
      rewrite size_high.
      simpl.
      reflexivity.
      exact Hcf.
      - (* tail *)
      move => n rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd. 
      rewrite size_low.
      simpl.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      assert (Hwf : well_formed_fstmt_inline (Snode v e0) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt Hid //.
      specialize IHe with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe.
      apply IHe in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      rewrite Hcf //.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf.
      exact Hcf.
    - (* case ebinop *)  
    case e1; try by done.
    - (* add *)
    move => rs1 s1 te v Hcf Hwf.
    simpl.
    apply SV.conform_upd.
    rewrite /well_formed_fstmt_inline in Hwf.
    move : Hwf => /andP [Hwt Hid].
    simpl in Hwt.
    simpl in Hid.
    move : Hid => /andP [Hid2 Hid3].
    case H2:(type_of_fexpr e2 te) => [n0|n0|||].
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      simpl.
      rewrite size_addB_ext.
      assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt3 Hid3 //.
      specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe1.
      specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe2.
      generalize Hcf.
      apply IHe1 in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      rewrite -Hcf H2.
      move => Hcf0.
      apply IHe2 in Hcf0.
      apply SV.conform_mem with (v:=v) in Hcf0.
      rewrite TE.vsize_add_eq in Hcf0.
      rewrite SV.acc_upd_eq in Hcf0.
      rewrite -Hcf0 H3.
      simpl.
      rewrite addn1 //.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt3 Hid3 //.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf2.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      simpl.
      rewrite size_SadcB_ext.
      assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt3 Hid3 //.
      specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe1.
      specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe2.
      generalize Hcf.
      apply IHe1 in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      rewrite 2!size_sext -Hcf H2.
      move => Hcf0.
      apply IHe2 in Hcf0.
      apply SV.conform_mem with (v:=v) in Hcf0.
      rewrite TE.vsize_add_eq in Hcf0.
      rewrite SV.acc_upd_eq in Hcf0.
      rewrite -Hcf0 H3.
      simpl.
      rewrite subnKC.
      rewrite subnKC.
      rewrite maxnn //.
      rewrite leq_maxr //.
      rewrite leq_maxl //.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf3.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt2 Hid2 //.
      assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt2 Hid2 //.
      assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt3 Hid3 //.
      specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe1.
      specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
      simpl in IHe2.
      generalize Hcf.
      apply IHe1 in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      rewrite 2!size_sext -Hcf H2.
      move => Hcf0.
      apply IHe2 in Hcf0.
      apply SV.conform_mem with (v:=v) in Hcf0.
      rewrite TE.vsize_add_eq in Hcf0.
      rewrite SV.acc_upd_eq in Hcf0.
      rewrite -Hcf0 H3.
      simpl.
      rewrite subnKC.
      rewrite subnKC.
      reflexivity.
      rewrite leq_maxr //.
      rewrite leq_maxl //.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      exact Hwf3.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwt2 Hid2 //.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      exact Hcf. 
      - (* sub *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_subB_ext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf0 H3.
        simpl.
        rewrite addn1 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_SsbbB_ext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite 2!size_sext -Hcf H2.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf3.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite 2!size_sext -Hcf H2.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        reflexivity.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf3.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        exact Hcf. 
      - (* mul *)
        move => rs1 s1 te v Hcf Hwf.
        simpl.
        apply SV.conform_upd.
        rewrite /well_formed_fstmt_inline in Hwf.
        move : Hwf => /andP [Hwt Hid].
        simpl in Hwt.
        simpl in Hid.
        move : Hid => /andP [Hid2 Hid3].
        case H2:(type_of_fexpr e2 te) => [n0|n0|||].
          - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
          rewrite H2 H3 in Hwt.
          move : Hwt => /andP [Hwt2 Hwt3].
          simpl.
          rewrite size_full_mul.
          assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt2 Hid2 //.
          assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt3 Hid3 //.
          specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
          simpl in IHe1.
          specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
          simpl in IHe2.
          generalize Hcf.
          apply IHe1 in Hcf.
          apply SV.conform_mem with (v:=v) in Hcf.
          rewrite TE.vsize_add_eq in Hcf.
          rewrite SV.acc_upd_eq in Hcf.
          rewrite -Hcf H2.
          move => Hcf0.
          apply IHe2 in Hcf0.
          apply SV.conform_mem with (v:=v) in Hcf0.
          rewrite TE.vsize_add_eq in Hcf0.
          rewrite SV.acc_upd_eq in Hcf0.
          rewrite -Hcf0 H3.
          simpl.
          reflexivity.
          reflexivity.
          reflexivity.
          apply SV.Lemmas.mem_add_eq.
          apply TE.SE.eq_refl.
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt3 Hid3 //.
          reflexivity.
          reflexivity.
          apply SV.Lemmas.mem_add_eq.
          apply TE.SE.eq_refl.
          exact Hwf2.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          discriminate.
          - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          move : Hwt => /andP [Hwt2 Hwt3].
          simpl.
          rewrite size_Sfull_mul.
          assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt2 Hid2 //.
          assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt3 Hid3 //.
          specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
          simpl in IHe1.
          specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
          simpl in IHe2.
          generalize Hcf.
          apply IHe1 in Hcf.
          apply SV.conform_mem with (v:=v) in Hcf.
          rewrite TE.vsize_add_eq in Hcf.
          rewrite SV.acc_upd_eq in Hcf.
          move => Hcf0.
          apply IHe2 in Hcf0.
          apply SV.conform_mem with (v:=v) in Hcf0.
          rewrite TE.vsize_add_eq in Hcf0.
          rewrite SV.acc_upd_eq in Hcf0.
          rewrite -Hcf H2 -Hcf0 H3.
          simpl.
          reflexivity.
          reflexivity.
          reflexivity.
          apply SV.Lemmas.mem_add_eq.
          apply TE.SE.eq_refl.
          exact Hwf3.
          reflexivity.
          reflexivity.
          apply SV.Lemmas.mem_add_eq.
          apply TE.SE.eq_refl.
          rewrite /well_formed_fstmt_inline.
          simpl.
          rewrite Hwt2 Hid2 //.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 H3 in Hwt.
          discriminate.
          rewrite H2 in Hwt.
          discriminate.
          rewrite H2 in Hwt.
          discriminate.
          rewrite H2 in Hwt.
          discriminate.
        exact Hcf. 
      - (* div *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_udivB.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        simpl.
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_sext size_sdivB.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        simpl.
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf. 
      - (* rem *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_low //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_low //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf. 
      - (* cmp *)
      move => b rs1 s1 te v Hcf Hwf.
      case b.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt _].
      simpl in Hwt.
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        simpl.
        reflexivity.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* dshl *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_zext size_cat size_zeros.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        simpl.
        rewrite addnBA.
        rewrite (addnC (to_nat (no_mem_eval_fexpr e3 s1 te)) n0).
        rewrite addnACl -addnBA.
        rewrite -addnBAC.
        rewrite subnn add0n addnC //.
        rewrite -Hcf0 H3.
        simpl.
        reflexivity.
        rewrite leqnn //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite subn1 Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_sext size_cat size_zeros.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        simpl.
        rewrite addnBA.
        rewrite (addnC (to_nat (no_mem_eval_fexpr e3 s1 te)) n0).
        rewrite addnACl -addnBA.
        rewrite -addnBAC.
        rewrite subnn add0n addnC //.
        rewrite -Hcf0 H3.
        simpl.
        reflexivity.
        rewrite leqnn //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite subn1 Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* dshr *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_shrB.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        simpl.
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_sarB.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite -Hcf H2.
        simpl.
        reflexivity.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* and *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_andB 2!size_zext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_andB 2!size_sext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* or *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_orB 2!size_zext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_orB 2!size_sext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* xor *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_xorB 2!size_zext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_xorB 2!size_sext.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
      - (* cat *)
      move => rs1 s1 te v Hcf Hwf.
      simpl.
      apply SV.conform_upd.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_cat.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite addnC //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        simpl.
        rewrite size_cat.
        assert (Hwf2 : well_formed_fstmt_inline (Snode v e2) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        assert (Hwf3 : well_formed_fstmt_inline (Snode v e3) te s1 rs1).
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        specialize IHe1 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe1.
        specialize IHe2 with (rs1:=rs1) (s1:=s1) (te:=te) (v:=v).
        simpl in IHe2.
        generalize Hcf.
        apply IHe1 in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        move => Hcf0.
        apply IHe2 in Hcf0.
        apply SV.conform_mem with (v:=v) in Hcf0.
        rewrite TE.vsize_add_eq in Hcf0.
        rewrite SV.acc_upd_eq in Hcf0.
        rewrite -Hcf H2 -Hcf0 H3.
        simpl.
        rewrite addnC //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        exact Hwf2.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
        rewrite H2 in Hwt.
        discriminate.
      exact Hcf.
    - (* case emux *)
    move => rs1 s1 te v Hcf Hwf.
      apply SV.conform_upd.
      simpl.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hid => /andP [Hid2 Hid3].
      move : Hid2 => /andP [_ Hid2].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        move : Hwt2 => /andP [_ Hwt2].
        case (is_zero (no_mem_eval_fexpr e1 s1 te)).
        simpl.
        rewrite size_zext.
        apply IHe3 with (rs1:=rs1) (v:=v) in Hcf.
        simpl in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite H3 in Hcf.
        simpl in Hcf.
        rewrite -Hcf subnKC //.
        rewrite leq_maxr //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        simpl.
        rewrite size_zext.
        apply IHe2 with (rs1:=rs1) (v:=v) in Hcf.
        simpl in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite H2 in Hcf.
        simpl in Hcf.
        rewrite -Hcf subnKC //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        move : Hwt => /andP [Hwt2 Hwt3].
        move : Hwt2 => /andP [_ Hwt2].
        case (is_zero (no_mem_eval_fexpr e1 s1 te)).
        simpl.
        rewrite size_sext.
        apply IHe3 with (rs1:=rs1) (v:=v) in Hcf.
        simpl in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite H3 in Hcf.
        simpl in Hcf.
        rewrite -Hcf subnKC //.
        rewrite leq_maxr //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt3 Hid3 //.
        simpl.
        rewrite size_sext.
        apply IHe2 with (rs1:=rs1) (v:=v) in Hcf.
        simpl in Hcf.
        apply SV.conform_mem with (v:=v) in Hcf.
        rewrite TE.vsize_add_eq in Hcf.
        rewrite SV.acc_upd_eq in Hcf.
        rewrite H2 in Hcf.
        simpl in Hcf.
        rewrite -Hcf subnKC //.
        rewrite leq_maxl //.
        reflexivity.
        reflexivity.
        apply SV.Lemmas.mem_add_eq.
        apply TE.SE.eq_refl.
        rewrite /well_formed_fstmt_inline.
        simpl.
        rewrite Hwt2 Hid2 //.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
        rewrite H2 H3 in Hwt.
        discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      exact Hcf.
    - (* case evalidif *)
    move => rs1 s1 te v Hcf Hwf.
    apply SV.conform_upd.
    simpl.
      rewrite /well_formed_fstmt_inline in Hwf.
      move : Hwf => /andP [Hwt Hid].
      simpl in Hwt.
      simpl in Hid.
      move : Hwt => /andP [_ Hwf].
      move : Hid => /andP [_ Hid].
      apply IHe2 with (rs1:=rs1) (v:=v) in Hcf.
      simpl in Hcf.
      apply SV.conform_mem with (v:=v) in Hcf.
      rewrite TE.vsize_add_eq in Hcf.
      rewrite SV.acc_upd_eq in Hcf.
      exact Hcf.
      reflexivity.
      reflexivity.
      apply SV.Lemmas.mem_add_eq.
      apply TE.SE.eq_refl.
      rewrite /well_formed_fstmt_inline.
      simpl.
      rewrite Hwf Hid //.
      exact Hcf.
    - (* case ref *)
    move => rs1 s1 te v Hcf Hwf.
    rewrite /well_formed_fstmt_inline in Hwf.
    move : Hwf => /andP [Hwt Hid].
    simpl in Hwt.
    simpl in Hid.
    rewrite /is_defined in Hid.
    apply SV.conform_upd.
    simpl.
    apply SV.conform_mem with (v:=s) in Hcf.
    rewrite -Hcf.
    rewrite (TE.vtyp_vsize (eqP(eqxx (TE.vtyp s te))))//.
    exact Hid.
    exact Hcf.
  Qed.

  Lemma conform_eval_sfcnct_upd_env0_inline e : forall rs1 s1 te r ,
    SV.conform s1 te ->
    well_formed_fstmt_inline (Sfcnct r e) te s1 rs1 ->
    (SV.acc r rs1 == [::]) = true ->
    SV.conform (snd (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te).
  Proof.
  Admitted.

  Lemma conform_eval_sfcnct_upd_envr0_inline e : forall rs1 s1 te r ,
    SV.conform s1 te ->
    SV.conform rs1 te ->
    well_formed_fstmt_inline (Sfcnct r e) te s1 rs1 ->
    (SV.acc r rs1 == [::]) = false ->
    SV.conform (fst (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te) /\
    SV.conform (snd (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te).
  Proof.
  Admitted.

  Fixpoint well_formed_fstmts_inline sts te s rs := match sts with
    | [::] => true
    | hd :: tl => well_formed_fstmt_inline hd te s rs && 
                  well_formed_fstmts_inline tl (no_mem_upd_typenv_fstmt hd te) (snd (no_mem_eval_noninst_fstmt hd rs s (no_mem_upd_typenv_fstmt hd te))) 
                  (fst (no_mem_eval_noninst_fstmt hd rs s (no_mem_upd_typenv_fstmt hd te)))
  end.

  Lemma conform_eval_stmts_inline sts : forall rs s te,
    SV.conform s te ->
    SV.conform rs te ->
    well_formed_fstmts_inline sts te s rs ->
    SV.conform (fst (no_mem_eval_fstmts_inline sts rs s te)) (no_mem_upd_typenv_fstmts sts te) /\ SV.conform (snd (no_mem_eval_fstmts_inline sts rs s te)) (no_mem_upd_typenv_fstmts sts te).
  Proof.
    induction sts.
    - move => rs s te Hcf Hcfr Hwf.
    simpl.
    split.
    exact Hcfr.
    exact Hcf.
    - move => rs s te Hcf Hcfr Hwf.
    simpl in Hwf.
    move : Hwf => /andP [Hwf Hwfs].
    simpl.
    case Hhd : (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) => [rs0 s0].
    specialize IHsts with (rs:=rs0) (s:=s0) (te:=(no_mem_upd_typenv_fstmt a te)).
    apply IHsts.

    have ->: s0 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Hhd//.
    - case Hs : a => [||||||v e|||].
      (* sskip *)
      simpl.
      exact Hcf.
      (* swire *)
      apply conform_eval_swire_upd_env_inline.
      exact Hcf.
      rewrite -Hs.
      exact Hwf.
      (* sreg *)
      apply conform_eval_reg_upd_env_inline.
      exact Hcf.
      exact Hcfr.
      rewrite -Hs.
      exact Hwf.
      (* smem *)
      simpl.
      done.
      (* sinst *)
      rewrite Hs /well_formed_fstmt_inline /well_typed_fstmt_inline in Hwf.
      discriminate.
      (* snode *)
      apply conform_eval_node_upd_env_inline.
      exact Hcf.
      rewrite -Hs.
      exact Hwf.
      (* sfcnct *)
      case Hr : (SV.acc v rs == [::]).
      apply conform_eval_sfcnct_upd_env0_inline.
      exact Hcf.
      rewrite -Hs.
      exact Hwf.
      exact Hr.
      apply conform_eval_sfcnct_upd_envr0_inline.
      exact Hcf.
      exact Hcfr.
      rewrite -Hs.
      exact Hwf.
      exact Hr.
      (* sinvalid *)
      apply conform_eval_invalid_upd_env_inline.
      exact Hcf.
      rewrite -Hs.
      exact Hwf.
      (* swhen *)
      simpl.
      exact Hcf.
      (* sstop *)
      simpl.
      exact Hcf.

    have ->: rs0 = fst (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Hhd//.
    - case Hs : a => [||||||v e|||].
      (* sskip *)
      simpl.
      exact Hcfr.
      (* swire *)
      simpl.
      admit.
      (* sreg *)
      apply conform_eval_reg_upd_env_inline.
      exact Hcf.
      exact Hcfr.
      rewrite -Hs.
      exact Hwf.
      (* smem *)
      simpl.
      done.
      (* sinst *)
      admit.
      (* snode *)
      simpl.
      admit.
      (* sfcnct *)
      case Hr : (SV.acc v rs == [::]).
      simpl.
      case : (TE.vtyp v te) => [n0|n0|||].
      rewrite Hr.
      simpl.
      exact Hcfr.
      rewrite Hr.
      simpl.
      exact Hcfr.
      simpl.
      exact Hcfr.
      simpl.
      exact Hcfr.
      simpl.
      exact Hcfr.
      apply conform_eval_sfcnct_upd_envr0_inline.
      exact Hcf.
      exact Hcfr.
      rewrite -Hs.
      exact Hwf.
      exact Hr.
      (* sinvalid *)
      simpl.
      admit.
      (* swhen *)
      simpl.
      exact Hcfr.
      (* sstop *)
      simpl.
      exact Hcfr.
      have -> : s0 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Hhd //.
      have -> : rs0 = fst (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Hhd //.
      exact Hwfs.
  Admitted.

  (************************************************************)
  (* non_inline *)

  Definition well_typed_fstmt (st : fstmt) (te : TE.env) s rs finstoutl finstoutm ffmodsmap fterss finstin 
  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n : Prop :=
  match st with 
  | Sfcnct v (Eref r0) => if mylListIn r0 finstoutl
                          then 
                          match TE.find r0 finstoutm with
                          | Some (a4,a0) => match TE.find a4 ffmodsmap with
                                            | Some mst => match TE.find a0 fterss with
                                                          | Some (((te0,rs1),s1),_) => match TE.find a4 finstin with
                                                                                  | Some a2 => match TE.find a0 finstinmap with
                                                                                              | Some updfinstin => match TE.find a4 allfinstoutl with
                                                                                                          | Some finstoutl0 => match TE.find r0 finstoutmap with
                                                                                                                  | Some a3 => match TE.find a4 allfinstoutm with
                                                                                                                              | Some finstoutm0 => match TE.find a4 allfinstportmap with
                                                                                                                                          | Some (finstinmap0, finstoutmap0) => ((TE.vtyp v te) = (TE.vtyp a3 (no_mem_upd_typenv_fstmts (rev mst) te0))) /\
                                                                                                                                            TE.mem a3 (no_mem_upd_typenv_fstmts (rev mst) te0) /\
                                                                                                                                            (let ts := snd (fst (fold_left
                                                                                                                                            (fun '(y, tfterss) =>
                                                                                                                                             let
                                                                                                                                             '(trs, ts) := y in
                                                                                                                                              fun tempst : fstmt =>
                                                                                                                                              no_mem_eval_fstmt tempst trs ts (no_mem_upd_typenv_fstmts (rev mst) te0) finstoutl0 finstoutm0
                                                                                                                                                ffmodsmap tfterss finstin finstinmap0 finstoutmap0 allfinstoutl
                                                                                                                                                allfinstoutm allfinstportmap n.-1) (rev mst)
                                                                                                                                            (rs1, upd_inner s s1 a2 updfinstin, fterss))) in 
                                                                                                                                            SV.conform ts (no_mem_upd_typenv_fstmts (rev mst) te0)) /\ (well_typed_fstmt_inline st te s rs)
                                                                                                                                          | None => false
                                                                                                                                          end
                                                                                                                              | None => false
                                                                                                                              end
                                                                                                                  | None => false
                                                                                                                  end
                                                                                                          | None => false
                                                                                                          end
                                                                                              | None => false
                                                                                              end
                                                                                  | None => false
                                                                                  end
                                                          | None => false
                                                          end
                                            | None => false
                                            end
                          | None => false
                          end 
                          else well_typed_fstmt_inline st te s rs
  | Sinst inst => (SV.conform s (upd_typenv_fports (iports inst) te)) /\ well_typed_fstmt_inline st te s rs
  | _ => well_typed_fstmt_inline st te s rs
  end.

  (* well formed statement *)
  Definition well_formed_fstmt s te s1 rs1 finstoutl finstoutm ffmodsmap fterss finstin 
  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n
  := well_typed_fstmt s te s1 rs1 finstoutl finstoutm ffmodsmap fterss finstin 
  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n /\ is_defined_fstmt s te.

  Fixpoint well_formed_fstmts sts (te : TE.env) s rs finstoutl finstoutm ffmodsmap fterss finstin 
  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n : Prop := match sts with
    | [::] => true
    | hd :: tl => well_formed_fstmt hd te s rs finstoutl finstoutm ffmodsmap fterss finstin 
                  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n /\
                  well_formed_fstmts tl (no_mem_upd_typenv_fstmt hd te) (snd (fst (no_mem_eval_fstmt hd rs s (no_mem_upd_typenv_fstmt hd te) finstoutl 
                  finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n))) 
                  (fst (fst (no_mem_eval_fstmt hd rs s (no_mem_upd_typenv_fstmt hd te) finstoutl finstoutm ffmodsmap fterss finstin 
                  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n))) finstoutl finstoutm ffmodsmap fterss finstin 
                  finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n
  end.
(*
  Lemma conform_eval_sfcnct_upd_env0 e : forall rs1 s1 te r ,
    SV.conform s1 te ->
    well_formed_fstmt (Sfcnct r e) te s1 rs1 ->
    (SV.acc r rs1 == [::]) = true ->
    SV.conform (snd (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te).
  Proof.
    move => rs1 s1 te r.
    move => Hcf Hwf.
    rewrite /well_formed_fstmt in Hwf.
    move : Hwf => /andP [Hwt Hid].
    simpl in Hwt.
    move : Hid => /andP [Hid Hide].
    rewrite /is_defined in Hid.
    assert (Hte : TE.Equal (TE.add r (TE.vtyp r te) te) te).
    rewrite SV.Lemmas.add_same.
    apply SV.Lemmas.Equal_refl.
    case H: (TE.find r te).
    rewrite (TE.find_some_vtyp H) //.
    apply SV.Lemmas.find_none_not_mem in H.
    rewrite Hid in H.
    discriminate.

    case Ht : (TE.vtyp r te) => [n|n|||].
    (* uint not reg *)
    rewrite Ht in Hwt.
    move : Hwt => /andP [Hwt Hsf].
    move : rs1 s1 Hcf.
    rewrite /no_mem_upd_typenv_fstmt.
    induction e.
      (* cosnt *)
    - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      move : Hwt => /eqP Hwt.
      rewrite Hwt subnn zext0 sext0.
      simpl in Hsf.
      rewrite Hwt in Hsf.
      assert (Htcf : SV.conform
      (SV.upd r
         (zext (n - size match f with
                         | Fuint _ | _ => b
                         end) match f with
                              | Fuint _ | _ => b
                              end) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext subnKC.
      simpl.
      reflexivity.
      case f;done.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* cast *)
    - case Hu:u; try by done.
      simpl in Hide.
      simpl in Hwt.
      (* uint *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hr.
      (* sint *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hr.
      (* clk *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* rst *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    - (* unop *)
      move : Hide Hwt Hsf.
      case :e; try by done.
      (* upad *)
      - move => pn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hn:(pn < size (no_mem_eval_fexpr e0 s1 te)).
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
              (SV.upd r
                (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
                s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
          (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
          s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
        (SV.upd r
        (zext (n - size (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
           (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite size_zext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
        (zext (n - size (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
           (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite size_sext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
      (* shl *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (zeros sn ++ no_mem_eval_fexpr e0 s1 te))
         (zeros sn ++ no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext size_cat size_zeros subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* shr *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hsn:(sn < size (no_mem_eval_fexpr e0 s1 te)).
      assert (Htcf : SV.conform
      (SV.upd r
     (zext
        (n -
         size
           (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
              (no_mem_eval_fexpr e0 s1 te)))
        (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
           (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext size_high subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
     (zext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (zext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* cvt *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (sext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
     s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* neg *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (-# zext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# zext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_zext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (-# sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# sext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* not *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
     (zext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (zext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* and *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr andb b1 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* or *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr orb b0 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* xor *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr xorb b0 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* extr *)
    - move => n0 n1 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - size (extract n0 n1 (no_mem_eval_fexpr e0 s1 te)))
      (extract n0 n1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_extract.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* head *)
    - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - size (high n0 (no_mem_eval_fexpr e0 s1 te)))
      (high n0 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_high.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* tail *)
    - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext
      (n -
       size
         (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
            (no_mem_eval_fexpr e0 s1 te)))
      (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
         (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_low typeof_eval_fexpr.
      exact Hsf.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    - (* binop *)
    move : Hide Hwt Hsf.
      case :e1; try by done.
      (* add *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
              (n -
               size
                 (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                 (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_addB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
         size
           (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SadcB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* sub *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
              (n -
               size
                 (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                 (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_subB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
         size
           (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SsbbB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* mul *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
         size
           (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_full_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
         size
           (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_Sfull_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* div *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
         size
           (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_udivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te)))
     (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sext size_sdivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* rem *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te)))
     (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
           (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* cmp *)
      move => b.
      case : b.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* dshl *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_zext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        rewrite H2 H1 in Hsf.
        simpl in Hsf.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
           apply SV.conform_upd.
           rewrite Ht size_zext subnKC.
           simpl.
           reflexivity.
           simpl.
           rewrite size_sext size_cat size_zeros.
           rewrite subn1 addnACl subnK.
           rewrite H2 H1 in Hsf.
           simpl in Hsf.
           rewrite typeof_eval_fexpr.
           rewrite typeof_eval_fexpr.
           rewrite H1 H2.
           simpl.
           rewrite -subn1 addnBA //.
           rewrite -Nats.expn_pow Nats.expn2_gt0 //.
           exact Hcf.
           move : Hwt => /andP [Hwt1 Hwt2].
           rewrite /well_formed_fexpr Hwt2 Hide2 //.
           exact Hcf.
           move : Hwt => /andP [Hwt1 Hwt2].
           rewrite /well_formed_fexpr Hwt1 Hide1 //.
           rewrite -Nats.expn_pow.
           apply ltnSE.
           rewrite Nat.succ_pred.
           rewrite to_nat_bounded //.
           rewrite Nats.expn_pow.
           apply Nat.pow_nonzero.
           lia.
           exact Hcf.
           move : Hte Htcf.
           apply SV.conform_equal.
           rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H1 H2 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
      (* shr *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_shrB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sarB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* and *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* or *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* xor *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* cat *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
    - (* mux *)
    move => rs1 s1 Hcf Hr.
    simpl.
    rewrite Hr Ht.
    simpl.
    simpl in Hwt.
    simpl in Hsf.
    simpl in Hide.
    move : Hide => /andP [Hid2 Hid3].
    move : Hid2 => /andP [Hid1 Hid2].
    case H2:(type_of_fexpr e2 te) => [n0|n0|||].
    - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
         (zext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
         (zext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
         (sext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
         (sext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
    - (* validif *)
      move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid1 Hid2].
      move : Hwt => /andP [Hwt1 Hwt2].
      apply IHe2 with (s1:=s1) (rs1:=rs1) in Hcf.
      simpl in Hcf.
      rewrite Ht Hr in Hcf.
      simpl in Hcf.
      exact Hcf.
      exact Hid2.
      exact Hwt2.
      exact Hsf.
      exact Hr.
    - (* case ref *)
    move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform (SV.upd r (zext (n - size (SV.acc s s1)) (SV.acc s s1)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext subnKC.
      simpl.
      reflexivity.
      rewrite -(typeof_eval_fexpr Hcf) in Hsf.
      simpl in Hsf.
      exact Hsf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* sint *)
    rewrite Ht in Hwt.
    move : Hwt => /andP [Hwt Hsf].
    move : rs1 s1 Hcf.
    rewrite /no_mem_upd_typenv_fstmt.
    induction e.
      (* cosnt *)
    - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      move : Hwt => /eqP Hwt.
      rewrite Hwt subnn zext0 sext0.
      simpl in Hsf.
      rewrite Hwt in Hsf.
      assert (Htcf : SV.conform
      (SV.upd r
         (sext (n - size match f with
                         | Fuint _ | _ => b
                         end) match f with
                              | Fuint _ | _ => b
                              end) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext subnKC.
      simpl.
      reflexivity.
      case f;done.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* cast *)
    - case Hu:u; try by done.
      simpl in Hide.
      simpl in Hwt.
      (* uint *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hr.
      (* sint *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hr.
      (* clk *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* rst *)
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      - move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) s1)
         (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    - (* unop *)
      move : Hide Hwt Hsf.
      case :e; try by done.
      (* upad *)
      - move => pn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hn:(pn < size (no_mem_eval_fexpr e0 s1 te)).
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
              (SV.upd r
                (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
                s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
          (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
          s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
        (SV.upd r
        (sext (n - size (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
           (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite size_zext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
        (sext (n - size (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
           (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite size_sext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
      (* shl *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (zeros sn ++ no_mem_eval_fexpr e0 s1 te))
         (zeros sn ++ no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext size_cat size_zeros subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      (* shr *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hsn:(sn < size (no_mem_eval_fexpr e0 s1 te)).
      assert (Htcf : SV.conform
      (SV.upd r
     (sext
        (n -
         size
           (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
              (no_mem_eval_fexpr e0 s1 te)))
        (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
           (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext size_high subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
     (sext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (sext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* cvt *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (sext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
     s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* neg *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (-# zext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# zext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_zext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (-# sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# sext 1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* not *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
     (sext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
     (sext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
    (* and *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr andb b1 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* or *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr orb b0 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* xor *)
    - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr xorb b0 (no_mem_eval_fexpr e0 s1 te)]) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* extr *)
    - move => n0 n1 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - size (extract n0 n1 (no_mem_eval_fexpr e0 s1 te)))
      (extract n0 n1 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_extract.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* head *)
    - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - size (high n0 (no_mem_eval_fexpr e0 s1 te)))
      (high n0 (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_high.
      exact Hsf.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    (* tail *)
    - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext
      (n -
       size
         (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
            (no_mem_eval_fexpr e0 s1 te)))
      (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
         (no_mem_eval_fexpr e0 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_low typeof_eval_fexpr.
      exact Hsf.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
    - (* binop *)
    move : Hide Hwt Hsf.
      case :e1; try by done.
      (* add *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
              (n -
               size
                 (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                 (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_addB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
         size
           (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SadcB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* sub *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
              (n -
               size
                 (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                 (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_subB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        (*exact Hsf.*)
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
         size
           (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SsbbB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* mul *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
         size
           (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_full_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
         size
           (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_Sfull_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* div *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
         size
           (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_udivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te)))
     (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sext size_sdivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* rem *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te)))
     (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
           (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* cmp *)
      move => b.
      case : b.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1) 
           (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* dshl *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_zext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        rewrite H2 H1 in Hsf.
        simpl in Hsf.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
           apply SV.conform_upd.
           rewrite Ht size_sext subnKC.
           simpl.
           reflexivity.
           simpl.
           rewrite size_sext size_cat size_zeros.
           rewrite subn1 addnACl subnK.
           rewrite H2 H1 in Hsf.
           simpl in Hsf.
           rewrite typeof_eval_fexpr.
           rewrite typeof_eval_fexpr.
           rewrite H1 H2.
           simpl.
           rewrite -subn1 addnBA //.
           rewrite -Nats.expn_pow Nats.expn2_gt0 //.
           exact Hcf.
           move : Hwt => /andP [Hwt1 Hwt2].
           rewrite /well_formed_fexpr Hwt2 Hide2 //.
           exact Hcf.
           move : Hwt => /andP [Hwt1 Hwt2].
           rewrite /well_formed_fexpr Hwt1 Hide1 //.
           rewrite -Nats.expn_pow.
           apply ltnSE.
           rewrite Nat.succ_pred.
           rewrite to_nat_bounded //.
           rewrite Nats.expn_pow.
           apply Nat.pow_nonzero.
           lia.
           exact Hcf.
           move : Hte Htcf.
           apply SV.conform_equal.
           rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H1 H2 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
      (* shr *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_shrB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sarB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* and *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* or *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* xor *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      (* cat *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
           (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
    - (* mux *)
    move => rs1 s1 Hcf Hr.
    simpl.
    rewrite Hr Ht.
    simpl.
    simpl in Hwt.
    simpl in Hsf.
    simpl in Hide.
    move : Hide => /andP [Hid2 Hid3].
    move : Hid2 => /andP [Hid1 Hid2].
    case H2:(type_of_fexpr e2 te) => [n0|n0|||].
    - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
         (zext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
         (zext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
         (sext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
         (sext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
    - (* validif *)
      move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid1 Hid2].
      move : Hwt => /andP [Hwt1 Hwt2].
      apply IHe2 with (s1:=s1) (rs1:=rs1) in Hcf.
      simpl in Hcf.
      rewrite Ht Hr in Hcf.
      simpl in Hcf.
      exact Hcf.
      exact Hid2.
      exact Hwt2.
      exact Hsf.
      exact Hr.
    - (* case ref *)
    move => rs1 s1 Hcf Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      assert (Htcf : SV.conform (SV.upd r (sext (n - size (SV.acc s s1)) (SV.acc s s1)) s1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext subnKC.
      simpl.
      reflexivity.
      rewrite -(typeof_eval_fexpr Hcf) in Hsf.
      simpl in Hsf.
      exact Hsf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      move : Hte Htcf.
      apply SV.conform_equal.

    rewrite Ht in Hwt.
    discriminate.
    rewrite Ht in Hwt.
    discriminate.
    rewrite Ht in Hwt.
    discriminate.
  Qed.

  Lemma conform_eval_sfcnct_upd_envr0 e : forall rs1 s1 te r ,
    SV.conform s1 te ->
    SV.conform rs1 te ->
    well_formed_fstmt (Sfcnct r e) te s1 rs1 ->
    (SV.acc r rs1 == [::]) = false ->
    SV.conform (fst (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te) /\
    SV.conform (snd (no_mem_eval_noninst_fstmt (Sfcnct r e) rs1 s1 te)) (no_mem_upd_typenv_fstmt (Sfcnct r e) te).
  Proof.
    move => rs1 s1 te r.
    move => Hcf Hcfr Hwf.
    rewrite /well_formed_fstmt in Hwf.
    move : Hwf => /andP [Hwt Hid].
    simpl in Hwt.
    move : Hid => /andP [Hid Hide].
    rewrite /is_defined in Hid.
    assert (Hte : TE.Equal (TE.add r (TE.vtyp r te) te) te).
    rewrite SV.Lemmas.add_same.
    apply SV.Lemmas.Equal_refl.
    case H: (TE.find r te).
    rewrite (TE.find_some_vtyp H) //.
    apply SV.Lemmas.find_none_not_mem in H.
    rewrite Hid in H.
    discriminate.

    case Ht : (TE.vtyp r te) => [n|n|||].
    (* uint not reg *)
    rewrite Ht in Hwt.
    move : Hwt => /andP [Hwt Hsf].
    move : rs1 s1 Hcf Hcfr.
    rewrite /no_mem_upd_typenv_fstmt.
    induction e.
    (* cosnt *)
    - rewrite /upd_typenv_fstmt.
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hwt.
      move : Hwt => /eqP Hwt.
      rewrite Hwt subnn zext0 sext0.
      simpl in Hsf.
      rewrite Hwt in Hsf.
      assert (Htcf : SV.conform
        (SV.upd r
          (zext (n - size match f with
                          | Fuint _ | _ => b
                          end) match f with
                                | Fuint _ | _ => b
                                end) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext subnKC.
      simpl.
      reflexivity.
      case f;done.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
    exact Hcf.

    (* cast *)
    - case Hu:u; try by done.
      simpl in Hide.
      simpl in Hwt.
      (* uint *) 
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hcfr.
      exact Hr.
      (* sint *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hcfr.
      exact Hr.
      (* clk *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* rst *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - (* unop *)
      move : Hide Hwt Hsf.
      case :e; try by done.
      (* upad *)
      - move => pn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hn:(pn < size (no_mem_eval_fexpr e0 s1 te)).
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
              (SV.upd r
                (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
                rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
          (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
          rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
        (SV.upd r
        (zext (n - size (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
          (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite size_zext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
        (zext (n - size (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
          (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        rewrite size_sext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
      exact Hcf.
      (* shl *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (zeros sn ++ no_mem_eval_fexpr e0 s1 te))
        (zeros sn ++ no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext size_cat size_zeros subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* shr *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hsn:(sn < size (no_mem_eval_fexpr e0 s1 te)).
      assert (Htcf : SV.conform
      (SV.upd r
      (zext
        (n -
        size
          (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
              (no_mem_eval_fexpr e0 s1 te)))
        (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
          (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext size_high subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* cvt *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (sext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
      rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* neg *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (-# zext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# zext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_zext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (-# sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# sext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* not *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (zext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* and *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr andb b1 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* or *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr orb b0 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* xor *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - 1) [:: foldr xorb b0 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* extr *)
      - move => n0 n1 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - size (extract n0 n1 (no_mem_eval_fexpr e0 s1 te)))
      (extract n0 n1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_extract.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* head *)
      - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext (n - size (high n0 (no_mem_eval_fexpr e0 s1 te)))
      (high n0 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_high.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* tail *)
      - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (zext
      (n -
      size
        (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
            (no_mem_eval_fexpr e0 s1 te)))
      (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
        (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_zext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_low typeof_eval_fexpr.
      exact Hsf.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - (* binop *)
      move : Hide Hwt Hsf.
      case :e1; try by done.
      (* add *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
              (n -
              size
                (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_addB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SadcB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* sub *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
              (n -
              size
                (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_subB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SsbbB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* mul *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_full_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_Sfull_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* div *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_udivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te)))
      (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sext size_sdivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
      exact Hcf.
      (* rem *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te)))
      (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
          (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* cmp *)
      move => b.
      case : b.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* dshl *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_zext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        rewrite H2 H1 in Hsf.
        simpl in Hsf.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
          apply SV.conform_upd.
          rewrite Ht size_zext subnKC.
          simpl.
          reflexivity.
          simpl.
          rewrite size_sext size_cat size_zeros.
          rewrite subn1 addnACl subnK.
          rewrite H2 H1 in Hsf.
          simpl in Hsf.
          rewrite typeof_eval_fexpr.
          rewrite typeof_eval_fexpr.
          rewrite H1 H2.
          simpl.
          rewrite -subn1 addnBA //.
          rewrite -Nats.expn_pow Nats.expn2_gt0 //.
          exact Hcf.
          move : Hwt => /andP [Hwt1 Hwt2].
          rewrite /well_formed_fexpr Hwt2 Hide2 //.
          exact Hcf.
          move : Hwt => /andP [Hwt1 Hwt2].
          rewrite /well_formed_fexpr Hwt1 Hide1 //.
          rewrite -Nats.expn_pow.
          apply ltnSE.
          rewrite Nat.succ_pred.
          rewrite to_nat_bounded //.
          rewrite Nats.expn_pow.
          apply Nat.pow_nonzero.
          lia.
          exact Hcfr.
          move : Hte Htcf.
          apply SV.conform_equal.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H1 H2 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          exact Hcf.
      (* shr *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_shrB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sarB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* and *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* or *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* xor *) 
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* cat *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (zext
        (n -
        size
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_zext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      - (* mux *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid2 Hid3].
      move : Hid2 => /andP [Hid1 Hid2].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
        (zext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
        (zext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
        (sext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (zext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
        (sext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      exact Hcf.
      - (* validif *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid1 Hid2].
      move : Hwt => /andP [Hwt1 Hwt2].
      apply IHe2 with (s1:=s1) (rs1:=rs1) in Hcf.
      simpl in Hcf.
      rewrite Ht Hr in Hcf.
      simpl in Hcf.
      exact Hcf.
      exact Hid2.
      exact Hwt2.
      exact Hsf.
      exact Hcfr.
      exact Hr.
      - (* case ref *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform (SV.upd r (zext (n - size (SV.acc s s1)) (SV.acc s s1)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_zext subnKC.
      simpl.
      reflexivity.
      rewrite -(typeof_eval_fexpr Hcf) in Hsf.
      simpl in Hsf.
      exact Hsf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* sint *)
      rewrite Ht in Hwt.
      move : Hwt => /andP [Hwt Hsf].
      move : rs1 s1 Hcf Hcfr.
      rewrite /no_mem_upd_typenv_fstmt.
      induction e.
      (* cosnt *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hwt.
      move : Hwt => /eqP Hwt.
      rewrite Hwt subnn zext0 sext0.
      simpl in Hsf.
      rewrite Hwt in Hsf.
      assert (Htcf : SV.conform
      (SV.upd r
        (sext (n - size match f with
                        | Fuint _ | _ => b
                        end) match f with
                              | Fuint _ | _ => b
                              end) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext subnKC.
      simpl.
      reflexivity.
      case f;done.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* cast *)
      - case Hu:u; try by done.
      simpl in Hide.
      simpl in Hwt.
      (* uint *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hcfr.
      exact Hr.
      (* sint *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      specialize IHe with (rs1:=rs1) (s1:=s1).
      simpl in IHe.
      apply IHe in Hide.
      rewrite Ht Hr in Hide.
      simpl in Hide.
      exact Hide.
      exact Hwt.
      exact Hsf.
      exact Hcf.
      exact Hcfr.
      exact Hr.
      (* clk *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* rst *)
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - 1) [:: lsb (no_mem_eval_fexpr e s1 te)]) rs1)
        (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext.
      simpl.
      rewrite subnKC.
      rewrite Ht //.
      simpl in Hsf.
      rewrite Hu in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - (* unop *)
      move : Hide Hwt Hsf.
      case :e; try by done.
      (* upad *)
      - move => pn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hn:(pn < size (no_mem_eval_fexpr e0 s1 te)).
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
              (SV.upd r
                (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
                rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
          (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
          rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn in Hsf.
        rewrite typeof_eval_fexpr.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
        - assert (Htcf : SV.conform
        (SV.upd r
        (sext (n - size (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
          (zext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite size_zext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - assert (Htcf : SV.conform
        (SV.upd r
        (sext (n - size (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te)))
          (sext (pn - n0) (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        rewrite size_sext typeof_eval_fexpr.
        rewrite Htyp.
        rewrite subnKC //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Hn Htyp in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        rewrite typeof_eval_fexpr in Hn.
        rewrite Htyp in Hn.
        apply contraFleq with (b:=(pn < sizeof_fgtyp (Fuint n0))).
        trivial.
        exact Hn.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcf.
        rewrite Htyp in Hwt.
        rewrite /well_formed_fexpr Hwt Hide //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        - rewrite Htyp in Hwt.
        discriminate.
        exact Hcf.
      (* shl *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (zeros sn ++ no_mem_eval_fexpr e0 s1 te))
        (zeros sn ++ no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext size_cat size_zeros subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      rewrite addnC //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* shr *)
      - move => sn Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Hsn:(sn < size (no_mem_eval_fexpr e0 s1 te)).
      assert (Htcf : SV.conform
      (SV.upd r
      (sext
        (n -
        size
          (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
              (no_mem_eval_fexpr e0 s1 te)))
        (high (size (no_mem_eval_fexpr e0 s1 te) - sn)
          (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext size_high subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      simpl.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size [:: msb (no_mem_eval_fexpr e0 s1 te)])
        [:: msb (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr in Hsn.
      rewrite Htyp in Hsn.
      simpl in Hsn.
      rewrite Htyp Hsn in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* cvt *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (sext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl in Hsf.
      simpl.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (no_mem_eval_fexpr e0 s1 te)) (no_mem_eval_fexpr e0 s1 te))
      rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* neg *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (-# zext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# zext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_zext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (-# sext 1 (no_mem_eval_fexpr e0 s1 te)))
        (-# sext 1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_negB size_sext typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* not *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      case Htyp:(type_of_fexpr e0 te) => [n0|n0|||].
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      assert (Htcf : SV.conform
      (SV.upd r
      (sext (n - size (~~# no_mem_eval_fexpr e0 s1 te))
        (~~# no_mem_eval_fexpr e0 s1 te)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_invB typeof_eval_fexpr.
      rewrite Htyp.
      rewrite Htyp in Hsf.
      simpl.
      simpl in Hsf.
      exact Hsf.
      exact Hcf.
      rewrite Htyp in Hwt.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      rewrite Htyp in Hwt.
      discriminate.
      exact Hcf.
      (* and *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr andb b1 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* or *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr orb b0 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* xor *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - 1) [:: foldr xorb b0 (no_mem_eval_fexpr e0 s1 te)]) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      simpl.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* extr *)
      - move => n0 n1 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - size (extract n0 n1 (no_mem_eval_fexpr e0 s1 te)))
      (extract n0 n1 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_extract.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* head *)
      - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext (n - size (high n0 (no_mem_eval_fexpr e0 s1 te)))
      (high n0 (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_high.
      exact Hsf.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      (* tail *)
      - move => n0 Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      assert (Htcf : SV.conform
      (SV.upd r (sext
      (n -
      size
        (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
            (no_mem_eval_fexpr e0 s1 te)))
      (low (size (no_mem_eval_fexpr e0 s1 te) - n0)
        (no_mem_eval_fexpr e0 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite size_sext subnKC.
      rewrite Ht.
      simpl.
      reflexivity.
      rewrite size_low typeof_eval_fexpr.
      exact Hsf.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.
      - (* binop *)
      move : Hide Hwt Hsf.
      case :e1; try by done.
      (* add *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
              (n -
              size
                (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Badd (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_addB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Badd (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SadcB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* sub *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
              (n -
              size
                (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                    (no_mem_eval_fexpr e3 s1 te)))
              (ebinop_op Bsub (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
                (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_subB_ext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        apply ltnSE.
        apply /ltP.
        apply Nat.lt_succ_r.
        apply Nats.leq_le in Hsf.
        rewrite -addn1 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bsub (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_SsbbB_ext 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC //.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* mul *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_full_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bmul (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_Sfull_mul typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H2 H1 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* div *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdiv (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_udivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te)))
      (ebinop_op Bdiv (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sext size_sdivB typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* rem *)
      - move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te)))
      (ebinop_op Brem (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
        (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
          (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Brem (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_low.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* cmp *)
      move => b.
      case : b.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Blt) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bleq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgt) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bgeq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Beq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
      discriminate.
      exact Hcf.
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fuint n0) (Fuint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1)
              (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op (Bcomp Bneq) (Fsint n0) (Fsint n1) 
          (no_mem_eval_fexpr e2 s1 te) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        exact Hsf.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* dshl *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_zext size_cat size_zeros.
        rewrite subn1 addnACl subnK.
        rewrite H2 H1 in Hsf.
        simpl in Hsf.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite -subn1 addnBA //.
        rewrite -Nats.expn_pow Nats.expn2_gt0 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        rewrite -Nats.expn_pow.
        apply ltnSE.
        rewrite Nat.succ_pred.
        rewrite to_nat_bounded //.
        rewrite Nats.expn_pow.
        apply Nat.pow_nonzero.
        lia.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshl (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
          apply SV.conform_upd.
          rewrite Ht size_sext subnKC.
          simpl.
          reflexivity.
          simpl.
          rewrite size_sext size_cat size_zeros.
          rewrite subn1 addnACl subnK.
          rewrite H2 H1 in Hsf.
          simpl in Hsf.
          rewrite typeof_eval_fexpr.
          rewrite typeof_eval_fexpr.
          rewrite H1 H2.
          simpl.
          rewrite -subn1 addnBA //.
          rewrite -Nats.expn_pow Nats.expn2_gt0 //.
          exact Hcf.
          move : Hwt => /andP [Hwt1 Hwt2].
          rewrite /well_formed_fexpr Hwt2 Hide2 //.
          exact Hcf.
          move : Hwt => /andP [Hwt1 Hwt2].
          rewrite /well_formed_fexpr Hwt1 Hide1 //.
          rewrite -Nats.expn_pow.
          apply ltnSE.
          rewrite Nat.succ_pred.
          rewrite to_nat_bounded //.
          rewrite Nats.expn_pow.
          apply Nat.pow_nonzero.
          lia.
          exact Hcfr.
          move : Hte Htcf.
          apply SV.conform_equal.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H2 H1 in Hwt.
          discriminate.
          rewrite H1 H2 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          rewrite H1 in Hwt.
          discriminate.
          exact Hcf.
      (* shr *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_shrB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bdshr (Fsint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_sarB.
        rewrite typeof_eval_fexpr.
        rewrite H1.
        simpl.
        rewrite H1 in Hsf.
        simpl in Hsf.
        exact Hsf.
        exact Hcf.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* and *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Band (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_andB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* or *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_orB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* xor *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_zext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bxor (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_xorB.
        rewrite 2!size_sext typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite subnKC.
        rewrite subnKC.
        rewrite maxnn.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        exact Hsf.
        rewrite leq_maxr //.
        rewrite leq_maxl //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      (* cat *)
      move => Hide Hwt Hsf rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hsf.
      simpl in Hwt.
      simpl in Hide.
      move : Hide => /andP [Hide1 Hide2].
      case H1:(type_of_fexpr e2 te) => [n0|n0|||].
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fuint n0) (Fuint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        case H2:(type_of_fexpr e3 te) => [n1|n1|||].
        rewrite H2 H1 in Hwt.
        discriminate.
        - assert (Htcf : SV.conform
              (SV.upd r
              (sext
        (n -
        size
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
              (no_mem_eval_fexpr e3 s1 te)))
        (ebinop_op Bcat (Fsint n0) (Fsint n1) (no_mem_eval_fexpr e2 s1 te)
          (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
        apply SV.conform_upd.
        rewrite Ht size_sext subnKC.
        simpl.
        reflexivity.
        simpl.
        rewrite size_cat.
        rewrite typeof_eval_fexpr.
        rewrite typeof_eval_fexpr.
        rewrite H1 H2.
        simpl.
        rewrite H1 H2 in Hsf.
        simpl in Hsf.
        rewrite addnC //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt1 Hide1 //.
        exact Hcf.
        rewrite H1 H2 in Hwt.
        move : Hwt => /andP [Hwt1 Hwt2].
        rewrite /well_formed_fexpr Hwt2 Hide2 //.
        exact Hcfr.
        move : Hte Htcf.
        apply SV.conform_equal.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H2 H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        rewrite H1 in Hwt.
        discriminate.
        exact Hcf.
      - (* mux *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid2 Hid3].
      move : Hid2 => /andP [Hid1 Hid2].
      case H2:(type_of_fexpr e2 te) => [n0|n0|||].
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
        (zext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_zext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
        (zext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_zext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      - case H3:(type_of_fexpr e3 te) => [n1|n1|||].
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      move : Hwt => /andP [Hwt2 Hwt3].
      move : Hwt2 => /andP [_ Hwt2].
      case (is_zero (no_mem_eval_fexpr e1 s1 te)).
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e3 s1 te) + (maxn n0 n1 - n1)))
        (sext (maxn n0 n1 - n1) (no_mem_eval_fexpr e3 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H3 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxr.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt3 Hid3 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      simpl.
      rewrite size_sext.
      rewrite H2 H3 in Hsf.
      simpl in Hsf.
      assert (Htcf : SV.conform (SV.upd r
      (sext (n - (size (no_mem_eval_fexpr e2 s1 te) + (maxn n0 n1 - n0)))
        (sext (maxn n0 n1 - n0) (no_mem_eval_fexpr e2 s1 te))) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext size_sext subnKC.
      simpl.
      reflexivity.
      rewrite typeof_eval_fexpr.
      rewrite H2 subnKC.
      exact Hsf.
      simpl.
      apply leq_maxl.
      exact Hcf.
      rewrite /well_formed_fexpr Hwt2 Hid2 //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 H3 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      rewrite H2 in Hwt.
      discriminate.
      exact Hcf.
      - (* validif *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      simpl in Hwt.
      simpl in Hsf.
      simpl in Hide.
      move : Hide => /andP [Hid1 Hid2].
      move : Hwt => /andP [Hwt1 Hwt2].
      apply IHe2 with (s1:=s1) (rs1:=rs1) in Hcf.
      simpl in Hcf.
      rewrite Ht Hr in Hcf.
      simpl in Hcf.
      exact Hcf.
      exact Hid2.
      exact Hwt2.
      exact Hsf.
      exact Hcfr.
      exact Hr.
      - (* case ref *)
      move => rs1 s1 Hcf Hcfr Hr.
      simpl.
      rewrite Hr Ht.
      simpl.
      split.
      assert (Htcf : SV.conform (SV.upd r (sext (n - size (SV.acc s s1)) (SV.acc s s1)) rs1) (TE.add r (TE.vtyp r te) te)).
      apply SV.conform_upd.
      rewrite Ht size_sext subnKC.
      simpl.
      reflexivity.
      rewrite -(typeof_eval_fexpr Hcf) in Hsf.
      simpl in Hsf.
      exact Hsf.
      rewrite /well_formed_fexpr Hwt Hide //.
      exact Hcfr.
      move : Hte Htcf.
      apply SV.conform_equal.
      exact Hcf.

      rewrite Ht in Hwt.
      discriminate.
      rewrite Ht in Hwt.
      discriminate.
      rewrite Ht in Hwt.
      discriminate.
  Qed.

  Lemma conform_updinner : forall a2 s s0 te te0 finstinmap,
    SV.conform s te ->
    SV.conform s0 te0 ->
    (forall a, match TE.find a finstinmap with
                          | Some a0 => TE.mem a0 te /\ TE.mem a te0 /\ TE.vtyp a te0 = TE.vtyp a0 te
                          | None => false
    end) ->
    SV.conform (upd_inner s s0 a2 finstinmap) te0.
  Proof.
    induction a2.
    - simpl.
      trivial.
    - move => s s0 te te0 finstinmap Hcf Hcf0 Ht.
      simpl.
      case Hfind : (TE.find a finstinmap) =>[a0|].
      generalize Ht.
      specialize Ht with (a:=a).
      (*rewrite in_cons eq_refl orb_true_l in Ht.*)
      rewrite Hfind in Ht.
      (*move:(Ht (eqxx true)).
      clear Ht.*)
      move => Ht0.
      move : Ht => [Hmem Ht].
      move : Ht => [Hmem0 Ht].
      assert (Hte : TE.Equal (TE.add a (TE.vtyp a0 te) te0) te0).
      rewrite -Ht.
      rewrite SV.Lemmas.add_same.
      apply SV.Lemmas.Equal_refl.
      case H: (TE.find a te0).
      rewrite (TE.find_some_vtyp H) //.
      apply SV.Lemmas.find_none_not_mem in H.
      rewrite H in Hmem0.
      discriminate.
      assert (Hupd0 : SV.conform (SV.upd a (SV.acc a0 s) s0) (TE.add a (TE.vtyp a0 te) te0)).
      apply SV.conform_upd.
      rewrite -(SV.conform_mem Hcf) //.
      symmetry.
      apply TE.vtyp_vsize.
      reflexivity.
      exact Hcf0.
      assert (Hupd : SV.conform (SV.upd a (SV.acc a0 s) s0) te0).
      move : Hte Hupd0.
      apply SV.conform_equal.
      specialize IHa2 with (s:=s) (s0:=(SV.upd a (SV.acc a0 s) s0)) (te:=te) (te0:=te0) (finstinmap:=finstinmap).
      apply IHa2.
      exact Hcf.
      exact Hupd.
      exact Ht0.
      apply IHa2 with (te:=te).
      exact Hcf.
      exact Hcf0.
      exact Ht.
  Qed.
*)
  Lemma conform_eval_stmt : forall a rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
  allfinstoutl allfinstoutm allfinstportmap n,
    SV.conform s te ->
    SV.conform rs te ->
    well_formed_fstmt a te s rs finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap n ->
    SV.conform (snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te))) (no_mem_upd_typenv_fstmt a te) /\
    SV.conform (fst (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te))) (no_mem_upd_typenv_fstmt a te).
  Proof.
    move => a rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap n.
    move => Hcf Hcfr Hwf.
    split.
    - case Hs : a => [||||||v e|||].
      (* sskip *)
      simpl.
      done.
      (* swire *)
      apply conform_eval_swire_upd_env_inline.
      exact Hcf.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.
      (* sreg *)
      apply conform_eval_reg_upd_env_inline.
      exact Hcf.
      exact Hcfr.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.
      (* smem *)
      simpl.
      done.
      (* sinst *)
      simpl.
      rewrite Hs /well_formed_fstmt /well_typed_fstmt in Hwf.
      move : Hwf => [[Hwf _]_].
      done.
      (* snode *)
      apply conform_eval_node_upd_env_inline.
      exact Hcf.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.
      (* sfcnct *)
      case Hr : (SV.acc v rs == [::]).
      apply conform_eval_sfcnct_upd_env0_inline.
      exact Hcf.
      
      rewrite Hs in Hwf.
      move : Hwf Hs.
      case : e.
      1,2,3,6: move => t1 t2 Hwt Hs.
      5,6: move => t1 t2 t3 Hwt Hs.
      7: move => v1 Hwt Hs.
      1,2,3,4,5,6,7: rewrite /well_formed_fstmt /well_typed_fstmt in Hwt.
      1,2,3,4,5,6,7: rewrite /well_formed_fstmt_inline.
      1,2,3,4,5,6,7: apply /andP.
      1,2,3,4,5,6: done.
      case H0: (mylListIn v1 finstoutl).
      case H1: (TE.find v1 finstoutm) => [[a4 a0]|].
      case H2: (TE.find a4 ffmodsmap) => [mst|].
      case H3: (TE.find a0 fterss) => [[[[te0 rs1]s1]mem0]|].
      case H4: (TE.find a4 finstin) => [a2|].
      case H5: (TE.find a0 finstinmap) => [updfinstin|].
      case H6: (TE.find a4 allfinstoutl) =>[finstoutl0|].
      case H7: (TE.find v1 finstoutmap) => [a3|].
      case H8: (TE.find a4 allfinstoutm) => [finstoutm0|].
      case H9: (TE.find a4 allfinstportmap) => [[finstinmap0 finstoutmap0]|].
      rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
      move : Hwt => [Hwt Hid].
      move : Hwt => [_ Hwt].
      move : Hwt => [_ Hwt].
      move : Hwt => [_ Hwt].
      rewrite Hwt Hid //.
      1: rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
      2: rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 in Hwt.
      3: rewrite H0 H1 H2 H3 H4 H5 H6 H7 in Hwt.
      4: rewrite H0 H1 H2 H3 H4 H5 H6 in Hwt.
      5: rewrite H0 H1 H2 H3 H4 H5 in Hwt.
      6: rewrite H0 H1 H2 H3 H4 in Hwt.
      7: rewrite H0 H1 H2 H3 in Hwt.
      8: rewrite H0 H1 H2 in Hwt.
      9: rewrite H0 H1 in Hwt.
      1,2,3,4,5,6,7,8,9: move : Hwt => [Hwt Hid].
      1,2,3,4,5,6,7,8,9: discriminate.
      rewrite H0 in Hwt.
      done.
      exact Hr.
      apply conform_eval_sfcnct_upd_envr0_inline.
      exact Hcf.
      exact Hcfr.
      rewrite Hs in Hwf.
      move : Hwf Hs.
      case : e.
      1,2,3,6: move => t1 t2 Hwt Hs.
      5,6: move => t1 t2 t3 Hwt Hs.
      7: move => v1 Hwt Hs.
      1,2,3,4,5,6,7: rewrite /well_formed_fstmt /well_typed_fstmt in Hwt.
      1,2,3,4,5,6,7: rewrite /well_formed_fstmt_inline.
      1,2,3,4,5,6,7: apply /andP.
      1,2,3,4,5,6: done.
      case H0: (mylListIn v1 finstoutl).
      case H1: (TE.find v1 finstoutm) => [[a4 a0]|].
      case H2: (TE.find a4 ffmodsmap) => [mst|].
      case H3: (TE.find a0 fterss) => [[[[te0 rs1]s1]mem0]|].
      case H4: (TE.find a4 finstin) => [a2|].
      case H5: (TE.find a0 finstinmap) => [updfinstin|].
      case H6: (TE.find a4 allfinstoutl) =>[finstoutl0|].
      case H7: (TE.find v1 finstoutmap) => [a3|].
      case H8: (TE.find a4 allfinstoutm) => [finstoutm0|].
      case H9: (TE.find a4 allfinstportmap) => [[finstinmap0 finstoutmap0]|].
      rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
      move : Hwt => [Hwt Hid].
      move : Hwt => [_ Hwt].
      move : Hwt => [_ Hwt].
      move : Hwt => [_ Hwt].
      rewrite Hwt Hid //.
      1: rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
      2: rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 in Hwt.
      3: rewrite H0 H1 H2 H3 H4 H5 H6 H7 in Hwt.
      4: rewrite H0 H1 H2 H3 H4 H5 H6 in Hwt.
      5: rewrite H0 H1 H2 H3 H4 H5 in Hwt.
      6: rewrite H0 H1 H2 H3 H4 in Hwt.
      7: rewrite H0 H1 H2 H3 in Hwt.
      8: rewrite H0 H1 H2 in Hwt.
      9: rewrite H0 H1 in Hwt.
      1,2,3,4,5,6,7,8,9: move : Hwt => [Hwt Hid].
      1,2,3,4,5,6,7,8,9: discriminate.
      rewrite H0 in Hwt.
      done.
      exact Hr.
      (* sinvalid *)
      apply conform_eval_invalid_upd_env_inline.
      exact Hcf.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.
      (* swhen *)
      simpl.
      exact Hcf.
      (* sstop *)
      simpl.
      exact Hcf.

    - case Hs : a => [||||||v e|||].
      (* sskip *)
      simpl.
      exact Hcfr.
      (* swire *)
      simpl.
      admit.
      (* sreg *)
      apply conform_eval_reg_upd_env_inline.
      exact Hcf.
      exact Hcfr.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.
      (* smem *)
      simpl.
      done.
      (* sinst *)
      admit.
      (* snode *)
      simpl.
      admit.
      (* sfcnct *)
      case Hr : (SV.acc v rs == [::]).
      simpl.
      case : (TE.vtyp v te) => [n0|n0|||].
      1,2: rewrite Hr.
      1,2,3,4,5: simpl.
      1,2,3,4,5: exact Hcfr.
      apply conform_eval_sfcnct_upd_envr0_inline.
      exact Hcf.
      exact Hcfr.
      rewrite Hs /well_formed_fstmt in Hwf.
      move : Hwf => [Hwt Hid].
      (*rewrite /well_typed_fstmt in Hwt.
      rewrite /well_formed_fstmt_inline Hwt Hid //.*)
      admit.
      exact Hr.
      (* sinvalid *)
      simpl.
      admit.
      (* swhen *)
      simpl.
      exact Hcfr.
      (* sstop *)
      simpl.
      exact Hcfr.
  Admitted.

  Lemma conform_eval_stmts sts : forall rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap n,
    SV.conform s te ->
    SV.conform rs te ->
    well_formed_fstmts sts te s rs finstoutl finstoutm ffmodsmap fterss finstin 
    finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n ->
    SV.conform (fst (fst (no_mem_eval_fstmts sts rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n))) (no_mem_upd_typenv_fstmts sts te)
    /\ SV.conform (snd (fst (no_mem_eval_fstmts sts rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n))) (no_mem_upd_typenv_fstmts sts te).
  Proof.
  induction sts. 
  - move => rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n.
    move => Hcf Hcfr Hwfs.
    split.
    simpl.
    exact Hcfr.
    simpl.
    exact Hcf.
  - move => rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n.
    move => Hcf Hcfr Hwfs.
    simpl in Hwfs.
    move : Hwfs => [Hwf Hwfs].
    simpl.
    case Hhd : (no_mem_eval_fstmt a rs s
    (no_mem_upd_typenv_fstmt a te)
    finstoutl finstoutm ffmodsmap
    fterss finstin finstinmap
    finstoutmap allfinstoutl
    allfinstoutm allfinstportmap n) => [[rs0 s0] temp].
    specialize IHsts with (rs:=rs0) (s:=s0) (te:=(no_mem_upd_typenv_fstmt a te))
          (finstoutl := finstoutl) (finstoutm := finstoutm)
          (ffmodsmap := ffmodsmap) (fterss := fterss)
          (finstin := finstin) (finstinmap := finstinmap)
          (finstoutmap := finstoutmap) (allfinstoutl := allfinstoutl)
          (allfinstoutm := allfinstoutm) (allfinstportmap := allfinstportmap)
          (n := n).
    apply IHsts.

    have ->: s0 = snd (fst (no_mem_eval_fstmt a rs s (no_mem_upd_typenv_fstmt a te) finstoutl finstoutm
    ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm
    allfinstportmap n)) by rewrite Hhd//.
    induction n. 
    simpl.

    case Htemp : (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) => [rs1 s1].
    simpl.
    have -> : s1 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Htemp.
    clear Htemp rs1 s1.
    apply conform_eval_stmt with (finstoutl := finstoutl) (finstoutm := finstoutm)
    (ffmodsmap := ffmodsmap) (fterss := fterss)
    (finstin := finstin) (finstinmap := finstinmap)
    (finstoutmap := finstoutmap) (allfinstoutl := allfinstoutl)
    (allfinstoutm := allfinstoutm) (allfinstportmap := allfinstportmap)
    (n := 0).
    exact Hcf.
    exact Hcfr.
    exact Hwf.

    simpl.
    case Ha : a => [||||inst||v e|||]; try by done.
    1,2,4,6: rewrite -Ha.
    1,2,3,4: case Htemp : (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) => [rs1 s1].
    1,2,3,4: simpl.
    1,2,3,4: have -> : s1 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Htemp.
    1,2,3,4: apply conform_eval_stmt with (finstoutl := finstoutl) (finstoutm := finstoutm)
    (ffmodsmap := ffmodsmap) (fterss := fterss)
    (finstin := finstin) (finstinmap := finstinmap)
    (finstoutmap := finstoutmap) (allfinstoutl := allfinstoutl)
    (allfinstoutm := allfinstoutm) (allfinstportmap := allfinstportmap)
    (n := n.+1).
    1,4,7,10: exact Hcf.
    1,3,5,7: exact Hcfr.
    1,2,3,4: exact Hwf.

    (* sinst *)
    case H1: (TE.find (imid inst) ffmodsmap) => [mst|].
    case H2: (TE.find (iid inst) fterss) => [[[[te0 rs1]s1]mem0]|].
    case H3: (TE.find (imid inst) finstin) => [a2|].
    case H4: (TE.find (iid inst) finstinmap) => [updfinstin|].
    case H5: (TE.find (imid inst) allfinstoutl) =>[finstoutl0|].
    case H6: (TE.find (imid inst) allfinstoutm) => [finstoutm0|].
    case H7: (TE.find (imid inst) allfinstportmap) => [[finstinmap0 finstoutmap0]|].
    case Htemp : (fold_left
    (fun '(y, tfterss) =>
     let
     '(trs, ts) := y in
      fun tempst : fstmt =>
      no_mem_eval_fstmt tempst trs ts te0 finstoutl0
        finstoutm0 ffmodsmap tfterss finstin finstinmap0
        finstoutmap0 allfinstoutl allfinstoutm
        allfinstportmap n) (rev mst)
    (rs1, upd_inner s s1 a2 updfinstin, fterss)) => [[trs ts] tm].
    clear Htemp.
    1,2,3,4,5,6,7,8: simpl.
    1,2,3,4,5,6,7,8: rewrite Ha /well_formed_fstmt /well_typed_fstmt in Hwf.
    1,2,3,4,5,6,7,8: move : Hwf => [[Hwf _]_].
    1,2,3,4,5,6,7,8: done.
    (* cnct *)
    case He : e => [||||||v1].
    1,2,3,4,5,6: rewrite -He -Ha.
    1,2,3,4,5,6: case Htemp : (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) => [rs1 s1].
    1,2,3,4,5,6:simpl.
    1,2,3,4,5,6:have -> : s1 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Htemp.
    1,2,3,4,5,6:clear Htemp rs1 s1.
    1,2,3,4,5,6:apply conform_eval_stmt with (finstoutl := finstoutl) (finstoutm := finstoutm)
    (ffmodsmap := ffmodsmap) (fterss := fterss)
    (finstin := finstin) (finstinmap := finstinmap)
    (finstoutmap := finstoutmap) (allfinstoutl := allfinstoutl)
    (allfinstoutm := allfinstoutm) (allfinstportmap := allfinstportmap)
    (n := n.+1).
    1,4,7,10,13,16:exact Hcf.
    1,3,5,7,9,11:exact Hcfr.
    1,2,3,4,5,6: exact Hwf.

    rewrite /well_formed_fstmt in Hwf.
    move : Hwf => [Hwt Hid].
    rewrite Ha He /well_typed_fstmt in Hwt.

    case H0 : (mylListIn v1 finstoutl).
    case Hr: (SV.acc v rs == [::]).
    2:simpl.
    2:done.

    case H1: (TE.find v1 finstoutm) => [[a4 a0]|].
    case H2: (TE.find a4 ffmodsmap) => [mst|].
    case H3: (TE.find a0 fterss) => [[[[te0 rs1]s1]mem0]|].
    case H4: (TE.find a4 finstin) => [a2|].
    case H5: (TE.find a0 finstinmap) => [updfinstin|].
    case H6: (TE.find a4 allfinstoutl) =>[finstoutl0|].
    case H7: (TE.find v1 finstoutmap) => [a3|].
    case H8: (TE.find a4 allfinstoutm) => [finstoutm0|].
    case H9: (TE.find a4 allfinstportmap) => [[finstinmap0 finstoutmap0]|].
    rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
    move : Hwt => [Hiot Hcfi].
    move : Hcfi => [Hmemi Hcfi].
    move : Hcfi => [Hcfi _].
    rewrite Nat.pred_succ in Hcfi.
    rewrite Ha in Hid.
    simpl in Hid.
    move : Hid => /andP [Hid Hide].
    rewrite /is_defined in Hid.
    assert (Hte : TE.Equal (TE.add v (TE.vtyp v te) te) te).
    rewrite SV.Lemmas.add_same.
    apply SV.Lemmas.Equal_refl.
    case H: (TE.find v te).
    rewrite (TE.find_some_vtyp H) //.
    apply SV.Lemmas.find_none_not_mem in H.
    rewrite Hid in H.
    discriminate.
    assert (Htcf : SV.conform
    (SV.upd v
    (SV.acc a3
       (snd
          (fst
          (fold_left
                 (fun '(y, tfterss) =>
                  let
                  '(trs, ts) := y in
                   fun tempst : fstmt =>
                   no_mem_eval_fstmt tempst trs ts (no_mem_upd_typenv_fstmts (rev mst) te0) finstoutl0 finstoutm0
                     ffmodsmap tfterss finstin finstinmap0 finstoutmap0
                     allfinstoutl allfinstoutm allfinstportmap n) 
                 (rev mst) (rs1, upd_inner s s1 a2 updfinstin, fterss))))) s) (TE.add v (TE.vtyp v te) te)).
    apply SV.conform_upd.
    rewrite Hiot.

    apply SV.conform_mem with (v:=a3) in Hcfi.
    rewrite -Hcfi.
    rewrite -(TE.vtyp_vsize (eqP(eqxx (TE.vtyp a3 (no_mem_upd_typenv_fstmts (rev mst) te0)))))//.
    exact Hmemi.
    exact Hcf.
    move : Hte Htcf.
    apply SV.conform_equal.

    rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 H4 H5 H6 H7 H8 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 H4 H5 H6 H7 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 H4 H5 H6 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 H4 H5 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 H4 in Hwt.
    discriminate.
    rewrite H0 H1 H2 H3 in Hwt.
    discriminate.
    rewrite H0 H1 H2 in Hwt.
    discriminate.
    rewrite H0 H1 in Hwt.
    discriminate.

    rewrite -He -Ha.
    case Htemp : (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) => [rs1 s1].
    simpl.
    have -> : s1 = snd (no_mem_eval_noninst_fstmt a rs s (no_mem_upd_typenv_fstmt a te)) by rewrite Htemp.
    apply conform_eval_stmt with (finstoutl := finstoutl) (finstoutm := finstoutm)
    (ffmodsmap := ffmodsmap) (fterss := fterss)
    (finstin := finstin) (finstinmap := finstinmap)
    (finstoutmap := finstoutmap) (allfinstoutl := allfinstoutl)
    (allfinstoutm := allfinstoutm) (allfinstportmap := allfinstportmap)
    (n := n.+1).
    exact Hcf.
    exact Hcfr.
    rewrite H0 in Hwt.
    rewrite Ha He in Hid.
    rewrite /well_formed_fstmt Ha He /well_typed_fstmt H0 Hwt Hid //.

    (* rs *)
    admit.

    have -> : s0 = snd (fst (no_mem_eval_fstmt a rs s (no_mem_upd_typenv_fstmt a te)
    finstoutl finstoutm ffmodsmap fterss finstin finstinmap
    finstoutmap allfinstoutl allfinstoutm allfinstportmap n)) by rewrite Hhd //.
    have -> : rs0 = fst (fst (no_mem_eval_fstmt a rs s (no_mem_upd_typenv_fstmt a te)
    finstoutl finstoutm ffmodsmap fterss finstin finstinmap
    finstoutmap allfinstoutl allfinstoutm allfinstportmap n)) by rewrite Hhd //.
    exact Hwfs.
  Admitted.

(*
  Lemma conform_eval_inst_upd_env n : forall rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap inst ,
    SV.conform s te ->
    SV.conform rs te ->
    conform_terss fterss ->
    well_formed_fstmt (Sinst inst) te ->
    match TE.find (imid inst) ffmodsmap with
    | Some mst => match TE.find (iid inst) fterss with
                  | Some _ => match TE.find (imid inst) finstin with
                              | Some _ => true
                              | None => false
                              end
                  | None => false
                  end
    | None => false
    end ->
    conform_terss (snd (no_mem_eval_fstmt (Sinst inst) rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap n)).
  Proof.
    induction n.

    move => rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap inst.
    move => Hcf Hcfr Hterss Hwf Ht.

    simpl.
    exact Hterss.
    simpl.
    move => rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    allfinstoutl allfinstoutm allfinstportmap inst.
    move => Hcf Hcfr Hterss Hwf Ht.
    case H0 : (TE.find (imid inst) ffmodsmap) => [t0|].
    case H1 : (TE.find (iid inst) fterss) => [[[[t10 t11]t12]t13]|].
    case H2 : (TE.find (imid inst) finstin) => [t2|].
    case H3 : (TE.find (iid inst) finstinmap) => [t3|].
    case H4 : (TE.find (imid inst) allfinstoutl) => [t4|].
    case H5 : (TE.find (imid inst) allfinstoutm) => [t5|].
    case H6 : (TE.find (imid inst) allfinstportmap) => [[t60 t61]|].
    (* rs2 s2 对 t10 conform *)
    (* fterss2 conform *)
    admit.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
    simpl.
    exact Hterss.
Admitted.
*)

End MakeFirrtl.
Module LoFirrtl := MakeFirrtl VarOrder TE Store.

*)