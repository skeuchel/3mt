Require Import Ascii.
Require Import String.
Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffState.

Section Ref.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Reference Type. *)
    Inductive RefType (A : Set) : Set :=
    | TRef : A -> RefType A.

    Definition RefType_fmap (A B : Set) (f : A -> B) (rta : RefType A)
      : RefType B :=
      match rta with
        | TRef a => TRef B (f a)
      end.

    Global Instance RefType_Functor : Functor RefType :=
      {| fmap := RefType_fmap |}.
    Proof.
      destruct a; reflexivity.
    (* fmap id *)
      destruct a; reflexivity.
    Defined.

    Variable D : Set -> Set.
    Context {Fun_D : Functor D}.
    Let DType := DType D.
    Context {Sub_RefType_D  : RefType :<: D}.

    (* Constructor + Universal Property. *)
    Context {WF_Sub_RefType_D : WF_Functor _ _ Sub_RefType_D _ _}.

    Definition tref' (t : DType) : DType := inject' (TRef _ t).
    Definition tref (t : Fix D)
      {t_UP' : Universal_Property'_fold t}
      : Fix D := proj1_sig (tref' (exist _ _ t_UP')).
    Global Instance UP'_tref
      (t : Fix D)
      {t_UP' : Universal_Property'_fold t}
      : Universal_Property'_fold (tref t) := proj2_sig (tref' (exist _ _ t_UP')).

  (* Induction Principle for Ref Types. *)
    Definition ind_alg_RefType
      (P : forall d : Fix D, Universal_Property'_fold d -> Prop)
      (H : forall t (IHt : UP'_P P t),
        UP'_P P (@tref _ (proj1_sig IHt)))
      (d : RefType (sig (UP'_P P))) : sig (UP'_P P) :=
      match d with
        | TRef t => exist (UP'_P P) (tref (proj1_sig t)) (H (proj1_sig t) (proj2_sig t))
      end.

    Lemma ind_PAlg_RefType
      {Sub_RefType_D' : RefType :<: D}
      (eq_Sub_RefType : forall A (d : RefType A),
        inj (Sub_Functor := Sub_RefType_D) d = inj (Sub_Functor := Sub_RefType_D') d)
      (Name : Set)
      (P : forall e : Fix D, Universal_Property'_fold e -> Prop)
      (H : forall t (IHt : UP'_P P t),
        UP'_P P (@tref _ (proj1_sig IHt)))
      :
      PAlgebra (sub_F_G := Sub_RefType_D') Name RefType D (UP'_P P).
      econstructor 1 with (p_algebra := ind_alg_RefType P H).
      destruct e; simpl; unfold tref, tref'; simpl;
        rewrite wf_functor; simpl; rewrite eq_Sub_RefType; reflexivity.
    Qed.

  (* Type Equality Section. *)
    Definition isTRef : Fix D -> option DType :=
      fun typ =>
        match project typ with
          | Some (TRef t) => Some t
          | None      => None
        end.

    Definition RefType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D)
      (e : RefType R) : eq_DTypeR D :=
      match e with
        | TRef t => fun t' =>
          match (isTRef (proj1_sig t')) with
            | Some t'' => rec t t''
            | None => false
          end
      end.

    Global Instance MAlgebra_eq_DType_TRef T:
      FAlgebra eq_DTypeName T (eq_DTypeR D) RefType :=
      {| f_algebra := RefType_eq_DType T|}.

    Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
    Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
      Sub_RefType_D (MAlgebra_eq_DType_TRef T) (eq_DType_DT _)}.

    Global Instance PAlgebra_eq_DType_eq_RefType
      {Sub_RefType_D' : RefType :<: D}
      (eq_Sub_RefType : forall A (d : RefType A),
        inj (Sub_Functor := Sub_RefType_D) d = inj (Sub_Functor := Sub_RefType_D') d) :
      PAlgebra (sub_F_G := Sub_RefType_D') eq_DType_eqName RefType D (UP'_P (eq_DType_eq_P D)).
    Proof.
      apply ind_PAlg_RefType; eauto.
      unfold UP'_P; econstructor.
      unfold eq_DType_eq_P; intros.
      unfold eq_DType, mfold, tref, tref', inject' in H; simpl in H;
        repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
      rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
      unfold isTRef in H.
      caseEq (project (subGF := Sub_RefType_D) (proj1_sig d2)); rewrite H0 in H;
        try discriminate; destruct r.
      apply project_inject in H0.
      destruct IHt as [t_UP' IHt]; unfold eq_DType_eq_P in IHt.
      rewrite H0; unfold tref, tref', inject; simpl;
        repeat rewrite wf_functor; simpl; unfold RefType_fmap; simpl.
      rewrite (IHt s H); auto.
      auto with typeclass_instances.
      exact (proj2_sig d2).
    Qed.

    Global Instance PAlgebra_eq_DType_neq_RefType
      {Sub_RefType_D' : RefType :<: D}
      (eq_Sub_RefType : forall A (d : RefType A),
        inj (Sub_Functor := Sub_RefType_D) d = inj (Sub_Functor := Sub_RefType_D') d) :
      PAlgebra (sub_F_G := Sub_RefType_D') eq_DType_neqName RefType D (UP'_P (eq_DType_neq_P D)).
    Proof.
      apply ind_PAlg_RefType; eauto.
      unfold UP'_P; econstructor.
      unfold eq_DType_neq_P; intros.
      unfold eq_DType, mfold, tref, tref', inject' in H; simpl in H;
        repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
      rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
      destruct IHt as [t_UP' IHt]; unfold eq_DType_neq_P in IHt.
      unfold not; intros; rewrite <- H0 in H.
      unfold isTRef, project, tref, inject in H; simpl in H.
      rewrite out_in_fmap in H; repeat rewrite wf_functor in H;
        simpl in H; rewrite prj_inj in H.
      unfold eq_DType in IHt; apply (IHt _ H).
      rewrite in_out_UP'_inverse; eauto.
    Qed.

    (* The Unit Type. *)
    Inductive UnitType (A : Set) : Set :=
    | TUnit : UnitType A.

    Definition UnitType_fmap (A B : Set) (f : A -> B) (rta : UnitType A)
      : UnitType B :=
      match rta with
        | TUnit => TUnit B
      end.

    Global Instance UnitType_Functor : Functor UnitType :=
      {| fmap := UnitType_fmap |}.
    Proof.
      destruct a; reflexivity.
    (* fmap id *)
      destruct a; reflexivity.
    Defined.

    Context {Sub_UnitType_D  : UnitType :<: D}.

    (* Constructor + Universal Property. *)
    Context {WF_Sub_UnitType_D : WF_Functor _ _ Sub_UnitType_D _ _}.

    Definition tunit' : DType := inject' (TUnit _).
    Definition tunit : Fix D := proj1_sig tunit'.
    Global Instance UP'_tunit : Universal_Property'_fold tunit :=
      proj2_sig tunit'.

  (* Induction Principle for Unit Types. *)
    Definition ind_alg_UnitType
      (P : forall d : Fix D, Universal_Property'_fold d -> Prop)
      (H : UP'_P P tunit)
      (d : UnitType (sig (UP'_P P))) : sig (UP'_P P) :=
      match d with
        | TUnit => exist (UP'_P P) tunit H
      end.

    Lemma ind_PAlg_UnitType
      {Sub_UnitType_D' : UnitType :<: D}
      (eq_Sub_UnitType : forall A (d : UnitType A),
        inj (Sub_Functor := Sub_UnitType_D) d = inj (Sub_Functor := Sub_UnitType_D') d)
      (Name : Set)
      (P : forall e : Fix D, Universal_Property'_fold e -> Prop)
      (H : UP'_P P tunit)
      :
      PAlgebra (sub_F_G := Sub_UnitType_D') Name UnitType D (UP'_P P).
      econstructor 1 with (p_algebra := ind_alg_UnitType P H).
      destruct e; simpl; unfold tunit, tunit'; simpl;
        rewrite wf_functor; simpl; rewrite eq_Sub_UnitType; auto.
    Qed.

  (* Type Equality Section. *)
  Definition isTUnit : Fix D -> bool :=
    fun typ =>
      match project typ with
        | Some TUnit => true
        | None           => false
      end.

  Definition UnitType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D)
    (e : UnitType R) : eq_DTypeR D :=
    match e with
      | TUnit => fun t => isTUnit (proj1_sig t)
    end.

  Global Instance MAlgebra_eq_DType_TUnit T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) UnitType :=
    {| f_algebra := UnitType_eq_DType T|}.

  Context {WF_Unit_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_UnitType_D (MAlgebra_eq_DType_TUnit T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_DType_eq_UnitType
    {Sub_UnitType_D' : UnitType :<: D}
    (eq_Sub_UnitType : forall A (d : UnitType A),
      inj (Sub_Functor := Sub_UnitType_D) d = inj (Sub_Functor := Sub_UnitType_D') d):
    PAlgebra (sub_F_G := Sub_UnitType_D') eq_DType_eqName UnitType D (UP'_P (eq_DType_eq_P D)).
  Proof.
    apply ind_PAlg_UnitType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tunit, tunit', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_Unit_eq_DT _)) in H; simpl in H.
    unfold isTUnit in H.
    caseEq (project (subGF := Sub_UnitType_D) (proj1_sig d2)); rewrite H0 in H;
      try discriminate; destruct u.
    apply project_inject in H0.
    rewrite H0; unfold tunit, tunit', inject; simpl;
      repeat rewrite wf_functor; simpl; unfold UnitType_fmap; auto.
    auto with typeclass_instances.
    exact (proj2_sig d2).
  Qed.

  Global Instance PAlgebra_eq_DType_neq_UnitType
    {Sub_UnitType_D' : UnitType :<: D}
    (eq_Sub_UnitType : forall A (d : UnitType A),
      inj (Sub_Functor := Sub_UnitType_D) d = inj (Sub_Functor := Sub_UnitType_D') d) :
    PAlgebra (sub_F_G := Sub_UnitType_D') eq_DType_neqName UnitType D (UP'_P (eq_DType_neq_P D)).
  Proof.
    apply ind_PAlg_UnitType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_neq_P; intros.
    unfold eq_DType, mfold, tunit, tunit', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_Unit_eq_DT _)) in H; simpl in H.
    unfold not; intros; rewrite <- H0 in H.
    unfold isTUnit, project, tunit, inject in H; simpl in H.
    rewrite out_in_fmap in H; repeat rewrite wf_functor in H;
      simpl in H; rewrite prj_inj in H; discriminate.
  Qed.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive RefE (a : Set) : Set :=
  | Ref : a -> RefE a
  | DeRef : a -> RefE a
  | Assign : a -> a -> RefE a.

  Definition RefE_fmap (B C : Set) (f : B -> C) (Aa : RefE B) : RefE C :=
    match Aa with
      | Ref e => Ref _ (f e)
      | DeRef e => DeRef _ (f e)
      | Assign e1 e2 => Assign _ (f e1) (f e2)
    end.

  Global Instance RefE_Functor : Functor RefE :=
    {| fmap := RefE_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Definition Exp := Exp E.
  Context {Sub_RefE_E : RefE :<: E}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_RefE_E : WF_Functor _ _ Sub_RefE_E _ _}.

  Definition assign' (e1 e2 : Exp) : Exp :=  inject' (Assign _ e1 e2).

  Definition assign (e1 e2 : Fix E)
    {UP'_e1 : Universal_Property'_fold e1}
    {UP'_e2 : Universal_Property'_fold e2}
    : Fix E := proj1_sig (assign' (exist _ _ UP'_e1) (exist _ _ UP'_e2)).

   Global Instance UP'_assign {e1 e2 : Fix E}
     {UP'_e1 : Universal_Property'_fold e1}
     {UP'_e2 : Universal_Property'_fold e2}
     :
     Universal_Property'_fold (assign e1 e2) :=
     proj2_sig (assign' (exist _ _ UP'_e1) (exist _ _ UP'_e2)).

  Definition ref' (e : Exp) : Exp :=  inject' (Ref _ e).

  Definition ref (e : Fix E)
    {UP'_e : Universal_Property'_fold e}
    : Fix E := proj1_sig (ref' (exist _ _ UP'_e)).

   Global Instance UP'_ref {e : Fix E}
     {UP'_e : Universal_Property'_fold e}
     :
     Universal_Property'_fold (ref e) :=
     proj2_sig (ref' (exist _ _ UP'_e)).

  Definition deref' (e : Exp) : Exp :=  inject' (DeRef _ e).

  Definition deref (e : Fix E)
    {UP'_e : Universal_Property'_fold e}
    : Fix E := proj1_sig (deref' (exist _ _ UP'_e)).

   Global Instance UP'_deref {e : Fix E}
     {UP'_e : Universal_Property'_fold e}
     :
     Universal_Property'_fold (deref e) :=
     proj2_sig (deref' (exist _ _ UP'_e)).

  (* Induction Principles for RefE. *)
  Definition ind_alg_RefE
    (P : forall e : Fix E, Universal_Property'_fold e -> Prop)
    (H : forall e
      (IHe : UP'_P P e),
      UP'_P P (@ref e (proj1_sig IHe)))
    (H0 : forall e
      (IHe : UP'_P P e),
      UP'_P P (@deref e (proj1_sig IHe)))
    (H1 : forall e1 e2
      (IHe1 : UP'_P P e1)
      (IHe2 : UP'_P P e2),
      UP'_P P (@assign e1 e2 (proj1_sig IHe1) (proj1_sig IHe2)))
      (e : RefE (sig (UP'_P P)))
        :
        sig (UP'_P P) :=
    match e with
      | Ref e => exist (UP'_P P) _ (H _ (proj2_sig e))
      | DeRef e => exist (UP'_P P) _ (H0 _ (proj2_sig e))
      | Assign e1 e2 => exist (UP'_P P) _
        (H1 (proj1_sig e1) (proj1_sig e2) (proj2_sig e1) (proj2_sig e2))
    end.

  Lemma ind_PAlg_RefE (Name : Set)
    (P : forall e : Fix E, Universal_Property'_fold e -> Prop)
    (H : forall e
      (IHe : UP'_P P e),
      UP'_P P (@ref e (proj1_sig IHe)))
    (H0 : forall e
      (IHe : UP'_P P e),
      UP'_P P (@deref e (proj1_sig IHe)))
    (H1 : forall e1 e2
      (IHe1 : UP'_P P e1)
      (IHe2 : UP'_P P e2),
      UP'_P P (@assign e1 e2 (proj1_sig IHe1) (proj1_sig IHe2)))
    :
    PAlgebra Name RefE E (UP'_P P).
    econstructor 1 with (p_algebra := ind_alg_RefE P H H0 H1).
    destruct e; simpl.
    unfold ref, ref'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold deref, deref'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold assign, assign'; simpl; intros; rewrite wf_functor; reflexivity.
  Qed.

  Definition ind2_alg_RefE
    {F F' : Set -> Set}
    {Fun_F : Functor F}
    {Fun_F' : Functor F'}
    {Sub_Arith_F : RefE :<: F}
    {Sub_Arith_F' : RefE :<: F'}
    (P : forall e : (Fix F) * (Fix F'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall e
      (IHe : UP'_P2 P e),
      UP'_P2 P (inject (Ref _ (exist _ _ (proj1 (proj1_sig IHe)))),
      inject (Ref _ (exist _ _ (proj2 (proj1_sig IHe))))))
    (H0 : forall e
      (IHe : UP'_P2 P e),
      UP'_P2 P (inject (DeRef _ (exist _ _ (proj1 (proj1_sig IHe)))),
        inject (DeRef _ (exist _ _ (proj2 (proj1_sig IHe))))))
    (H1 : forall e1 e2
      (IHe1 : UP'_P2 P e1)
      (IHe2 : UP'_P2 P e2),
      UP'_P2 P (inject (Assign _
        (exist _ _ (proj1 (proj1_sig IHe1))) (exist _ _ (proj1 (proj1_sig IHe2)))),
      inject (Assign _
        (exist _ _ (proj2 (proj1_sig IHe1))) (exist _ _ (proj2 (proj1_sig IHe2))))))
      (e : RefE (sig (UP'_P2 P)))
        :
        sig (UP'_P2 P) :=
    match e with
      | Ref e => exist (UP'_P2 P) _ (H _ (proj2_sig e))
      | DeRef e => exist (UP'_P2 P) _ (H0 _ (proj2_sig e))
      | Assign e1 e2 => exist (UP'_P2 P) _
        (H1 (proj1_sig e1) (proj1_sig e2) (proj2_sig e1) (proj2_sig e2))
    end.

  Lemma ind_P2Alg_RefE (Name : Set)
    (F F' : Set -> Set)
    {Fun_F : Functor F}
    {Fun_F' : Functor F'}
    {Sub_RefF_F : RefE :<: F}
    {Sub_RefF_F' : RefE :<: F'}
    {WF_Fun_F : WF_Functor _ _ _ _ Fun_F}
    {WF_Fun_F' : WF_Functor _ _ _ _ Fun_F'}
    (P : forall e : (Fix F) * (Fix F'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall e
      (IHe : UP'_P2 P e),
      UP'_P2 P (inject (Ref _ (exist _ _ (proj1 (proj1_sig IHe)))),
      inject (Ref _ (exist _ _ (proj2 (proj1_sig IHe))))))
    (H0 : forall e
      (IHe : UP'_P2 P e),
      UP'_P2 P (inject (DeRef _ (exist _ _ (proj1 (proj1_sig IHe)))),
        inject (DeRef _ (exist _ _ (proj2 (proj1_sig IHe))))))
    (H1 : forall e1 e2
      (IHe1 : UP'_P2 P e1)
      (IHe2 : UP'_P2 P e2),
      UP'_P2 P (inject (Assign _
        (exist _ _ (proj1 (proj1_sig IHe1))) (exist _ _ (proj1 (proj1_sig IHe2)))),
      inject (Assign _
        (exist _ _ (proj2 (proj1_sig IHe1))) (exist _ _ (proj2 (proj1_sig IHe2))))))
        :
        P2Algebra Name RefE F F' (UP'_P2 P).
    econstructor 1 with (p2_algebra := ind2_alg_RefE P H H0 H1);
      destruct e; simpl; unfold inject; simpl;
        intros; rewrite wf_functor; reflexivity.
  Qed.

  (* Alternative Induction Principles for RefE. *)
  Definition indD_alg_RefE
    (P : forall e : Fix E, Universal_Property'_fold e -> Set)
    (H : forall e
      (IHe : UP'_SP P e),
      UP'_SP P (@ref e (projT1 IHe)))
    (H0 : forall e
      (IHe : UP'_SP P e),
      UP'_SP P (@deref e (projT1 IHe)))
    (H1 : forall e1 e2
      (IHe1 : UP'_SP P e1)
      (IHe2 : UP'_SP P e2),
      UP'_SP P (@assign e1 e2 (projT1 IHe1) (projT1 IHe2)))
      (e : RefE (sigT (UP'_SP P)))
        :
        sigT (UP'_SP P) :=
    match e with
      | Ref e => existT (UP'_SP P) _ (H _ (projT2 e))
      | DeRef e => existT (UP'_SP P) _ (H0 _ (projT2 e))
      | Assign e1 e2 => existT (UP'_SP P) _ (H1 _ _ (projT2 e1) (projT2 e2))
    end.

  Lemma ind_DAlg_RefE (Name : Set)
    (P : forall e : Fix E, Universal_Property'_fold e -> Set)
    (H : forall e
      (IHe : UP'_SP P e),
      UP'_SP P (@ref e (projT1 IHe)))
    (H0 : forall e
      (IHe : UP'_SP P e),
      UP'_SP P (@deref e (projT1 IHe)))
    (H1 : forall e1 e2
      (IHe1 : UP'_SP P e1)
      (IHe2 : UP'_SP P e2),
      UP'_SP P (@assign e1 e2 (projT1 IHe1) (projT1 IHe2)))
    :
    DAlgebra Name RefE E (UP'_SP P).
    econstructor 1 with (d_algebra := indD_alg_RefE P H H0 H1).
    destruct e; simpl.
    unfold ref, ref'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold deref, deref'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold assign, assign'; simpl; intros; rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.

   Inductive LocValue (A : Set) : Set :=
   | Loc : nat -> LocValue A.

   Definition Loc_fmap : forall (A B : Set) (f : A -> B),
     LocValue A -> LocValue B :=
     fun A B _ e => match e with
                      | Loc n => Loc _ n
                    end.

   Global Instance Loc_Functor : Functor LocValue :=
     {| fmap := Loc_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Context {Sub_LocValue_V : LocValue :<: V}.
   Context {Sub_BotValue_V : BotValue :<: V}.
   Context {Dis_Loc_Bot : Distinct_Sub_Functor _ Sub_LocValue_V Sub_BotValue_V}.

   (* Constructor + Universal Property. *)
   Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
   Context {WF_Sub_LocValue_F : WF_Functor _ _ Sub_LocValue_V _ _}.

   Definition loc' (n : nat) : Value := inject' (Loc _ n).
   Definition loc (n : nat) : Fix V := proj1_sig (loc' n).

   Global Instance UP'_loc {n : nat} :
     Universal_Property'_fold (loc n) := proj2_sig (loc' n).

   (* Constructor Testing for Locations. *)

   Definition isLoc : Fix V -> option nat :=
     fun exp =>
       match project exp with
         | Some (Loc n) => Some n
         | None        => None
       end.

    Lemma project_loc_loc : forall n,
      project (F := V) (G := LocValue) (loc n) = Some (Loc _ n).
    Proof.
      intros; unfold project, loc, inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold Loc_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

    (* Unit Values *)

   Inductive UnitValue (A : Set) : Set :=
   | Unit : UnitValue A.

   Definition Unit_fmap : forall (A B : Set) (f : A -> B),
     UnitValue A -> UnitValue B :=
     fun A B _ e => match e with
                      | Unit => Unit B
                    end.

   Global Instance Unit_Functor : Functor UnitValue :=
     {| fmap := Unit_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Context {Sub_UnitValue_V : UnitValue :<: V}.
   Context {Dis_Unit_Bot : Distinct_Sub_Functor _ Sub_UnitValue_V Sub_BotValue_V}.

   (* Constructor + Universal Property. *)
   Context {WF_Sub_UnitValue_F : WF_Functor _ _ Sub_UnitValue_V _ _}.

   Definition unit' : Value := inject' (Unit _).
   Definition unit : Fix V := proj1_sig unit'.

   Global Instance UP'_unit :
     Universal_Property'_fold unit := proj2_sig unit'.

   (* Constructor Testing for Unitations. *)

   Definition isUnit : Fix V -> bool :=
     fun exp =>
       match project exp with
         | Some Unit => true
         | None      => false
       end.

    Lemma project_unit_unit : project (F := V) (G := UnitValue) unit = Some (Unit _).
    Proof.
      intros; unfold project, unit, inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold Unit_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Definition stuck : nat -> Fix V := stuck _.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Reference Expressions. *)

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.


  Definition RefE_typeof (R : Set) (rec : R -> typeofR D MT)
     (e : RefE R) : typeofR D MT :=
     match e with
       | Ref e => do t <- rec e;
                  return_ (tref' t)
       | DeRef e => do te <- rec e;
                   match isTRef (proj1_sig te) with
                     | Some t => return_ t
                     | None => fail
                   end
       | Assign e1 e2 => do t1 <- rec e1;
                           match isTRef (proj1_sig t1) with
                             | Some t =>
                               do t2 <- rec e2;
                                 if (eq_DType D (proj1_sig t) t2) then
                                   return_ tunit'
                                   else
                                     fail
                             | None => fail
                           end
     end.

  Global Instance MAlgebra_typeof_RefE T:
    FAlgebra TypeofName T (typeofR D MT) RefE :=
    {| f_algebra := RefE_typeof T|}.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {FailM : FailMonad ME}.
  Context {State_M : StateM ME (list Value)}.

  (* Monadic Evaluation Algebra for RefEemetic Expressions. *)

  Definition RefE_evalM (R : Set) (rec : R -> evalMR V ME)
     (e : RefE R) : evalMR V ME :=
       match e with
         | Ref e =>
           do v <- (rec e);
             do env <- get;
               put (insert _ v env) >> return_ (loc' (length env))
         | DeRef e =>
           do v <- (rec e);
             match isLoc (proj1_sig v) with
               | Some n => do env <- get;
                 return_ match (@lookup Value env n) with
                           | Some mv => mv
                           | _ => stuck' 457
                         end
               | None => return_ (stuck' 456)
             end
         | Assign e1 e2 =>
           do v <- (rec e1);
             match isLoc (proj1_sig v) with
               | Some n =>
                 do v2 <- rec e2;
                   do env <- get;
                     put (replace_el n v2 env) >> return_ unit'
               | None => return_ (stuck' 3)
             end
       end.

  Global Instance MAlgebra_evalM_RefE T :
    FAlgebra EvalName T (evalMR V ME) RefE :=
    {| f_algebra := RefE_evalM T|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Global Instance MAlgebra_ExpPrint_RefE T :
    FAlgebra ExpPrintName T (ExpPrintR) RefE :=
    {| f_algebra := fun rec e =>
      match e with
        | Ref e => fun i => append "ref (" ((rec e i) ++ ")")
        | DeRef e => fun i => append "! (" ((rec e i) ++ ")")
        | Assign e1 e2 => fun i => append (rec e1 i) (" := " ++ (rec e2 i))
    end |}.

  Global Instance MAlgebra_ValuePrint_Loc T :
    FAlgebra ValuePrintName T ValuePrintR LocValue :=
    {| f_algebra := fun rec e =>
      match e with
        | Loc n => append "loc_" (String (ascii_of_nat (n + 48)) EmptyString)
      end |}.

  Context {evalM_E : FAlgebra EvalName Exp (evalMR V ME) E}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ RefE E
    Sub_RefE_E (MAlgebra_evalM_RefE _) evalM_E}.

  Ltac WF_FAlg_rewrite := repeat rewrite wf_functor; simpl;
    repeat rewrite out_in_fmap; simpl;
      repeat rewrite wf_functor; simpl;
        repeat rewrite wf_algebra; simpl.

  Section WFValue_Sec.

  (* ============================================== *)
  (* WELL-FORMED REFERENCE VALUES                   *)
  (* ============================================== *)

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.

    (** Typing rules for unit values **)

    Inductive WFValue_Unit (WFV : WFValue_i D V TypContext -> Prop) : WFValue_i D V TypContext -> Prop :=
    | WFVS_Unit : forall Sigma v T,
      proj1_sig v = unit ->
      proj1_sig T = tunit ->
      WFValue_Unit WFV (mk_WFValue_i D V _ Sigma v T).

    Definition ind_alg_WFV_Unit (P : WFValue_i D V TypContext -> Prop)
      (H : forall Sigma v T v_eq T'_eq, P (mk_WFValue_i D V _ Sigma v T))
      i (e : WFValue_Unit P i) : P i :=
      match e in WFValue_Unit _ i return P i with
        | WFVS_Unit Sigma v T v_eq T_eq =>
          H Sigma v T v_eq T_eq
      end.

    Definition WFV_Unit_ifmap (A B : WFValue_i D V TypContext -> Prop) i (f : forall i, A i -> B i)
      (WFVS_a : WFValue_Unit A i) : WFValue_Unit B i :=
      match WFVS_a in (WFValue_Unit _ s) return (WFValue_Unit B s)
        with
        | WFVS_Unit Sigma v T v_eq T_eq =>
          WFVS_Unit _ Sigma v T v_eq T_eq
      end.

    Global Instance iFun_WFVS_Unit : iFunctor WFValue_Unit.
      constructor 1 with (ifmap := WFV_Unit_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.
    Context {Sub_WFV_Unit_WFV : Sub_iFunctor WFValue_Unit WFV}.

    Global Instance WFV_proj1_a_Unit :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFValue_Unit.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WFV_proj1_a_P.
      inversion H; subst; simpl; intros.
      apply (inject_i (subGF := Sub_WFV_Unit_WFV)); econstructor; simpl; eauto.
      rewrite H3; eauto.
    Defined.

    Global Instance WFV_proj1_b_Unit :
      iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFValue_Unit.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WFV_proj1_b_P.
      inversion H; subst; simpl; intros.
      apply (inject_i (subGF := Sub_WFV_Unit_WFV)); econstructor; simpl; eauto.
      rewrite H3; eauto.
    Defined.

    Global Instance WFV_Weaken_Unit :
      iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFValue_Unit.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WFValue_Weaken_P.
      inversion H; subst; simpl; intros.
      apply inject_i; econstructor; eassumption.
    Defined.

    (** Typing rules for location values **)

    Context {TypContext_S : SigTypContextC D TypContext}.
    Context {TypContext_SCE : SigConsExtensionC D TypContext _ _}.

    Inductive WFValue_Loc (WFV : WFValue_i D V TypContext -> Prop) : WFValue_i D V TypContext -> Prop :=
    | WFVS_Loc : forall Sigma v n (T T' : DType),
      SigLookup D Sigma n = Some T' ->
      proj1_sig v = loc n ->
      proj1_sig T = @tref _ (proj2_sig T') ->
      WFValue_Loc WFV (mk_WFValue_i D V _ Sigma v T).

    Definition ind_alg_WFV_Loc (P : WFValue_i D V _ -> Prop)
      (H : forall Sigma v n T T' lookup_n v_eq T'_eq, P (mk_WFValue_i D V _ Sigma v T))
      i (e : WFValue_Loc P i) : P i :=
      match e in WFValue_Loc _ i return P i with
        | WFVS_Loc Sigma v n T T' lookup_n v_eq T_eq =>
          H Sigma v n T T' lookup_n v_eq T_eq
      end.

    Definition WFV_Loc_ifmap (A B : WFValue_i D V _ -> Prop) i (f : forall i, A i -> B i)
      (WFVS_a : WFValue_Loc A i) : WFValue_Loc B i :=
      match WFVS_a in (WFValue_Loc _ s) return (WFValue_Loc B s)
        with
        | WFVS_Loc Sigma v n T T' lookup_n v_eq T_eq =>
          WFVS_Loc _ Sigma v n T T' lookup_n v_eq T_eq
      end.

    Global Instance iFun_WFVS_Loc : iFunctor WFValue_Loc.
      constructor 1 with (ifmap := WFV_Loc_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Context {Sub_WFV_Loc_WFV : Sub_iFunctor WFValue_Loc WFV}.

    Global Instance WFV_Weaken_Loc :
      iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFValue_Loc.
    Proof.
      constructor; intros.
      unfold iAlgebra; intros; apply ind_alg_WFV_Loc; try eassumption;
        unfold WFValue_Weaken_P; simpl; intros.
      apply inject_i; econstructor; eauto.
      eapply ConsExtension_SigLookup; eauto.
    Qed.

    Global Instance WFV_proj1_a_Loc :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFValue_Loc.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WFV_proj1_a_P.
      inversion H; subst; simpl; intros.
      apply (inject_i (subGF := Sub_WFV_Loc_WFV)); econstructor; simpl; eauto.
      rewrite H4; eauto.
    Defined.

    Global Instance WFV_proj1_b_Loc :
      iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFValue_Loc.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WFV_proj1_b_P.
      inversion H; subst; simpl; intros.
      apply (inject_i (subGF := Sub_WFV_Loc_WFV)); econstructor; simpl; eauto.
      rewrite H4; eauto.
    Defined.

    (* Inversion principles for well-formed location values. *)

    Definition WF_invertLoc_P (i : WFValue_i D V _) :=
      forall T' T'_UP,
        proj1_sig (wfv_T _ _ _ i) = @tref T' T'_UP ->
        WFValue_Loc (iFix WFV) i.

    Inductive WF_invertLoc_Name := wfv_invertloc_name.
    Context {WF_invertLoc_WFV :
      iPAlgebra WF_invertLoc_Name WF_invertLoc_P WFV}.

    Global Instance WF_invertLoc_Loc :
      iPAlgebra WF_invertLoc_Name WF_invertLoc_P WFValue_Loc.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertLoc_P.
      inversion H; subst; simpl; intros.
      econstructor; eassumption.
    Defined.

    Context {Dis_TRef_TUnit : Distinct_Sub_Functor _ Sub_RefType_D Sub_UnitType_D}.

    Global Instance WF_invertLoc_Unit :
      iPAlgebra WF_invertLoc_Name WF_invertLoc_P WFValue_Unit.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertLoc_P.
      inversion H; subst; simpl; intros.
      rewrite H2 in H1.
    unfold tunit, tref, tunit', tref' in H1.
    elimtype False.
    generalize (inject_discriminate Dis_TRef_TUnit
      (TRef (sig Universal_Property'_fold) (exist _ T' T'_UP)) (TUnit (sig Universal_Property'_fold))).
    revert H1; unfold inject, inject'; eauto.
    Defined.

    Definition WF_invertLoc := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertLoc_WFV)).

    Definition WF_invertLoc'_P (i : WFValue_i D V _) :=
      forall n,
        proj1_sig (wfv_v _ _ _ i) = loc n ->
        WFValue_Loc (iFix WFV) i.

    Inductive WF_invertLoc'_Name := wfv_invertloc'_name.
    Context {WF_invertLoc'_WFV :
      iPAlgebra WF_invertLoc'_Name WF_invertLoc'_P WFV}.

    Global Instance WF_invertLoc'_Loc :
      iPAlgebra WF_invertLoc'_Name WF_invertLoc'_P WFValue_Loc.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertLoc'_P.
      inversion H; subst; simpl; intros.
      econstructor; eassumption.
    Defined.

    Context {Dis_LocValue_UnitValue : Distinct_Sub_Functor _ Sub_LocValue_V Sub_UnitValue_V}.

    Global Instance WF_invertLoc'_Unit :
      iPAlgebra WF_invertLoc'_Name WF_invertLoc'_P WFValue_Unit.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertLoc'_P.
      inversion H; subst; simpl; intros.
      rewrite H2 in H0.
      unfold tunit, tref, tunit', tref' in H0.
      elimtype False.
      generalize (inject_discriminate Dis_LocValue_UnitValue
        (Loc _ n) (Unit (sig Universal_Property'_fold))).
      revert H0; unfold inject, inject'; eauto.
    Defined.

    Definition WF_invertLoc' := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertLoc'_WFV)).

    End WFValue_Sec.

    Variable TypContext : Set.

    Context {TypContextCE : ConsExtensionC TypContext}.
    Context {TypContext_S : SigTypContextC D TypContext}.
    Context {TypContext_SCE : SigConsExtensionC D TypContext _ _}.
    Context {TypContext_WFE : WF_EnvC V TypContext}.

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.

    Context {TypContext_SWFE : Sig_WF_EnvC D V TypContext WFV _ _}.

    Context {Sub_WFV_Unit_WFV : Sub_iFunctor (WFValue_Unit _) WFV}.
    Context {Sub_WFV_Loc_WFV : Sub_iFunctor (WFValue_Loc _) WFV}.

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Context {funWFVM : iFunctor WFVM}.

    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME TypContext WFV) WFVM}.
    Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME TypContext) WFVM}.

    Context {WFV_proj1_a_WFV : iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFV}.
    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) E}.
    Context {WF_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ RefE E
      Sub_RefE_E (MAlgebra_typeof_RefE _) (Typeof_F T)}.

    Context {evalM_E' : forall T, FAlgebra EvalName T (evalMR V ME) E}.
    Context {WF_eval_E' : forall T, @WF_FAlgebra EvalName _ _ RefE E
      Sub_RefE_E (MAlgebra_evalM_RefE _) (evalM_E' T)}.

    Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

    Definition WFV_Weaken := ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_Weaken_WFV)).

    Context {wfvm_bind_alg :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

    Lemma eval_soundness_H (typeof_R eval_R : Set)
      typeof_rec eval_rec
      :
      forall (eT : typeof_R) (eE : eval_R) Sigma
        (IHe : WFValueMC _ _ _ _ _ WFVM Sigma
          (eval_rec eE) (typeof_rec eT)),
        WFValueMC _ _ _ _ _ WFVM Sigma
        (RefE_evalM _ eval_rec (Ref _ eE))
        (RefE_typeof _ typeof_rec (Ref _ eT)).
    Proof.
      simpl; intros.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros.
      repeat rewrite fmap_return; simpl.
      repeat rewrite wf_functor; simpl.
      rewrite H; reflexivity.
      intros.
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)).
      constructor.
      intros.
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)).
      econstructor 2 with (Sigma' := SigInsert D T Sigma'); simpl.
      apply (WF_EnvInsert D V); auto.
      apply (WFV_Weaken _ H0); simpl; eauto.
      apply ConsExtension_SigInsert; auto.
      apply ConsExtension_SigInsert; auto.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)).
      constructor 1 with (T := tref' T).
      apply inject_i; econstructor 1 with (T' := T);
        try unfold loc; try (unfold tref; destruct T as [T T_UP']; simpl); eauto.
      apply (WF_EnvInsertLookup D V); auto.
      apply return_orn.
      reflexivity.
    Qed.

    Context {WF_invertLoc'_WFV :
      iPAlgebra WF_invertLoc'_Name (WF_invertLoc'_P _ WFV) WFV}.
    Context {WF_invertLoc_WFV :
      iPAlgebra WF_invertLoc_Name (WF_invertLoc_P _ WFV) WFV}.

    Lemma eval_soundness_H0 (typeof_R eval_R : Set)
      typeof_rec eval_rec
      :
      forall (eT : typeof_R) (eE : eval_R) Sigma
        (IHe : WFValueMC _ _ _ _ _ WFVM Sigma
          (eval_rec eE) (typeof_rec eT)),
        WFValueMC _ _ _ _ _ WFVM Sigma
        (RefE_evalM _ eval_rec (DeRef _ eE))
        (RefE_typeof _ typeof_rec (DeRef _ eT)).
    Proof.
      simpl; intros.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros; rewrite H; reflexivity.
      intros.
      unfold isLoc.
      caseEq (project (G := LocValue) (proj1_sig v)).
      destruct l.
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)); econstructor; intros.
      apply project_inject in H1; auto with typeclass_instances.
      generalize (WF_invertLoc' TypContext WFV _ H0 _ H1) as WF_v_T; intros;
        inversion WF_v_T; subst.
      rewrite H8.
      unfold isTRef, tref, project; simpl; rewrite out_in_fmap, fmap_fusion;
        rewrite wf_functor; simpl; rewrite prj_inj; auto with typeclass_instances.
      rewrite H7 in H1; unfold loc, inject in H1; simpl in H1;
        apply in_t_UP'_inject in H1; repeat rewrite wf_functor in H1;
          simpl in H1; apply (f_equal (prj (sub_F := LocValue))) in H1;
            repeat rewrite prj_inj in H1; injection H1; intros; subst.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); constructor 1 with (T := T'); intros.
      rename H2 into WF_env_Sigma.
      destruct (WF_EnvLookup D V _ _ _ _ WF_env_Sigma H6) as [v' [lookup_v' WF_v'_T']];
        unfold Value in *; rewrite lookup_v'; auto.
      apply return_orn.
      rewrite in_out_UP'_inverse; auto.
      exact (proj2_sig _).
      exact (proj2_sig _).
      unfold isTRef; caseEq (project (G := RefType) (proj1_sig T)); auto.
      destruct r; apply project_inject in H2; generalize (WF_invertLoc _ _ _ H0 _ (proj2_sig s));
        eauto with typeclass_instances; try (intros; exact (proj2_sig _)); simpl.
      revert H2; unfold inject, tref; simpl; repeat rewrite wf_functor; simpl;
        intros; apply H3 in H2; inversion H2; subst.
      rewrite H8 in H1.
      rewrite project_loc_loc in H1; discriminate; auto.
      apply wfvm_fail with (WFV := WFV) (Monad_ME := Mon_M); auto.
    Qed.

    Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
    Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Lemma eval_soundness_H1 (typeof_R eval_R : Set)
      typeof_rec eval_rec
      :
      forall (e1T e2T : typeof_R) (e1E e2E : eval_R) Sigma
        (IHe1 : WFValueMC _ _ _ _ _ WFVM Sigma
          (eval_rec e1E) (typeof_rec e1T))
        (IHe2 : forall Sigma', ConsExtension Sigma' Sigma ->
          WFValueMC _ _ _ _ _ WFVM Sigma'
          (eval_rec e2E) (typeof_rec e2T)),
        WFValueMC _ _ _ _ _ WFVM Sigma
        (RefE_evalM _ eval_rec (Assign _ e1E e2E))
        (RefE_typeof _ typeof_rec (Assign _ e1T e2T)).
    Proof.
      simpl; intros.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros; rewrite H; reflexivity.
      intros.
      unfold isLoc; caseEq (project (G := LocValue) (proj1_sig v)).
      destruct l.
      apply project_inject in H1.
      generalize (WF_invertLoc' _ _ _ H0 _ H1) as WF_v_T;
        intros; inversion WF_v_T; subst.
      rewrite H7; unfold isTRef, tref, project; simpl; rewrite wf_functor; simpl;
        rewrite out_in_fmap, wf_functor; simpl; rewrite prj_inj.
      rewrite in_out_UP'_inverse.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros.
      caseEq (eq_DType D (proj1_sig T') T0);
        caseEq (eq_DType D (proj1_sig T') T'0);
        try reflexivity; rewrite fmap_return; rewrite fmap_fail.
      apply eq_DType_eq in H3 ; apply eq_DType_neq in H4; auto with typeclass_instances; congruence.
      apply eq_DType_neq in H3; apply eq_DType_eq in H4; auto with typeclass_instances; congruence.
      intros.
      caseEq (eq_DType D (proj1_sig T') T0).
      rewrite H6 in H1; unfold loc, inject in H1; simpl in H1;
        apply in_t_UP'_inject in H1; repeat rewrite wf_functor in H1;
          simpl in H2; apply (f_equal (prj (sub_F := LocValue))) in H1;
            repeat rewrite prj_inj in H1; injection H1; intros; subst; auto.
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)); constructor; intros.
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)); constructor 2 with (Sigma' := Sigma'0).
      apply (ConsExtension_SigLookup _ _ Sigma'0) in H5; auto.
      apply (WF_EnvReplace D V _ _ _ T'); auto.
      apply eq_DType_eq in H4; auto.
      destruct T' as [T' T'_UP']; apply (WFV_proj1_b D V _ WFV _ _ H3 T' T'_UP'); auto.
      apply ConsExtension_id.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); constructor 1 with (T := tunit').
      apply (inject_i (subGF := Sub_WFV_Unit_WFV)); constructor.
      unfold unit; simpl; auto.
      unfold tunit; simpl; auto.
      apply return_orn; simpl; auto.
      apply wfvm_fail with (Monad_ME := Mon_M) (WFV := WFV); auto with typeclass_instances.
      exact (proj2_sig _).
      auto with typeclass_instances.
      exact (proj2_sig _).
      unfold isTRef; caseEq (project (G := RefType) (proj1_sig T)); auto.
      destruct r; apply project_inject in H2; generalize (WF_invertLoc _ _ _ H0 _ (proj2_sig s));
        eauto with typeclass_instances; simpl; try (intros; exact (proj2_sig _)).
      revert H2; unfold inject, tref; simpl; repeat rewrite wf_functor; simpl.
      intros; apply H3 in H2; inversion H2; subst.
      rewrite H8 in H1; rewrite project_loc_loc in H1; discriminate; auto.
      apply wfvm_fail with (Monad_ME := Mon_M) (WFV := WFV);
        auto with typeclass_instances.
    Qed.

    Section PSoundness.

      Variable P_bind : Set.
      Variable E' : Set -> Set.
      Context {Fun_E' : Functor E'}.
      Context {Sub_RefE_E' : RefE :<: E'}.
      Context {WF_Fun_E' : WF_Functor _ _ Sub_RefE_E' _ _}.

      Variable P : UP'_F E -> UP'_F E' -> P_bind -> TypContext -> Prop.

      Variable Ref_Decomp :
        forall e1 e2 ref1_UP' ref2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Ref _ e2)))) ref2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Ref _ e1)))) ref1_UP')
          pb Sigma ->
          forall e2_UP' e1_UP',
            P (exist _ (proj1_sig (P := Universal_Property'_fold) e2) e2_UP')
            (exist _ (proj1_sig (P := Universal_Property'_fold) e1) e1_UP') pb Sigma.

      Variable DeRef_Decomp :
        forall e1 e2 ref1_UP' ref2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (DeRef _ e2)))) ref2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (DeRef _ e1)))) ref1_UP')
          pb Sigma ->
          forall e2_UP' e1_UP',
            P (exist _ (proj1_sig (P := Universal_Property'_fold) e2) e2_UP')
            (exist _ (proj1_sig (P := Universal_Property'_fold) e1) e1_UP') pb Sigma.

      Variable Assign_Decomp1 :
        forall e11 e12 e21 e22 assign1_UP' assign2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Assign _ e12 e22)))) assign2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Assign _ e11 e21)))) assign1_UP')
          pb Sigma ->
          forall e12_UP' e11_UP',
            P (exist _ (proj1_sig (P := Universal_Property'_fold) e12) e12_UP')
            (exist _ (proj1_sig (P := Universal_Property'_fold) e11) e11_UP') pb Sigma.

      Variable Assign_Decomp2 :
        forall e11 e12 e21 e22 assign1_UP' assign2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Assign _ e12 e22)))) assign2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (Assign _ e11 e21)))) assign1_UP')
          pb Sigma ->
          forall e22_UP' e21_UP',
            P (exist _ (proj1_sig (P := Universal_Property'_fold) e22) e22_UP')
            (exist _ (proj1_sig (P := Universal_Property'_fold) e21) e21_UP') pb Sigma.

      Global Instance Ref_eval_soundness'
      (P_Sub : forall e e' pb Sigma Sigma',
        P e e' pb Sigma -> ConsExtension Sigma' Sigma ->
        P e e' pb Sigma')
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D MT) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_RefE_E' (MAlgebra_typeof_RefE T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalMR V ME)
      (typeof_rec : UP'_F E' -> typeofR D MT)
      :
      P2Algebra ES'_ExpName RefE E' E
      (UP'_P2 (eval_soundness'_P D V E MT ME _ WFVM
        _ _ _ P pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := evalM_E)))).
    Proof.
      apply ind_P2Alg_RefE; eauto.
      (* ref case *)
      destruct e as [eE eT]; destruct IHe as [[UP'_eE UP'_eT] IHe].
      assert (Universal_Property'_fold
        (inject
          (Ref (sig Universal_Property'_fold)
            (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT))))) /\
        Universal_Property'_fold
        (inject
          (Ref (sig Universal_Property'_fold)
            (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT)))))) as WF_Ref
      by (simpl; split; unfold inject; exact (proj2_sig _)).
      unfold eval_soundness'_P, UP'_P2; simpl; intros;
        constructor 1 with (x := WF_Ref).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold RefE_fmap.
      apply eval_soundness_H.
      generalize (IHa _ _ (exist _ _ UP'_eE, exist _ _ UP'_eT)
        (Ref_Decomp _ _ _ _ _ _ WF_Sigma _ _));
        simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_eE)); simpl;
        intros eE_eq WF_ref; rewrite <- eE_eq; eauto.
      apply WF_ref.
      apply IHe; eauto.
      apply (Ref_Decomp _ _ _ _ _ _ WF_Sigma _ _).
      (* deref case *)
      destruct e as [eE eT]; destruct IHe as [[UP'_eE UP'_eT] IHe].
      assert (Universal_Property'_fold
        (inject
          (DeRef (sig Universal_Property'_fold)
            (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT))))) /\
        Universal_Property'_fold
        (inject
          (DeRef (sig Universal_Property'_fold)
            (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT)))))) as WF_DeRef
      by (simpl; split; unfold inject; exact (proj2_sig _)).
      unfold eval_soundness'_P, UP'_P2; simpl; intros;
        constructor 1 with (x := WF_DeRef).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold RefE_fmap.
      apply eval_soundness_H0.
      generalize (IHa _ _ (exist _ _ UP'_eE, exist _ _ UP'_eT)
      (DeRef_Decomp _ _ _ _ _ _ WF_Sigma _ _)); simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_eE)); simpl;
        intros eE_eq WF_ref; rewrite <- eE_eq; eauto.
      apply WF_ref.
      apply IHe; eauto.
      apply (DeRef_Decomp _ _ _ _ _ _ WF_Sigma _ _).
      (* assign case *)
      destruct e1 as [e1E e1T]; destruct e2 as [e2E e2R];
        destruct IHe1 as [[UP'_e1E UP'_e1T] IHe1];
          destruct IHe2 as [[UP'_e2E UP'_e2T] IHe2]; simpl in *|-*.
      unfold eval_soundness'_P, UP'_P2; intros.
      assert (Universal_Property'_fold
        (fst
          (inject
            (Assign (sig Universal_Property'_fold)
              (exist Universal_Property'_fold e1E
                (proj1 (conj UP'_e1E UP'_e1T)))
              (exist Universal_Property'_fold e2E
                (proj1 (conj UP'_e2E UP'_e2T)))),
            inject
            (Assign (sig Universal_Property'_fold)
              (exist Universal_Property'_fold e1T
                (proj2 (conj UP'_e1E UP'_e1T)))
              (exist Universal_Property'_fold e2R
                (proj2 (conj UP'_e2E UP'_e2T)))))) /\
        Universal_Property'_fold
        (snd
          (inject
            (Assign (sig Universal_Property'_fold)
              (exist Universal_Property'_fold e1E
                (proj1 (conj UP'_e1E UP'_e1T)))
              (exist Universal_Property'_fold e2E
                (proj1 (conj UP'_e2E UP'_e2T)))),
            inject
            (Assign (sig Universal_Property'_fold)
              (exist Universal_Property'_fold e1T
                (proj2 (conj UP'_e1E UP'_e1T)))
              (exist Universal_Property'_fold e2R
                (proj2 (conj UP'_e2E UP'_e2T))))))) as WF_Assign
      by (simpl; split; unfold inject; exact (proj2_sig _)).
      constructor 1 with (x := WF_Assign); simpl.
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold RefE_fmap.
      intros; apply eval_soundness_H1.
      generalize (IHa _ _ (exist _ _ UP'_e1E, exist _ _ UP'_e1T)
        (Assign_Decomp1 _ _ _ _ _ _ _ _ WF_Sigma _ _)); simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_e1E)); simpl;
        intros e1E_eq WF_ref; rewrite <- e1E_eq; eauto.
      apply WF_ref.
      apply IHe1; eauto.
      apply (Assign_Decomp1 _ _ _ _ _ _ _ _ WF_Sigma _ _).
      intros Sigma' ConsExt_Sig'_Sig;
        generalize (IHa _ _ (exist _ _ UP'_e2E, exist _ _ UP'_e2T)
          (Assign_Decomp2 _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig) _ _)); simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_e2E)); simpl;
        intros e2E_eq WF_ref; rewrite <- e2E_eq; eauto.
      apply WF_ref.
      apply IHe2; eauto.
      apply (Assign_Decomp2 _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig) _ _).
    Defined.

  End PSoundness.

  Global Instance Ref_eval_soundness'' typeof_rec eval_rec :
    P2Algebra ES'_ExpName RefE E E
    (UP'_P2 (eval_soundness'_P D V E MT ME _ WFVM
      _ _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
      (f_algebra (FAlgebra := Typeof_F _)) (f_algebra (FAlgebra := evalM_E)))).
  Proof.
    eapply Ref_eval_soundness'; eauto.
  Defined.

End Ref.

  Hint Extern 5 (iPAlgebra WF_invertLoc_Name (WF_invertLoc_P _ _ _ _) _) =>
    constructor; unfold iAlgebra;
    let H := fresh in let T' := fresh in let T'_UP := fresh in
      intros i H T' T'_UP; unfold WF_invertLoc_P;
        inversion H; simpl;
          match goal with
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
                  apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)];
                fail
          end : typeclass_instances.

  Hint Extern 5 (iPAlgebra WF_invertLoc'_Name (WF_invertLoc'_P _ _ _ _) _) =>
    constructor; unfold iAlgebra, WF_invertLoc'_P;
    let H := fresh in let n := fresh in
      intros i H n;
        inversion H; simpl;
          match goal with
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
                  apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)];
                fail
          end : typeclass_instances.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
