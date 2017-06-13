Require Import List.
Require Import FunctionalExtensionality.
Require Import FJ_tactics.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffState.
Require Import EffReader.
Require Import Lambda.
Require Import Ref.
Require Import ESoundRS.

Section Lambda_Ref.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {Sub_RefType_D : RefType :<: D}.
  Context {Sub_UnitType_D : UnitType :<: D}.
  Context {WF_Sub_RefType_D : WF_Functor _ _ (Sub_RefType_D) _ _}.
  Context {WF_Sub_UnitType_D : WF_Functor _ _ (Sub_UnitType_D) _ _}.
  Context {WF_Sub_LType_F : WF_Functor _ _ (Sub_LType_D) _ _}.
  Context {Distinct_RefType_LType : Distinct_Sub_Functor Fun_D Sub_RefType_D Sub_LType_D}.
  Context {Distinct_UnitType_LType : Distinct_Sub_Functor Fun_D Sub_UnitType_D Sub_LType_D}.

  Variable E : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (E A)}.
  Context {Sub_RefE_E : forall A, RefE :<: E A}.
  Context {Sub_Lambda_E : forall A, Lambda D A :<: E A}.
  Context {WF_Sub_RefE_F : forall A, WF_Functor _ _ (Sub_RefE_E A) _ _}.
  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_E A) _ _}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_LocValue_V : LocValue :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Context {Sub_UnitValue_V : UnitValue :<: V}.
  Context {WF_Sub_LocValue_V : WF_Functor _ _ (Sub_LocValue_V) _ _}.
  Context {WF_Sub_ClosValue_V : WF_Functor _ _ (Sub_ClosValue_V) _ _}.
  Context {Distinct_LocValue_RefValue : Distinct_Sub_Functor Fun_V Sub_LocValue_V Sub_ClosValue_V}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
  Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Environment_ME : Environment ME (list (Names.Value V))}.
  Context {StateM_ME : StateM ME (list (Names.Value V))}.
  Context {FailME : FailMonad ME}.

  Context {evalM_E : FAlgebra EvalName (Exp (E nat)) (evalMR V ME) (E nat)}.

  Context {WF_eval_Lambda_E :
    @WF_FAlgebra EvalName _ _ (Lambda D nat) (E nat)
    (Sub_Lambda_E nat) (MAlgebra_evalM_Lambda D E V ME) evalM_E}.
  Context {WF_eval_Ref_F : @WF_FAlgebra EvalName _ _ RefE (E nat)
    (Sub_RefE_E _) (MAlgebra_evalM_RefE V ME _) evalM_E}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D))}.
  Context {WF_Lambda_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ (Lambda D _) (E _)
    (Sub_Lambda_E _) (MAlgebra_typeof_Lambda D MT _) (Typeof_E T)}.
  Context {WF_RefE_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ RefE (E _)
    (Sub_RefE_E _) (MAlgebra_typeof_RefE D MT _) (Typeof_E T)}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

  (* ============================================== *)
  (* EQUIVALENCE OF REFERENCE EXPRESSIONS           *)
  (* ============================================== *)

  Inductive RefE_eqv (A B : Set) (C : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
  | Ref_eqv : forall (gamma : Env _) gamma' a a' e e',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    proj1_sig e = proj1_sig (ref' (E A) a) ->
    proj1_sig e' = proj1_sig (ref' (E B) a') ->
    RefE_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
  | DeRef_eqv : forall (gamma : Env _) gamma' a a' e e',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    proj1_sig e = proj1_sig (deref' (E A) a) ->
    proj1_sig e' = proj1_sig (deref' (E B) a') ->
    RefE_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
  | Assign_eqv : forall (gamma : Env _) gamma' a b a' b' e e',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    C (mk_eqv_i _ _ _ gamma gamma' b b') ->
    proj1_sig e = proj1_sig (assign' (E _) a b) ->
    proj1_sig e' = proj1_sig (assign' (E _) a' b') ->
    RefE_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e').

  Definition ind_alg_RefE_eqv
    (A B : Set)
    (P : eqv_i E A B -> Prop)
    (Href : forall gamma gamma' a a' e e'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    (Hderef : forall gamma gamma' a a' e e'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    (Hassign : forall gamma gamma' a b a' b' e e'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b'))
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    i (e : RefE_eqv A B P i) : P i :=
    match e in RefE_eqv _ _ _ i return P i with
      | Ref_eqv gamma gamma' a a' e e'
        eqv_a_a' e_eq e'_eq =>
        Href gamma gamma' a a' e e' eqv_a_a' e_eq e'_eq
      | DeRef_eqv gamma gamma' a a' e e'
        eqv_a_a' e_eq e'_eq =>
        Hderef gamma gamma' a a' e e'
        eqv_a_a' e_eq e'_eq
      | Assign_eqv gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq =>
        Hassign gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq
    end.

  Definition RefE_eqv_ifmap (A B : Set)
    (A' B' : eqv_i E A B -> Prop) i (f : forall i, A' i -> B' i)
    (eqv_a : RefE_eqv A B A' i) : RefE_eqv A B B' i :=
    match eqv_a in RefE_eqv _ _ _ i return RefE_eqv _ _ _ i with
      | Ref_eqv gamma gamma' a a' e e'
        eqv_a_a' e_eq e'_eq =>
        Ref_eqv _ _ _ gamma gamma' a a' e e'
        (f _ eqv_a_a') e_eq e'_eq
      | DeRef_eqv gamma gamma' a a' e e'
        eqv_a_a' e_eq e'_eq =>
        DeRef_eqv _ _ _ gamma gamma' a a' e e'
        (f _ eqv_a_a') e_eq e'_eq
      | Assign_eqv gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq =>
        Assign_eqv _ _ _ gamma gamma' a b a' b' e e'
        (f _ eqv_a_a') (f _ eqv_b_b') e_eq e'_eq
    end.

  Global Instance iFun_RefE_eqv A B : iFunctor (RefE_eqv A B).
    constructor 1 with (ifmap := RefE_eqv_ifmap A B).
    destruct a; simpl; intros; reflexivity.
    destruct a; simpl; intros; unfold id; eauto.
  Defined.

  Variable Sub_RefE_eqv_EQV_E : forall A B,
    Sub_iFunctor (RefE_eqv A B) (EQV_E A B).

  Global Instance EQV_proj1_RefE_eqv :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (RefE_eqv _ _).
    econstructor; intros.
    unfold iAlgebra; intros; apply ind_alg_RefE_eqv;
      unfold EQV_proj1_P; simpl; intros; subst.
    apply (inject_i (subGF := Sub_RefE_eqv_EQV_E A B)); econstructor; simpl; eauto.
    destruct a; destruct a'; eapply IHa; eauto.
    apply (inject_i (subGF := Sub_RefE_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
    destruct a; destruct a'; eapply IHa; eauto.
    apply (inject_i (subGF := Sub_RefE_eqv_EQV_E A B)); econstructor 3; simpl; eauto.
    destruct a; destruct a'; eapply IHa; eauto.
    destruct b; destruct b'; eapply IHb; eauto.
    apply H.
  Qed.

  Context {Sub_Lambda_eqv_EQV_E : forall A B, Sub_iFunctor (Lambda_eqv _ _ A B) (EQV_E A B)}.

  Variable TypContext : Set.
  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {GammaTypContext : GammaTypContextC D TypContext}.
  Context {TypContext_GCE : GammaConsExtensionC D TypContext _ _}.
  Context {TypContext_S : SigTypContextC D TypContext}.
  Context {TypContext_SCE : SigConsExtensionC D TypContext _ _}.
  Context {TypContext_WFE : WF_EnvC V TypContext}.
  Context {TypContext_SWFE : Sig_WF_EnvC D V TypContext WFV _ _}.

  Context {funWFV : iFunctor WFV}.

  Context {Sub_WFV_Loc_WFV : Sub_iFunctor (WFValue_Loc D V _) WFV}.
  Context {Sub_WFV_Unit_WFV : Sub_iFunctor (WFValue_Unit D V _) WFV}.
  Context {Sub_WFV_Clos_WFV : Sub_iFunctor (WFValue_Clos D E MT V EQV_E _) WFV}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext-> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.
  Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME TypContext) WFVM}.

  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.
  Context {WF_invertLoc_WFV :
    iPAlgebra WF_invertLoc_Name (WF_invertLoc_P _ _ _ WFV) WFV}.
  Context {WF_invertLoc'_WFV :
    iPAlgebra WF_invertLoc'_Name (WF_invertLoc'_P _ _ _ WFV) WFV}.
  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

  Context {wfvm_bind_alg :
    iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (EQV_E _ _)}.

  Global Instance eqv_soundness_X'_RefE_eqv eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V E MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := Typeof_E _))
      (f_algebra (FAlgebra := evalM_E))) (RefE_eqv _ _).
  Proof.
    econstructor; unfold iAlgebra; intros.
    eapply ind_alg_RefE_eqv; try eassumption;
      unfold soundness_X'_P, eval_soundness'_P; unfold bevalM; simpl; intros.
      (* Ref case *)
    intros; destruct a as [aE aT]; destruct (IHa IH) as [eqv_a_a' IHa'].
    split; intros.
    apply (inject_i (subGF := Sub_RefE_eqv_EQV_E _ _));
      econstructor; eauto.
    rewrite e_eq, e'_eq.
    simpl; repeat rewrite out_in_fmap.
    repeat rewrite wf_functor.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_Ref_F));
      rewrite (wf_algebra (WF_FAlgebra := WF_RefE_Typeof_F _));
        simpl fmap; simpl f_algebra; unfold RefE_fmap;
          unfold RefE_typeof, RefE_evalM.
    eapply Ref.eval_soundness_H; eauto with typeclass_instances.
    eapply IH with (pb := (gamma, gamma')).
    split; destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
    destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
      (* DeRef case *)
    intros; destruct a as [aE aT]; destruct (IHa IH) as [eqv_a_a' IHa'].
    split; intros.
    apply (inject_i (subGF := Sub_RefE_eqv_EQV_E _ _));
      econstructor 2; eauto.
    rewrite e_eq, e'_eq.
    simpl; repeat rewrite out_in_fmap.
    repeat rewrite wf_functor.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_Ref_F));
      rewrite (wf_algebra (WF_FAlgebra := WF_RefE_Typeof_F _));
        simpl fmap; simpl f_algebra; unfold RefE_fmap;
          unfold RefE_typeof, RefE_evalM.
    eapply Ref.eval_soundness_H0; eauto with typeclass_instances.
    eapply IH with (pb := (gamma, gamma')).
    split; destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
    destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
    intros; destruct a as [aE aT]; destruct b as [bE bT];
      destruct (IHa IH) as [eqv_a_a' IHa'];
        destruct (IHb IH) as [eqv_b_b' IHn']; simpl in *|-*.
    split; intros.
      apply (inject_i (subGF := Sub_RefE_eqv_EQV_E _ _));
        econstructor 3.
      eapply eqv_a_a'.
      eapply eqv_b_b'.
      rewrite e_eq; reflexivity.
      rewrite e'_eq; reflexivity.
      rewrite e_eq, e'_eq; simpl; repeat rewrite out_in_fmap.
    simpl; repeat rewrite out_in_fmap.
    repeat rewrite wf_functor.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_Ref_F));
      rewrite (wf_algebra (WF_FAlgebra := WF_RefE_Typeof_F _));
        simpl fmap; simpl f_algebra; unfold RefE_fmap;
          unfold RefE_typeof, RefE_evalM.
    eapply Ref.eval_soundness_H1; eauto with typeclass_instances.
    eapply IH with (pb := (gamma, gamma')).
    split; destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
    destruct WF_Gamma; eauto.
    apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
    generalize in_out_UP'_inverse; simpl; intros in_out';
      eapply (in_out' _ _ _ (proj2_sig a')).
      intros; eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_b_b'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
      eapply WF_eqv_environment_P_Sub; eauto.
      destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_b_b'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
  Qed.

  Global Instance WF_invertClos_WFV_Unit :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E MT V EQV_E _ WFV) (WFValue_Unit D V _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_Unit with (Sub_UnitValue_V := Sub_UnitValue_V)
      (Sub_UnitType_D := Sub_UnitType_D); unfold WF_invertClos_P; simpl; intros; auto; split.
    apply (inject_i (subGF := Sub_WFV_Unit_WFV)); econstructor; eauto.
    rewrite T'_eq; intros.
    unfold tunit in H0; simpl in H0; apply in_t_UP'_inject in H0.
    repeat rewrite wf_functor in H0; simpl in H0.
    elimtype False; eapply (inj_discriminate _ _ _ H0).
  Qed.

  Global Instance WF_invertClos_WFV_Loc :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E MT V EQV_E _ WFV) (WFValue_Loc D V _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_Loc with (Sub_LocValue_V := Sub_LocValue_V)
      (TypContext_S := TypContext_S)
      (Sub_RefType_D := Sub_RefType_D); unfold WF_invertClos_P; simpl; intros; auto; split.
    apply (inject_i (subGF := Sub_WFV_Loc_WFV)); econstructor; eauto.
    rewrite T'_eq; intros.
    unfold tref in H0; simpl in H0; apply in_t_UP'_inject in H0.
    repeat rewrite wf_functor in H0; simpl in H0.
    elimtype False; eapply (inj_discriminate _ _ _ H0).
  Qed.

  Context {SigGammaTypContext : SigGammaTypContextC D TypContext}.

  Global Instance WFV_Loc_Weaken' :
    iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V TypContext WFV) (WFValue_Loc D V _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_Loc with (Sub_LocValue_V := Sub_LocValue_V)
      (TypContext_S := TypContext_S)
      (Sub_RefType_D := Sub_RefType_D); unfold WFValue_Weaken'_P; simpl; intros; auto.
    apply (inject_i (subGF := Sub_WFV_Loc_WFV)); econstructor; eauto.
    rewrite SigLookup_GammaSet; auto.
  Qed.

  Global Instance WFV_Unit_Weaken' :
    iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V TypContext WFV) (WFValue_Unit D V _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_Unit with (Sub_UnitValue_V := Sub_UnitValue_V)
      (Sub_UnitType_D := Sub_UnitType_D); unfold WFValue_Weaken'_P; simpl; intros; auto.
    apply (inject_i (subGF := Sub_WFV_Unit_WFV)); econstructor; eauto.
  Qed.

End Lambda_Ref.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
