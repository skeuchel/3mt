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

Section ESoundRS.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  Variable E : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (E A)}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.

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


  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D))}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

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

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext-> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.
  Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME TypContext) WFVM}.

  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.
  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

  Context {wfvm_bind_alg :
    iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (EQV_E _ _)}.

  Class SigGammaTypContextC (TypContext : Set)
    {SigTypContext : SigTypContextC D TypContext}
    {GammaTypContext : GammaTypContextC D TypContext} : Set :=
    {SigLookup_GammaSet : forall Sigma env n,
      SigLookup (SigTypContextC := SigTypContext) D (GammaSet D Sigma env) n =
      SigLookup (SigTypContextC := SigTypContext) D Sigma n}.

  Context {SigGammaTypContext : SigGammaTypContextC TypContext}.

  Section State_Sound_X_Sec.

    Variable WFV' : (WFValue_i D V (list (Names.DType D) * list (Names.DType D)) -> Prop) ->
      WFValue_i D V (list (Names.DType D) * list (Names.DType D)) -> Prop.
    Context {funWFV' : iFunctor WFV'}.
    Variable WFVM' : (WFValueM_i D V MT ME (list (Names.DType D) * list (Names.DType D)) -> Prop) ->
      WFValueM_i D V MT ME (list (Names.DType D) * list (Names.DType D)) -> Prop.
    Variable funWFVM' : iFunctor WFVM'.

    Global Instance SigGamma_GammaTypContext : GammaTypContextC D (list (DType D) * list (DType D)) :=
      {| Gamma := @snd _ _;
        GammaSet := fun Sigma env => (fst Sigma, env);
        GammaInsert := fun T Sigma => (fst Sigma, insert _ T (snd Sigma))|}.
    Proof.
      unfold id; simpl; intros; auto.
      intros; destruct Sigma; auto.
      intros; destruct Sigma; simpl in *|-*; subst; auto.
    Defined.

    Global Instance SigGamma_GammaTypContextCE : ConsExtensionC (list (DType D) * list (DType D)) :=
      {| ConsExtension := fun gamma' gamma =>
        (forall n T, lookup (fst gamma) n = Some T -> lookup (fst gamma') n = Some T ) /\
        snd gamma = snd gamma' |}.
    Proof.
      (* ConsExtension_id *)
      intros; destruct Sigma; eauto.
      (* ConsExtension_trans *)
      intros; destruct Sigma; destruct Sigma'; destruct Sigma''; simpl in *|-*;
        split; eauto; destruct H; destruct H0; eauto; congruence.
    Defined.

    Global Instance SigGamma_GammaTypContextGCE :
      GammaConsExtensionC D (list (DType D) * list (DType D)) (SigGamma_GammaTypContextCE)
      (SigGamma_GammaTypContext).
    Proof.
      econstructor; eauto; intros; destruct Sigma; destruct Sigma'; simpl.
      destruct H; simpl in *|-*; auto.
    Defined.

  Global Instance SigGamma_WF_EnvC : WF_EnvC V (list (Names.DType D) * list (Names.DType D)) :=
    {| WF_Env := fun env Sigma =>
      P2_Env (WFValueC _ _ _ WFV' Sigma) env (fst Sigma) |}.

  Global Instance SigGamma_S : SigTypContextC D (list (Names.DType D) * list (Names.DType D)) :=
    {| SigLookup := fun Sigma => lookup (fst Sigma);
      SigInsert := fun T Sigma => (insert _ T (fst Sigma), snd Sigma)|}.

    Global Instance SigGamma_SCE : SigConsExtensionC D (list (Names.DType D) * list (Names.DType D)) _ _.
    Proof.
      constructor.
    (* ConsExtension_SigLookup *)
      destruct Sigma; destruct Sigma'; simpl; intros; eapply H; auto.
    (* ConsExtension_SigInsert *)
      simpl; intros; split; auto.
      intros; erewrite lookup_Some_insert; eauto.
    Qed.

    Global Instance SigGamma_SigGammaTypContextC :
      @SigGammaTypContextC (list (Names.DType D) * list (Names.DType D))
      SigGamma_S SigGamma_GammaTypContext.
    Proof.
      econstructor.
      intros; simpl; auto.
    Qed.

  Context {WFV_Weaken_WFV' : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV') WFV'}.
  Context {WFV_Weaken'_WFV' : iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P _ _ _ WFV') WFV'}.

  Global Instance SigGamma_Sig_WF_EnvC : Sig_WF_EnvC D V
     (list (DType D) * list (DType D)) WFV' SigGamma_WF_EnvC SigGamma_S.
  Proof.
    constructor; simpl; intros.
      (* WF_EnvLookup *)
    apply (P2_Env_lookup' _ _ _ _ _ H); auto.
      (* WF_EnvInsertLookup *)
    unfold Value, DType, Names.DType in *.
    rewrite (P2_Env_length _ _ _ _ _ H); apply lookup_insert.
      (* WF_EnvInsert *)
    apply P2_Env_insert; eauto.
    eapply P2_Env_P_P'; eauto.
    intros; apply (WFV_Weaken D V _ WFV' _ _ H1); simpl; split; auto.
    simpl; intros; erewrite lookup_Some_insert; eauto.
      (* WF_EnvReplace *)
    eapply P2_Env_replace_el; eauto.
  Qed.

  Definition State_Sound_X_P (i : WFValueM_i D V MT ME _ ) :=
    forall T gamma'' env
      (WF_env : WF_Environment _ _ _ WFV' (wfvm_S _ _ _ _ _ i) env (fst (wfvm_S _ _ _ _ _ i)))
      (WF_gamma'' : WF_Environment _ _ _ WFV' (wfvm_S _ _ _ _ _ i) gamma'' (snd (wfvm_S _ _ _ _ _ i))),
      wfvm_T _ _ _ _ _ i = return_ T ->
      (exists env', put env >> local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = put env' >> fail) \/
        exists v : Value V,
          exists env' : Env (Value V),
          exists Sigma' : list (DType D) * list (DType D),
            ConsExtension Sigma' (wfvm_S _ _ _ _ _ i) /\
            (put env) >> local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = (put env') >> return_ (M := ME) v /\
          WFValueC _ _ _ WFV' Sigma' v T /\
          WF_Environment D V _ WFV' Sigma' env' (fst Sigma').

  Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.

  Inductive State_Sound_X_Name := state_sound_X_name.

  Context {soundness_X'_alg :
    forall eval_rec,
      iPAlgebra soundness_X'_Name
      (soundness_X'_P D V E MT ME _ EQV_E WFVM' (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := evalM_E))) (EQV_E _ _)}.
  Context {State_Sound_X_WFVM : iPAlgebra State_Sound_X_Name State_Sound_X_P WFVM'}.

  Context {WFV_proj1_b_WFV' : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.
  Context {Sub_WFVM_Bot_WFVM' : Sub_iFunctor (WFValueM_Bot _ _ _ _ _) WFVM'}.

  Theorem eval_State_Sound_X :
    forall (n : nat) Sigma gamma gamma' gamma'' e' e'',
      E_eqvC E EQV_E gamma' gamma e'' e' ->
      forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
        exists T, lookup gamma b = Some T)
      (WF_gamma'' : WF_Environment _ _ _ WFV' Sigma gamma'' gamma)
      (WF_gamma2 : List.length gamma = List.length gamma')
      (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
      (WF_Sigma : Gamma _ Sigma = gamma) (T : DType D)
      (env : Env (Names.Value V))
      (WF_env : WF_Environment _ _ _ WFV' Sigma env (fst Sigma)),
      typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e') = return_ T ->
      (exists env', put env >>
        local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = put env' >> fail) \/
        exists v : Value V,
          exists env' : Env (Value V),
          exists Sigma' : list (DType D) * list (DType D),
            ConsExtension Sigma' Sigma /\
          put env >> local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') =
          put env' >> return_ (M := ME) v /\ WFValueC _ _ _ WFV' Sigma' v T
          /\ WF_Environment D V _ WFV' Sigma' env' (fst Sigma').
  Proof.
    intros.
    intros; eapply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := State_Sound_X_WFVM))
      _ (eval_soundness_X' D V E MT ME _ EQV_E WFVM' n _ _ _ _ H Sigma WF_gamma WF_gamma2 WF_gamma' WF_Sigma));
    simpl in *|-*; unfold DType in *|-*; eauto;
      simpl in H0; auto.
    rewrite WF_Sigma; auto.
  Qed.

  Global Instance State_Sound_WFVM_base :
    iPAlgebra State_Sound_X_Name State_Sound_X_P (WFValueM_base D V MT ME _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV')
      (Fail_MT := _) (Monad_ME := _);
      try assumption; unfold Pure_Sound_X_P; intros; right.
    (* WFVM_Return' *)
    simpl; rewrite local_return; exists v; exists env; exists Sigma; repeat split; simpl in *; auto.
    destruct H1 as [mt' mt'_eq]; subst.
    destruct (MT_eq_dec _ mt') as [[s mt'_eq] | mt'_eq]; subst.
    rewrite fmap_return in H2; apply inj_return in H2; subst.
    destruct s as [T0 T0_UP']; simpl in *.
    destruct T0; apply (WFV_proj1_b D V _ WFV' _ _ H0); simpl; auto.
    rewrite fmap_fail in H2.
    elimtype False; eapply (FailMonad_Disc MT _ _ T0 (fail (A := Fix D)));
      unfold wbind; rewrite bind_fail; eauto with typeclass_instances.
      (* WFVM_Untyped' *)
    simpl in H0; apply sym_eq in H0.
    elimtype False; eapply (FailMonad_Disc MT _ _ T mt); auto.
  Qed.

  Global Instance State_Sound_X_WFVM_Environment :
    iPAlgebra State_Sound_X_Name State_Sound_X_P (WFValueM_Environment D MT V ME _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_Environment with (WFV := WFV')
      (TypContextCE := SigGamma_GammaTypContextCE) (Fun_MT := Fun_MT) (Mon_MT := Mon_MT)
      (GammaTypContext := SigGamma_GammaTypContext)
      (Environment_ME := Environment_ME); try eassumption;
        unfold State_Sound_X_P; simpl; intros.
      (* WFVM_Local *)
    destruct (H0 gamma'' WF_gamma'' _ _ env WF_env WF_gamma'' H1) as
      [[env' eval_fail] | [v [env' [Sigma' [Sub_Sig'_Sig [eval_k [WF_v_T0 WF_env'_Sigma']]]]]]].
    left; exists env'; generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit; auto.
    right; exists v; exists env'; exists Sigma'; repeat split; auto.
    apply Sub_Sig'_Sig.
    apply Sub_Sig'_Sig.
    generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit.
    apply eval_k; auto.
      (* WFVM_Ask *)
    rewrite local_bind, local_local; unfold Basics.compose.
    destruct Sigma; simpl in *|-*.
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV'
         (l, Gamma') env l) as WF_Sigma_env by
    (eapply P2_Env_P_P'; try eassumption; intros;
      generalize (WFV_Weaken' _ _ _ WFV' _ H4 Gamma'); simpl; auto).
    destruct (H1 _ _ _ WF_Sigma_env (H0 _ WF_gamma'') (refl_equal _)) as
      [[env' eval_fail] | [v [env' [Sigma' [Sub_Sig'_Sig [eval_m [WF_v_T' WF_env'_Sigma']]]]]]].
    left; exists env'; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite associativity, eval_fail, <- associativity, bind_fail; auto.
    destruct Sub_Sig'_Sig as [Sub_Sig'_Sig Sig'_eq].
    assert (WFValueC D V (list (Names.DType D) * list (Names.DType D)) WFV'
      (fst Sigma', l0) v T') as WF_v_T'' by
    (generalize (WFV_Weaken' _ _ _ WFV' _ WF_v_T' l0); simpl; auto).
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV'
    (fst Sigma', l0) env' (fst (fst Sigma', l0))) as WF_env''_Sigma'
    by (eapply P2_Env_P_P'; try eassumption; intros;
      generalize (WFV_Weaken' _ _ _ WFV' _ H4 l0); simpl; auto).
    assert (ConsExtension (fst Sigma', l0) (l, l0)) as Sub_Sig'_Sig'' by
      (constructor; simpl; auto).
    destruct (H2 (fst Sigma', l0) _ (conj Sub_Sig'_Sig (refl_equal _)) WF_v_T'' _ _ _ WF_env''_Sigma'
      (WF_Environment_Weaken D V _ WFV' _ _ _ WF_gamma'' _ Sub_Sig'_Sig'') H3)
    as [eval_fail | [v' [env'' [Sigma'' [Sub_Sig''_Sig' [eval_k [WF_v'_T0 WF_env''_Sigma'']]]]]]].
    left; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite associativity; rewrite eval_m, <- associativity, <- left_unit; auto.
    right; exists v'; exists env''; exists Sigma''; repeat split; auto.
    intros; eapply Sub_Sig''_Sig'; auto.
    apply Sub_Sig''_Sig'.
    unfold wbind, Env in *|-*;
      rewrite associativity; rewrite eval_m, <- associativity, <- left_unit; auto.
  Qed.

  Variable put_local : forall (A : Set) sigma f (m : ME A),
    put (M := ME) sigma >> (local f m) = local f (put sigma >> m).

  Global Instance State_Sound_X_WFVM_State' :
    iPAlgebra State_Sound_X_Name State_Sound_X_P (WFValueM_State D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_State with
      (TypContextCE := SigGamma_GammaTypContextCE) (TypContext_WFE := SigGamma_WF_EnvC)
      (State_M := StateM_ME);
      try eassumption; unfold State_Sound_X_P; simpl; intros.
    (* WFVM_Get *)
    destruct (H0 env WF_env _ _ _ WF_env WF_gamma'' H1 ) as
      [[env' eval_fail] | [v [env' [Sigma' [Sub_Sig'_Sig [eval_k [WF_v_T0 WF_env'_Sigma']]]]]]].
    left; exists env'; rewrite put_local, <- eval_fail.
    generalize put_get as put_get'; intros; unfold wbind in *|-*;
      rewrite associativity, put_get', <- associativity, put_local;
        apply f_equal; apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    right; exists v; exists env'; exists Sigma'; repeat split; auto.
    eapply Sub_Sig'_Sig.
    eapply Sub_Sig'_Sig.
    generalize put_get as put_get'; intros; unfold wbind in *|-*;
      rewrite put_local, associativity, put_get', <- associativity, <- put_local, <- eval_k;
        apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    (* WFVM_Put *)
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV'
      Sigma' gamma'' (snd Sigma')) as WF_gamma''' by
    (destruct H1 as [H1' H1]; rewrite <- H1; eapply (WF_Environment_Weaken D V _ WFV');
      eauto; split; eauto).
    destruct (H2 _ _ _ H0 WF_gamma'''  H3) as
      [[env' eval_fail] | [v [env' [Sigma'' [Sub_Sig''_Sig' [eval_k [WF_v_T0 WF_env'_Sigma'']]]]]]].
    left; exists env'; rewrite put_local.
    generalize put_put as put_put'; intros; unfold wbind in *|-*.
      rewrite associativity, put_put', <- put_local, <- eval_fail; auto.
    right; exists v; exists env'; exists Sigma''; repeat split; auto.
    intros; eapply Sub_Sig''_Sig'; eapply H1; eauto.
    rewrite <- (proj2 Sub_Sig''_Sig'); eapply H1.
    generalize put_put as put_put'; intros; unfold wbind in *|-*;
      rewrite put_local, associativity, put_put', <- put_local; auto.
  Qed.

  Context {FailEnvM : FailEnvironmentMonad (Env (Value V)) ME}.

  Global Instance State_Sound_X_WFVM_Bot :
    iPAlgebra State_Sound_X_Name State_Sound_X_P (WFValueM_Bot D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; eapply ind_alg_WFVM_Bot;
      try eassumption; unfold State_Sound_X_P; simpl; intros.
    (* WFVM_fail *)
    left; exists env; rewrite local_fail; auto.
  Qed.

  End State_Sound_X_Sec.

End ESoundRS.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
