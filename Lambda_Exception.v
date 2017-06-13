Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Exception.
Require Import Lambda.

Section Lambda_Exception.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_LType_F : WF_Functor _ _ (Sub_LType_D) _ _}.

  Variable E : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (E A)}.
  Context {Sub_ExceptE_E : forall A, ExceptE D :<: E A}.
  Context {Sub_Lambda_E : forall A, Lambda D A :<: E A}.
  Context {WF_Sub_ExceptE_F : forall A, WF_Functor _ _ (Sub_ExceptE_E A) _ _}.
  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_E A) _ _}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Context {WF_Sub_ClosValue_V : WF_Functor _ _ (Sub_ClosValue_V) _ _}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
  Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_ME : Functor ME}.
  Context {Mon_ME : Monad ME}.
  Context {Environment_ME : Environment ME (list (Names.Value V))}.
  Context {Exception_ME : Exception ME Datatypes.unit}.
  Context {Fail_ME : FailMonad ME}.
  Context {Reasonable_ME : Reasonable_Monad ME}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D))}.
  Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
  Context {WF_ExceptE_Typeof_E : forall T, @WF_FAlgebra TypeofName _ _ (ExceptE D) (E _)
    (Sub_ExceptE_E _) (MAlgebra_typeof_ExceptE _ MT _) (Typeof_E T)}.
  Context {WF_Lambda_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ (Lambda D _) (E _)
    (Sub_Lambda_E _) (MAlgebra_typeof_Lambda D MT _) (Typeof_E T)}.

  Context {evalM_E : FAlgebra EvalName (Names.Exp (E nat)) (evalMR V ME) (E nat)}.
  Context {WF_ExceptE_eval_E : @WF_FAlgebra EvalName _ _ (ExceptE D) (E nat)
    (Sub_ExceptE_E _) (MAlgebra_evalM_ExceptE D V ME _) evalM_E}.
  Context {WF_eval_Lambda_E :
    @WF_FAlgebra EvalName _ _ (Lambda D nat) (E nat)
    (Sub_Lambda_E nat) (MAlgebra_evalM_Lambda D E V ME) evalM_E}.

  Inductive Exception_eqv (A B : Set) (A_i : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
  | Throw_eqv : forall (gamma : Env _) gamma' t e e',
    proj1_sig e = throw' D (E A) t ->
    proj1_sig e' = throw' D (E B) t ->
    Exception_eqv A B A_i (mk_eqv_i _ _ _ gamma gamma' e e')
  | Catch_eqv : forall (gamma : Env _) gamma' ce ce' e e' h h',
    A_i (mk_eqv_i _ _ _ gamma gamma' e e') ->
    (forall t, A_i (mk_eqv_i _ _ _ gamma gamma' (h t) (h' t))) ->
    proj1_sig ce = proj1_sig (catch'' D (E A) e h) ->
    proj1_sig ce' = proj1_sig (catch'' D (E B) e' h') ->
    Exception_eqv A B A_i (mk_eqv_i _ _ _ gamma gamma' ce ce').

  Definition ind_alg_Exception_eqv
    (A B : Set)
    (P : eqv_i E A B -> Prop)
    (H : forall gamma gamma' t e e' e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    (H0 : forall gamma gamma' ce ce' e e' h h'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (IHb : forall t, P (mk_eqv_i _ _ _ gamma gamma' (h t) (h' t)))
      ce_eq ce'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' ce ce'))
    i (e : Exception_eqv A B P i) : P i :=
    match e in Exception_eqv _ _ _ i return P i with
      | Throw_eqv gamma gamma' t e e' e_eq e'_eq =>
        H gamma gamma' t e e' e_eq e'_eq
      | Catch_eqv gamma gamma' ce ce' e e' h h' eqv_e_e' eqv_h_h' ce_eq ce'_eq =>
        H0 gamma gamma' ce ce' e e' h h' eqv_e_e' eqv_h_h' ce_eq ce'_eq
    end.

    Definition Exception_eqv_ifmap (A B : Set)
      (A' B' : eqv_i E A B -> Prop) i (f : forall i, A' i -> B' i)
      (eqv_a : Exception_eqv A B A' i) : Exception_eqv A B B' i :=
      match eqv_a in Exception_eqv _ _ _ i return Exception_eqv _ _ _ i with
        | Throw_eqv gamma gamma' t e e' e_eq e'_eq =>
          Throw_eqv _ _ _ gamma gamma' t e e' e_eq e'_eq
        | Catch_eqv gamma gamma' ce ce' e e' h h' eqv_e_e' eqv_h_h' ce_eq ce'_eq =>
          Catch_eqv _ _ _ gamma gamma' ce ce' e e' h h' (f _ eqv_e_e') (fun t => f _ (eqv_h_h' t)) ce_eq ce'_eq
      end.

    Global Instance iFun_Exception_eqv A B : iFunctor (Exception_eqv A B).
      constructor 1 with (ifmap := Exception_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; unfold id; eauto.
    Defined.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {Sub_Lambda_eqv_EQV_E : forall A B, Sub_iFunctor (Lambda_eqv _ _ A B) (EQV_E A B)}.
  Context {Sub_Except_eqv_EQV_E : forall A B : Set,
    Sub_iFunctor (Exception_eqv A B) (EQV_E A B)}.

  Global Instance EQV_proj1_Lambda_eqv :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (Exception_eqv _ _).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; apply ind_alg_Exception_eqv;
      unfold EQV_proj1_P; try eassumption; simpl; intros; subst.
    apply (inject_i (subGF := Sub_Except_eqv_EQV_E A B)); econstructor; simpl; eauto.
    apply (inject_i (subGF := Sub_Except_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
    destruct e; destruct e'; eapply IHa; eauto.
    intros; generalize (IHb t); intros IHb'; destruct (h t); destruct (h' t);
      eapply IHb'; eauto.
  Qed.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {GammaTypContext : GammaTypContextC D TypContext}.
  Context {TypContext_GCE : GammaConsExtensionC _ TypContext _ _}.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.
  Context {Sub_WFV_Clos_WFV : Sub_iFunctor (WFValue_Clos D E MT V EQV_E _) WFV}.

  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.
  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Except_WFVM : Sub_iFunctor (WFValueM_Except D V MT ME _) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.

  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (EQV_E _ _)}.
  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

  Global Instance eqv_soundness_X'_Except_eqv eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V E MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := Typeof_E _))
      (f_algebra (FAlgebra := evalM_E))) (Exception_eqv _ _).
  Proof.
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_Exception_eqv; try eassumption;
        unfold soundness_X'_P, eval_soundness'_P; unfold bevalM; simpl; intros.
      (* throw case *)
      split; intros.
      apply (inject_i (subGF := Sub_Except_eqv_EQV_E _ _));
        econstructor; eauto.
      rewrite e_eq, e'_eq.
      unfold throw', throw''; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_ExceptE_eval_E));
        rewrite (wf_algebra (WF_FAlgebra := WF_ExceptE_Typeof_E _));
          simpl fmap; simpl f_algebra; unfold ExceptE_fmap; simpl.
      apply (inject_i (subGF := Sub_WFVM_Except_WFVM)); econstructor.
      (* catch case *)
      intros; destruct e as [eE eT]; destruct (h tt) as [hE hT];
        destruct (IHa IH) as [eqv_e_e' IHe];
          destruct (IHb tt IH) as [eqv_h_h' IHh']; simpl in *|-*.
      split; intros.
      apply (inject_i (subGF := Sub_Except_eqv_EQV_E _ _));
        econstructor 2.
      eapply eqv_e_e'.
      intros; eapply (IHb t IH).
      eauto.
      eauto.
      rewrite ce_eq, ce'_eq.
      unfold catch', catch''; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_ExceptE_eval_E));
        rewrite (wf_algebra (WF_FAlgebra := WF_ExceptE_Typeof_E _));
          simpl fmap; simpl f_algebra; unfold ExceptE_fmap.
      intros; apply Exception.eval_soundness_H0 with (TypContextCE := TypContextCE);
        eauto with typeclass_instances.
      eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_e_e'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig e')).
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_e_e'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig e')).
      intros.
      eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      destruct n; destruct (h tt);
        apply (EQV_proj1 _ EQV_E _ _ _ eqv_h_h'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig (h' tt))).
      eapply WF_eqv_environment_P_Sub; eauto.
      destruct WF_Gamma; eauto.
      destruct n; destruct (h tt);
        apply (EQV_proj1 _ EQV_E _ _ _ eqv_h_h'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig (h' tt))).
  Qed.

  Section Except_Sound_X_Sec.

    Variable WFV' : (WFValue_i D V (list (Names.DType D)) -> Prop) -> WFValue_i D V (list (Names.DType D)) -> Prop.
    Context {funWFV' : iFunctor WFV'}.
    Variable WFVM' : (WFValueM_i D V MT ME (list (Names.DType D)) -> Prop) ->
      WFValueM_i D V MT ME (list (Names.DType D)) -> Prop.
    Variable funWFVM' : iFunctor WFVM'.

  Definition Except_Sound_X_P (i : WFValueM_i D V MT ME _) :=
    forall T gamma''
      (WF_gamma'' : WF_Environment _ _ _ WFV' (wfvm_S _ _ _ _ _ i) gamma'' (wfvm_S _ _ _ _ _ i)),
      wfvm_T _ _ _ _ _ i = return_ T ->
      (local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = fail) \/
      (exists t, local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = throw t) \/
      exists v : Value V,
        local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = return_ (M := ME) v /\
        WFValueC _ _ _ WFV' (wfvm_S _ _ _ _ _ i) v T.

  Context {WFV_proj1_b_WFV' : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.

  Inductive Except_Sound_X_Name := except_sound_X_name.

  Global Instance Except_Sound_WFVM_base' :
    iPAlgebra Except_Sound_X_Name Except_Sound_X_P (WFValueM_base D V MT ME _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV')
      (Fail_MT := _) (Monad_ME := _);
      try assumption; unfold Except_Sound_X_P; intros; repeat right.
    (* WFVM_Return' *)
    simpl; rewrite local_return; exists v; repeat split; simpl in *; auto.
    destruct H1 as [mt' mt'_eq]; subst.
    destruct (MT_eq_dec _ mt') as [[s s_eq] | s_eq]; subst.
    rewrite fmap_return in H2.
    apply inj_return in H2; subst.
    simpl in *; subst; auto.
    destruct s as [T0 T0_UP']; simpl in *.
    destruct T0; apply (WFV_proj1_b D V _ WFV' _ _ H0); simpl; auto.
    failmonaddisc.
      (* WFVM_Untyped' *)
    simpl in H0; apply sym_eq in H0.
    elimtype False; eapply FailMonad_Disc with (M := MT) (a := T) (mb := mt); auto.
  Qed.

  Context {WFV_Weaken'_WFV : iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P _ _ _ WFV') WFV'}.

  Global Instance Except_Sound_X_WFVM_Environment :
    iPAlgebra Except_Sound_X_Name Except_Sound_X_P
    (WFValueM_Environment (TypContextCE := GammaTypContextCE D) D MT V ME _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_Environment with (MT := MT)
      (Fun_MT := Fun_MT) (Mon_MT := Mon_MT) (WFV := WFV')
      (TypContextCE := GammaTypContextCE D)
      (GammaTypContext := PNames.GammaTypContext D)
      (Environment_ME := Environment_ME); try eassumption;
        unfold Except_Sound_X_P; simpl; intros.
      (* WFVM_Local *)
    destruct (H0 gamma'' WF_gamma'' _ _ WF_gamma'' H1) as
      [eval_fail | [eval_throw | [v [eval_k WF_v_T0]]]].
    left; generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit; auto.
    right; left; generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit; auto.
    right; right; exists v; repeat split; auto.
    generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit.
    apply eval_k; auto.
      (* WFVM_Ask *)
    rewrite local_bind, local_local; unfold Basics.compose.
    destruct (H1 _ _ (H0 _ WF_gamma'') (refl_equal _)) as
      [eval_fail | [[t eval_throw] | [v [eval_m WF_v_T0]]]].
    left; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite eval_fail, bind_fail; auto.
    right; left; exists t; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite eval_throw, bind_throw; auto.
    unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite eval_m, <- left_unit; destruct (H2 _ _ (refl_equal _)
        (WFV_Weaken' _ _ _ WFV' funWFV' _ WF_v_T0 Sigma) _ _
        WF_gamma'' H3)
      as [eval_fail | [[t eval_throw] | [v' [eval_k WF_v'_T0]]]].
    auto.
    right; left; eexists _; eauto.
    repeat right; exists v'; repeat split; auto.
  Qed.

  Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (env : list (Names.Value (Fun_V := Fun_V) V)),
    (exists a : A, local (fun _ => env) mte = return_ (Monad := Mon_ME) a) \/
    (local (fun _ => env) mte = fail) \/
    (local (fun _ => env) mte = throw tt)}.

  Variable local_throw : forall (A : Set) f t,
    local f (throw t) = throw t (A := A).
  Variable local_catch : forall (A : Set) e h f,
    local f (catch (A := A) e h) = catch (local f e) (fun t => local f (h t)).
  Variable catch_fail : forall (A : Set) h,
    catch (A := A) fail h = fail.
  Variable throw_neq_fail : forall (A : Set) t,
    throw t <> fail (A := A).

  Global Instance Except_Sound_X_WFVM_Except :
    iPAlgebra Except_Sound_X_Name Except_Sound_X_P
    (WFValueM_Except (TypContextCE := GammaTypContextCE D) D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_Except with (Fail_MT := Fail_MT)
      (TypContextCE := GammaTypContextCE D)
      (Exception_ME := Exception_ME) (eq_DType_DT := eq_DType_DT);
      try assumption; unfold Except_Sound_X_P; simpl; intros.
      (* throw case *)
    simpl; right; left; exists tt; apply local_throw.
    (* catch case *)
    destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
    destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
    repeat rewrite <- left_unit in H2.
    caseEq (eq_DType _ (proj1_sig T') T''); rewrite H3 in H2.
    destruct (H0 _ _ WF_gamma'' H2) as
      [eval_fail | [[t eval_throw] | [v [eval_k WF_v_T0]]]].
    rewrite local_bind, local_catch.
    destruct (ME_eq_dec' _ e' gamma'') as [[v'' e'_eq] | [e'_eq | e'_eq]];
      unfold Env in *|-*; rewrite e'_eq in *|-*.
    left; rewrite catch_return, <- left_unit;
      rewrite local_bind, e'_eq, <- left_unit in eval_fail; auto.
    rewrite catch_fail, bind_fail; auto.
    rewrite local_bind, e'_eq, bind_throw in eval_fail;
      elimtype False; eapply throw_neq_fail; eauto.
    rewrite local_bind, local_catch.
    destruct (ME_eq_dec' _ e' gamma'') as [[v'' e'_eq] | [e'_eq | e'_eq]];
      unfold Env in *|-*; rewrite e'_eq in *|-*.
    right; left; rewrite catch_return, <- left_unit;
      rewrite local_bind, e'_eq, <- left_unit in eval_throw; eauto.
    rewrite local_bind, e'_eq, bind_fail in eval_throw;
      elimtype False; eapply throw_neq_fail; eauto.
    rewrite catch_throw', <- local_bind.
    destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst.
    repeat rewrite <- left_unit in H1, H2.
    destruct (MT_eq_dec _ (kT c T'')) as [[d kTcT''_eq] | kTcT''_eq].
    destruct (H1 tt _ (refl_equal _) _ _ WF_gamma'' kTcT''_eq) as
      [eval_fail | [[t' eval_throw'] | [v [eval_k WF_v_T0]]]];
      eauto.
    repeat right; exists v; repeat split; eauto.
    destruct T; apply (WFV_proj1_b D V _ WFV' _ _ WF_v_T0); simpl; auto.
    generalize (kt_eq _ _ (eq_DType_eq _ _ _ H3)).
      repeat rewrite <- left_unit;
      rewrite H2, kTcT''_eq; simpl;
      repeat rewrite fmap_return;
      intros x_eq; apply inj_return in x_eq; auto.
    elimtype False; generalize (kt_eq _ _ (eq_DType_eq _ _ _ H3));
      repeat rewrite <- left_unit; rewrite H2, kTcT''_eq; simpl;
      rewrite fmap_return; rewrite fmap_fail; intros x_eq.
    failmonaddisc.
    failmonaddisc.
    rewrite local_bind, local_catch.
    destruct (ME_eq_dec' _ e' gamma'') as [[v'' e'_eq] | [e'_eq | e'_eq]];
      unfold Env in *|-*; rewrite e'_eq in *|-*.
    repeat right; rewrite catch_return, <- left_unit;
      rewrite local_bind, e'_eq, <- left_unit in eval_k; eauto.
    rewrite catch_fail, bind_fail; auto.
    rewrite local_bind, e'_eq, bind_throw in eval_k.
    elimtype False; eapply Exception_Disc with (M := ME) (a := v) (mb := return_ tt);
    eauto; unfold wbind; rewrite <- left_unit; eauto.
    destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
    destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
    destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
  Qed.

  Context {FailEnvM : FailEnvironmentMonad (Env (Value V)) ME}.

  Global Instance Except_Sound_X_WFVM_Bot :
    iPAlgebra Except_Sound_X_Name Except_Sound_X_P (WFValueM_Bot D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; eapply ind_alg_WFVM_Bot;
      try eassumption; unfold Except_Sound_X_P; simpl; intros.
    (* WFVM_fail *)
    left; rewrite local_fail; auto.
  Qed.

  Context {soundness_X'_alg :
    forall eval_rec,
      iPAlgebra soundness_X'_Name
      (soundness_X'_P D V E MT ME _ EQV_E WFVM' (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := evalM_E))) (EQV_E _ _)}.
  Context {Except_Sound_X_WFVM : iPAlgebra Except_Sound_X_Name Except_Sound_X_P WFVM'}.

  Context {Sub_WFVM_Bot_WFVM' : Sub_iFunctor (WFValueM_Bot _ _ _ _ (list (DType D))) WFVM'}.

  Theorem Except_Sound_X :
    forall (n : nat) Sigma gamma gamma' gamma'' e' e'',
      E_eqvC E EQV_E gamma' gamma e'' e' ->
      forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
        exists T, lookup gamma b = Some T)
      (WF_gamma'' : WF_Environment _ _ _ WFV' Sigma gamma'' gamma)
      (WF_gamma2 : List.length gamma = List.length gamma')
      (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
      (WF_Sigma : Gamma D Sigma = gamma) (T : DType D),
      typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e') = return_ T ->
      (local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = fail) \/
      (exists t, local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = throw t) \/
        exists v : Value V,
          local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') =
          return_ (M := ME) v /\ WFValueC _ _ _ WFV' Sigma v T.
  Proof.
    intros.
    intros; eapply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := Except_Sound_X_WFVM))
      _ (eval_soundness_X' D V E MT ME _ EQV_E WFVM' n _ _ _ _ H Sigma WF_gamma WF_gamma2 WF_gamma' WF_Sigma));
    simpl in *|-*; unfold DType in *|-*; eauto;
    simpl in H0; eauto.
    unfold id in *|-*; subst; eauto.
  Qed.

  End Except_Sound_X_Sec.

End Lambda_Exception.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
