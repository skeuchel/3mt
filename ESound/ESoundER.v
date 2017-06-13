Require Import FunctionalExtensionality.
Require Import List.
Require Import FJ_tactics.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffExcept.
Require Import EffReader.

Section ESoundER.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  Variable E : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (E A)}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.

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

  Context {evalM_E : FAlgebra EvalName (Names.Exp (E nat)) (evalMR V ME) (E nat)}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {GammaTypContext : GammaTypContextC D TypContext}.
  Context {TypContext_GCE : GammaConsExtensionC _ TypContext _ _}.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.

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
        (WFV_Weaken' _ _ _ WFV' _ WF_v_T0 Sigma) _ _
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

End ESoundER.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
