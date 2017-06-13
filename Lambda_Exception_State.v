Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Exception.
Require Import Lambda.
Require Import Ref.
Require Import Lambda_Ref.
Require Import Lambda_Exception.
Require Import Ref_Exception.

Section Lambda_Exception_State.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_LType_F : WF_Functor _ _ (Sub_LType_D) _ _}.
  Context {Sub_RefType_D : RefType :<: D}.
  Context {Sub_UnitType_D : UnitType :<: D}.
  Context {WF_Sub_RefType_D : WF_Functor _ _ (Sub_RefType_D) _ _}.
  Context {WF_Sub_UnitType_D : WF_Functor _ _ (Sub_UnitType_D) _ _}.

  Variable E : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (E A)}.
  Context {Sub_ExceptE_E : forall A, ExceptE D :<: E A}.
  Context {Sub_Lambda_E : forall A, Lambda D A :<: E A}.
  Context {Sub_RefE_E : forall A, RefE :<: E A}.
  Context {WF_Sub_RefE_F : forall A, WF_Functor _ _ (Sub_RefE_E A) _ _}.
  Context {WF_Sub_ExceptE_F : forall A, WF_Functor _ _ (Sub_ExceptE_E A) _ _}.
  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_E A) _ _}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_LocValue_V : LocValue :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Context {Sub_UnitValue_V : UnitValue :<: V}.
  Context {WF_Sub_LocValue_V : WF_Functor _ _ (Sub_LocValue_V) _ _}.
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
  Context {StateM_ME : StateM ME (list (Names.Value V))}.
  Context {Reasonable_ME : Reasonable_Monad ME}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D))}.
  Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
  Context {WF_ExceptE_Typeof_E : forall T, @WF_FAlgebra TypeofName _ _ (ExceptE D) (E _)
    (Sub_ExceptE_E _) (MAlgebra_typeof_ExceptE _ MT _) (Typeof_E T)}.
  Context {WF_Lambda_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ (Lambda D _) (E _)
    (Sub_Lambda_E _) (MAlgebra_typeof_Lambda D MT _) (Typeof_E T)}.
  Context {WF_RefE_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ RefE (E _)
    (Sub_RefE_E _) (MAlgebra_typeof_RefE D MT _) (Typeof_E T)}.

  Context {evalM_E : FAlgebra EvalName (Names.Exp (E nat)) (evalMR V ME) (E nat)}.
  Context {WF_ExceptE_eval_E : @WF_FAlgebra EvalName _ _ (ExceptE D) (E nat)
    (Sub_ExceptE_E _) (MAlgebra_evalM_ExceptE D V ME _) evalM_E}.
  Context {WF_eval_Lambda_E :
    @WF_FAlgebra EvalName _ _ (Lambda D nat) (E nat)
    (Sub_Lambda_E nat) (MAlgebra_evalM_Lambda D E V ME) evalM_E}.
  Context {WF_eval_Ref_F : @WF_FAlgebra EvalName _ _ RefE (E nat)
    (Sub_RefE_E _) (MAlgebra_evalM_RefE V ME _) evalM_E}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {Sub_Lambda_eqv_EQV_E : forall A B, Sub_iFunctor (Lambda_eqv _ _ A B) (EQV_E A B)}.

  Variable WFV : (WFValue_i D V (list (DType D) * list (DType D)) -> Prop) ->
    WFValue_i D V (list (DType D) * list (DType D)) -> Prop.
  Context {funWFV : iFunctor WFV}.
  Context {Sub_WFV_Clos_WFV : Sub_iFunctor (WFValue_Clos D E MT V EQV_E _) WFV}.
  Context {Sub_WFV_Loc_WFV : Sub_iFunctor (WFValue_Loc D V (list (DType D) * list (DType D))) WFV}.
  Context {Sub_WFV_Unit_WFV : Sub_iFunctor (WFValue_Unit D V _) WFV}.
  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

  Variable WFVM : (WFValueM_i D V MT ME (list (DType D) * list (DType D)) -> Prop) ->
    WFValueM_i D V MT ME (list (DType D) * list (DType D)) -> Prop.
  Context {funWFVM : iFunctor WFVM}.
  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Except_WFVM : Sub_iFunctor (WFValueM_Except D V MT ME _) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.
  Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME _
    (TypContext_WFE := SigGamma_WF_EnvC _ _ WFV)) WFVM}.

  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

  Definition Except_State_Sound_X_P (i : WFValueM_i D V MT ME _ ) :=
    forall T gamma'' env
      (WF_env : WF_Environment _ _ _ WFV (wfvm_S _ _ _ _ _ i) env (fst (wfvm_S _ _ _ _ _ i)))
      (WF_gamma'' : WF_Environment _ _ _ WFV (wfvm_S _ _ _ _ _ i) gamma'' (snd (wfvm_S _ _ _ _ _ i))),
      wfvm_T _ _ _ _ _ i = return_ T ->
      (exists env', put env >> local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = put env' >> fail) \/
      (exists t, exists env', exists Sigma',
        put env >> local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = put env' >> throw t
        /\ WF_Environment D V _ WFV Sigma' env' (fst Sigma') /\
        ConsExtension Sigma' (wfvm_S _ _ _ _ _ i)) \/
        exists v : Value V,
          exists env' : Env (Value V),
          exists Sigma' : list (DType D) * list (DType D),
            ConsExtension Sigma' (wfvm_S _ _ _ _ _ i) /\
            (put env) >> local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = (put env') >> return_ (M := ME) v /\
          WFValueC _ _ _ WFV Sigma' v T /\
          WF_Environment D V _ WFV Sigma' env' (fst Sigma').

  Inductive Except_State_Sound_X_Name := except_state_sound_X_name.

  Global Instance Except_State_Sound_WFVM_base :
    iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P (WFValueM_base D V MT ME _ WFV).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV)
      (Fail_MT := _) (Monad_ME := _);
      try assumption; unfold Except_State_Sound_X_P; intros; repeat right.
    (* WFVM_Return' *)
    simpl; rewrite local_return; exists v; exists env; exists Sigma;
      repeat split; simpl in *; auto.
    destruct H1 as [mt' mt'_eq]; subst.
    destruct (MT_eq_dec _ mt') as [[s mt'_eq] | mt'_eq]; subst.
    rewrite fmap_return in H2; apply inj_return in H2; subst.
    destruct s as [T0 T0_UP']; simpl in *.
    destruct T0; apply (WFV_proj1_b D V _ WFV _ _ H0); simpl; auto.
    failmonaddisc.
    (* WFVM_Untyped' *)
    simpl in H0; apply sym_eq in H0.
    elimtype False; eapply (FailMonad_Disc MT _ _ T mt); auto.
  Qed.

  Context {WFV_Weaken'_WFV : iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P _ _ _ WFV) WFV}.

  Global Instance Except_State_Sound_X_WFVM_Environment :
    iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P (WFValueM_Environment D MT V ME _ WFV).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_Environment with (WFV := WFV)
      (TypContextCE := SigGamma_GammaTypContextCE _) (Fun_MT := Fun_MT) (Mon_MT := Mon_MT)
      (GammaTypContext := _)
      (Environment_ME := Environment_ME); try eassumption;
        unfold Except_State_Sound_X_P; simpl; intros.
      (* WFVM_Local *)
    destruct (H0 gamma'' WF_gamma'' _ _ env WF_env WF_gamma'' H1) as
      [[env' eval_fail] |
        [[t [env' [Sigma' [eval_throw [WF_env'_Sigma' Sub_Sig_Sig']]]]] |
          [v [env' [Sigma' [Sub_Sig'_Sig [eval_m [WF_v_T0 WF_env'_Sigma']]]]]]]].
    left; generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit; eauto.
    right; left; generalize ask_query; unfold wbind; intro ask_query'.
    exists t; exists env'; exists Sigma';
      rewrite local_bind, local_ask, ask_query', <- left_unit; eauto.
    right; right; exists v; exists env'; exists Sigma'; repeat split; auto.
    intros; eapply Sub_Sig'_Sig; auto.
    intros; eapply Sub_Sig'_Sig.
    generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit.
    apply eval_m; auto.
      (* WFVM_Ask *)
    rewrite local_bind, local_local; unfold Basics.compose.
    destruct Sigma; simpl in *|-*.
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV
         (l, Gamma') env l) as WF_Sigma_env by
    (eapply P2_Env_P_P'; try eassumption; intros;
      generalize (WFV_Weaken' _ _ _ WFV funWFV _ H4 Gamma'); simpl; auto).
    destruct (H1 _ _ _ WF_Sigma_env (H0 _ WF_gamma'') (refl_equal _)) as
      [[env' eval_fail] |
        [[t [env' [Sigma' [eval_throw [WF_env'_Sigma' Sub_Sig_Sig']]]]] |
          [v [env' [Sigma' [Sub_Sig'_Sig [eval_m [WF_v_T0 WF_env'_Sigma']]]]]]]].
    left; exists env'; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite associativity, eval_fail, <- associativity, bind_fail; auto.
    right; left; exists t; exists env'; exists (fst Sigma', l0);
      unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
        rewrite associativity, eval_throw, <- associativity, bind_throw; auto;
          repeat split; auto.
    eapply P2_Env_P_P'; try eassumption; intros;
      generalize (WFV_Weaken' _ _ _ WFV funWFV _ H4 l0); simpl; auto.
    intros; eapply Sub_Sig_Sig'; auto.
    destruct Sub_Sig'_Sig as [Sub_Sig'_Sig Sig'_eq].
    assert (WFValueC D V (list (Names.DType D) * list (Names.DType D)) WFV
      (fst Sigma', l0) v T') as WF_v_T'' by
    (generalize (WFV_Weaken' _ _ _ WFV funWFV _ WF_v_T0 l0); simpl; auto).
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV
      (fst Sigma', l0) env' (fst (fst Sigma', l0))) as WF_env''_Sigma'
    by (eapply P2_Env_P_P'; try eassumption; intros;
      generalize (WFV_Weaken' _ _ _ WFV funWFV _ H4 l0); simpl; auto).
    assert (ConsExtension (fst Sigma', l0) (l, l0)) as Sub_Sig'_Sig'' by
      (constructor; simpl; auto).
    destruct (H2 (fst Sigma', l0) _ (conj Sub_Sig'_Sig (refl_equal _)) WF_v_T'' _ _ _ WF_env''_Sigma'
      (WF_Environment_Weaken D V _ WFV _ _ _ _ WF_gamma'' _ Sub_Sig'_Sig'') H3)
    as [[env'' eval_fail] |
        [[t [env'' [Sigma'' [eval_throw [WF_env''_Sigma'' Sub_Sig'_Sig''']]]]] |
          [v' [env'' [Sigma'' [Sub_Sig''_Sig' [eval_k [WF_v_T' WF_env''_Sigma'']]]]]]]].
    left; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite associativity; rewrite eval_m, <- associativity, <- left_unit; auto.
    eexists _; eauto.
    right; left; unfold DType, Value in *|-*; unfold wbind, Env in *|-*;
      rewrite associativity; rewrite eval_m, <- associativity, <- left_unit; auto.
    eexists _; eexists _; eexists _; eauto; repeat split; eauto.
    intros; eapply Sub_Sig'_Sig'''; simpl; eapply Sub_Sig'_Sig; eauto.
    eapply Sub_Sig'_Sig'''.
    repeat right; exists v'; exists env''; exists Sigma''; repeat split; auto.
    intros; eapply Sub_Sig''_Sig'; simpl; eapply Sub_Sig'_Sig; eauto.
    eapply Sub_Sig''_Sig'.
    unfold wbind, Env in *|-*;
      rewrite associativity; rewrite eval_m, <- associativity, <- left_unit; auto.
  Qed.

  Variable put_local : forall (A : Set) sigma f (m : ME A),
    put (M := ME) sigma >> (local f m) = local f (put sigma >> m).

  Global Instance Except_State_Sound_X_WFVM_State' :
    iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P
    (WFValueM_State (TypContext_WFE := SigGamma_WF_EnvC _ _ WFV) D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_State with
      (State_M := StateM_ME) (TypContext_WFE := SigGamma_WF_EnvC _ _ WFV)
      (TypContextCE := SigGamma_GammaTypContextCE _) ;
      try assumption; unfold Except_State_Sound_X_P; simpl; intros.
    (* WFVM_Get *)
    destruct (H0 env WF_env _ _ _ WF_env WF_gamma'' H1 ) as
      [[env' eval_fail] |
        [[t [env' [Sigma' [eval_throw [WF_env'_Sigma' Sub_Sig_Sig']]]]] |
          [v [env' [Sigma' [Sub_Sig'_Sig [eval_e [WF_v_T0 WF_env'_Sigma']]]]]]]].
    left; exists env'; rewrite put_local, <- eval_fail.
    generalize put_get as put_get'; intros; unfold wbind in *|-*;
      rewrite associativity, put_get', <- associativity, put_local;
        apply f_equal; apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    right; left; exists t; exists env'; exists Sigma';
      rewrite put_local, <- eval_throw; repeat split; eauto.
    generalize put_get as put_get'; intros; unfold wbind in *|-*;
      rewrite associativity, put_get', <- associativity, put_local;
        apply f_equal; apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    intros; eapply Sub_Sig_Sig'; auto.
    intros; eapply Sub_Sig_Sig'; auto.
    repeat right; exists v; exists env'; exists Sigma'; repeat split; auto.
    intros; eapply Sub_Sig'_Sig; auto.
    intros; eapply Sub_Sig'_Sig; auto.
    generalize put_get as put_get'; intros; unfold wbind in *|-*;
      rewrite put_local, associativity, put_get', <- associativity, <- put_local, <- eval_e;
        apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    (* WFVM_Put *)
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV
      Sigma' gamma'' (snd Sigma')) as WF_gamma''' by
    (unfold Value, DType in *|-*; destruct H1 as [H1' H1];
      rewrite <- H1; eapply (WF_Environment_Weaken D V _ WFV);
      eauto; split; eauto).
    destruct (H2 _ _ _ H0 WF_gamma''' H3) as
      [[env' eval_fail] |
        [[t [env' [Sigma'' [eval_throw [WF_env'_Sigma'' Sub_Sig_Sig'']]]]] |
          [v [env' [Sigma'' [Sub_Sig''_Sig [eval_e [WF_v_T0 WF_env'_Sigma'']]]]]]]].
    left; exists env'; rewrite put_local.
    generalize put_put as put_put'; intros; unfold wbind in *|-*.
      rewrite associativity, put_put', <- put_local, <- eval_fail; auto.
    right; left; exists t; exists env'; exists Sigma'';
      rewrite put_local, <- eval_throw; repeat split; eauto.
    generalize put_put as put_put'; intros; unfold wbind in *|-*;
      rewrite associativity, put_put', put_local; auto.
    intros; eapply Sub_Sig_Sig''; apply H1; auto.
    intros; rewrite <- (proj2 Sub_Sig_Sig''); apply H1; auto.
    repeat right; exists v; exists env'; exists Sigma''; repeat split; auto.
    intros; eapply Sub_Sig''_Sig; apply H1; auto.
    intros; rewrite <- (proj2 Sub_Sig''_Sig); apply H1; auto.
    generalize put_put as put_put'; intros; unfold wbind in *|-*;
      rewrite put_local, associativity, put_put', <- put_local; auto.
  Qed.

  Context {FailEnvM : FailEnvironmentMonad (Env (Value V)) ME}.

  Global Instance Except_State_Sound_X_WFVM_Bot :
    iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P (WFValueM_Bot D V MT ME _).
  Proof.
    econstructor.
    unfold iAlgebra; intros; eapply ind_alg_WFVM_Bot;
      try eassumption; unfold Except_State_Sound_X_P; simpl; intros.
    (* WFVM_fail *)
    left; exists env; rewrite local_fail; auto.
  Qed.

  Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (env gamma'' : list (Names.Value V)),
    (exists a : A, exists env' : list (Names.Value (Fun_V := Fun_V) V),
      put env >> (local (fun _ => gamma'') mte) = put env' >> return_ a) \/
    (exists env', put env >> (local (fun _ => gamma'') mte) = put env' >> fail) \/
    (exists env', put env >> (local (fun _ => gamma'') mte) = put env' >> throw tt)}.

  Variable local_throw : forall (A : Set) f t,
    local f (throw t) = throw t (A := A).
  Variable local_catch : forall (A : Set) e h f,
    local f (catch (A := A) e h) = catch (local f e) (fun t => local f (h t)).

  Variable catch_fail : forall (A : Set) h,
    catch (A := A) fail h = fail.
  Context {Put_Exception_Disc :
    forall (A B : Set) (a : A) (mb : ME B) env n,
      (put env >>= fun _ => return_ a) <> mb >>= fun _ => throw n}.
  Context {fail_neq_throw : forall A env env',
    put env >> fail (M := ME) <> put env' >> throw (A := A) tt}.

  Section Except_State_Sound_X_WFVM_Except'_Sec.
      (* Section with one possible put_catch law. *)
    Context {put_catch : forall (A : Set) (env : list (Value V)) e h,
      put env >>= (fun _ => catch (A := A) e h) = catch (put env >>= fun _ => e) h}.
    Context {put_throw : forall (A B : Set) (env env' : list (Value V)) t,
      put env >>= (fun _ => throw t (A := A)) = put env' >>= (fun _ => throw t) ->
      put env >>= (fun _ => throw t (A := B)) = put env' >>= (fun _ => throw t)}.

    Global Instance Except_State_Sound_X_WFVM_Except :
      iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P (WFValueM_Except D V MT ME _).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_Except with (Fail_MT := Fail_MT)
        (TypContextCE := SigGamma_GammaTypContextCE _)
        (Exception_ME := Exception_ME) (eq_DType_DT := eq_DType_DT);
        try assumption; unfold Except_State_Sound_X_P; simpl; intros.
    (* throw case *)
      simpl; right; left; exists tt; exists env; exists Sigma;
        repeat split; eauto; rewrite local_throw; auto.
    (* catch case *)
      destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
      destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
      repeat rewrite <- left_unit in H2.
      caseEq (eq_DType _ (proj1_sig T') T''); rewrite H3 in H2.
      destruct (H0 _ _ _ WF_env WF_gamma'' H2) as
        [[env' eval_fail] |
          [[t [env' [Sigma' [eval_throw [WF_env'_Sigma' Sub_Sig_Sig']]]]] |
            [v [env' [Sigma' [Sub_Sig'_Sig [eval_e [WF_v_T WF_env'_Sig']]]]]]]].
      rewrite local_bind, local_catch.
      destruct (ME_eq_dec' _ e' env gamma'') as
        [[v'' [env'' e'_eq]] | [
          [env'' e'_eq] | [env'' e'_eq]]];
        unfold Env in *|-*.
      unfold Value in *|-*; unfold wbind in *|-*; left; exists env';
        rewrite associativity, put_catch, e'_eq, <- put_catch,
          catch_return, <- associativity.
      rewrite local_bind, associativity, e'_eq, <- associativity,
        <- left_unit in eval_fail; rewrite <- left_unit; apply eval_fail.
      unfold Value in *|-*; unfold wbind in *|-*; left; exists env'';
        rewrite associativity, put_catch, e'_eq, <- put_catch,
          catch_fail, <- associativity, bind_fail; auto.
      unfold wbind in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_throw in eval_fail; elimtype False;
        eapply fail_neq_throw; eauto.
      rewrite local_bind, local_catch.
      destruct (ME_eq_dec' _ e' env gamma'') as
        [[v'' [env'' e'_eq]] | [
          [env'' e'_eq] | [env'' e'_eq]]];
        unfold Env in *|-*.
      unfold Value in *|-*; unfold wbind in *|-*; right; left;
        exists t; exists env'; exists Sigma';
          rewrite associativity, put_catch, e'_eq, <- put_catch,
            catch_return, <- associativity; repeat split; eauto.
      rewrite local_bind, associativity, e'_eq, <- associativity,
        <- left_unit in eval_throw; rewrite <- left_unit; apply eval_throw.
      intros; apply Sub_Sig_Sig'; auto.
      intros; apply Sub_Sig_Sig'; auto.
      unfold wbind in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_fail in eval_throw; elimtype False;
        eapply fail_neq_throw; destruct t; apply sym_eq; eauto.
      destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst.
      repeat rewrite <- left_unit in H1, H2.
      destruct (MT_eq_dec _ (kT c T'')) as [[d kTcT''_eq] | kTcT''_eq].
      destruct Sigma; simpl in *|-*.
    assert (WF_Environment D V (list (Names.DType D) * list (Names.DType D)) WFV
      Sigma' gamma'' (snd Sigma')) as WF_gamma''' by
    (unfold Value, DType in *|-*; destruct Sub_Sig_Sig' as [H1' H1''];
      rewrite <- H1''; eapply (WF_Environment_Weaken D V _ WFV);
      eauto; split; eauto).
    destruct (H1 tt _ Sub_Sig_Sig' _ _ _ WF_env'_Sigma' WF_gamma''' kTcT''_eq) as
      [[env''' eval_fail] |
        [[t' [env''' [Sigma''' [eval_throw' [WF_env'''_Sig''' Sub_Sig''_Sig''']]]]] |
          [v' [env''' [Sigma'' [Sub_Sig'_Sig'' [eval_h [WF_v'_d WF_env''_Sig'']]]]]]]];
      eauto.
      left.
      unfold wbind in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_throw in eval_throw.
      exists env'''; unfold Value in *|-*;
        rewrite associativity, put_catch, e'_eq.
      destruct t; rewrite (put_throw _ _ _ _ _ eval_throw),
        <- put_catch, catch_throw', <- associativity, <- local_bind; auto.
      right; left.
      unfold wbind in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_throw in eval_throw.
      destruct t.
      exists t'; exists env'''; exists Sigma'''; repeat split; auto.
      unfold Value in *|-*;
        rewrite associativity, put_catch, e'_eq,
          (put_throw _ _ _ _ _ eval_throw), <- put_catch, catch_throw',
          <- associativity, <- local_bind; auto.
      intros; eapply Sub_Sig''_Sig'''; eapply Sub_Sig_Sig'; eauto.
      intros; rewrite <- (proj2 Sub_Sig''_Sig'''); eapply Sub_Sig_Sig'; eauto.
      repeat right; exists v'; exists env'''; exists Sigma'';
        repeat split; eauto.
      intros; eapply Sub_Sig'_Sig''; eapply Sub_Sig_Sig'; eauto.
      intros; rewrite <- (proj2 Sub_Sig'_Sig''); eapply Sub_Sig_Sig'; eauto.
      unfold wbind, Value in *|-*; rewrite associativity, put_catch,
        e'_eq.
      unfold wbind in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_throw in eval_throw; destruct t.
      rewrite (put_throw _ _ _ _ _ eval_throw),
        <- put_catch, <- associativity, catch_throw', <- local_bind; auto.
      destruct T; apply (WFV_proj1_b D V _ WFV _ _ WF_v'_d); simpl; auto.
      generalize (kt_eq _ _ (eq_DType_eq _ _ _ H3)).
      repeat rewrite <- left_unit;  rewrite H2, kTcT''_eq; repeat rewrite fmap_return.
      intros x_eq; apply inj_return in x_eq; auto.
      elimtype False; generalize (kt_eq _ _ (eq_DType_eq _ _ _ H3)).
      repeat rewrite <- left_unit; rewrite H2, kTcT''_eq.
      rewrite fmap_return; rewrite fmap_fail.
      intros x_eq.
      elimtype False; eapply (FailMonad_Disc MT _ _ (proj1_sig T) (fail (A := Fix D)));
      unfold wbind; rewrite bind_fail; eauto with typeclass_instances.
      rewrite bind_fail in H2.
      elimtype False; eapply (FailMonad_Disc MT _ _ T (fail (A := Fix D)));
      unfold wbind; rewrite bind_fail; eauto with typeclass_instances.
      destruct (ME_eq_dec' _ e' env gamma'') as
        [[v'' [env'' e'_eq]] | [
          [env'' e'_eq] | [env'' e'_eq]]];
      unfold Env in *|-*.
      repeat right; exists v; exists env'; exists Sigma';
        repeat split; eauto.
      intros; eapply Sub_Sig'_Sig; eauto.
      intros; eapply Sub_Sig'_Sig; eauto.
      rewrite put_local; unfold wbind in *|-*.
      rewrite associativity, put_catch, local_bind, local_catch,
        <- put_local, e'_eq, <- put_catch, catch_return, <- associativity,
        <- left_unit.
      rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        <- left_unit in eval_e; auto.
      left; exists env''; unfold wbind, Value in *|-*.
      rewrite local_bind, local_catch, associativity, put_catch,
        e'_eq, <- put_catch, catch_fail, <- associativity, bind_fail; auto.
      unfold wbind, Value in *|-*; rewrite put_local, associativity,
        local_bind, <- put_local, e'_eq, <- associativity,
        bind_throw in eval_e; elimtype False; eapply Put_Exception_Disc;
          eauto.
      destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
      destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
      destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq]; subst; failmonaddisc.
    Qed.

  End Except_State_Sound_X_WFVM_Except'_Sec.

  Context {soundness_X'_alg :
    forall eval_rec,
      iPAlgebra soundness_X'_Name
      (soundness_X'_P D V E MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := evalM_E))) (EQV_E _ _)}.
  Context {Except_State_Sound_X_WFVM : iPAlgebra Except_State_Sound_X_Name Except_State_Sound_X_P WFVM}.
  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P E EQV_E A B) (EQV_E _ _)}.

  Theorem Except_State_Sound_X :
    forall (n : nat) Sigma gamma gamma' gamma'' e' e'',
      E_eqvC E EQV_E gamma' gamma e'' e' ->
      forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
        exists T, lookup gamma b = Some T)
      (WF_gamma'' : WF_Environment _ _ _ WFV Sigma gamma'' gamma)
      (WF_gamma2 : List.length gamma = List.length gamma')
      (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
      (WF_Sigma : Gamma D Sigma = gamma)
      (T : DType D)
      (env : Env (Names.Value V))
      (WF_env : WF_Environment _ _ _ WFV Sigma env (fst Sigma)),
      typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e') = return_ T ->
      (exists env', put env >>
        local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = put env' >> fail) \/
      (exists t, exists env', exists Sigma',
        put env >> local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = put env' >> throw t
        /\ WF_Environment D V _ WFV Sigma' env' (fst Sigma')
        /\ ConsExtension Sigma' Sigma) \/
        exists v : Value V,
          exists env' : Env (Value V),
          exists Sigma' ,
            ConsExtension Sigma' Sigma /\
          put env >> local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') =
          put env' >> return_ (M := ME) v /\ WFValueC _ _ _ WFV Sigma' v T
          /\ WF_Environment D V _ WFV Sigma' env' (fst Sigma').
  Proof.
    intros.
    intros; eapply (ifold_ WFVM _ (ip_algebra (iPAlgebra := Except_State_Sound_X_WFVM))
      _ (eval_soundness_X' D V E MT ME _ EQV_E WFVM n _ _ _ _ H Sigma WF_gamma WF_gamma2 WF_gamma' WF_Sigma));
    simpl in *|-*; unfold DType in *|-*; eauto;
    simpl in H0; eauto.
    rewrite WF_Sigma; eauto.
  Qed.

End Lambda_Exception_State.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
