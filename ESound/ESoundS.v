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

Section ESoundS.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Let DType := DType D.

  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Let Exp := Exp E.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Let Value := Value V.

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {FailM : FailMonad ME}.
  Context {State_M : StateM ME (list Value)}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) E}.
  Context {evalM_E' : forall T, FAlgebra EvalName T (evalMR V ME) E}.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {TypContext_S : SigTypContextC D TypContext}.
  Context {TypContext_SCE : SigConsExtensionC D TypContext _ _}.
  Context {TypContext_WFE : WF_EnvC V TypContext}.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.

  Context {TypContext_SWFE : Sig_WF_EnvC D V TypContext WFV _ _}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME TypContext WFV) WFVM}.
  Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME TypContext) WFVM}.

  Context {WFV_proj1_a_WFV : iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFV}.
  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.


  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

  Context {wfvm_bind_alg :
             iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

  Section State_Sound_Sec.

    Variable WFV' : (WFValue_i D V (list DType) -> Prop) -> WFValue_i D V (list DType) -> Prop.
    Context {funWFV' : iFunctor WFV'}.

    Variable WFVM' : (WFValueM_i D V MT ME (list DType) -> Prop) -> WFValueM_i D V MT ME (list DType) -> Prop.
    Context {funWFVM' : iFunctor WFVM'}.

    Global Instance DType_Env_CE : ConsExtensionC (list DType) :=
      {| ConsExtension := fun Sigma' Sigma =>
        forall n T, lookup Sigma n = Some T -> lookup Sigma' n = Some T |}.
    Proof.
      (* ConsExtension_id *)
      eauto.
      (* ConsExtension_trans *)
      eauto.
    Defined.

    Global Instance DType_Env_S : SigTypContextC D (list DType) :=
      {| SigLookup := lookup;
        SigInsert := insert _|}.

    Global Instance DType_Env_WFE : WF_EnvC V (list DType) :=
      {| WF_Env := fun env Sigma =>
        P2_Env (WFValueC _ _ _ WFV' Sigma) env Sigma |}.

    Global Instance DType_Env_SCE : SigConsExtensionC D (list DType) _ _.
    Proof.
      constructor.
    (* ConsExtension_SigLookup *)
      eauto.
    (* ConsExtension_SigInsert *)
      simpl; intros; erewrite lookup_Some_insert; eauto.
    Qed.

    Context {WFV_Weaken_WFV' : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV') WFV'}.

    Definition WFV'_Weaken := ifold_ WFV' _ (ip_algebra (iPAlgebra := WFV_Weaken_WFV')).

    Global Instance DType_Env_SWFE : Sig_WF_EnvC D V (list DType) WFV' _ _.
    Proof.
      constructor; simpl; intros.
      (* WF_EnvLookup *)
      unfold WF_Env in H; simpl in H.
      apply (P2_Env_lookup' _ _ _ _ _ H); auto.
      (* WF_EnvInsertLookup *)
      unfold Value.
      rewrite (P2_Env_length _ _ _ _ _ H); apply lookup_insert.
      (* WF_EnvInsert *)
      apply P2_Env_insert; eauto.
      eapply P2_Env_P_P'; eauto.
      intros; generalize (WFV'_Weaken _ H1).
      unfold WFValue_Weaken_P; simpl; intros; eapply H2.
      simpl; intros; erewrite lookup_Some_insert; eauto.
      (* WF_EnvReplace *)
      eapply P2_Env_replace_el; eauto.
    Qed.

    Definition State_Sound_P (i : WFValueM_i D V MT ME (list DType)) :=
      forall T (env : list Value),
        WF_Env V env (wfvm_S _ _ _ _ _ i) ->
        wfvm_T _ _ _ _ _ i = return_ T ->
        exists v : Value, exists env', exists Sigma',
          (put env) >> wfvm_v _ _ _ _ _ i = put env' >> return_ (M := ME) v /\
          WFValueC _ _ _ WFV' Sigma' v T.

    Inductive State_Sound_Name := State_Sound_name.

    Context {WFV_proj1_a_WFV' : iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV') WFV'}.
    Context {WFV_proj1_b_WFV' : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.

    Global Instance State_Sound_WFVM_State :
      iPAlgebra State_Sound_Name State_Sound_P (WFValueM_State D V MT ME (list DType)).
    Proof.
      econstructor.
      unfold iAlgebra; intros; eapply ind_alg_WFVM_State with (TypContextCE := DType_Env_CE)
        (TypContext_WFE := DType_Env_WFE);
        try assumption; unfold State_Sound_P; simpl; intros.
      (* WFVM_Get *)
      destruct (H0 env H1 T0 env H1 H2) as [v [env' [Sigma' [eval_eq WF_v_T]]]].
      exists v; exists env'; exists Sigma'.
      unfold wbind; rewrite associativity.
      generalize put_get as put_get'; intros; unfold wbind in put_get'; rewrite put_get'.
      rewrite <- associativity.
      rewrite <- left_unit.
      split; unfold wbind; auto.
      (* WFVM_Put *)
      unfold wbind; rewrite associativity.
      generalize put_put as put_put'; intros; unfold wbind in put_put'; rewrite put_put'.
      destruct (H2 T0 env H0 H4) as [v [env' [Sigma'' [eval_eq WF_v_T]]]].
      exists v; exists env'; exists Sigma''; split; auto.
    Qed.

    Global Instance State_Sound_WFVM_base :
      iPAlgebra State_Sound_Name State_Sound_P (WFValueM_base D V MT ME _ WFV').
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (Monad_ME := Mon_M)
        (Fail_MT := Fail_MT) (WFV := WFV');
        try assumption; unfold State_Sound_P; simpl; intros.
      exists v; exists env; exists Sigma; split; auto.
      destruct H1 as [mt' mt'_eq]; subst.
      destruct (fmap_exists _ _ _ _ _ H3) as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0 as [T0 T0_UP'].
      apply (WFV_proj1_b _ _ _ WFV' _ _ H0); simpl; auto.
      (* WFVM_Untyped' *)
      simpl in H1; apply sym_eq in H1.
      apply FailMonad_Disc in H1; destruct H1; auto.
    Qed.

    Context {State_Sound_WFVM : iPAlgebra State_Sound_Name State_Sound_P WFVM'}.

    Context {eval_soundness'_Exp_E : forall (typeof_rec : UP'_F E -> typeofR D MT)
       (eval_rec : Names.Exp E -> evalMR V ME),
       P2Algebra ES'_ExpName E E E
       (UP'_P2
         (eval_soundness'_P D V E MT ME _ WFVM'
           Datatypes.unit E Fun_E
           (fun _ _ _ _ => True)
           tt typeof_rec eval_rec f_algebra
           (f_algebra (FAlgebra := evalM_E' (@Names.Exp E Fun_E)))))}.

     Context {WF_MAlg_typeof : WF_MAlgebra Typeof_F}.
     Context {WF_MAlg_eval : WF_MAlgebra evalM_E'}.

    Lemma eval_State_soundness : forall (e : Exp) Sigma,
      WFValueMC _ _ _ _ _ WFVM' Sigma (evalM (evalM_E := evalM_E') _ _ _ (proj1_sig e))
      (typeof _ _ MT (proj1_sig e)).
    Proof.
      intro; rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig e)).
      simpl; unfold typeof, evalM, fold_, mfold, in_t.
      repeat rewrite wf_malgebra; unfold mfold.
      destruct (Ind2 (Ind_Alg := eval_soundness'_Exp_E
        (fun e => typeof _ _ _ (proj1_sig e))
        (fun e => evalM (evalM_E := evalM_E') _ _ _ (proj1_sig e)))
        _ (proj2_sig e)) as [e' eval_e'].
      unfold eval_soundness'_P in eval_e'.
      intros; eapply eval_e'; intros; auto; try constructor.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig (fst a)) (proj2_sig _)).
      unfold typeof, evalM, mfold; simpl; unfold in_t;
        repeat rewrite wf_malgebra; unfold mfold; apply H; auto.
    Qed.

    Theorem eval_State_Sound :
      forall (Sigma : Env DType) (e : Exp) (T : DType) (env : Env Value),
        WF_Env V env Sigma ->
        typeof D E MT (proj1_sig e) = return_ T ->
        exists v : Value,
          exists env' : Env Value,
            exists Sigma' : Env DType,
              (put env) >> evalM (evalM_E := evalM_E') _ _ _ (proj1_sig e) =
              put env' >> return_ (M := ME) v /\
              WFValueC _ _ _ WFV' Sigma' v T.
    Proof.
      intros Sigma e.
      apply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := State_Sound_WFVM)) _
        (eval_State_soundness e Sigma)).
    Qed.

  End State_Sound_Sec.

End ESoundS.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
