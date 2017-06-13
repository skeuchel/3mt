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

End Lambda_Exception.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
