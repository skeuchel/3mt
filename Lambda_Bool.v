Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Bool.
Require Import Lambda.

Section Lambda_Bool.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {Sub_BType_D : BType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {Distinct_BType_LType : Distinct_Sub_Functor Fun_D Sub_BType_D Sub_LType_D}.
  Context {WF_Sub_BType_D : WF_Functor _ _ (Sub_BType_D) _ _}.
   Context {WF_Sub_LType_F : WF_Functor _ _ (Sub_LType_D) _ _}.

  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Context {Sub_Bool_F : forall A, Bool :<: F A}.
  Context {Sub_Lambda_F : forall A : Set, Lambda D A :<: F A}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_ExceptE_F : forall A, WF_Functor _ _ (Sub_Lambda_F A) _ _}.
   Context {WF_Sub_Bool_F : forall A, WF_Functor _ _ (Sub_Bool_F A) _ _}.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Context {Sub_BoolValue_V : BoolValue :<: V}.
   Context {Sub_ClosValue_V : ClosValue F :<: V}.
   Context {WF_Sub_BoolValue_V : WF_Functor _ _ (Sub_BoolValue_V) _ _}.

   Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
   Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
   Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

   Variable MT : Set -> Set.
   Context {Fun_MT : Functor MT}.
   Context {Mon_MT : Monad MT}.
   Context {Fail_MT : FailMonad MT}.
   Context {MT_eq_dec : forall (A : Set) (mta : MT A),
     {exists a, mta = return_ a} + {mta = fail}}.

   Variable ME : Set -> Set.
   Context `{Enviroment_ME : Environment ME (Env (Value V))}.
   Context {Fail_ME : FailMonad ME}.
   Context {FailEnvME : FailEnvironmentMonad _ ME}.

  Context {Reasonable_ME : Reasonable_Monad ME}.

  Context {evalM_F : FAlgebra EvalName (Exp F nat) (evalMR V ME) (F nat)}.
  Context {WF_eval_Lambda_F :
    @WF_FAlgebra EvalName _ _ (Lambda D nat) (F nat)
    (Sub_Lambda_F nat) (MAlgebra_evalM_Lambda D F V ME) evalM_F}.
  Context {WF_eval_Bool_F : @WF_FAlgebra EvalName _ _ Bool (F nat)
    (Sub_Bool_F _) (MAlgebra_evalM_Bool V ME _) evalM_F}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) (F (DType D))}.
  Context {WF_ExceptE_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ (Lambda D _) (F _)
    (Sub_Lambda_F _) (MAlgebra_typeof_Lambda D MT _) (Typeof_F T)}.
  Context {WF_Bool_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ Bool (F _)
    (Sub_Bool_F _) (MAlgebra_typeof_Bool _ MT _) (Typeof_F T)}.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {Sub_Lambda_eqv_EQV_E : forall A B, Sub_iFunctor (Lambda_eqv _ _ A B) (EQV_E A B)}.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {GammaTypContext : GammaTypContextC D TypContext}.
  Context {TypContext_GCE : GammaConsExtensionC _ TypContext _ _}.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.
  Context {Sub_WFV_VB_WFV : Sub_iFunctor (WFValue_VB D V _ ) WFV}.

  Context {WF_invertVB_WFV : iPAlgebra WF_invertVB_Name (WF_invertVB_P _ _ _ WFV) WFV}.

  (* ============================================== *)
  (* EQUIVALENCE OF BOOLEAN EXPRESSIONS             *)
  (* ============================================== *)

  Inductive Bool_eqv (A B : Set) (C : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
  | BLit_eqv : forall (gamma : Env _) gamma' b e e',
    proj1_sig e = blit (F A) b ->
    proj1_sig e' = blit (F B) b ->
    Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
  | If_eqv : forall (gamma : Env _) gamma' a b c a' b' c' e e',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    C (mk_eqv_i _ _ _ gamma gamma' b b') ->
    C (mk_eqv_i _ _ _ gamma gamma' c c') ->
    proj1_sig e = proj1_sig (cond' (F _) a b c) ->
    proj1_sig e' = proj1_sig (cond' (F _) a' b' c') ->
    Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e').

  Definition ind_alg_Bool_eqv
    (A B : Set)
    (P : eqv_i F A B -> Prop)
    (Hblit : forall gamma gamma' n e e'
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    (Hif : forall gamma gamma' a b c a' b' c' e e'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b'))
      (IHc : P (mk_eqv_i _ _ _ gamma gamma' c c'))
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    i (e : Bool_eqv A B P i) : P i :=
    match e in Bool_eqv _ _ _ i return P i with
      | BLit_eqv gamma gamma' b e e' e_eq e'_eq =>
        Hblit gamma gamma' b e e' e_eq e'_eq
      | If_eqv gamma gamma' a b c a' b' c' e e'
        eqv_a_a' eqv_b_b' eqv_c_c' e_eq e'_eq =>
        Hif gamma gamma' a b c a' b' c' e e'
        eqv_a_a' eqv_b_b' eqv_c_c' e_eq e'_eq
    end.

  Definition Bool_eqv_ifmap (A B : Set)
    (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i)
    (eqv_a : Bool_eqv A B A' i) : Bool_eqv A B B' i :=
    match eqv_a in Bool_eqv _ _ _ i return Bool_eqv _ _ _ i with
      | BLit_eqv gamma gamma' b e e' e_eq e'_eq =>
        BLit_eqv _ _ _ gamma gamma' b e e' e_eq e'_eq
      | If_eqv gamma gamma' a b c a' b' c' e e'
        eqv_a_a' eqv_b_b' eqv_c_c' e_eq e'_eq =>
        If_eqv _ _ _ gamma gamma' a b c a' b' c' e e'
        (f _ eqv_a_a') (f _ eqv_b_b') (f _ eqv_c_c') e_eq e'_eq
    end.

  Global Instance iFun_Bool_eqv A B : iFunctor (Bool_eqv A B).
    constructor 1 with (ifmap := Bool_eqv_ifmap A B).
    destruct a; simpl; intros; reflexivity.
    destruct a; simpl; intros; unfold id; eauto.
  Defined.

  Variable Sub_Bool_eqv_EQV_E : forall A B,
    Sub_iFunctor (Bool_eqv A B) (EQV_E A B).

  Global Instance EQV_proj1_Bool_eqv :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (Bool_eqv _ _).
    econstructor; intros.
    unfold iAlgebra; intros; apply ind_alg_Bool_eqv;
      unfold EQV_proj1_P; simpl; intros; subst.
    apply (inject_i (subGF := Sub_Bool_eqv_EQV_E A B)); econstructor; simpl; eauto.
    apply (inject_i (subGF := Sub_Bool_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
    destruct a; destruct a'; eapply IHa; eauto.
    destruct b; destruct b'; eapply IHb; eauto.
    destruct c; destruct c'; eapply IHc; eauto.
    apply H.
  Qed.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.
  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.

  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (EQV_E _ _)}.
  Context {wfvm_bind_alg :
    iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

  Global Instance eqv_soundness_X'_Bool_eqv eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V F MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := Typeof_F _))
      (f_algebra (FAlgebra := evalM_F))) (Bool_eqv _ _).
  Proof.
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_Bool_eqv; try eassumption;
        unfold soundness_X'_P, eval_soundness'_P; unfold bevalM; simpl; intros.
      (* blit case *)
      split; intros.
      apply (inject_i (subGF := Sub_Bool_eqv_EQV_E _ _));
        econstructor; eauto.
      rewrite e_eq, e'_eq.
      unfold blit, blit'; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_Bool_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_Bool_Typeof_F _));
          simpl fmap; simpl f_algebra; unfold Bool_fmap;
            unfold Bool_typeof, Bool_evalM.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor.
      apply inject_i; econstructor; unfold vb; simpl; reflexivity.
      apply return_orn; eauto.
      (* if case *)
      intros; destruct a as [aE aT]; destruct b as [bE bT]; destruct c as [cE cT];
        destruct (IHa IH) as [eqv_a_a' IHa'];
          destruct (IHb IH) as [eqv_b_b' IHn'];
            destruct (IHc IH) as [eqv_c_c' IHc']; simpl in *|-*.
      split; intros.
      apply (inject_i (subGF := Sub_Bool_eqv_EQV_E _ _));
        econstructor 2.
      eapply eqv_a_a'.
      eapply eqv_b_b'.
      eapply eqv_c_c'.
      rewrite e_eq; reflexivity.
      rewrite e'_eq; reflexivity.
      rewrite e_eq, e'_eq; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_Bool_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_Bool_Typeof_F _));
          simpl fmap; simpl f_algebra; unfold Bool_fmap.
      intros; apply Bool_eval_soundness'_H0 with (WFV := WFV) (TypContextCE := TypContextCE);
        eauto with typeclass_instances.
      eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig a')).
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_a_a'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig a')).
      intros; eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_b_b'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
      eapply WF_eqv_environment_P_Sub; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_b_b'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
      intros; eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_c_c'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig c')).
      eapply WF_eqv_environment_P_Sub; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_c_c'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig c')).
  Qed.

  Global Instance WF_invertClos_WFV_VB :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D F MT V EQV_E _ WFV) (WFValue_VB D V _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_VB with (Sub_BoolValue_V := Sub_BoolValue_V)
      (Sub_BType_D := Sub_BType_D); unfold WF_invertClos_P; simpl; intros; auto; split.
    apply inject_i; econstructor; eauto.
    rewrite Teq; intros.
    unfold tbool in H0; simpl in H0; apply in_t_UP'_inject in H0.
    repeat rewrite wf_functor in H0; simpl in H0.
    elimtype False; eapply (inj_discriminate _ _ _ H0).
  Qed.

  Global Instance WFV_VB_Weaken' :
    iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V TypContext WFV)
    (WFValue_VB _ _ TypContext).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_VB with (Sub_BoolValue_V := Sub_BoolValue_V)
      (Sub_BType_D := Sub_BType_D); unfold WFValue_Weaken'_P; simpl; intros; auto.
    apply inject_i; econstructor; eauto.
  Qed.

End Lambda_Bool.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
