Require Import List.
Require Import FunctionalExtensionality.
Require Import FJ_tactics.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffReader.
Require Import Arith.
Require Import Lambda.

Section Lambda_Arith.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {Sub_AType_D : AType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {Distinct_AType_LType : Distinct_Sub_Functor Fun_D Sub_AType_D Sub_LType_D}.
  Context {WF_Sub_AType_D : WF_Functor _ _ (Sub_AType_D) _ _}.
   Context {WF_Sub_LType_F : WF_Functor _ _ (Sub_LType_D) _ _}.

  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Context {Sub_Arith_F : forall A, Arith :<: F A}.
  Context {Sub_Lambda_F : forall A : Set, Lambda D A :<: F A}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_ExceptE_F : forall A, WF_Functor _ _ (Sub_Lambda_F A) _ _}.
   Context {WF_Sub_Arith_F : forall A, WF_Functor _ _ (Sub_Arith_F A) _ _}.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Context {Sub_NatValue_V : NatValue :<: V}.
   Context {Sub_ClosValue_V : ClosValue F :<: V}.

   Context {WF_Sub_NatValue_V : WF_Functor _ _ Sub_NatValue_V _ _}.
   Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
   Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
   Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

   Variable MT : Set -> Set.
   Context {Fun_MT : Functor MT}.
   Context {Mon_MT : Monad MT}.
   Context {Fail_MT : FailMonad MT}.

   Variable ME : Set -> Set.
   Context `{Enviroment_ME : Environment ME (Env (Value V))}.
   Context {Fail_ME : FailMonad ME}.
   Context {FailEnvME : FailEnvironmentMonad _ ME}.

  Context {Reasonable_ME : Reasonable_Monad ME}.

  Context {evalM_F : FAlgebra EvalName (Exp F nat) (evalMR V ME) (F nat)}.
  Context {WF_eval_Lambda_F :
    @WF_FAlgebra EvalName _ _ (Lambda D nat) (F nat)
    (Sub_Lambda_F nat) (MAlgebra_evalM_Lambda D F V ME) evalM_F}.
  Context {WF_eval_Arith_F : @WF_FAlgebra EvalName _ _ Arith (F nat)
    (Sub_Arith_F _) (MAlgebra_evalM_Arith V ME _) evalM_F}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) (F (DType D))}.
  Context {WF_ExceptE_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ (Lambda D _) (F _)
    (Sub_Lambda_F _) (MAlgebra_typeof_Lambda D MT _) (Typeof_F T)}.
  Context {WF_Arith_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ Arith (F _)
    (Sub_Arith_F _) (MAlgebra_typeof_Arith _ MT _) (Typeof_F T)}.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {GammaTypContext : GammaTypContextC D TypContext}.
  Context {TypContext_GCE : GammaConsExtensionC _ TypContext _ _}.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.
  Context {Sub_WFV_VI_WFV : Sub_iFunctor (WFValue_VI V D _) WFV}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.
  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
  Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.
  Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot D V MT ME _) WFVM}.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

  (* ============================================== *)
  (* EQUIVALENCE OF ARITHMETIC EXPRESSIONS          *)
  (* ============================================== *)

  Inductive Arith_eqv (A B : Set) (C : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
  | Lit_eqv : forall (gamma : Env _) gamma' n e e',
    proj1_sig e = lit (F A) n ->
    proj1_sig e' = lit (F B) n ->
    Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
  | Add_eqv : forall (gamma : Env _) gamma' a b a' b' e e',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    C (mk_eqv_i _ _ _ gamma gamma' b b') ->
    proj1_sig e = proj1_sig (add' (F _) a b) ->
    proj1_sig e' = proj1_sig (add' (F _) a' b') ->
    Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e').

  Definition ind_alg_Arith_eqv
    (A B : Set)
    (P : eqv_i F A B -> Prop)
    (Hlit : forall gamma gamma' n e e'
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    (Hadd : forall gamma gamma' a b a' b' e e'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b'))
      e_eq e'_eq,
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
    i (e : Arith_eqv A B P i) : P i :=
    match e in Arith_eqv _ _ _ i return P i with
      | Lit_eqv gamma gamma' n e e' e_eq e'_eq =>
        Hlit gamma gamma' n e e' e_eq e'_eq
      | Add_eqv gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq =>
        Hadd gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq
    end.

  Definition Arith_eqv_ifmap (A B : Set)
    (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i)
    (eqv_a : Arith_eqv A B A' i) : Arith_eqv A B B' i :=
    match eqv_a in Arith_eqv _ _ _ i return Arith_eqv _ _ _ i with
      | Lit_eqv gamma gamma' n e e' e_eq e'_eq =>
        Lit_eqv _ _ _ gamma gamma' n e e' e_eq e'_eq
      | Add_eqv gamma gamma' a b a' b' e e'
        eqv_a_a' eqv_b_b' e_eq e'_eq =>
        Add_eqv _ _ _ gamma gamma' a b a' b' e e'
        (f _ eqv_a_a') (f _ eqv_b_b') e_eq e'_eq
    end.

  Global Instance iFun_Arith_eqv A B : iFunctor (Arith_eqv A B).
    constructor 1 with (ifmap := Arith_eqv_ifmap A B).
    destruct a; simpl; intros; reflexivity.
    destruct a; simpl; intros; unfold id; eauto.
  Defined.

  Context {Sub_Arith_eqv_EQV_E : forall A B,
    Sub_iFunctor (Arith_eqv A B) (EQV_E A B)}.
  Context {Sub_Lambda_eqv_EQV_E : forall A B,
    Sub_iFunctor (Lambda_eqv _ _ A B) (EQV_E A B)}.

  Global Instance EQV_proj1_Arith_eqv :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (Arith_eqv _ _).
    econstructor; intros.
    unfold iAlgebra; intros; apply ind_alg_Arith_eqv;
      unfold EQV_proj1_P; simpl; intros; subst.
    apply (inject_i (subGF := Sub_Arith_eqv_EQV_E A B)); econstructor; simpl; eauto.
    apply (inject_i (subGF := Sub_Arith_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
    destruct a; destruct a'; eapply IHa; eauto.
    destruct b; destruct b'; eapply IHb; eauto.
    apply H.
  Qed.

  Context {WF_invertVI_WFV :
    iPAlgebra WF_invertVI_Name (WF_invertVI_P _ _ _ WFV) WFV}.
  Context {WFVM_bind_WFVM :
    iPAlgebra wfvm_bind_Name (wfvm_bind_P _ _ _ _ _ WFV WFVM) WFVM}.
  Context {EQV_proj1_EQV_E :
    forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (EQV_E _ _)}.

  Global Instance eqv_soundness_X'_Arith_eqv eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V F MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := Typeof_F _))
      (f_algebra (FAlgebra := evalM_F))) (Arith_eqv _ _).
  Proof.
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_Arith_eqv; try eassumption;
        unfold soundness_X'_P, eval_soundness'_P; unfold bevalM; simpl; intros.
      (* lit case *)
      split; intros.
      apply (inject_i (subGF := Sub_Arith_eqv_EQV_E _ _));
        econstructor; eauto.
      rewrite e_eq, e'_eq.
      unfold lit, lit'; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_Arith_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_Arith_Typeof_F _));
          simpl fmap; simpl f_algebra; unfold Arith_fmap;
            unfold Arith_typeof, Arith_evalM.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor.
      apply inject_i; econstructor; unfold vi; simpl; reflexivity.
      apply return_orn; eauto.
      (* add case *)
      intros; destruct a as [mE mT]; destruct b as [nE nT];
        destruct (IHa IH) as [eqv_m_m' IHm];
          destruct (IHb IH) as [eqv_n_n' IHn]; simpl in *|-*.
      split; intros.
      apply (inject_i (subGF := Sub_Arith_eqv_EQV_E _ _));
        econstructor 2.
      eapply eqv_m_m'.
      eapply eqv_n_n'.
      rewrite e_eq; reflexivity.
      rewrite e'_eq; reflexivity.
      rewrite e_eq, e'_eq; unfold add, add'; simpl; repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_Arith_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_Arith_Typeof_F _));
          simpl fmap; simpl f_algebra; unfold Arith_fmap.
      intros; apply Arith_eval_soundness'_H0 with (WFV := WFV) (TypContextCE := TypContextCE);
        eauto with typeclass_instances.
      eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_m_m'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig a')).
      destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_m_m'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig a')).
      intros; eapply IH with (pb := (gamma, gamma')).
      split; destruct WF_Gamma; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_n_n'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
      eapply WF_eqv_environment_P_Sub; eauto.
      apply (EQV_proj1 _ EQV_E _ _ _ eqv_n_n'); simpl; eauto.
      generalize in_out_UP'_inverse; simpl; intros in_out';
        eapply (in_out' _ _ _ (proj2_sig b')).
  Qed.

  Lemma functional_extensionality2 : forall (A B C : Set) (f g : A -> B -> C),
    (forall a b, f a b = g a b) -> f = g.
  Proof.
    repeat (intros; apply functional_extensionality_dep); auto.
  Qed.

  Lemma rewrite_do2 : forall (M : Set -> Set)
    {Fun_M : Functor M}
    {Monad_M : Monad M},
    forall (A B C : Set) (n : M A) (o : M B) (m m' : A -> B -> M C),
      m = m' -> (do n' <- n; do o' <- o; m n' o') = (do n' <- n; do o' <- o; m' n' o').
    intros; rewrite H; reflexivity.
  Qed.

  Global Instance WF_invertClos_WFV_VI :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D F MT V EQV_E _ WFV) (WFValue_VI V D _).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_VI with (Sub_NatValue_V := Sub_NatValue_V)
      (Sub_AType_D := Sub_AType_D); unfold WF_invertClos_P; simpl; intros; auto; split.
    apply inject_i; econstructor; eauto.
    rewrite Teq; intros.
    unfold tnat in H0; simpl in H0; apply in_t_UP'_inject in H0.
    repeat rewrite wf_functor in H0; simpl in H0.
    elimtype False; eapply (inj_discriminate _ _ _ H0).
  Qed.

  Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

  Global Instance WFV_VI_Weaken' :
    iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V TypContext WFV)
    (WFValue_VI V D TypContext).
  Proof.
    constructor.
    unfold iAlgebra; intros; apply ind_alg_WFV_VI with (Sub_NatValue_V := Sub_NatValue_V)
      (Sub_AType_D := Sub_AType_D); unfold WFValue_Weaken'_P; simpl; intros; auto.
    apply inject_i; econstructor; eauto.
  Qed.

End Lambda_Arith.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
