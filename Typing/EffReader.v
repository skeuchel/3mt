Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import List.
Require Import FJ_tactics.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.

Section EffReader.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Let DType := DType D.


  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.


  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Let Exp (A : Set) := Exp (F A).

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Let Value := Value V.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_ME : Functor ME}.
  Context {Mon_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.
  Context {Environment_ME : Environment ME (Env Value)}.

  Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {evalM_F : FAlgebra EvalName (Exp nat) (evalMR V ME) (F nat)}.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Let E_eqv A B := iFix (EQV_E A B).
  Let E_eqvC {A B : Set} gamma gamma' e e' :=
    E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) (F DType)}.

  Section WFValue_Sec.

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.
    Context {GammaTypContext : GammaTypContextC D TypContext}.
    Context {TypContext_GCE : GammaConsExtensionC D TypContext _ _}.

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.


    (* ============================================== *)
    (* WELL-FORMED MONADIC STATE VALUES               *)
    (* ============================================== *)

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Let WFValueM := iFix WFVM.
    Let WFValueMC Sigma v T:= WFValueM (mk_WFValueM_i D V MT ME _ Sigma v T).

    Inductive WFValueM_Environment (A : WFValueM_i D V MT ME TypContext -> Prop) : WFValueM_i D V MT ME TypContext -> Prop :=
    | WFVM_Ask : forall Sigma (k : list Value -> ME Value) T,
      (forall env, WF_EnvG _ _ _ WFV env Sigma ->
        A (mk_WFValueM_i D V MT ME _ Sigma (k env) T)) ->
      WFValueM_Environment A (mk_WFValueM_i D V MT ME _ Sigma (do env <- ask; k env) T)
    | WFVM_Local : forall Sigma Gamma' f m k T' T,
      (* Local Changes are keep the environment well-formed in some Gamma'. *)
      (*ConsExtension (ConsExtensionC := TypContextCE') Sigma' Sigma -> *)
      (forall env, WF_EnvG _ V _ WFV env Sigma -> WF_EnvG _ V _ WFV (f env) (GammaSet _ Sigma Gamma')) ->
      (* The body of the local update is well-formed in the new environment *)
      (A (mk_WFValueM_i _ _ _ _ _ (GammaSet _ Sigma Gamma') m (return_ T'))) ->
      (* In any conservative extension of Sigma, the body of the bind
         is well-formed. *)
      (forall Sigma' v,
        ConsExtension Sigma' Sigma ->
        WFValueC _ _ _ WFV Sigma' v T' ->
        A (mk_WFValueM_i D V MT ME _ Sigma' (k v) T)) ->
      WFValueM_Environment A (mk_WFValueM_i _ _ _ _ _ Sigma (local f m >>= k) T).

    Definition ind_alg_WFVM_Environment (P : WFValueM_i D V MT ME TypContext -> Prop)
      (H_Ask : forall Sigma (k : list Value -> ME Value) T,
      (forall env, WF_EnvG _ _ _ _  env Sigma ->
        P (mk_WFValueM_i D V MT ME _ Sigma (k env) T)) ->
      P (mk_WFValueM_i D V MT ME _ Sigma (do env <- ask; k env) T))
      (H_Local : forall Sigma Gamma' f m k T' T,
        (* ConsExtension (ConsExtensionC := TypContextCE') Sigma' Sigma ->*)
      (forall env, WF_EnvG _ _ _ WFV env Sigma -> WF_EnvG _ _ _ WFV (f env) (GammaSet _ Sigma Gamma')) ->
      (P (mk_WFValueM_i _ _ _ _ _ (GammaSet _ Sigma Gamma') m (return_ T'))) ->
      (forall Sigma' v,
        ConsExtension Sigma' Sigma ->
        WFValueC _ _ _ WFV Sigma' v T' ->
        P (mk_WFValueM_i D V MT ME _ Sigma' (k v) T)) ->
      P (mk_WFValueM_i _ _ _ _ _ Sigma (local f m >>= k) T))
      (i : WFValueM_i D V MT ME _)
      (e : WFValueM_Environment P i)
      :
      P i :=
      match e in WFValueM_Environment _ i return P i with
        | WFVM_Ask Sigma k T WF_k =>
          H_Ask Sigma k T WF_k
        | WFVM_Local Sigma Gamma' f m k T' T (*Sub_Sig'_Sig *) WF_env WF_m WF_k =>
          H_Local Sigma Gamma' f m k T' T (*Sub_Sig'_Sig *) WF_env WF_m WF_k
      end.

    Definition WFVM_Environment_ifmap
      (A B : WFValueM_i D V MT ME _ -> Prop)
      (i : WFValueM_i D V MT ME _)
      (f : forall i, A i -> B i)
      (WFVM_a : WFValueM_Environment A i)
      :
      WFValueM_Environment B i :=
      match WFVM_a in WFValueM_Environment _ i return WFValueM_Environment B i with
        | WFVM_Ask Sigma k T WF_k =>
          WFVM_Ask _ Sigma k T (fun env WF_env => f _ (WF_k env WF_env))
        | WFVM_Local Sigma Gamma' f' m k T' T (*Sub_Sig'_Sig *) WF_env WF_m WF_k =>
          WFVM_Local _ Sigma Gamma' f' m k T' T (*Sub_Sig'_Sig *) WF_env (f _ WF_m)
          (fun Sigma'' v Sub_Sig''_Sig' WF_v_T' => (f _ (WF_k Sigma'' v Sub_Sig''_Sig' WF_v_T')))
      end.

    Global Instance iFun_wfvm_Environment : iFunctor WFValueM_Environment.
      constructor 1 with (ifmap := WFVM_Environment_ifmap).
      (* ifmap_fusion *)
      destruct a; simpl; intros; reflexivity.
      (* ifmap_id *)
      destruct a; simpl; intros; auto;
        apply f_equal; repeat (apply functional_extensionality_dep; intros); auto.
    Defined.

    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
    Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor WFValueM_Environment WFVM}.

    Global Instance wfvm_bind_Environment :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME TypContext WFV WFVM) WFValueM_Environment.
    Proof.
      constructor; unfold iAlgebra; intros.
      apply ind_alg_WFVM_Environment; try eassumption;
        unfold wfvm_bind_P; simpl; intros.
      (* ask *)
      rewrite <- associativity.
      apply (inject_i (subGF := Sub_WFVM_Environment_WFVM)).
      constructor.
      intros.
      apply H0; auto.
      (* local *)
      repeat rewrite <- associativity.
      apply (inject_i (subGF := Sub_WFVM_Environment_WFVM)).
      constructor 2 with (Gamma' := Gamma') (T' := T'); simpl in *; auto.
      generalize (H1 return_ return_); rewrite <- right_unit; rewrite <- left_unit; intro WF_m_T; apply WF_m_T.
      simpl; intros; repeat rewrite fmap_return; apply inj_return; congruence.
      intros; apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor; eauto.
      apply return_orn; auto.
      intros; apply H2; eauto.
      intros; eapply WFVM_ke_kt; eauto; eapply ConsExtension_trans; eauto.
    Defined.

    Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

    Context {TypContextCE' : ConsExtensionC TypContext}.
    Context {WFV_Weaken_WFV' : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P (TypContextCE := TypContextCE') D V _ WFV) WFV}.

    Lemma WF_Environment_Weaken : forall Sigma env gamma,
      WF_Environment D V _ WFV Sigma env gamma ->
      forall Sigma',
        ConsExtension Sigma' Sigma ->
        WF_Environment D V _ WFV Sigma' env gamma.
    Proof.
      intros; eapply P2_Env_P_P'; try eassumption.
      intros; eapply (WFV_Weaken D V _ WFV _ _ H1); eauto.
    Qed.

    Definition WFValue_Weaken'_P (i : WFValue_i D V TypContext) :=
      forall env,
        WFValueC _ _ _ WFV (GammaSet _ (wfv_S _ _ _ i) env) (wfv_v _ _ _ i) (wfv_T _ _ _ i).

    Inductive WFValue_Weaken'_Name := wfvalue_weaken'_name.

    Context {WFV_Weaken'_WFV : iPAlgebra WFValue_Weaken'_Name WFValue_Weaken'_P WFV}.

    Definition WFV_Weaken' := ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_Weaken'_WFV)).

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

    Context {wfvm_bind_alg :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.
    Context {EQV_proj1_alg :
      forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (EQV_E _ _)}.
    Context {WFV_proj1_a_WFV :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFV}.
     Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.
     Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
     Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Class GammaConsExtension'C (TypContext : Set)
      (ConsExt : ConsExtensionC TypContext)
      (GammaTyp : GammaTypContextC D TypContext) : Type :=
      {
        ConsExtension_GammaInsert : forall Sigma T,
          ConsExtension (ConsExtensionC := ConsExt) (GammaInsert _ T Sigma) Sigma}.

    Context {TypContextGCE' : GammaConsExtension'C TypContext TypContextCE' GammaTypContext}.

  End WFValue_Sec.

End EffReader.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
