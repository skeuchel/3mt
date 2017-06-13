Require Import FJ_tactics.
Require Import Functors.
Require Import List.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import MonadLib.

Section PNames.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (** SuperFunctor for Types. **)
  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (** SuperFunctor for Values. **)
  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.

  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {WF_SubStuckValue_V : WF_Functor _ _ Sub_StuckValue_V _ _}.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set -> Set.
  Context {Fun_E : forall A, Functor (E A)}.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)

  (** TYPING **)

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.

  Context {Typeof_E : forall T,
    FAlgebra TypeofName T (typeofR D MT) (E (DType D))}.

  Variable ME : Set -> Set.
  Context {Fun_ME : Functor ME}.
  Context {Mon_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.

  Context {bevalM_E : FAlgebra EvalName (Exp (E nat)) (evalMR V ME) (E nat)}.

  Definition bevalM (n: nat) := boundedFix_UP n (@f_algebra _ _ _ _ bevalM_E) (fail (A := Value V)).

  Section WFValue_Sec.

  Variable TypContext : Set.
  Context {TypContextCE : ConsExtensionC TypContext}.

  (* ============================================== *)
  (* WELL-FORMED NONTERMINATION                     *)
  (* ============================================== *)

  Inductive WFValueM_Bot (A : WFValueM_i D V MT ME TypContext -> Prop) :
    WFValueM_i D V MT ME TypContext -> Prop :=
  | WFVM_fail : forall Sigma T,
    WFValueM_Bot A (mk_WFValueM_i D V MT ME TypContext Sigma fail T).

  Definition ind_alg_WFVM_Bot (P : WFValueM_i D V MT ME _ -> Prop)
    (H_fail : forall Sigma T,
      P (mk_WFValueM_i _ _ _ _ _ Sigma fail T))
      (i : WFValueM_i D V MT ME _)
      (e : WFValueM_Bot P i)
      :
      P i :=
      match e in WFValueM_Bot _ i return P i with
        | WFVM_fail Sigma T => H_fail Sigma T
      end.

  Definition WFVM_Bot_ifmap
    (A B : WFValueM_i D V MT ME _ -> Prop)
    (i : WFValueM_i D V MT ME _)
    (f : forall i, A i -> B i)
    (WFVM_a : WFValueM_Bot A i)
    :
    WFValueM_Bot B i :=
    match WFVM_a in WFValueM_Bot _ i return WFValueM_Bot B i with
      | WFVM_fail Sigma T => WFVM_fail B Sigma T
    end.

    Global Instance iFun_wfvm_Bot : iFunctor WFValueM_Bot.
      constructor 1 with (ifmap := WFVM_Bot_ifmap).
      (* ifmap_fusion *)
      destruct a; simpl; intros; reflexivity.
      (* ifmap_id *)
      destruct a; simpl; intros; auto;
        apply f_equal; repeat (apply functional_extensionality_dep; intros); auto.
    Defined.

  (* ============================================== *)
  (* EXPRESSION EQUIVALENCE RELATION                *)
  (* ============================================== *)

  Section eqv_Section.

    Record eqv_i (A B : Set) : Set := mk_eqv_i
      {env_A : Env A;
        env_B : Env B;
        eqv_a : UP'_F (E A);
        eqv_b : UP'_F (E B)}.

    (** SuperFunctor for Equivalence Relation. **)
    Variable EQV_E : forall A B,
      (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.

    Definition E_eqv A B := iFix (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' :=
      E_eqv _ _ (mk_eqv_i A B gamma gamma' e e').

    (* Projection doesn't affect Equivalence Relation.*)

     Definition EQV_proj1_P A B (i : eqv_i A B) :=
      forall a' b' H H0, a' = proj1_sig (eqv_a _ _ i) ->
        b' = proj1_sig (eqv_b _ _ i) ->
        E_eqvC (env_A _ _ i) (env_B _ _ i) (exist _ a' H) (exist _ b' H0).

     Inductive EQV_proj1_Name := eqv_proj1_name.
     Context {EQV_proj1_EQV : forall A B,
       iPAlgebra EQV_proj1_Name (@EQV_proj1_P A B) (EQV_E A B)}.
     Context {Fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.

     Definition EQV_proj1 A B:=
       ifold_ (EQV_E A B) _ (ip_algebra (iPAlgebra := EQV_proj1_EQV A B)).

   End eqv_Section.

   Variable EQV_E : forall A B, (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.
   Context {Fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
   Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
   Context {funWFV : iFunctor WFV}.

    Class GammaTypContextC (TypContext : Set) : Set :=
      { Gamma : TypContext -> list (DType D);
        GammaSet : TypContext -> list (DType D) -> TypContext;
        GammaInsert : DType D -> TypContext -> TypContext;
        Gamma_GammaSet : forall Sigma env,
          Gamma (GammaSet Sigma env) = env;
        GammaSet_Gamma : forall Sigma,
          GammaSet Sigma (Gamma Sigma) = Sigma;
        Gamma_Insert : forall Sigma gamma T,
          Gamma Sigma = gamma ->
          Gamma (GammaInsert T Sigma) = insert _ T gamma
      }.

    Class GammaConsExtensionC (TypContext : Set)
      (ConsExt : ConsExtensionC TypContext)
      (GammaTyp : GammaTypContextC TypContext) : Type :=
      {
        ConsExtension_Gamma : forall Sigma Sigma',
          ConsExtension Sigma' Sigma ->
          Gamma Sigma = Gamma Sigma'}.

    Context {GammaTypContext : GammaTypContextC TypContext}.
    Context {TypContext_GCE : GammaConsExtensionC TypContext _ _}.

   Definition WF_eqv_environment_P
     (gamma_gamma' : prod (Env nat) (Env (DType D))) (Sigma : TypContext) :=
     (forall m b : nat,
       lookup (fst gamma_gamma') m = Some b ->
       exists T, lookup (snd gamma_gamma') b = Some T) /\
     Datatypes.length (snd gamma_gamma') = Datatypes.length (fst gamma_gamma') /\
     (forall m b : nat, lookup (fst gamma_gamma') m = Some b -> b = m) /\
     (Gamma Sigma = snd gamma_gamma').

   Lemma WF_eqv_environment_P_Sub : forall gamma_gamma' Sigma Sigma',
        WF_eqv_environment_P gamma_gamma' Sigma ->
        ConsExtension Sigma' Sigma ->
        WF_eqv_environment_P gamma_gamma' Sigma'.
   Proof.
     intros; destruct H as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
     repeat split; eauto.
     intros; apply sym_eq; erewrite <- WF_gamma'', ConsExtension_Gamma; eauto.
   Qed.

    Lemma WF_eqv_environment_P_insert : forall Sigma gamma gamma' T,
      WF_eqv_environment_P (gamma, gamma') Sigma ->
      WF_eqv_environment_P (insert _ (Datatypes.length gamma) gamma, insert _ T gamma')
      (GammaInsert T Sigma).
    Proof.
      intros; destruct H as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
      unfold WF_eqv_environment_P; simpl in *|-*; repeat split; auto.
      rewrite <- WF_gamma2.
      revert WF_gamma; clear; simpl; induction gamma;
        destruct m; simpl; intros; try discriminate.
      injection H; intros; subst.
      clear; induction gamma'; simpl; eauto; eexists.
      injection H; intros; subst.
      generalize b (WF_gamma 0 _ (eq_refl _)); clear; induction gamma'; simpl; intros b H;
        destruct H as [T' lookup_T']; try discriminate.
      destruct b; eauto.
      eapply IHgamma.
      intros n0 b0 H0; eapply (WF_gamma (S n0) _ H0).
      eassumption.
      assert (exists m', Datatypes.length gamma = m') as m'_eq
        by (eexists _; reflexivity); destruct m'_eq as [m' m'_eq].
      rewrite m'_eq; generalize m' gamma WF_gamma2; clear; induction gamma';
        destruct gamma; intros; simpl; try discriminate;
          try injection H7; intros; eauto.
      simpl in *|-*.
      intro; caseEq (beq_nat m (Datatypes.length gamma)).
      assert (exists m', m' = Datatypes.length gamma) as ex_m' by
        (eexists _; reflexivity); destruct ex_m' as [m' m'_eq];
          rewrite <- m'_eq in H at 1.
      rewrite <- WF_gamma2 in H0.
      rewrite (beq_nat_true _ _ H).
      rewrite (beq_nat_true _ _ H), m'_eq in H0.
      rewrite <- WF_gamma2 in m'_eq; rewrite m'_eq.
      generalize m' b H0; clear.
      induction gamma; simpl; intros; try discriminate.
      injection H0; auto.
      eauto.
      eapply WF_gamma'.
      rewrite <- WF_gamma2 in H0.
      assert (exists m', m' = Datatypes.length gamma) as ex_m' by
      (eexists _; reflexivity); destruct ex_m' as [m' m'_eq].
      generalize m' m (beq_nat_false _ _ H) H0; clear;
        induction gamma; simpl; destruct m; intros;
          try discriminate; eauto.
      elimtype False; eauto.
      intros; eapply Gamma_Insert; eauto.
    Qed.

    Definition WF_eqv_environment'_P e e'
     (gamma_gamma' : prod (Env nat) (Env (DType D))) (Sigma : TypContext) :=
     E_eqvC EQV_E (fst gamma_gamma') (snd gamma_gamma') e e' /\
     WF_eqv_environment_P gamma_gamma' Sigma.

   Lemma WF_eqv_environment'_P_Sub : forall e e' gamma_gamma' Sigma Sigma',
        WF_eqv_environment'_P e e' gamma_gamma' Sigma ->
        ConsExtension Sigma' Sigma ->
        WF_eqv_environment'_P e e' gamma_gamma' Sigma' .
   Proof.
     intros; destruct H as [WF_gamma [WF_gamma2 [WF_gamma' [WF_gamma'' WF_Sigma]]]].
     repeat split; eauto.
     intros; apply sym_eq; erewrite <- WF_Sigma, ConsExtension_Gamma; eauto.
   Qed.

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) ->
      WFValueM_i D V MT ME TypContext -> Prop.
    Variable funWFVM : iFunctor WFVM.

    Definition eqv_soundness_X_P i :=
      forall n
      (IH : forall gamma gamma' e'  e'',
        E_eqvC EQV_E gamma' gamma e'' e' ->
        forall Sigma
          (WF_gamma : forall n b, lookup gamma' n = Some b ->
            exists T, lookup gamma b = Some T)
          (WF_gamma2 : List.length gamma = List.length gamma')
          (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
          (WF_Sigma : Gamma Sigma = gamma),
          WFValueMC _ _ MT ME _ WFVM Sigma (bevalM n e'')
          (typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e'))),
      E_eqv EQV_E _ _ i /\
      forall Sigma
        (WF_gamma : forall n b, lookup (env_A _ _ i) n = Some b ->
          exists T, lookup (env_B _ _ i) b = Some T)
        (WF_gamma2 : List.length (env_B _ _ i) = List.length (env_A _ _ i))
        (WF_gamma' : forall n b, lookup (env_A _ _ i) n = Some b -> b = n)
        (WF_Sigma : Gamma Sigma = env_B _ _ i),
        WFValueMC _ _ MT ME _ WFVM Sigma (bevalM (S n) (eqv_a _ _ i))
        (typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig (eqv_b _ _ i))).

    Inductive eqv_soundness_X_Name : Set := eqv_soundness_X_name.

    Context {eqv_soundness_X_alg :
      iPAlgebra eqv_soundness_X_Name eqv_soundness_X_P (EQV_E _ _)}.
    Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor WFValueM_Bot WFVM}.

    Lemma eval_soundness_X :
      forall n gamma gamma' e'  e'',
        E_eqvC EQV_E gamma' gamma e'' e' ->
        forall Sigma
          (WF_gamma : forall n b, lookup gamma' n = Some b ->
            exists T, lookup gamma b = Some T)
          (WF_gamma2 : List.length gamma = List.length gamma')
          (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
          (WF_Sigma : Gamma Sigma = gamma),
          WFValueMC _ _ MT ME _ WFVM Sigma (bevalM n e'')
          (typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e')).
    Proof.
      induction n; simpl.
      (* Base case. *)
      unfold bevalM; simpl; intros; apply (inject_i (subGF := Sub_WFVM_Bot_WFVM)); constructor.
      (* Inductive case. *)
      intros gamma gamma' e' e'' e'_e''_eqv; revert n IHn.
      eapply (ifold_ (EQV_E _ _) _ (ip_algebra (iPAlgebra := eqv_soundness_X_alg)) _ e'_e''_eqv).
    Qed.

    Definition eqv_soundness_X'_P
      (typeof_rec : Exp (E (DType D)) -> typeofR D MT)
      (eval_rec : Exp (E nat) -> evalMR V ME)
      (typeof_F : Mixin (Exp (E (DType D))) (E (DType D)) (typeofR D MT))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalMR V ME))
      (i : eqv_i nat (DType D)) :=
      E_eqv EQV_E _ _ i /\
      eval_soundness'_P D V (E nat) MT ME _ WFVM
      _ (E (DType D)) _ WF_eqv_environment'_P
      (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec
      typeof_F eval_F
      (proj1_sig (eqv_b _ _ i), proj1_sig (eqv_a _ _ i))
      (conj (proj2_sig (eqv_b _ _ i)) (proj2_sig (eqv_a _ _ i))).

    Definition soundness_X'_P
      (typeof_rec : Exp (E (DType D)) -> typeofR D MT)
      (eval_rec : Exp (E nat) -> evalMR V ME)
      (typeof_F : Mixin (Exp (E (DType D))) (E (DType D)) (typeofR D MT))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalMR V ME))
      (i : eqv_i nat (DType D)) :=
      forall (IH : forall (e : Exp _) (e' : Exp _)
        pb Sigma (WF_gamma'' : WF_eqv_environment'_P e e' pb Sigma),
        E_eqvC EQV_E (fst pb) (snd pb) e e' ->
        WFValueMC _ _ MT ME _ WFVM Sigma (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e))))
        (typeof_rec e')),
      E_eqv EQV_E _ _ i /\
      eval_soundness'_P D V (E nat) MT ME _ WFVM
      _ (E (DType D)) _ WF_eqv_environment'_P
      (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec
      typeof_F eval_F
      (proj1_sig (eqv_b _ _ i), proj1_sig (eqv_a _ _ i))
      (conj (proj2_sig (eqv_b _ _ i)) (proj2_sig (eqv_a _ _ i))).

    Inductive eqv_soundness_X'_Name : Set := eqv_soundness_X'_name.
    Inductive soundness_X'_Name : Set := soundness_X'_name.

    Context {eqv_soundness_X'_alg :
      forall eval_rec,
      iPAlgebra soundness_X'_Name
      (soundness_X'_P (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := bevalM_E))) (EQV_E _ _)}.

    Global Instance Lift_soundness_X_alg
      typeof_rec eval_rec typeof_alg eval_alg
      EQV_G {fun_EQV_G : iFunctor EQV_G}
      {EQV_G_EQV_Alg : iPAlgebra eqv_soundness_X'_Name (eqv_soundness_X'_P typeof_rec
        eval_rec typeof_alg eval_alg) EQV_G} :
        iPAlgebra soundness_X'_Name (soundness_X'_P
          typeof_rec eval_rec typeof_alg eval_alg) EQV_G.
      intros; econstructor; generalize (ip_algebra); unfold iAlgebra; intros.
      unfold soundness_X'_P; intros.
      assert (EQV_G (eqv_soundness_X'_P typeof_rec eval_rec typeof_alg eval_alg) i).
      eapply ifmap; try eapply H0.
      intros; apply H1; apply IH.
      apply (H _ H1).
    Defined.

    Lemma soundness_X' :
      forall eval_rec gamma gamma' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' ->
        soundness_X'_P (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := bevalM_E)) (mk_eqv_i nat (DType D) gamma gamma' e' e'').
    Proof.
      intros; apply (ifold_ (EQV_E _ _ )); try assumption.
      apply ip_algebra.
    Qed.

    Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.

    (* ============================================== *)
    (* Evaluation preserves Well-Formedness           *)
    (* ============================================== *)

    Context {EQV_proj1_EQV : forall A B,
      iPAlgebra EQV_proj1_Name (@EQV_proj1_P EQV_E A B) (EQV_E A B)}.

    Lemma eval_soundness_X' : forall n gamma gamma' e'  e'',
      E_eqvC EQV_E gamma gamma' e' e'' ->
      forall Sigma
        (WF_gamma : forall n b, lookup gamma n = Some b ->
          exists T, lookup gamma' b = Some T)
        (WF_gamma2 : List.length gamma' = List.length gamma)
        (WF_gamma' : forall n b, lookup gamma n = Some b -> b = n)
        (WF_Sigma : Gamma Sigma = gamma'),
        WFValueMC _ _ MT ME _ WFVM Sigma (bevalM n e')
        (typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e'')).
    Proof.
      induction n; simpl;
        intros; unfold beval; simpl in *|-*.
      apply (inject_i (subGF := Sub_WFVM_Bot_WFVM)); econstructor; eauto.
      generalize (soundness_X' (bevalM n) _ _ _ _ H).
      unfold soundness_X'_P; simpl; intros.
      unfold bevalM; intros; simpl.
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig e'') (proj2_sig _)).
      unfold typeof, evalM, mfold; simpl; unfold in_t;
        repeat rewrite wf_malgebra; unfold mfold; apply H0; auto.
      intros; unfold bevalM; erewrite bF_UP_in_out.
      instantiate (1 := proj2_sig _).
      destruct e; simpl; auto.
      unfold bevalM in IHn.
      destruct WF_gamma'' as [e'0_eqv [WF_gamma'' [WF_gamma''2 [WF_gamma''' Sub_Gamma_gamma'']]]].
      subst; eapply IHn; eauto.
      intros; unfold bevalM; erewrite bF_UP_in_out.
      instantiate (1 := proj2_sig _); destruct e; auto.
      intro; rewrite in_out_UP'_inverse; auto; exact (proj2_sig _).
      repeat split; auto.
      simpl; destruct e'; destruct e''; auto.
      simpl; eapply (EQV_proj1 _ _ _ _ H); simpl; auto.
      intros;
        destruct WF_Gamma as [e'0_eqv [WF_gamma'' [WF_gamma''2 [WF_gamma''' Sub_Gamma_gamma'']]]];
          subst.
      eapply IHn with (gamma := fst pb) (gamma' := snd pb); eauto.
      simpl; destruct (fst a); destruct (snd a);
        apply (EQV_proj1 _ _ _ _ e'0_eqv); simpl; auto.
      generalize in_out_UP'_inverse; simpl; intros in_eq';
        apply in_eq'; auto.
    Qed.

    Definition WF_EnvG (env : list (Value V)) (Sigma : TypContext) : Prop :=
      P2_Env (WFValueC _ _ _ WFV Sigma) env (Gamma Sigma).

    Context {wfvm_bind_alg : iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME TypContext WFV WFVM) WFVM}.
    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.

    Global Instance wfvm_bind_Bot :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME TypContext WFV WFVM) WFValueM_Bot.
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_Bot;
        try assumption; unfold wfvm_bind_P; simpl; intros.
    (* WFVM_fail *)
      rewrite bind_fail; apply (inject_i (subGF := Sub_WFVM_Bot_WFVM)); constructor.
    Qed.

  End WFValue_Sec.

  Section Pure_Sound_X_Sec.

    Context {Environment_ME : Environment ME (Env (Value V))}.

   Variable EQV_E : forall A B, (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.
   Context {Fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
    Variable WFV : (WFValue_i D V (list (DType D)) -> Prop) -> WFValue_i D V (list (DType D)) -> Prop.
    Context {funWFV : iFunctor WFV}.
    Variable WFVM : (WFValueM_i D V MT ME (list (DType D)) -> Prop) ->
      WFValueM_i D V MT ME (list (DType D)) -> Prop.
    Variable funWFVM : iFunctor WFVM.

    Global Instance GammaTypContext : GammaTypContextC (list (DType D)) :=
      {| Gamma := id;
        GammaSet := fun _ => id;
        GammaInsert := insert _|}.
    Proof.
      unfold id; intros; congruence.
      unfold id; intros; congruence.
      unfold id; intros; congruence.
    Defined.

    Global Instance GammaTypContextCE : ConsExtensionC (list (DType D)) :=
      {| ConsExtension := fun gamma gamma' => gamma = gamma' |}.
    Proof.
      (* ConsExtension_id *)
      eauto.
      (* ConsExtension_trans *)
      intros; congruence.
    Defined.

    Global Instance GammaTypContextGCE :
      GammaConsExtensionC (list (DType D)) (GammaTypContextCE)
      (GammaTypContext).
    Proof.
      econstructor; eauto.
    Defined.

    Definition Pure_Sound_X_P (i : WFValueM_i D V MT ME (list (DType D))) :=
      forall T gamma''
        (WF_gamma'' : WF_EnvG (GammaTypContext := GammaTypContext) _ WFV gamma'' (wfvm_S _ _ _ _ _ i)),
        wfvm_T _ _ _ _ _ i = return_ T ->
        local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = fail \/
        exists v : Value V,
          local (fun _ => gamma'') (wfvm_v _ _ _ _ _ i) = return_ (M := ME) v /\
          WFValueC _ _ _ WFV (wfvm_S _ _ _ _ _ i) v T.

    Inductive Pure_Sound_X_Name := pure_sound_X_name.

    Context {Pure_Sound_X_WFVM : iPAlgebra Pure_Sound_X_Name Pure_Sound_X_P WFVM}.
    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.
    Context {EQV_proj1_EQV : forall A B,
      iPAlgebra EQV_proj1_Name (@EQV_proj1_P EQV_E A B) (EQV_E A B)}.
    Context {eqv_soundness_X'_alg :
      forall eval_rec,
      iPAlgebra soundness_X'_Name
      (soundness_X'_P _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := bevalM_E))) (EQV_E _ _)}.
    Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
    Context {Sub_WFVM_Bot_WFVM : Sub_iFunctor (WFValueM_Bot (list (DType D))) WFVM}.

    Theorem eval_Pure_Sound_X :
      forall n Sigma gamma gamma' gamma'' e' e'',
        E_eqvC EQV_E gamma' gamma e'' e' ->
        forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
          exists T, lookup gamma b = Some T)
        (WF_gamma'' : WF_EnvG (GammaTypContext := GammaTypContext) _ WFV gamma'' Sigma)
        (WF_gamma2 : List.length gamma = List.length gamma')
        (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
        (WF_Sigma : Gamma Sigma = gamma) (T : DType D),
        typeof D (E (DType D)) MT (Typeof_E := Typeof_E) (proj1_sig e') = return_ T ->
        local (fun _ => gamma'') (bevalM n e'') = fail \/
        exists v : Value V,
          local (fun _ => gamma'') (bevalM n e'') = return_ (M := ME) v /\
          WFValueC _ _ _ WFV Sigma v T.
    Proof.
      intros.
      intros; eapply (ifold_ WFVM _ (ip_algebra (iPAlgebra := Pure_Sound_X_WFVM))
        _ (eval_soundness_X' (list (DType D)) _ WFVM n _ _ _ _ H Sigma WF_gamma WF_gamma2 WF_gamma' WF_Sigma)); eauto.
    Qed.

    Global Instance Pure_Sound_WFVM_base' :
      iPAlgebra Pure_Sound_X_Name Pure_Sound_X_P (WFValueM_base D V MT ME _ WFV).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV)
        (Fail_MT := _) (Monad_ME := _);
        try assumption; unfold Pure_Sound_X_P; intros; right.
      (* WFVM_Return' *)
      simpl; rewrite local_return; exists v; repeat split; simpl in *; auto.
      destruct H1 as [mt' mt'_eq]; subst.
      destruct (fmap_exists _ _ _ _ _ H2) as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0; apply (WFV_proj1_b D V _ WFV _ _ H0); simpl; auto.
      (* WFVM_Untyped' *)
      simpl in H0; apply sym_eq in H0.
      apply FailMonad_Disc in H0; destruct H0; auto.
    Qed.

    Context {FailEnvME : FailEnvironmentMonad (Env (Value V)) ME}.

    Global Instance Pure_Sound_WFVM_Bot :
      iPAlgebra Pure_Sound_X_Name Pure_Sound_X_P (WFValueM_Bot (list (DType D))).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_Bot;
        try assumption; unfold Pure_Sound_X_P; intros.
    (* WFVM_fail *)
      left; simpl.
      apply local_fail.
    Qed.

  End Pure_Sound_X_Sec.

End PNames.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
