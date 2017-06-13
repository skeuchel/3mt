Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffState.
Require Import EffExcept.
Require Export ESoundS.

Section ESoundES.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Exception_ME : Exception ME Datatypes.unit}.
  Context {StateM_ME : StateM ME (list (Names.Value V))}.
  Context {Fail_ME : FailMonad ME}.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
  Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D MT) E}.

  Context {evalM_E : FAlgebra EvalName (Exp E) (evalMR V ME) E}.
  Context {evalM_E' : forall T, FAlgebra EvalName T (evalMR V ME) E}.

  Variable TypContext : Set.
  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Context {funWFV : iFunctor WFV}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Context {TypContextCE : ConsExtensionC TypContext}.
  Context {TypContext_WFE : WF_EnvC V TypContext}.

  Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME TypContext WFV) WFVM}.
  Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State D V MT ME TypContext) WFVM}.
  Context {Sub_WFVM_Except_WFVM : Sub_iFunctor (WFValueM_Except D V MT ME _) WFVM}.

  Context {TypContext_S : SigTypContextC D TypContext}.
  Context {TypContext_SCE : SigConsExtensionC D TypContext _ _}.

  Section Except_State_Sound_Sec.

    Variable WFV' : (WFValue_i D V (list (DType D)) -> Prop) -> WFValue_i D V (list (DType D)) -> Prop.
    Context {funWFV' : iFunctor WFV'}.

    Variable WFVM' : (WFValueM_i D V MT ME (list (DType D)) -> Prop) ->
      WFValueM_i D V MT ME (list (DType D)) -> Prop.
    Context {funWFVM' : iFunctor WFVM'}.

    Definition Except_State_Sound_P (i : WFValueM_i D V MT ME (list (DType D))) :=
      forall T (env : list (Value V)),
        WF_Env (WF_EnvC := DType_Env_WFE D V WFV') _ env (wfvm_S _ _ _ _ _ i) ->
        fmap (@proj1_sig _ _) (wfvm_T _ _ _ _ _ i) = return_ (proj1_sig T) ->
        (exists v : Value V, exists env', exists Sigma' : list (DType D),
          (put env) >> wfvm_v _ _ _ _ _ i = put env' >> return_ (M := ME) v /\
          WFValueC D V _ WFV' Sigma' v T) \/
        (exists t, exists env', exists Sigma' : list (DType D),
          put env >> wfvm_v _ _ _ _ _ i = put env' >> throw t
        /\ WF_Env (WF_EnvC := DType_Env_WFE D V WFV') _ env' Sigma'
        /\ (forall n T, lookup (wfvm_S _ _ _ _ _ i) n = Some T -> lookup Sigma' n = Some T)).

    Inductive Except_State_Sound_Name := except_state_sound_name.

    Global Instance Except_State_Sound_WFVM_State :
      iPAlgebra Except_State_Sound_Name Except_State_Sound_P
      (WFValueM_State (TypContext_WFE := DType_Env_WFE _ _ WFV') D V MT ME (list (DType D))).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_State with (State_M := StateM_ME)
        (TypContextCE := DType_Env_CE _) (TypContext_WFE := DType_Env_WFE _ _ WFV');
        try assumption; unfold Except_State_Sound_P; simpl; intros.
      (* WFVM_Get *)
      destruct (H0 env H1 T0 env H1 H2) as [[v [env' [Sigma' [eval_eq WF_v_T]]]]
        | [[] [env' [Sigma' [k_eq [WF_env_Sigma' Sigma'_Cons]]]]]].
      left; exists v; exists env'; exists Sigma'.
      unfold wbind; rewrite associativity.
      generalize put_get as put_get'; intros; unfold wbind in put_get'; rewrite put_get'.
      rewrite <- associativity.
      rewrite <- left_unit.
      split; unfold wbind; auto.
      right; exists tt; exists env'; exists Sigma';
        unfold wbind; rewrite associativity; repeat split; auto.
      generalize put_get; unfold wbind; intros pg; rewrite pg;
        rewrite <- associativity; rewrite <- left_unit; auto.
      (* WFVM_Put *)
      unfold wbind; rewrite associativity.
      generalize put_put as put_put'; intros; unfold wbind in put_put'; rewrite put_put';
        clear put_put'.
      destruct (H2 T0 env H0 H4) as [[v [env' [Sigma'' [eval_eq WF_v_T]]]]
        | [[] [env' [Sigma'' [k_eq [WF_env_Sigma'' Sigma''_Cons]]]]]].
      left; exists v; exists env'; exists Sigma''; split; auto.
      right; exists tt; exists env'; exists Sigma''; split; auto.
    Qed.

    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.

    Global Instance Except_State_Sound_WFVM_Base :
      iPAlgebra Except_State_Sound_Name Except_State_Sound_P (WFValueM_base D V MT ME _ WFV').
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV')
        (Fail_MT := Fail_MT) (Monad_ME := Mon_M);
        try assumption; unfold Except_State_Sound_P; simpl; intros.
      (* WFVM_Return' *)
      left; exists v; exists env; exists Sigma; split; auto.
      destruct H1 as [mt' mt'_eq]; subst.
      rewrite fmap_fusion in H3.
      destruct (fmap_exists _ _ _ _ _ H3) as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0 as [T0 T0_UP'].
      apply (WFV_proj1_b _ _ _ _ _ _ H0); simpl; auto.
      simpl in T'_eq; congruence.
      (* WFVM_Untyped' *)
      simpl in H1; apply sym_eq in H1.
      unfold wbind in H1;
        rewrite fmap_m, <- associativity, bind_fail in H1.
      apply FailMonad_Disc in H1; destruct H1; auto.
    Defined.

    Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (env : list (Names.Value (Fun_V := Fun_V) V)),
      (exists a : A, exists env' : list (Names.Value (Fun_V := Fun_V) V),
        wbind (H := Mon_M) (put (StateM := StateM_ME) env)
        mte = wbind (H := Mon_M) (put (StateM := StateM_ME) env') (return_ (Monad := Mon_M) a)) \/
      (exists env', put env >> mte = put env' >> throw tt)}.
    Context {MT_eq_dec : forall (A : Set) (mta : MT A),
      {exists a, mta = return_ a} + {mta = fail}}.

    Section Except_State_Sound_WFVM_Except_Sec.
      (* Section with one possible put_catch law. *)
      Context {put_catch : forall (A : Set) (env : list (Value V)) e h,
        put env >>= (fun _ => catch (A := A) e h) = catch (put env >>= fun _ => e) h}.
      Context {put_throw : forall (A B : Set) (env env' : list (Value V)) t,
        put env >>= (fun _ => throw t (A := A)) = put env' >>= (fun _ => throw t) ->
        put env >>= (fun _ => throw t (A := B)) = put env' >>= (fun _ => throw t)}.
      Context {Put_Exception_Disc :
        forall (A : Set) (a : A) env env' n,
          (put env >>= fun _ => return_ a) <> put env' >>= fun _ => throw n}.

      Global Instance Except_State_Sound_WFVM_Except :
        iPAlgebra Except_State_Sound_Name Except_State_Sound_P (WFValueM_Except D V MT ME _).
      Proof.
        econstructor.
        unfold iAlgebra; intros; apply ind_alg_WFVM_Except with (Exception_ME := Exception_ME)
          (Fail_MT := Fail_MT) (eq_DType_DT := eq_DType_DT) (TypContextCE := DType_Env_CE _);
          try assumption; unfold Except_State_Sound_P; simpl; intros.
      (* throw case *)
        simpl; right; exists tt; exists env; exists Sigma; split; auto.
      (* catch case *)
        destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
        destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
        repeat rewrite <- left_unit in H3.
        caseEq (eq_DType _ (proj1_sig T') T''); rewrite H4 in H3.
        destruct (H0 _ _ H2 H3) as [[v' [env' [Sigma' [ek'_eq WF_v'_T']]]] |
          [[] [env' [Sigma' [ek'_eq [WF_env'_Sigma' Sigma'_Cons]]]]]].
        destruct (ME_eq_dec' _ e' env) as [[v'' [env'' e'_eq]] | [env'' e'_eq]];
          subst.
        left; exists v'; exists env'; exists Sigma'; split; auto.
        unfold wbind; rewrite associativity, put_catch.
        unfold Value in *|-*; unfold wbind in e'_eq, ek'_eq; rewrite e'_eq, <- put_catch,
          catch_return, <- ek'_eq, associativity, e'_eq; auto.
        unfold Value in *|-*; unfold wbind in *|-*; rewrite associativity in ek'_eq;
          rewrite e'_eq in ek'_eq; rewrite <- associativity, bind_throw in ek'_eq.
        elimtype False; eapply Put_Exception_Disc with (a := v') (env' := env'') (env := env');
          eauto with typeclass_instances; unfold wbind; rewrite <- left_unit; eauto.
        destruct (ME_eq_dec' _ e' env) as [[v'' [env'' e'_eq]] | [env'' e'_eq]];
          subst.
        right; exists tt; exists env'; exists Sigma'; unfold wbind in *|-*; split; auto.
        unfold Value in *|-*; rewrite associativity, e'_eq in ek'_eq.
        rewrite associativity, put_catch, e'_eq, <- put_catch, catch_return; auto.
        unfold Value in *|-*; unfold wbind in *|-*; rewrite associativity, e'_eq, <- associativity in ek'_eq.
        rewrite rewrite_do with (m' := fun _ => throw tt) in ek'_eq.
        destruct (H1 tt Sigma' Sigma'_Cons T env' WF_env'_Sigma') as
          [[v'' [env''' [Sigma''' [ek''_eq WF_v''_T'']]]] |
            [[] [env''' [Sigma''' [ek''_eq [WF_env'''_Sigma''' Sigma'''_Cons]]]]]].
        rewrite <- H3.
        rewrite (rewrite_do) with (m' := fun U => kT U T'').
        rewrite (rewrite_do) with (m := fun U => return_ T' >>= _) (m' := fun U => kT U T').
        apply kt_eq; rewrite (eq_DType_eq _ _ _ H4); auto.
        apply functional_extensionality; intros; rewrite <- left_unit; auto.
        apply functional_extensionality; intros; rewrite <- left_unit; auto.
        left; exists v''; exists env'''; exists Sigma'''; split; auto.
        unfold wbind in *|-*; rewrite associativity, put_catch, e'_eq.
        rewrite (put_throw _ _ _ _ _ ek'_eq), <-put_catch, catch_throw',
          <- associativity; auto.
        right; exists tt; exists env'''; exists Sigma'''; repeat split; auto.
        unfold wbind in *|-*.
        unfold wbind in *|-*; rewrite associativity, put_catch, e'_eq.
        rewrite (put_throw _ _ _ _ _ ek'_eq), <-put_catch, catch_throw',
          <- associativity; auto.
        rewrite bind_throw; reflexivity.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
        rewrite <- left_unit in H3.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
      Qed.

    End Except_State_Sound_WFVM_Except_Sec.

    Section Except_State_Sound_WFVM_Except_Sec2.
      (* Section with the other possible put_catch law. *)
      Context {put_catch' : forall (A : Set) (env : list (Value V)) e h,
        put env >>= (fun _ => catch (A := A) e h) =
        catch (put env >>= fun _ => e) (fun t => put env >>= fun _ => (h t))}.
      Context {Put_Exception_Disc :
        forall (A B : Set) (a : A) env env' n,
          (put env >>= fun _ => return_ a) <> put env' >>= fun _ => throw n}.

      Lemma put_catch'' : forall (A : Set) (env env' : list (Value V)) (e : ME A) h,
        catch (put env >>= fun _ => e) (fun t => put env' >>= fun _ => (h t)) =
        put env >> catch e (fun t => put env' >>= (fun _ => h t)).
      Proof.
        intros; generalize (put_put env env'); unfold wbind; intros put_put'.
        rewrite put_catch'.
        assert ((fun t : Datatypes.unit => put env' >>= (fun _ : Datatypes.unit => h t))
          = (fun t : Datatypes.unit =>
            put env >>=
            (fun _ : Datatypes.unit => put env' >>= (fun _ : Datatypes.unit => h t)))) as H
        by (apply functional_extensionality; destruct x; rewrite associativity, put_put'; auto).
        rewrite H; auto.
      Qed.

      Global Instance Except_State_Sound_WFVM_Except2 :
        iPAlgebra Except_State_Sound_Name Except_State_Sound_P (WFValueM_Except D V MT ME _).
      Proof.
        econstructor.
        unfold iAlgebra; intros; apply ind_alg_WFVM_Except with (Exception_ME := Exception_ME)
          (Fail_MT := Fail_MT) (eq_DType_DT := eq_DType_DT) (TypContextCE := DType_Env_CE _);
          try assumption; unfold Except_State_Sound_P; simpl; intros.
      (* throw case *)
        simpl; right; exists tt; exists env; exists Sigma; split; auto.
      (* catch case *)
        destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
        destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
        repeat rewrite <- left_unit in H3.
        caseEq (eq_DType _ (proj1_sig T') T''); rewrite H4 in H3.
        destruct (H0 _ _ H2 H3) as [[v' [env' [Sigma' [ek'_eq WF_v'_T']]]] |
          [[] [env' [Sigma' [ek'_eq [WF_env'_Sigma' Sigma'_Cons]]]]]].
        destruct (ME_eq_dec' _ e' env) as [[v'' [env'' e'_eq]] | [env'' e'_eq]];
          subst.
        left; exists v'; exists env'; exists Sigma'; split; auto.
        unfold wbind; rewrite associativity, put_catch'.
        unfold Value in *|-*; unfold wbind in e'_eq, ek'_eq; rewrite e'_eq.
        rewrite put_catch'', catch_return, <- ek'_eq, associativity, e'_eq; auto.
        unfold Value in *|-*; unfold wbind in *|-*; rewrite associativity in ek'_eq;
          rewrite e'_eq in ek'_eq; rewrite <- associativity, bind_throw in ek'_eq.
        elimtype False; eapply Put_Exception_Disc with (a := v') (env' := env'') (env := env');
          eauto with typeclass_instances; unfold wbind; rewrite <- left_unit; eauto.
        destruct (ME_eq_dec' _ e' env) as [[v'' [env'' e'_eq]] | [env'' e'_eq]];
          subst.
        right; exists tt; exists env'; exists Sigma'; unfold wbind in *|-*; split; auto.
        unfold Value in *|-*; rewrite associativity, e'_eq in ek'_eq.
        rewrite associativity, put_catch', e'_eq, put_catch'', catch_return; auto.
        unfold Value in *|-*; unfold wbind in *|-*; rewrite associativity, e'_eq, <- associativity in ek'_eq.
        rewrite rewrite_do with (m' := fun _ => throw tt) in ek'_eq.
        destruct (H1 tt Sigma (fun _ _ => id) T env H2) as
          [[v'' [env''' [Sigma''' [ek''_eq WF_v''_T'']]]] |
            [[] [env''' [Sigma''' [ek''_eq [WF_env'''_Sigma''' Sigma'''_Cons]]]]]].
        rewrite <- H3.
        rewrite (rewrite_do) with (m' := fun U => kT U T'').
        rewrite (rewrite_do) with (m := fun U => return_ T' >>= _) (m' := fun U => kT U T').
        apply kt_eq; rewrite (eq_DType_eq _ _ _ H4); auto.
        apply functional_extensionality; intros; rewrite <- left_unit; auto.
        apply functional_extensionality; intros; rewrite <- left_unit; auto.
        left; exists v''; exists env'''; exists Sigma'''; split; auto.
        generalize put_put; unfold wbind; intros put_put'.
        unfold wbind in *|-*; rewrite associativity, put_catch', e'_eq,
          put_catch'', catch_throw'; unfold wbind; rewrite associativity,
            put_put', <- associativity; auto.
        right; exists tt; exists env'''; exists Sigma'''; repeat split; auto.
        generalize put_put; unfold wbind in *|-*; intros put_put'.
        unfold wbind in *|-*; rewrite associativity, put_catch', e'_eq,
          put_catch'', catch_throw'; unfold wbind; rewrite associativity,
            put_put', <- associativity; auto.
        rewrite bind_throw; auto.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
        rewrite <- left_unit in H3.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
        elimtype False; eapply FailMonad_Disc with (M := MT) (a := (proj1_sig T)) (mb := kT');
          eauto with typeclass_instances; unfold wbind;
            rewrite fmap_m in H3; rewrite <- associativity in H3;
              rewrite rewrite_do with (m' := fun _ : C => fail) in H3; auto;
                apply functional_extensionality; intros; repeat rewrite bind_fail; auto.
      Qed.

    End Except_State_Sound_WFVM_Except_Sec2.

    Context {Except_State_Sound_WFVM : iPAlgebra Except_State_Sound_Name Except_State_Sound_P WFVM'}.
    Context {eval_soundness'_Exp_E : forall (typeof_rec : UP'_F E -> typeofR D MT)
      (eval_rec : Names.Exp E -> evalMR V ME),
      P2Algebra ES'_ExpName E E E
      (UP'_P2
        (eval_soundness'_P D V E MT ME _ WFVM'
          Datatypes.unit E Fun_E
          (fun _ _ _ _ => True)
          tt typeof_rec eval_rec f_algebra
          (f_algebra (FAlgebra := evalM_E' (@Names.Exp E Fun_E)))))}.
    Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
    Context {WF_MAlg_eval : WF_MAlgebra evalM_E'}.

    Theorem eval_Except_State_Sound :
      forall (e : Exp E) Sigma (T : DType D)
        (env : list (Value V)),
        WF_Environment D V _ WFV' Sigma env Sigma ->
        fmap (@proj1_sig _ _) (typeof D E MT (proj1_sig e)) = return_ (proj1_sig T) ->
        (exists v : Value V, exists env', exists Sigma',
          (put env) >> evalM (evalM_E := evalM_E') V E ME (proj1_sig e) = put env' >> return_ (M := ME) v /\
          WFValueC D V _ WFV' Sigma' v T) \/
        (exists t, exists env', exists Sigma',
          put env >> evalM (evalM_E := evalM_E') V E ME (proj1_sig e) = put env' >> throw t
        /\ WF_Environment D V _ WFV' Sigma' env' Sigma'
        /\ (forall n T, lookup Sigma n = Some T -> lookup Sigma' n = Some T)).
    Proof.
      intros e Sigma.
      apply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := Except_State_Sound_WFVM)) _
        (eval_State_soundness (eval_soundness'_Exp_E := eval_soundness'_Exp_E) _ _ _ MT ME WFVM' e Sigma)).
    Qed.

  End Except_State_Sound_Sec.

End ESoundES.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
