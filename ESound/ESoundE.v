Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffExcept.

Section ESoundE.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  (* Let DType := DType D. *)

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Let Exp := Exp F.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Let Value := Value V.

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
  Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

  Variable (ME : Set -> Set).
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Exception_ME : Exception ME unit}.
  Context {Fail_ME : FailMonad ME}.

  Context {evalM_F : FAlgebra EvalName Exp (evalMR V ME) F}.

  Variable WFV' : (WFValue_i D V unit -> Prop) -> WFValue_i D V unit -> Prop.
  Context {funWFV' : iFunctor WFV'}.

  Variable WFVM' : (WFValueM_i D V MT ME unit -> Prop) -> WFValueM_i D V MT ME unit -> Prop.
  Context {funWFVM' : iFunctor WFVM'}.

  Definition Except_Sound_P (i : WFValueM_i D V MT ME unit) :=
    forall T, fmap (@proj1_sig _ _) (wfvm_T _ _ _ _ _ i) =
      return_ (proj1_sig T) ->
      (exists v : Value,
        wfvm_v _ _ _ _ _ i = return_ (M := ME) v /\
        WFValueC D V _ WFV' tt v T) \/
      exists t, wfvm_v _ _ _ _ _ i = throw t.

  Inductive Except_Sound_Name := except_sound_name.

  Context {Reasonable_MT : Reasonable_Monad MT}.

  Context {WFV_proj1_a_WFV : iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV') WFV'}.
  Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.

  Global Instance Except_Sound_WFVM_base :
    iPAlgebra Except_Sound_Name Except_Sound_P (WFValueM_base D V MT ME _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply ind_alg_WFVM_base with (Monad_ME := Mon_M)
      (Fail_MT := Fail_MT) (WFV := WFV');
      try assumption; unfold Except_Sound_P; intros.
    (* WFVM_Return' *)
    left; exists v; split; simpl in *; auto.
    destruct H1 as [mt' mt'_eq]; subst.
    rewrite fmap_fusion in H2.
    destruct (fmap_exists _ _ _ _ _ H2) as [[T' T_eq] T'_eq].
    simpl in *; subst; auto.
    destruct T0 as [T0 T0_UP']; simpl in *.
    destruct Sigma.
    apply (WFV_proj1_b _ _ _ _ _ _ H0); simpl; auto; congruence.
    (* WFVM_Untyped' *)
    left; simpl in H0; apply sym_eq in H0.
    unfold wbind in H0; rewrite fmap_m, <- associativity, bind_fail in H0.
    apply FailMonad_Disc in H0; destruct H0; auto.
  Qed.

  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.
  Context {ME_eq_dec : forall (A : Set) (mte : ME A),
    (exists a, mte = return_ a) \/ (mte = fail) \/ (mte = throw tt)}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_ME : Reasonable_Monad ME}.
  Context {fail_neq_throw : forall (A B C : Set) (ma : ME A) (mb : ME B),
    (ma >>= fun _ => fail (M := ME)) <> mb >>= fun _ => throw (A := C) tt}.

  Global Instance Except_Sound_WFVM_Except' :
    iPAlgebra Except_Sound_Name Except_Sound_P (WFValueM_Except D V MT ME unit).
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply (ind_alg_WFVM_Except D V MT ME) with (TypContextCE := ConsExtensionUnit);
      try assumption; unfold Except_Sound_P; simpl; intros.
    (* throw case *)
    simpl; right; exists tt; reflexivity.
    (* catch case *)
    destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
    destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
    repeat rewrite <- left_unit in H2.
    caseEq (eq_DType _ (proj1_sig T') T''); rewrite H3 in H2.
    destruct (H0 _ H2) as [[v' [ek'_eq WF_v'_T']] | [[] ek'_eq]].
    destruct (ME_eq_dec _ e') as [[v'' e'_eq] | [e'_eq | e'_eq]];
      subst.
    rewrite catch_return; left; exists v'; split; auto.
    failmonaddisc.
    rewrite bind_throw in ek'_eq.
    elimtype False; eapply Exception_Disc with (M := ME) (a := v') (e := tt) (mb := return_ v');
      eauto with typeclass_instances; unfold wbind; rewrite <- left_unit; auto.
    destruct (ME_eq_dec _ e') as [[v'' e'_eq] | [e'_eq | e'_eq]];
      subst.
    rewrite catch_return; right; eexists _; eauto.
    rewrite bind_fail in ek'_eq; elimtype False;
    rewrite left_unit with (a := tt) (f := fun _ => throw tt) in ek'_eq;
      rewrite left_unit with (a := tt) (f := fun _ => fail) in ek'_eq;
        eapply fail_neq_throw; eauto.
    rewrite catch_throw'.
    destruct (H1 tt Sigma (ConsExtension_id _) T) as [[v' [h_eq WF_v'_T']] | [[] h_eq]].
    rewrite rewrite_do with (m := fun U => return_ T' >>= kT U)
      (m' := fun U => kT U T') in H2; [auto |
        apply functional_extensionality; intros; repeat rewrite <- left_unit; auto].
    rewrite rewrite_do with (m := fun U => return_ T'' >>= kT U)
      (m' := fun U => kT U T''); [auto |
        apply functional_extensionality; intros; repeat rewrite <- left_unit; auto].
    rewrite <- H2; apply kt_eq; apply sym_eq; apply (eq_DType_eq D _ _ H3).
    left; exists v'; split; auto.
    right; eauto.
    destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
    destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
    destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
  Qed.

  Context {Except_Sound_WFVM : iPAlgebra Except_Sound_Name Except_Sound_P WFVM'}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) F}.

  Context {evalM_F' : forall T, FAlgebra EvalName T (evalMR V ME) F}.
  Context {eval_soundness'_Exp_F : forall (typeof_rec : UP'_F F -> typeofR D MT)
     (eval_rec : Names.Exp F -> evalMR V ME),
     P2Algebra ES'_ExpName F F F
     (UP'_P2
       (eval_soundness'_P D V F MT ME _ WFVM'
         Datatypes.unit F Fun_F
         (fun _ _ _ _ => True)
         tt typeof_rec eval_rec f_algebra
         (f_algebra (FAlgebra := evalM_F' (@Names.Exp F Fun_F)))))}.

   Context {WF_MAlg_typeof : WF_MAlgebra Typeof_F}.
   Context {WF_MAlg_eval : WF_MAlgebra evalM_F'}.

  Theorem eval_Except_Sound :
    forall (e : Exp) (T : DType D),
      fmap (@proj1_sig _ _) (typeof D F MT (proj1_sig e)) = return_ (proj1_sig T) ->
      (exists v : Value,
        evalM V F ME (proj1_sig e) = return_ (M := ME) v /\
        WFValueC D V _ WFV' tt v T) \/
      exists t, evalM V F ME (proj1_sig e) = throw (M := ME) t.
  Proof.
    intro e.
    apply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := Except_Sound_WFVM)) _
      (eval_soundness (eval_soundness'_Exp_E := eval_soundness'_Exp_F) D V F MT ME WFVM' e tt)).
  Qed.

End ESoundE.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
