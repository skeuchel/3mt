Require Import Functors.
Require Import List.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.

Section EffectPure.

  (** SuperFunctor for Types. **)
  Variable DT : Set -> Set.
  Context {Fun_DT : Functor DT}.

  (** SuperFunctor for Values. **)
  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.

  (** TYPING **)
  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.

  (** EVALUATION **)
  Variable ME : Set -> Set.
  Context {Functor_ME : Functor ME}.
  Context {Monad_ME : Monad ME}.

  Section WFValue_Sec.

    (* ============================================== *)
    (* WELL-FORMED VALUES RELATION                     *)
    (* ============================================== *)

    Variable TypContext : Set.
    Variable WFV : (WFValue_i DT V TypContext -> Prop) -> WFValue_i DT V TypContext -> Prop.

    Inductive WFValueM_base (A : WFValueM_i DT V MT ME TypContext -> Prop) : WFValueM_i DT V MT ME TypContext -> Prop :=
    | WFVM_Return : forall Sigma v (T : DType DT) (mt : MT (DType DT)),
      WFValueC DT V TypContext WFV Sigma v T ->
      {mt' : MT {T' : DType DT | proj1_sig T = proj1_sig T'} &
        fmap (@proj1_sig _ _) mt' = mt} ->
      WFValueM_base A (mk_WFValueM_i DT V MT ME TypContext Sigma (return_ v) mt)
    | WFVM_Untyped : forall B Sigma me (mt : MT B),
      WFValueM_base A (mk_WFValueM_i DT V MT ME TypContext Sigma me (mt >> fail)).

    Definition ind_alg_WFVM_base (P : WFValueM_i DT V MT ME TypContext -> Prop)
      (H_Return : forall Sigma v T mt,
        WFValueC DT V TypContext WFV Sigma v T ->
        {mt' : MT {T' : DType DT | proj1_sig T = proj1_sig T'} &
          fmap (@proj1_sig _ _) mt' = mt} ->
        P (mk_WFValueM_i DT V MT ME TypContext Sigma (return_ v) mt))
      (H_Untyped : forall B Sigma me mt,
        P (mk_WFValueM_i DT V MT ME TypContext Sigma me (mt >> fail)))
      (i : WFValueM_i DT V MT ME TypContext)
      (e : WFValueM_base P i)
      :
      P i :=
      match e in WFValueM_base _ i return P i with
        | WFVM_Return Sigma v T mt WF_v_T WF_mt => H_Return Sigma v T mt WF_v_T WF_mt
        | WFVM_Untyped B Sigma me mt => H_Untyped B Sigma me mt
      end.

    Definition WFVM_base_ifmap
      (A B : WFValueM_i  DT V MT ME TypContext-> Prop)
      (i : WFValueM_i DT V MT ME TypContext)
      (f : forall i, A i -> B i)
      (wfvm_v : WFValueM_base A i)
      :
      WFValueM_base B i :=
      match wfvm_v in WFValueM_base _ i return WFValueM_base B i with
        | WFVM_Return Sigma v T mt WF_v_T WF_mt => WFVM_Return B Sigma v T mt WF_v_T WF_mt
        | WFVM_Untyped C Sigma me mt => WFVM_Untyped B C Sigma me mt
      end.

    Global Instance iFun_WFVM_base : iFunctor WFValueM_base.
      constructor 1 with (ifmap := WFVM_base_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; auto.
    Defined.

    Lemma WFVM_Return_T : forall A Sigma v T,
      WFValueC DT V TypContext WFV Sigma v T ->
      WFValueM_base A (mk_WFValueM_i DT V MT ME TypContext Sigma (return_ v) (return_ T)).
    Proof.
      intros; constructor 1 with (T := T); auto.
      exists (return_ (exist (fun T' => proj1_sig T = proj1_sig T')
        T (refl_equal (proj1_sig T)))).
      rewrite fmap_m, <- left_unit; reflexivity.
    Qed.

    Lemma WFVM_Untyped_T : forall A Sigma v,
      WFValueM_base A (mk_WFValueM_i DT V MT ME TypContext Sigma (return_ v) fail).
    Proof.
      simpl; intros.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      intros; constructor 2.
    Qed.

  End WFValue_Sec.

  Section BindRule.

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.

    Variable WFV : (WFValue_i DT V TypContext -> Prop) -> WFValue_i DT V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.

    Variable WFVM : (WFValueM_i DT V MT ME TypContext -> Prop) -> WFValueM_i DT V MT ME TypContext -> Prop.
    (* Context {funWFVM : iFunctor WFVM}. *)

    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P DT V TypContext WFV) WFV}.
    Context {Sub_WFVM_Base'_WFVM : Sub_iFunctor (WFValueM_base _ WFV) WFVM}.

    Lemma wfvm_skip Sigma (me : ME (Value V)) (mt : MT (DType DT)) (kt : DType DT -> MT (DType DT))
         (WFVM_me_kt : forall T, WFValueMC DT V MT ME TypContext WFVM Sigma me (kt T)) :
      WFValueMC DT V MT ME TypContext WFVM Sigma me (mt >>= kt).
    Proof.
      destruct (MT_eq_dec _ mt) as [[T mt_eq] | mt_eq]; subst.
      rewrite <- left_unit.
      apply WFVM_me_kt.
      rewrite bind_fail.
      apply inject_i.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      constructor 2.
    Qed.

    Lemma wfvm_fail : forall Sigma ke,
      WFValueM DT V MT ME TypContext WFVM (mk_WFValueM_i DT V MT ME _ Sigma ke fail).
    Proof.
      intros.
      apply inject_i.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      constructor 2.
    Qed.

    Global Instance wfvm_bind_base' :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P DT V MT ME TypContext WFV WFVM) (WFValueM_base _ WFV).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV);
        try assumption; unfold wfvm_bind_P; simpl; intros.
      (* WFVM_Return' *)
      destruct (MT_eq_dec _ mt) as [[T0 mt_eq] | mt_eq]; subst.
      repeat rewrite <- left_unit; eapply WFVM_ke_kt; eauto.
      apply ConsExtension_id.
      destruct H1 as [mt' mt'_eq']; subst.
      destruct (MT_eq_dec _ mt') as [[T' mt'_eq] | mt'_eq]; subst.
      rewrite fmap_return in mt'_eq'.
      apply inj_return in mt'_eq'; subst.
      destruct T'.
      destruct x.
      apply (WFV_proj1_b DT V TypContext WFV _ _ H0); simpl; auto.
      destruct (fmap_exists _ _ _ _ _ mt'_eq') as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0.
      apply (WFV_proj1_b DT V TypContext WFV _ _ H0); simpl; auto.
      rewrite bind_fail.
      apply wfvm_fail.
      (* WFVM_Untyped' *)
      destruct (MT_eq_dec _ mt) as [[T0 mt_eq] | mt_eq]; subst.
      unfold wbind; rewrite <- left_unit.
      rewrite bind_fail.
      apply wfvm_fail.
      unfold wbind.
      rewrite <- associativity.
      rewrite bind_fail.
      apply wfvm_fail.
    Qed.

  End BindRule.

End EffectPure.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
