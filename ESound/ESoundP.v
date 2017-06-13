Require Import Functors.
Require Import List.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.

Section ESound_Pure.

  (** SuperFunctor for Types. **)
  Variable DT : Set -> Set.
  Context {Fun_DT : Functor DT}.
  (* Definition DType := UP'_F DT. *)

  (** SuperFunctor for Values. **)
  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  (* Definition Value := UP'_F V. *)

  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  (* Definition Exp := UP'_F E. *)

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.

  Variable ME : Set -> Set.
  Context {Functor_ME : Functor ME}.
  Context {Monad_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.

  Variable WFV : (WFValue_i DT V unit -> Prop) -> WFValue_i DT V unit -> Prop.
  Context {funWFV : iFunctor WFV}.

  Variable WFVM : (WFValueM_i DT V MT ME unit -> Prop) -> WFValueM_i DT V MT ME unit -> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Definition Pure_Sound_P (i : WFValueM_i DT V MT ME unit) :=
    forall T, wfvm_T DT V MT ME _ i = return_ T ->
      exists v : Value V,
        wfvm_v DT V MT ME unit i = return_ (M := ME) v /\
        WFValueC DT V unit WFV tt v T.

  Inductive Pure_Sound_Name := pure_sound_name.

  Context {WFV_proj1_b_WFV :
    iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P DT V unit WFV) WFV}.

  Global Instance Pure_Sound_WFVM_base :
    iPAlgebra Pure_Sound_Name Pure_Sound_P (WFValueM_base DT V MT ME unit WFV).
  Proof.
    econstructor.
    unfold iAlgebra; intros; eapply ind_alg_WFVM_base with (WFV := WFV);
      try assumption; unfold Pure_Sound_P; intros.
    - (* WFVM_Return' *)
      exists v; split; simpl in *; auto.
      destruct H1 as [mt' mt'_eq]; subst.
      destruct (fmap_exists _ _ _ _ _ H2) as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0 as [T0 T0_UP'].
      destruct Sigma.
      apply (WFV_proj1_b DT V _ _ _ _ H0); simpl; auto.
    - (* WFVM_Untyped' *)
      simpl in H0; apply sym_eq in H0.
      apply FailMonad_Disc in H0; destruct H0; auto.
  Qed.

  Context {Pure_Sound_WFVM : iPAlgebra Pure_Sound_Name Pure_Sound_P WFVM}.
  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR DT MT) E}.
  Context {eval_E : forall T, FAlgebra EvalName T (evalR V) E}.
  Context {evalM_E : forall T, FAlgebra EvalName T (evalMR V ME) E}.
  Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
  Context {WF_MAlg_eval : WF_MAlgebra evalM_E}.
  Context {eval_soundness_Exp_E : DAlgebra ES_ExpName E E (UP'_SP (eval_soundness_P DT V E MT ME unit WFVM))}.
  Context {eval_soundness'_Exp_E : forall typeof_rec eval_rec,
    P2Algebra ES'_ExpName E E E
    (UP'_P2 (eval_soundness'_P DT V E MT ME unit WFVM unit _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
      (f_algebra (FAlgebra := Typeof_E _)) (f_algebra (FAlgebra := evalM_E _))))}.

  Theorem eval_Pure_Sound' :
    forall (e : Exp E) (T : DType DT),
      typeof DT E MT (proj1_sig e) = return_ T ->
      exists v : Value V,
        evalM _ _ _ (proj1_sig e) = return_ (M := ME) v /\
        WFValueC _ _ _ WFV tt v T.
  Proof.
    intro; apply (ifold_ WFVM _ (ip_algebra (iPAlgebra := Pure_Sound_WFVM)) _
    (eval_soundness DT V E MT ME WFVM e tt)).
  Qed.

End ESound_Pure.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
