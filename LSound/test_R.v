Require Import String.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffState.
Require Import Ref.
Require Import ESoundS.

Open Scope string_scope.

Section Test_Section.

  Definition D := UnitType :+: RefType.

  Definition E := RefE.

  Definition V := StuckValue :+: LocValue :+: UnitValue.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{State_ME : StateM ME (list (Value V))}.
  Context {Fail_ME : FailMonad ME}.

  Definition WFV := (WFValue_Unit D V _) ::+:: (WFValue_Loc D V _).
  Definition WFVM := (WFValueM_base D V MT ME _ WFV) ::+::
    (WFValueM_State D V MT ME _
      (TypContextCE := DType_Env_CE _)
      (TypContext_WFE := DType_Env_WFE _ _ WFV)).

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D MT) (E).
  Proof.
    intros; eauto 150 with typeclass_instances.
  Defined.

  Lemma eval_Sound :
    forall (Sigma : Env (DType D)) (e : Exp E) (T : DType D) (env : Env (Value V)),
      WF_Environment D V _ WFV Sigma env Sigma ->
      typeof D E MT (proj1_sig e) = return_ T ->
      exists v : Value V,
        exists env' : Env (Value V),
          exists Sigma' : Env (DType D),
            (put env) >> evalM V E ME (proj1_sig e) =
            put env' >> return_ (M := ME) v /\
            WFValueC D V _ WFV Sigma' v T.
  Proof.
    intros; eapply eval_State_Sound with (WFVM' := WFVM);
      eauto 10 with typeclass_instances.
    eauto 15 with typeclass_instances.
    eapply Ref_eval_soundness'' with (WFV := WFV) (WFVM := WFVM)
      (TypContextCE :=  _) (TypContext_S := _)
      (TypContext_WFE := DType_Env_WFE _ _ WFV);
      eauto 250 with typeclass_instances.
    simpl; eauto.
  Qed.

  Eval compute in ("Soundness for 'References' Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
