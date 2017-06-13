Require Import String.
Require Import Names.
Require Import Arith.
Require Import Lambda.
Require Import Functors.
Require Import PNames.
Require Import MonadLib.
Require Import Lambda_Arith.

Open Scope string_scope.

Section Test_Section.

  Definition D := AType :+: LType.
  Definition E (A : Set) := Arith :+: Lambda D A.

  Global Instance Fun_E : forall (A : Set),
    Functor (E A).
  Proof.
    eauto with typeclass_instances.
  Defined.

  Definition V := StuckValue :+: NatValue :+: (ClosValue E).

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{Mon_ME : Environment ME (list (Value V))}.
  Context {Fail_ME : FailMonad ME}.
  Context {FailEnvM : FailEnvironmentMonad (Env (Value V)) ME}.

  Definition EQV_E (A B : Set) := (Arith_eqv E A B) ::+:: (Lambda_eqv D E A B).
  Definition WFV := (WFValue_VI V D (list (DType D))) ::+:: (WFValue_Clos D E MT V EQV_E _).
  Definition WFVM := (WFValueM_base D V MT ME _ WFV)
    ::+:: (WFValueM_Environment (TypContextCE := GammaTypContextCE _) D MT V ME _ WFV)
    ::+:: (WFValueM_Bot D V MT ME _).

  Instance eval_alg : FAlgebra EvalName (Exp E nat) (evalMR V ME) (E nat).
  Proof.
    unfold Exp.
    eauto 250 with typeclass_instances.
  Defined.

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D)).
  Proof.
    intros; eauto 150 with typeclass_instances.
  Defined.

  Instance Pure_Sound_X_WFVM : iPAlgebra Pure_Sound_X_Name (Pure_Sound_X_P D V MT ME WFV) WFVM.
  Proof.
    apply iPAlgebra_Plus;
      eauto 250 with typeclass_instances.
  Qed.

  Instance eqv_soundness_X_alg eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V E MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := typeof_alg _))
      (f_algebra (FAlgebra := eval_alg))) (EQV_E _ _).
  Proof.
    apply iPAlgebra_Plus.
    apply eqv_soundness_X'_Arith_eqv with (WFV := WFV) (TypContextCE := GammaTypContextCE _)
       (Sub_AType_D := _) (Fail_MT := Fail_MT) (monad := monad0)
      (Sub_StuckValue_V := _) (Sub_NatValue_V := _);
      intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Lambda_eqv with (WFV := WFV) (Fail_MT := Fail_MT)
      (TypContextCE := GammaTypContextCE _)
      (Environment_ME := Mon_ME) (Sub_LType_D := _)
      (Sub_StuckValue_V := _) (Sub_ClosValue_V := _)
      (eq_DType_DT := _); intros; eauto 550 with typeclass_instances.
  Qed.

  Lemma eval_Sound :
      forall (n : nat) Sigma gamma gamma' gamma'' e' (e'' : UP'_F (E nat)),
        E_eqvC E EQV_E gamma' gamma e'' e' ->
        forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
          exists T, lookup gamma b = Some T)
        (WF_gamma'' : WF_Environment _ _ _ WFV Sigma gamma'' gamma)
        (WF_gamma2 : List.length gamma = List.length gamma')
        (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
        (WF_Sigma : Gamma _ Sigma = gamma) (T : DType D),
        typeof D (E (DType D)) MT (proj1_sig e') = return_ T ->
        local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = (fail (A := Value V)) \/
        (exists v : Value V,
          local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = return_ (M := ME) v /\
          WFValueC _ _ _ WFV Sigma v T).
  Proof.
    intros.
    apply eval_Pure_Sound_X with (EQV_E := EQV_E) (WFVM := WFVM) (Mon_MT := monad)
      (Typeof_E := typeof_alg) (gamma := gamma) (gamma' := gamma') (e' := e');
      eauto 250 with typeclass_instances.
    unfold WF_EnvG, DType in *|-*; rewrite WF_Sigma; auto.
  Qed.

  Eval compute in ("Type Soundness for Arith + Lambda Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
