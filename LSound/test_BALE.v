Require Import String.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffExcept.
Require Import EffReader.
Require Import Arith.
Require Import Bool.
Require Import Lambda.
Require Import Lambda_Arith.
Require Import Lambda_Bool.
Require Import Exception.
Require Import Lambda_Exception.
Require Import ESoundER.

Section Test_Section.

  Definition D := AType :+: BType :+: LType.
  Definition E (A : Set) := Arith :+: Bool :+: Lambda D A :+: ExceptE D.

  Global Instance Fun_E : forall (A : Set),
    Functor (E A).
  Proof.
    eauto with typeclass_instances.
  Defined.

  Definition V := StuckValue :+: NatValue :+: BoolValue :+:
    (ClosValue E).

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
  Context {Exception_ME : Exception ME Datatypes.unit}.
  Context {Reasonable_ME : Reasonable_Monad ME}.

  Definition EQV_E (A B : Set) := (Arith_eqv E A B) ::+:: (Bool_eqv E A B)
    ::+:: (Lambda_eqv D E A B)
    ::+:: (Exception_eqv D E A B).

  Definition WFV := (WFValue_VI V D (list (Names.DType D)))
    ::+:: (WFValue_VB D V _) ::+:: (WFValue_Clos D E MT V EQV_E _).

  Definition WFVM := (WFValueM_base D V MT ME _ WFV)
    ::+:: (WFValueM_Environment (TypContextCE := GammaTypContextCE _) D MT V ME _ WFV)
    ::+:: (WFValueM_Bot D V MT ME _)
    ::+:: (WFValueM_Except (TypContextCE := GammaTypContextCE _) D V MT ME _).

  Instance eval_alg : FAlgebra EvalName (Exp (E nat)) (evalMR V ME) (E nat).
  Proof.
    eauto 250 with typeclass_instances.
  Defined.

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D MT) (E (DType D)).
  Proof.
    intros; eauto 150 with typeclass_instances.
  Defined.

  Instance eqv_soundness_X_alg eval_rec :
    iPAlgebra soundness_X'_Name
    (soundness_X'_P D V E MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
      (f_algebra (FAlgebra := typeof_alg _))
      (f_algebra (FAlgebra := eval_alg))) (EQV_E _ _).
  Proof.
    repeat apply iPAlgebra_Plus.
    apply eqv_soundness_X'_Arith_eqv with (WFV := WFV) (Fail_MT := Fail_MT)
      (TypContextCE := GammaTypContextCE _) (monad := monad0) (Sub_AType_D := _)
      (Sub_StuckValue_V := _) (Sub_NatValue_V := _);
      intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Bool_eqv with (WFV := WFV) (Fail_MT := Fail_MT)
      (TypContextCE := GammaTypContextCE _) (monad := monad0) (Sub_BType_D := _)
      (Sub_StuckValue_V := _) (Sub_BoolValue_V := _)
      (eq_DType_DT := _); intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Lambda_eqv with (WFV := WFV) (Fail_MT := Fail_MT)
      (TypContextCE := GammaTypContextCE _)
      (Environment_ME := Mon_ME) (Sub_LType_D := _)
      (Sub_StuckValue_V := _) (Sub_ClosValue_V := _)
      (eq_DType_DT := _); intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Except_eqv with (TypContextCE := GammaTypContextCE _)
      (Fail_MT := Fail_MT) (Exception_ME := Exception_ME) (eq_DType_DT := _);
      intros; eauto 550 with typeclass_instances.
  Qed.

  Variable local_throw : forall (A : Set) f t,
    local f (throw t) = throw t (A := A).
  Variable local_catch : forall (A : Set) e h f,
    local f (catch (A := A) e h) = catch (local f e) (fun t => local f (h t)).
  Variable catch_fail : forall (A : Set) h,
    catch (A := A) fail h = fail.

    Context {throw_neq_fail : forall A t,
      throw (A := A) t <> fail (M := ME)}.

    Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (gamma'' : list (Names.Value V)),
      (exists a : A,
        local (fun _ => gamma'') mte = return_ a) \/
      (local (fun _ => gamma'') mte = fail) \/
      (local (fun _ => gamma'') mte = throw tt)}.

  Instance Except_State_Sound_X_WFVM :
    iPAlgebra Except_Sound_X_Name (Except_Sound_X_P D V MT ME WFV) WFVM.
  Proof.
    eauto 850 with typeclass_instances.
  Qed.

  Theorem eval_Sound :
    forall (n : nat) Sigma gamma gamma' gamma'' e' e'',
      E_eqvC E EQV_E gamma' gamma e'' e' ->
      forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
        exists T, lookup gamma b = Some T)
      (WF_gamma'' : WF_Environment _ _ _ WFV Sigma gamma'' gamma)
      (WF_gamma2 : List.length gamma = List.length gamma')
      (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
      (WF_Sigma : Gamma _ Sigma = gamma) (T : DType D),
      typeof D (E (DType D)) MT (proj1_sig e') = return_ T ->
      (local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = fail) \/
      (exists t, local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = throw t) \/
        exists v : Value V,
          local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') =
          return_ (M := ME) v /\ WFValueC _ _ _ WFV Sigma v T.
  Proof.
    intros.
    apply Except_Sound_X with (EQV_E := EQV_E) (WFVM' := WFVM) (Mon_MT := monad)
      (Typeof_E := typeof_alg) (gamma := gamma) (gamma' := gamma') (e' := e');
      eauto 250 with typeclass_instances.
  Qed.

  Open Scope string_scope.

  Eval compute in ("Type Soundness for Arith + Bool + Lambda + Exception Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
