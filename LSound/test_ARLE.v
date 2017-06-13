Require Import String.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffState.
Require Import EffExcept.
Require Import EffReader.
Require Import Arith.
Require Import Lambda.
Require Import Ref.
Require Import Exception.
Require Import Lambda_Arith.
Require Import Lambda_Ref.
Require Import Lambda_Exception.
Require Import ESoundERS.

Section Test_Section.

  Definition D := AType :+: LType :+: UnitType :+: RefType.
  Definition E (A : Set) := Arith :+: Lambda D A :+: RefE :+: ExceptE D.

  Global Instance Fun_E : forall (A : Set),
    Functor (E A).
  Proof.
    eauto with typeclass_instances.
  Defined.

  Definition V := StuckValue :+: NatValue :+:
    (ClosValue E) :+: LocValue :+: UnitValue.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{Mon_ME : Environment ME (list (Value V))}.
  Context {State_ME : StateM ME (list (Value V))}.
  Context {Fail_ME : FailMonad ME}.
  Context {FailEnvM : FailEnvironmentMonad (Env (Value V)) ME}.
  Context {Exception_ME : Exception ME Datatypes.unit}.

  Definition EQV_E (A B : Set) := (Arith_eqv E A B) ::+:: (Lambda_eqv D E A B) ::+:: (RefE_eqv E A B)
    ::+:: (Exception_eqv D E A B).

  Definition WFV := (WFValue_VI V D (list (Names.DType D) * list (Names.DType D))) ::+::
    (WFValue_Clos D E MT V EQV_E _) ::+:: (WFValue_Unit D V _) ::+:: (WFValue_Loc D V _).

  Definition WFVM := (WFValueM_base D V MT ME _ WFV) ::+:: (WFValueM_Environment D MT V ME _ WFV)
    ::+:: (WFValueM_Bot D V MT ME _) ::+:: (WFValueM_State D V MT ME _
      (TypContextCE := SigGamma_GammaTypContextCE _)
      (TypContext_WFE := SigGamma_WF_EnvC _ _ WFV))
    ::+:: (WFValueM_Except D V MT ME _).

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
      (monad := monad0) (TypContextCE := SigGamma_GammaTypContextCE _)
      (Sub_AType_D := _) (Sub_StuckValue_V := _) (Sub_NatValue_V := _);
      intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Lambda_eqv with (WFV := WFV) (Fail_MT := Fail_MT)
      (TypContextCE := SigGamma_GammaTypContextCE _)
      (Environment_ME := Mon_ME) (Sub_LType_D := _)
      (Sub_StuckValue_V := _) (Sub_ClosValue_V := _)
      (eq_DType_DT := _); intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_RefE_eqv with (WFV := WFV) (TypContext_S := _)
      (TypContextCE := SigGamma_GammaTypContextCE _)
      (TypContext_WFE := SigGamma_WF_EnvC _ _ WFV)
      (Fail_MT := Fail_MT) (StateM_ME := State_ME) (Sub_RefType_D := _)
      (Sub_StuckValue_V := _) (Sub_LocValue_V := _)
      (eq_DType_DT := _) (Sub_UnitType_D := _) (Sub_UnitValue_V := _);
      intros; eauto 550 with typeclass_instances.
    apply eqv_soundness_X'_Except_eqv with (Fail_MT := Fail_MT)
      (TypContextCE := SigGamma_GammaTypContextCE _)
      (Exception_ME := Exception_ME) (eq_DType_DT := _);
      intros; eauto 550 with typeclass_instances.
  Qed.

  Variable put_local : forall (A : Set) sigma f (m : ME A),
    put (M := ME) sigma >> (local f m) = local f (put sigma >> m).

  Variable local_throw : forall (A : Set) f t,
    local f (throw t) = throw t (A := A).
  Variable local_catch : forall (A : Set) e h f,
    local f (catch (A := A) e h) = catch (local f e) (fun t => local f (h t)).

  Variable catch_fail : forall (A : Set) h,
    catch (A := A) fail h = fail.
  Context {fail_neq_throw : forall A env env',
    put env >> fail (M := ME) <> put env' >> throw (A := A) tt}.

  Context {Put_Exception_Disc :
    forall (A B : Set) (a : A) (mb : ME B) env n,
      (put env >>= fun _ => return_ a) <> mb >>= fun _ => throw n}.

  Context {put_catch : forall (A : Set) (env : list (Value V)) e h,
    put env >>= (fun _ => catch (A := A) e h) = catch (put env >>= fun _ => e) h}.
  Context {put_throw : forall (A B : Set) (env env' : list (Value V)) t,
    put env >>= (fun _ => throw t (A := A)) = put env' >>= (fun _ => throw t) ->
    put env >>= (fun _ => throw t (A := B)) = put env' >>= (fun _ => throw t)}.

  Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (env gamma'' : list (Names.Value V)),
    (exists a : A, exists env' : list (Names.Value V),
      put env >> (local (fun _ => gamma'') mte) = put env' >> return_ a) \/
    (exists env', put env >> (local (fun _ => gamma'') mte) = put env' >> fail) \/
    (exists env', put env >> (local (fun _ => gamma'') mte) = put env' >> throw tt)}.

  Instance Except_State_Sound_X_WFVM :
    iPAlgebra Except_State_Sound_X_Name (Except_State_Sound_X_P D V MT ME WFV) WFVM.
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
      (WF_Sigma : Gamma D Sigma = gamma)
      (T : DType D)
      (env : Env (Names.Value V))
      (WF_env : WF_Environment _ _ _ WFV Sigma env (fst Sigma)),
      typeof D (E (DType D)) MT (proj1_sig e') = return_ T ->
      (exists env', put env >>
        local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = put env' >> fail) \/
      (exists t, exists env', exists Sigma',
        put env >> local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') = put env' >> throw t
        /\ WF_Environment D V _ WFV Sigma' env' (fst Sigma')
        /\ ConsExtension Sigma' Sigma) \/
        exists v : Value V,
          exists env' : Env (Value V),
          exists Sigma' ,
            ConsExtension Sigma' Sigma /\
          put env >> local (M := ME) (fun _ => gamma'') (bevalM V E ME n e'') =
          put env' >> return_ (M := ME) v /\ WFValueC _ _ _ WFV Sigma' v T
          /\ WF_Environment D V _ WFV Sigma' env' (fst Sigma').
  Proof.
    intros.
    apply Except_State_Sound_X with (EQV_E := EQV_E) (WFVM := WFVM) (Mon_MT := monad)
      (Typeof_E := typeof_alg) (gamma := gamma) (gamma' := gamma') (e' := e');
      eauto 250 with typeclass_instances.
  Qed.

  Open Scope string_scope.

  Eval compute in ("Type Soundness for Arith + Ref + Lambda + Exception Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)

