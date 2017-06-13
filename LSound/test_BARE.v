Require Import String.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffState.
Require Import EffExcept.
Require Import Bool.
Require Import Arith.
Require Import Ref.
Require Import Exception.
Require Import ESoundES.

Open Scope string_scope.

Section Test_Section.

  Definition D := AType :+: BType :+: RefType :+: UnitType.

  Definition E := Bool :+: Arith :+: RefE :+: (ExceptE D).

  Definition V := StuckValue :+: BoolValue :+: NatValue :+:
    UnitValue :+: LocValue.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{StateM_ME : StateM ME (list (Value V))}.
  Context {Exception_ME : Exception ME Datatypes.unit}.
  Context {Reasonable_ME : Reasonable_Monad ME}.

  Definition WFV := (WFValue_VB D V (list (DType D))) ::+:: (WFValue_VI V D _) ::+::
                    (WFValue_Unit D V _) ::+:: (WFValue_Loc D V _).

  Instance DType_Env_CE : ConsExtensionC (list (DType D)). eauto with typeclass_instances. Defined.
  Instance DType_Env_WFE : WF_EnvC V (list (DType D)). apply (DType_Env_WFE _ _ WFV). Defined.

  Definition WFVM :=
    (WFValueM_base (Fail_MT := Fail_MT) D V MT ME (list (DType D)) WFV) ::+::
    (WFValueM_State D V MT ME _) ::+::
    (WFValueM_Except D V MT ME _).

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D MT) (E).
  Proof.
    intros; eauto 150 with typeclass_instances.
  Defined.

  Instance eval_alg : forall T : Set, FAlgebra EvalName T (evalMR V ME) E.
  Proof.
    intros; eauto 250 with typeclass_instances.
  Defined.

    Context {ME_eq_dec' : forall (A : Set) (mte : ME A) (env : list (Value V)),
      (exists a, exists env',
        put env >> mte = put env' >> return_ a) \/
      (exists env', put env >> mte = put env' >> throw tt)}.

    Context {Put_Exception_Disc :
      forall (A B : Set) (a : A) (mb : ME B) env n,
        (put env >>= fun _ => return_ a) <> mb >>= fun _ => throw n}.

    Context {put_catch : forall (A : Set) (env : list (Value V)) e h,
      put env >>= (fun _ => catch (A := A) e h) = catch (put env >>= fun _ => e) h}.
    Context {put_throw : forall (A B : Set) (env env' : list (Value V)) t,
      put env >>= (fun _ => throw t (A := A)) = put env' >>= (fun _ => throw t) ->
      put env >>= (fun _ => throw t (A := B)) = put env' >>= (fun _ => throw t)}.

  Theorem eval_Sound :
    forall (e : Exp E) Sigma (T : DType D)
      (env : list (Value V)),
      WF_Environment D V _ WFV Sigma env Sigma ->
      fmap (@proj1_sig _ _) (typeof D E MT (proj1_sig e)) = return_ (proj1_sig T) ->
      (exists v : Value V, exists env', exists Sigma',
        (put env) >> evalM (evalM_E := eval_alg) V E ME (proj1_sig e) = put env' >> return_ (M := ME) v /\
        WFValueC D V _ WFV Sigma' v T) \/
      (exists t, exists env', exists Sigma',
        put env >> evalM (evalM_E := eval_alg) V E ME (proj1_sig e) = put env' >> throw t
        /\ WF_Environment D V _ WFV Sigma' env' Sigma'
        /\ (forall n T, lookup Sigma n = Some T -> lookup Sigma' n = Some T)).
  Proof.
    apply eval_Except_State_Sound with (WFVM' := WFVM);
      eauto 5 with typeclass_instances.
    eauto 50 with typeclass_instances.
    intros; repeat apply @P2Algebra_Plus.
    eapply Bool_eval_soundness'' with (WFV := WFV);
      eauto 250 with typeclass_instances.
    eapply Arith_eval_soundness'' with (WFV := WFV);
      eauto 250 with typeclass_instances.
    eapply Ref_eval_soundness'' with (WFV := WFV);
      eauto 250 with typeclass_instances.
    eapply Except_eval_soundness'';
      eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Soundness for 'Bool :+: Arith :+: Ref :+: Exceptions ' Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
