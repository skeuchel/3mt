Require Import String.
Require Import Names.
Require Import Bool.
Require Import Ref.
Require Import Functors.
Require Import MonadLib.
Require Import Exception.
Require Import Ref_Exception.

Open Scope string_scope.

Section Test_Section.

  Definition D := BType :+: RefType :+: UnitType.

  Definition E := Bool :+: RefE :+: (ExceptE D).

  Definition V := StuckValue :+: BoolValue :+:
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

  Definition WFV := (WFValue_VB D V (list (Names.DType D))) ::+::
    (WFValue_Unit D V (list (Names.DType D)) ::+:: (WFValue_Loc D V (list (Names.DType D)))).

  Definition WFVM := (WFValueM_base D V MT ME _ WFV) ::+::
    (WFValueM_State D V MT ME _
      (TypContextCE := DType_Env_CE _)
      (TypContext_WFE := DType_Env_WFE _ _ WFV))
    ::+:: (WFValueM_Except D V MT ME _).

  Instance eq_DType_eq_alg : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D)).
  Proof.
    eauto 250 with typeclass_instances.
  Defined.

  Instance eq_DType_neq_alg : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D)).
  Proof.
    eauto 250 with typeclass_instances.
  Defined.

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
    Context {put_catch : forall (A : Set) (env : list (Value V)) e h,
      put env >>= (fun _ => catch (A := A) e h) = catch (put env >>= fun _ => e) h}.
    Context {Put_Exception_Disc :
      forall (A B : Set) (a : A) (mb : ME B) env n,
        (put env >>= fun _ => return_ a) <> mb >>= fun _ => throw n}.
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
    eapply Bool_eval_soundness' with (WFV := WFV) (WFVM := WFVM);
      eauto 250 with typeclass_instances.
    eapply Ref_eval_soundness'' with (WFV := WFV) (WFVM := WFVM)
      (TypContextCE :=  _) (TypContext_S := _)
      (TypContext_WFE := DType_Env_WFE _ _ WFV);
      eauto 250 with typeclass_instances.
    eapply Except_eval_soundness' with (WFVM := WFVM);
      eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Soundness for 'Bool :+: Ref :+: Exceptions ' Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
