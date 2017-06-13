Require Import String.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.
Require Import EffExcept.
Require Import Arith.
Require Import Exception.
Require Import ESoundE.

Open Scope string_scope.

Section Test_Section.

  Definition D := AType.

  Definition E := Arith :+: ExceptE D.

  Definition V := StuckValue :+: BotValue :+: NatValue.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.

  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{Exception_ME : Exception ME unit}.
  Context {Fail_ME : FailMonad ME}.

  Context {ME_eq_dec : forall (A : Set) (mte : ME A),
    (exists a, mte = return_ a) \/ (mte = fail) \/ (mte = throw tt)}.
  Context {Reasonable_ME : Reasonable_Monad ME}.
  Context {fail_neq_throw : forall (A B C : Set) (ma : ME A) (mb : ME B),
    (ma >>= fun _ => fail (M := ME)) <> mb >>= fun _ => throw (A := C) tt}.

  Definition WFV := (WFValue_VI V D unit).
  Definition WFVM := (WFValueM_base D V MT ME unit WFV) ::+:: (WFValueM_Except D V MT ME unit).

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
    intros; eauto with typeclass_instances.
    apply FAlgebra_Plus; eauto with typeclass_instances.
  Defined.

  Lemma eval_Sound :
    forall (e : Exp E) (T : DType D),
      fmap (@proj1_sig _ _) (typeof D E MT (proj1_sig e)) = return_ (proj1_sig T) ->
      (exists v : Value V,
        evalM V E ME (proj1_sig e) = return_ (M := ME) v /\
        WFValueC D V _ WFV tt v T) \/
      exists t, evalM V E ME (proj1_sig e) = throw (M := ME) t.
  Proof.
    apply eval_Except_Sound with (WFVM' := WFVM);
      eauto 10 with typeclass_instances.
    intros; repeat apply @P2Algebra_Plus.
    eapply Arith_eval_soundness'' with (WFV := WFV);
      eauto 250 with typeclass_instances.
    eapply Except_eval_soundness'';
      eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Soundness for 'Arith :+: Exceptions' Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
