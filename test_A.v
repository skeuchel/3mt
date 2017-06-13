Require Import String.
Require Import Names.
Require Import Arith.
Require Import Functors.
Require Import MonadLib.

Open Scope string_scope.

Section Test_Section.

  Definition D := AType.

  Definition E := Arith.

  Definition V := StuckValue :+: NatValue.

  Variable MT : Set -> Set.
  Context `{Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable ME : Set -> Set.
  Context `{Mon_ME : Monad ME}.

  Definition WFV := (WFValue_VI V D unit).
  Definition WFVM := WFValueM_base D V MT ME unit WFV.

  Lemma eval_Sound :
    forall (e : Exp E) (T : DType D),
    typeof D E MT (proj1_sig e) = return_ T ->
    exists v : Value V,
      evalM V E ME (proj1_sig e) = return_ (M := ME) v /\
      WFValueC D V _ WFV tt v T.
  Proof.
    apply eval_Pure_Sound' with (WFVM := WFVM);
      eauto 5 with typeclass_instances.
  Qed.

  Eval compute in ("Soundness for 'Arith' Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
