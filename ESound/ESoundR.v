Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import List.
Require Import FJ_tactics.
Require Import Functors.
Require Import MonadLib.
Require Import Names.
Require Import PNames.
Require Import EffPure.
Require Import EffReader.

Section ESoundR.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Let DType := DType D.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.


  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Let Exp (A : Set) := Exp (F A).

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Let Value := Value V.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_ME : Functor ME}.
  Context {Mon_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.
  Context {Environment_ME : Environment ME (Env Value)}.

  Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {evalM_F : FAlgebra EvalName (Exp nat) (evalMR V ME) (F nat)}.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Let E_eqv A B := iFix (EQV_E A B).
  Let E_eqvC {A B : Set} gamma gamma' e e' :=
    E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) (F DType)}.


    Variable WFV' : (WFValue_i D V (list (Names.DType D)) -> Prop) -> WFValue_i D V (list (Names.DType D)) -> Prop.
    Context {funWFV' : iFunctor WFV'}.
    Variable WFVM' : (WFValueM_i D V MT ME (list (Names.DType D)) -> Prop) ->
      WFValueM_i D V MT ME (list (Names.DType D)) -> Prop.
    Context {funWFVM' : iFunctor WFVM'}.

    Global Instance GammaTypContextCE' : ConsExtensionC (list (Names.DType D)) :=
      {| ConsExtension := fun Sigma' Sigma =>
        forall n T, lookup Sigma n = Some T -> lookup Sigma' n = Some T |}.
    Proof.
      (* ConsExtension_id *)
      eauto.
      (* ConsExtension_trans *)
      eauto.
    Defined.

    Context {WFV_Weaken'_WFV : iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V _ WFV') WFV'}.

  Global Instance Pure_Sound_X_WFVM_Environment :
    iPAlgebra Pure_Sound_X_Name (Pure_Sound_X_P D V MT ME WFV')
    (WFValueM_Environment D MT V ME (TypContextCE := GammaTypContextCE _) _ WFV').
  Proof.
    econstructor.
    unfold iAlgebra; intros; apply (ind_alg_WFVM_Environment D MT V ME) with (WFV := WFV')
      (TypContextCE := GammaTypContextCE _)
      (GammaTypContext := GammaTypContext _);
      try eassumption; unfold Pure_Sound_X_P; simpl; intros.
    (* WFVM_Local *)
    destruct (H0 gamma'' WF_gamma'' _ _ WF_gamma'' H1) as [eval_fail | [v [eval_k WF_v_T0]]].
    generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit; auto.
    right; exists v; repeat split; auto.
    generalize ask_query; unfold wbind; intro ask_query'.
    rewrite local_bind, local_ask, ask_query', <- left_unit.
    apply eval_k; auto.
      (* WFVM_Ask *)
    rewrite local_bind, local_local; unfold Basics.compose.
    destruct (H1 _ _ (H0 _ WF_gamma'') (refl_equal _)) as [eval_fail | [v [eval_m WF_v_T']]].
    left; unfold Env, DType, Value in *|-*; rewrite eval_fail, bind_fail; auto.
    subst; destruct (H2 _ _ (refl_equal _) (WFV_Weaken' D V _ WFV' _ WF_v_T' Sigma)
      _ _ WF_gamma'' (refl_equal _) )
    as [eval_fail | [v' [eval_k WF_v'_T0]]]; simpl in *|-*.
    left; unfold Env, DType, Value in *|-*; rewrite eval_m, <- left_unit, eval_fail; auto.
    right; exists v'; repeat split; auto.
    unfold Env, Value; rewrite eval_m, <- left_unit; auto.
  Qed.


End ESoundR.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
