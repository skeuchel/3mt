Require Import Ascii.
Require Import String.
Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.

Section EffState.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Let DType := DType D.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Let Value := Value V.

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  (* Context {Fail_MT : FailMonad MT}. *)

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {State_M : StateM ME (list Value)}.

  Section WFValue_Sec.

  (* ============================================== *)
  (* WELL-FORMED REFERENCE VALUES                   *)
  (* ============================================== *)

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.

    (** Typing rules for unit values **)

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.

    (* ============================================== *)
    (* WELL-FORMED MONADIC STATE VALUES               *)
    (* ============================================== *)

    (** SuperFunctor for Well-Formed Monadic Value Relation with
       Typing Environment. **)

    Class WF_EnvC (TypContext : Set) : Type :=
      {WF_Env : list Value -> TypContext -> Prop}.

    Context {TypContext_WFE : WF_EnvC TypContext}.

    Inductive WFValueM_State (A : WFValueM_i D V MT ME TypContext -> Prop) : WFValueM_i D V MT ME TypContext -> Prop :=
    | WFVM_Get : forall Sigma (k : list Value -> ME Value) T,
      (forall env, WF_Env env Sigma ->
        A (mk_WFValueM_i D V MT ME _ Sigma (k env) T)) ->
      WFValueM_State A (mk_WFValueM_i D V MT ME _ Sigma (do env <- get; k env) T)
    | WFVM_Put : forall Sigma Sigma' env k T,
      WF_Env env Sigma' -> ConsExtension Sigma' Sigma ->
      A (mk_WFValueM_i _ _ _ _ _ Sigma' k T) ->
      WFValueM_State A (mk_WFValueM_i _ _ _ _ _ Sigma (put env >> k) T).

    Definition ind_alg_WFVM_State (P : WFValueM_i D V MT ME TypContext -> Prop)
      (H_Get : forall Sigma k T,
        (forall env, WF_Env env Sigma ->
          P (mk_WFValueM_i _ _ _ _ _ Sigma (k env) T)) ->
        P (mk_WFValueM_i _ _ _ _ _ Sigma (do env <- get; k env) T))
      (H_Put : forall Sigma Sigma' env k T,
        WF_Env env Sigma' -> ConsExtension Sigma' Sigma ->
        P (mk_WFValueM_i _ _ _ _ _ Sigma' k T) ->
        P (mk_WFValueM_i _ _ _ _ _ Sigma (put env >> k) T))
      (i : WFValueM_i D V MT ME _)
      (e : WFValueM_State P i)
      :
      P i :=
      match e in WFValueM_State _ i return P i with
        | WFVM_Get Sigma k T WF_k =>
          H_Get Sigma k T WF_k
        | WFVM_Put Sigma Sigma' env k T WF_env Sub_Sig_Sig' WF_k =>
          H_Put Sigma Sigma' env k T WF_env Sub_Sig_Sig' WF_k
      end.

    Definition WFVM_State_ifmap
      (A B : WFValueM_i D V MT ME _ -> Prop)
      (i : WFValueM_i D V MT ME _)
      (f : forall i, A i -> B i)
      (WFVM_a : WFValueM_State A i)
      :
      WFValueM_State B i :=
      match WFVM_a in WFValueM_State _ i return WFValueM_State B i with
        | WFVM_Get Sigma k T WF_k =>
          WFVM_Get B Sigma k T (fun env WF_env => f _ (WF_k env WF_env))
        | WFVM_Put Sigma Sigma' env k T WF_env Sub_Sig_Sig' WF_k =>
          WFVM_Put B Sigma Sigma' env k T WF_env Sub_Sig_Sig' (f _ WF_k)
      end.

    Global Instance iFun_wfvm_State : iFunctor WFValueM_State.
      constructor 1 with (ifmap := WFVM_State_ifmap).
      (* ifmap_fusion *)
      destruct a; simpl; intros; reflexivity.
      (* ifmap_id *)
      destruct a; simpl; intros; auto;
        apply f_equal; repeat (apply functional_extensionality_dep; intros); auto.
    Defined.

    Class SigTypContextC (TypContext : Set) : Set :=
      {SigLookup : TypContext -> nat -> option DType;
       SigInsert : DType -> TypContext -> TypContext}.

    Class SigConsExtensionC (TypContext : Set)
      (ConsExt : ConsExtensionC TypContext)
      (SigTyp : SigTypContextC TypContext) : Type :=
      {
        ConsExtension_SigLookup : forall Sigma Sigma',
          ConsExtension Sigma' Sigma ->
          forall n T, SigLookup Sigma n = Some T ->
            SigLookup Sigma' n = Some T;
        ConsExtension_SigInsert : forall Sigma T,
          ConsExtension (SigInsert T Sigma) Sigma}.

    Class Sig_WF_EnvC (TypContext : Set)
      (WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop)
      (WF_Env' : WF_EnvC TypContext)
      (SigTyp : SigTypContextC TypContext) : Type :=
    {
      WF_EnvLookup : forall env Sigma T n,
        WF_Env env Sigma ->
        SigLookup Sigma n = Some T ->
        exists v, lookup env n = Some v /\
          WFValueC _ _ _ WFV Sigma v T;
      WF_EnvInsertLookup : forall env Sigma T,
        WF_Env env Sigma ->
        SigLookup (SigInsert T Sigma) (length env) = Some T;
      WF_EnvInsert : forall Sigma env v T,
        WFValueC _ _ _ WFV (SigInsert T Sigma) v T ->
        WF_Env env Sigma ->
        WF_Env (insert _ v env) (SigInsert T Sigma);
      WF_EnvReplace : forall Sigma env v T n,
        SigLookup Sigma n = Some T ->
        WFValueC _ _ _ WFV Sigma v T ->
        WF_Env env Sigma ->
        WF_Env (replace_el n v env) Sigma}.

  End WFValue_Sec.

  Section BindRule.

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.
    Context {TypContext_WFE : WF_EnvC TypContext}.

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Context {Sub_WFVM_State_WFVM : Sub_iFunctor (WFValueM_State TypContext) WFVM}.

    Global Instance wfvm_bind_State' :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM) (WFValueM_State _).
    Proof.
      constructor; unfold iAlgebra; intros.
      apply ind_alg_WFVM_State with
        (TypContextCE := TypContextCE) (TypContext_WFE := TypContext_WFE); try eassumption;
        unfold wfvm_bind_P; simpl; intros.
        (* get *)
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)).
      rewrite <- associativity.
      constructor.
      intros.
      apply H0; auto.
        (* put *)
      apply (inject_i (subGF := Sub_WFVM_State_WFVM)).
      unfold wbind.
      repeat rewrite <- associativity.
      constructor 2 with (Sigma' := Sigma'); auto.
      apply H2; auto.
      intros; eapply WFVM_ke_kt; eauto; eapply ConsExtension_trans; eauto.
    Qed.

  End BindRule.

End EffState.


(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
