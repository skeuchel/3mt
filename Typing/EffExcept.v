Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import FunctionalExtensionality.
Require Import MonadLib.
Require Import Names.
Require Import EffPure.

Section Exception.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  (* Let DType := DType D. *)

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Let Exp := Exp F.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Let Value := Value V.

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.

  Variable (ME : Set -> Set).
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Exception_ME : Exception ME unit}.
  Context {Fail_ME : FailMonad ME}.

  Context {evalM_F : FAlgebra EvalName Exp (evalMR V ME) F}.

  Section WFValue_Sec.

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.

    Inductive WFValueM_Except (A : WFValueM_i D V MT ME TypContext -> Prop) : WFValueM_i D V MT ME TypContext -> Prop :=
    | WFVM_Throw : forall Sigma T,
      WFValueM_Except A (mk_WFValueM_i D V MT ME _ Sigma (throw tt) T)
    | WFVM_Catch : forall (B C : Set) Sigma e' h mte mth
      (k : B -> ME Value) (kT : C -> DType D -> MT (DType D))
      (kT' : MT C)
      (kt_eq : forall (T T' : DType D), proj1_sig T = proj1_sig T' ->
        fmap (@proj1_sig _ _) (do U <- kT'; kT U T) = fmap (@proj1_sig _ _) (do U <- kT'; kT U T')),
      A (mk_WFValueM_i D V MT ME _ Sigma (e' >>= k) (do U <- kT'; mte >>= kT U)) ->
      (forall t Sigma', ConsExtension Sigma' Sigma ->
        A (mk_WFValueM_i D V MT ME _ Sigma' ((h t) >>= k) (do U <- kT'; mth >>= kT U))) ->
      WFValueM_Except A (mk_WFValueM_i D V MT ME _ Sigma ((catch e' h) >>= k)
        (do U <- kT'; (do te <- mte; do th <- mth; if (eq_DType D (proj1_sig te) th) then (return_ te) else fail) >>= kT U)).

    Definition ind_alg_WFVM_Except (P : WFValueM_i D V MT ME _ -> Prop)
      (H_Throw' : forall Sigma T,
        P (mk_WFValueM_i _ _ _ _ _ Sigma (throw tt) T))
      (H_Catch' : forall A C Sigma e' h mte mth k kT kT' kt_eq,
      P (mk_WFValueM_i D V MT ME _ Sigma (e' >>= k) (do U <- kT'; mte >>= kT U)) ->
      (forall t Sigma', ConsExtension Sigma' Sigma ->
        P (mk_WFValueM_i D V MT ME _ Sigma' ((h t) >>= k) (do U <- kT'; mth >>= kT U))) ->
      P (mk_WFValueM_i D V MT ME _ Sigma ((catch e' h) >>= k) _))
      (i : WFValueM_i D V MT ME _)
      (e : WFValueM_Except P i)
      :
      P i :=
      match e in WFValueM_Except _ i return P i with
        | WFVM_Throw Sigma T => H_Throw' Sigma T
        | WFVM_Catch A C Sigma e' h mte mth k kT kT' kT_eq P_e' P_h =>
          H_Catch' A C Sigma e' h mte mth k kT kT' kT_eq P_e' P_h
      end.

    Definition WFVM_Except_ifmap
      (A B : WFValueM_i D V MT ME _ -> Prop)
      (i : WFValueM_i D V MT ME _)
      (f : forall i, A i -> B i)
      (WFVM_a : WFValueM_Except A i)
      :
      WFValueM_Except B i :=
      match WFVM_a in WFValueM_Except _ i return WFValueM_Except B i with
        | WFVM_Throw Sigma T => WFVM_Throw B Sigma T
        | WFVM_Catch C D Sigma e' h mte mth k kT kT' kT_eq A_e' A_h =>
          WFVM_Catch B C D Sigma e' h mte mth k kT kT' kT_eq (f _ A_e')
          (fun t Sigma' Sig_sub_Sig' => f _ (A_h t Sigma' Sig_sub_Sig'))
      end.

    Global Instance iFun_wfvm_Except : iFunctor WFValueM_Except.
      constructor 1 with (ifmap := WFVM_Except_ifmap).
      (* ifmap_fusion *)
      destruct a; simpl; intros; reflexivity.
      (* ifmap_id *)
      destruct a; simpl; intros; auto;
        apply f_equal; repeat (apply functional_extensionality_dep; intros); auto.
    Defined.

  End WFValue_Sec.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.
    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Context {funWFV : iFunctor WFV}.

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Let WFValueM := iFix WFVM.
    Let WFValueMC Sigma v T:= WFValueM (mk_WFValueM_i D V MT ME _ Sigma v T).
    Context {funWFVM : iFunctor WFVM}.

    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME TypContext WFV) WFVM}.

    Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
    Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) F}.

    Context {evalM_F' : forall T, FAlgebra EvalName T (evalMR V ME) F}.

    Context {Sub_WFVM_Except_WFVM : Sub_iFunctor (WFValueM_Except TypContext) WFVM}.


    Lemma catch_msimp : forall (M : Set -> Set) `{Monad M} {A B C D : Set}
      (mta : M A) (mtb : M B) (mtc : A -> B -> M C) (mtd : A -> C -> M D),
      do a <- mta;
        do c <- (mtb >>= mtc a);
      mtd a c =
      do a <- mta;
        do b <- mtb;
          do c <- mtc a b;
            mtd a c.
    Proof.
      intros; apply f_equal; apply functional_extensionality; intros;
        repeat rewrite <- associativity; auto.
    Qed.

    Lemma kt_eq_msimp : forall (M : Set -> Set) `{Monad M} {A B C D : Set}
      (mta : M A) (mtb : A -> M B) (f : C -> M D) (g : B -> C),
      do a <- mta;
        do c <- (mtb a);
          f (g c) =
          fmap g (mta >>= mtb) >>= f.
    Proof.
      intros; rewrite associativity.
      rewrite eq_bind_fmap with (g := g) (f' := f);
        [rewrite Eta with (f := f); auto | auto].
    Qed.

    Lemma curry_msimp : forall (M : Set -> Set) `{Monad M} {A B C : Set}
      (mta : M A) (mtb : A -> M B) (f : A -> B -> M C),
      do a <- mta;
        do b <- mtb a;
          f a b =
          do ab <- (do a <- mta; do b <- mtb a; return_ (a, b)); f (fst ab) (snd ab).
    Proof.
      intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
        intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
          intros; rewrite <- left_unit; auto.
    Qed.

    Lemma curry3_msimp : forall (M : Set -> Set) `{Monad M} {A B C D : Set}
      (mta : M A) (mtb : A -> M B) (mtc : A -> B -> M C) (f : A -> B -> C -> M D),
      do a <- mta;
        do b <- mtb a;
          do c <- mtc a b;
            f a b c =
            do abc <- (do a <- mta; do b <- mtb a; do c <- mtc a b; return_ (a, (b, c)));
              f (fst abc) (fst (snd abc)) (snd (snd abc)).
    Proof.
      intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
        intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
          intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
            intros; rewrite <- left_unit; auto.
    Qed.

    Lemma curry3_msimp' : forall (M : Set -> Set) `{Monad M} {A B C D : Set}
      (mta : M A) (mtb : A -> M B) (mtc : prod A B -> M C) (f : A -> B -> C -> M D),
      do ab <- (do a <- mta; do b <- mtb a; return_ (a, b)); do c <- mtc ab;
        f (fst ab) (snd ab) c =
        do abc <- (do a <- mta; do b <- mtb a; do c <- mtc (a, b); return_ (a, (b, c)));
          f (fst abc) (fst (snd abc)) (snd (snd abc)).
    Proof.
      intros; repeat rewrite <- associativity; apply f_equal; apply functional_extensionality.
      intros; repeat rewrite <- associativity; apply f_equal; apply functional_extensionality.
      intros; repeat rewrite <- associativity, <- left_unit; apply f_equal;
        apply functional_extensionality; intros; rewrite <- left_unit; auto.
    Qed.

  Section BindRule.

    Context {Inj_MT : InjMonad MT}.
    Context {Reasonable_MT : Reasonable_Monad MT}.
    Context {MT_eq_dec : forall (A : Set) (mta : MT A),
      {exists a, mta = return_ a} + {mta = fail}}.

    Ltac failmonadsimpl :=
      repeat match goal with
        | [ |- context[bind (return_ _) _]  ] => rewrite <- left_unit
        | [ |- context[bind fail _]         ] => rewrite bind_fail
        | [ |- context[fmap _ fail]         ] => rewrite fmap_fail
        | [ |- context[fmap _ (return_ _)]  ] => rewrite fmap_return
      end.

    Global Instance wfvm_bind_Except :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P _ _ _ _ _ WFV WFVM) (WFValueM_Except TypContext).
    Proof.
      constructor; unfold iAlgebra; intros.
      apply ind_alg_WFVM_Except with (TypContextCE := TypContextCE); try eassumption;
        unfold wfvm_bind_P; intros.
      (* throw *)
      apply (inject_i (subGF := Sub_WFVM_Except_WFVM)).
      simpl; rewrite bind_throw.
      constructor.
      (* catch *)
      apply (inject_i (subGF := Sub_WFVM_Except_WFVM)).
      unfold wfvm_T.
      assert (bind (do U <- kT';
        (do te <- mte;
          do th <- mth;
            (if eq_DType D (proj1_sig te) th then return_ te else fail)) >>=
        kT U) kt =
      bind kT' (fun U =>
        (do te <- mte;
          do th <- mth;
            (if eq_DType D (proj1_sig te) th then return_ te else fail)) >>=
        (fun T => kT U T >>= kt))) as H2 by
      (rewrite <- associativity; apply f_equal; apply functional_extensionality;
        intros; rewrite <- associativity; apply f_equal; apply functional_extensionality;
          auto).
      simpl in *|-*; rewrite H2; clear H2.
      repeat rewrite <- associativity.
      generalize WFVM_Catch.
      simpl; intros; eapply H2; eauto; clear H2.
      intros; generalize (kt_eq _ _ H2).
      destruct (MT_eq_dec _ kT') as [[c kT'_eq] | kT'_eq];
        rewrite kT'_eq; failmonadsimpl; auto.
      destruct (MT_eq_dec _ (kT c T)) as [[kTT kTT_eq] | kTT_eq];
        destruct (MT_eq_dec _ (kT c T')) as [[kTT' kTT'_eq] | kTT'_eq];
        rewrite kTT_eq; rewrite kTT'_eq; failmonadsimpl; auto.
      intros.
      apply inj_return in H3.
      apply kt_proj1_eq; congruence.
      intros; failmonaddisc.
      intros; failmonaddisc.
      generalize (H0 ke kt); simpl;
        rewrite associativity;
        destruct (MT_eq_dec _ kT') as [[T kT'_eq] | kT'_eq];
        destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq];
        subst; failmonadsimpl; intros H0';
        try apply (wfvm_fail _ _ _ _ _ _ WFVM).
      apply H0'; intros; auto.
      intros; generalize (H1 t Sigma' H2 ke kt); simpl;
        rewrite associativity;
        destruct (MT_eq_dec _ kT') as [[T kT'_eq] | kT'_eq];
        destruct (MT_eq_dec _ mth) as [[T' mth_eq] | mth_eq];
        subst; failmonadsimpl; intros H2';
        try apply (wfvm_fail _ _ _ _ _ _ WFVM).
      apply H2'.
      intros; auto.
      intros; eapply WFVM_ke_kt; eauto; eapply ConsExtension_trans; eauto.
    Qed.

  End BindRule.

End Exception.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
