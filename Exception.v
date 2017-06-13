Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import MonadLib.

Section Exception.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Functor for Types. *)
  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  Inductive ExceptE (A : Set) : Set :=
  | Throw : DType D -> ExceptE A
  | Catch : A -> (unit -> A) -> ExceptE A.

  Definition ExceptE_fmap (B C : Set) (f : B -> C) (e : ExceptE B) : ExceptE C :=
    match e with
      | Throw n => Throw _ n
      | Catch e' h => Catch _ (f e') (fun n => f (h n))
    end.

  Global Instance ExceptE_Functor : Functor ExceptE :=
    {| fmap := ExceptE_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; simpl; auto.
  Defined.

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Definition Exp := Exp F.
  Context {Sub_ExceptE_F : ExceptE :<: F}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_ExceptE_F : WF_Functor _ _ Sub_ExceptE_F _ _}.
  Definition throw'' (t : DType D) : Exp := inject' (Throw _ t).
  Definition throw'  (t : DType D) : Fix F := proj1_sig (throw'' t).
  Global Instance UP'_lit (t : DType D) :
    Universal_Property'_fold (throw' t) := proj2_sig (throw'' t).

  Definition catch'' (e : Exp) (h : unit -> Exp) : Exp :=  inject' (Catch _ e h).

  Definition catch' (e : Fix F) (h : unit -> Fix F)
    {UP'_e : Universal_Property'_fold e}
    {UP'_h : forall n, Universal_Property'_fold (h n)}
    : Fix F := proj1_sig (catch'' (exist _ _ UP'_e) (fun n => exist _ _ (UP'_h n))).

   Global Instance UP'_add {e : Fix F} {h : unit -> Fix F}
    {UP'_e : Universal_Property'_fold e}
    {UP'_h : forall n, Universal_Property'_fold (h n)}
    : Universal_Property'_fold (catch' e h) :=
    proj2_sig (catch'' (exist _ _ UP'_e) (fun n => exist _ _ (UP'_h n))).

  (* Induction Principles for Arith. *)
  Definition ind_alg_ExceptE
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (H : forall n, UP'_P P (throw' n))
    (H0 : forall (e : Fix F) (h : unit -> Fix F)
      (IHe : UP'_P P e)
      (IHh : forall n, UP'_P P (h n)),
      UP'_P P (@catch' _ _ (proj1_sig IHe) (fun n => proj1_sig (IHh n))))
      (e : ExceptE (sig (UP'_P P)))
        :
        sig (UP'_P P) :=
    match e with
      | Throw n => exist _ (throw' n) (H n)
      | Catch e h => exist (UP'_P P) _
        (H0 _ _ (proj2_sig e) (fun n => proj2_sig (h n)))
    end.

  Lemma ind_PAlg_ExceptE (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (H : forall n, UP'_P P (throw' n))
    (H0 : forall e h
      (IHe : UP'_P P e)
      (IHh : forall n, UP'_P P (h n)),
      UP'_P P (@catch' e h (proj1_sig IHe) (fun n => proj1_sig (IHh n))))
    :
    PAlgebra Name ExceptE F (UP'_P P).
    econstructor 1 with (p_algebra := ind_alg_ExceptE P H H0).
    destruct e; simpl.
    unfold throw', throw''; simpl; rewrite wf_functor; reflexivity.
    unfold catch', catch''; simpl; rewrite wf_functor; reflexivity.
  Qed.

  Definition indD_alg_ExceptE
    (P : forall e : Fix F, Universal_Property'_fold e -> Set)
    (H : forall n, UP'_SP P (throw' n))
    (H0 : forall (e : Fix F) (h : unit -> Fix F)
      (IHe : UP'_SP P e)
      (IHh : forall n, UP'_SP P (h n)),
      UP'_SP P (@catch' _ _ (projT1 IHe) (fun n => projT1 (IHh n))))
      (e : ExceptE (sigT (UP'_SP P)))
        :
        sigT (UP'_SP P) :=
    match e with
      | Throw n => existT _ (throw' n) (H n)
      | Catch e h => existT (UP'_SP P) _
        (H0 _ _ (projT2 e) (fun n => projT2 (h n)))
    end.

  Lemma ind_DAlg_ExceptE (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Set)
    (H : forall n, UP'_SP P (throw' n))
    (H0 : forall (e : Fix F) (h : unit -> Fix F)
      (IHe : UP'_SP P e)
      (IHh : forall n, UP'_SP P (h n)),
      UP'_SP P (@catch' _ _ (projT1 IHe) (fun n => projT1 (IHh n))))
    :
    DAlgebra Name ExceptE F (UP'_SP P).
    econstructor 1 with (d_algebra := indD_alg_ExceptE P H H0).
    destruct e; simpl.
    unfold throw', throw''; simpl; rewrite wf_functor; reflexivity.
    unfold catch', catch''; simpl; rewrite wf_functor; reflexivity.
  Qed.

  Definition ind2_alg_ExceptE
    {E E' : Set -> Set}
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Arith_E : ExceptE :<: E}
    {Sub_Arith_E' : ExceptE :<: E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall n, UP'_P2 P (inject (Throw _ n), inject (Throw _ n)))
    (H0 : forall e h
      (IHe : UP'_P2 P e)
      (IHh : forall n, UP'_P2 P (h n)),
      UP'_P2 P (inject (Catch _ (exist _ _ (proj1 (proj1_sig IHe)))
        (fun n => exist _ _ (proj1 (proj1_sig (IHh n))))),
      inject (Catch _ (exist _ _ (proj2 (proj1_sig IHe)))
        (fun n => exist _ _ (proj2 (proj1_sig (IHh n)))))))
    (e : ExceptE (sig (UP'_P2 P)))
        :
        sig (UP'_P2 P) :=
    match e with
      | Throw n => exist _ _ (H n)
      | Catch e h => exist (UP'_P2 P) _
        (H0 _ _ (proj2_sig e) (fun n => proj2_sig (h n)))
    end.

  Lemma ind_P2Alg_ExceptE (Name : Set)
    (E E' : Set -> Set)
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Arith_E : ExceptE :<: E}
    {Sub_Arith_E' : ExceptE :<: E'}
    {WF_Fun_E : WF_Functor _ _ _ _ Fun_E}
    {WF_Fun_E' : WF_Functor _ _ _ _ Fun_E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall n, UP'_P2 P (inject (Throw _ n), inject (Throw _ n)))
    (H0 : forall e h
      (IHe : UP'_P2 P e)
      (IHh : forall n, UP'_P2 P (h n)),
      UP'_P2 P (inject (Catch _ (exist _ _ (proj1 (proj1_sig IHe)))
        (fun n => exist _ _ (proj1 (proj1_sig (IHh n))))),
      inject (Catch _ (exist _ _ (proj2 (proj1_sig IHe)))
        (fun n => exist _ _ (proj2 (proj1_sig (IHh n)))))))
    :
    P2Algebra Name ExceptE E E' (UP'_P2 P).
    econstructor 1 with (p2_algebra := ind2_alg_ExceptE P H H0);
    destruct e; simpl; unfold inject; simpl; rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* No Values for exceptions *)

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Definition stuck : nat -> Fix V := stuck _.

  (* Typing Reference Expressions. *)

   Variable (MT : Set -> Set).
   Context {Fun_MT : Functor MT}.
   Context {Mon_MT : Monad MT}.
   Context {Fail_MT : FailMonad MT}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.

  Definition ExceptE_typeof (R : Set) (rec : R -> typeofR D MT)
     (e : ExceptE R) : typeofR D MT :=
     match e with
       | Throw t => return_ t
       | Catch e' h => do te <- (rec e');
                       do th <- (rec (h tt));
                         if (eq_DType D (proj1_sig te) th) then
                           return_ te else fail
     end.

  Global Instance MAlgebra_typeof_ExceptE T:
    FAlgebra TypeofName T (typeofR D MT) ExceptE :=
    {| f_algebra := ExceptE_typeof T|}.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.

   (* Evaluation Algebra for Arithemetic Expressions. *)

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Exception_ME : Exception ME unit}.
  Context {Fail_ME : FailMonad ME}.
  (* Monadic Evaluation Algebra for Exception Expressions. *)

  Definition ExceptE_evalM (R : Set) (rec : R -> evalMR V ME)
     (e : ExceptE R) : evalMR V ME :=
       match e with
         | Throw t => throw (M := ME) tt
         | Catch e h => catch (rec e) (fun n => rec (h n))
       end.

  Global Instance MAlgebra_evalM_ExceptE T :
    FAlgebra EvalName T (evalMR V ME) ExceptE :=
    {| f_algebra := ExceptE_evalM T|}.

  Context {evalM_F : FAlgebra EvalName Exp (evalMR V ME) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ ExceptE F
    Sub_ExceptE_F (MAlgebra_evalM_ExceptE _) evalM_F}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.

  Global Instance MAlgebra_ExpPrint_ExceptE T :
    FAlgebra ExpPrintName T (ExpPrintR) ExceptE :=
    {| f_algebra := fun rec e => match e with
      | Throw n => fun i => append "(throw)" EmptyString (*(String (ascii_of_nat (n + 48)) EmptyString) ++ ")" *)
      | Catch m n => fun i => append "(catch" ((rec m i) ++ " with " ++ (rec (n tt) (i + 1)) ++ ")")
    end |}.

  Ltac WF_FAlg_rewrite := repeat rewrite wf_functor; simpl;
    repeat rewrite out_in_fmap; simpl;
      repeat rewrite wf_functor; simpl;
        repeat rewrite wf_algebra; simpl.

  (* ============================================== *)
  (* WELL-FORMED MONADIC EXCEPTIONS               *)
  (* ============================================== *)

    (** SuperFunctor for Well-Formed Monadic Value Relation with
       Typing Environment. **)

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
    Variable funWFV : iFunctor WFV.

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Definition WFValueM := iFix WFVM.
    Definition WFValueMC Sigma v T:= WFValueM (mk_WFValueM_i D V MT ME _ Sigma v T).
    Variable funWFVM : iFunctor WFVM.

    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME TypContext WFV) WFVM}.

    Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
    Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) F}.
    Context {WF_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ ExceptE F
      Sub_ExceptE_F (MAlgebra_typeof_ExceptE _) (Typeof_F T)}.

    Context {evalM_F' : forall T, FAlgebra EvalName T (evalMR V ME) F}.
    Context {WF_eval_F' : forall T, @WF_FAlgebra EvalName _ _ ExceptE F
      Sub_ExceptE_F (MAlgebra_evalM_ExceptE _) (evalM_F' T)}.

    Context {Sub_WFVM_Except_WFVM : Sub_iFunctor (WFValueM_Except TypContext) WFVM}.

  Lemma ExceptE_Soundness_H : forall n,
    UP'_SP (eval_soundness_P D V F MT ME _ WFVM) (throw' n).
  Proof.
    unfold eval_soundness_P; intros; econstructor; intros.
    auto with typeclass_instances.
    unfold evalM, typeof, mfold; simpl; unfold throw'; simpl; unfold in_t.
    WF_FAlg_rewrite.
    apply (inject_i (subGF := Sub_WFVM_Except_WFVM)); constructor.
  Qed.

  Lemma eval_soundness_H0 (typeof_R eval_R : Set)
      typeof_rec eval_rec
      :
      forall (eT : typeof_R) (hT : unit -> typeof_R)
        (eE : eval_R) (hE : unit -> eval_R) Sigma
        (IHe : WFValueMC Sigma
          (eval_rec eE) (typeof_rec eT))
        (IHh : forall n Sigma', ConsExtension Sigma' Sigma ->
          WFValueMC Sigma' (eval_rec (hE n)) (typeof_rec (hT n))),
        WFValueMC Sigma
        (ExceptE_evalM _ eval_rec (Catch _ eE hE))
        (ExceptE_typeof _ typeof_rec (Catch _ eT hT)).
    Proof.
      simpl; intros.
      rewrite right_unit with (a := catch _ _).
      rewrite (right_unit (M := MT)).
      rewrite (left_unit (M := MT) (A := unit) tt
        (fun _ => (do te <- typeof_rec eT;
                   do th <- typeof_rec (hT tt);
                     (if eq_DType D (proj1_sig te) th then return_ te else fail)) >>= return_)).
      apply (inject_i (subGF := Sub_WFVM_Except_WFVM)); econstructor 2.
      intros; repeat rewrite <- left_unit, fmap_return; congruence.
      rewrite <- left_unit, <- right_unit, <- right_unit.
      apply IHe.
      intros; rewrite <- right_unit, <- left_unit, <- right_unit;
        destruct t; eapply IHh; eauto.
    Qed.

  Lemma ExceptE_Soundness_H0 : forall (e : Fix F) (h : unit -> Fix F)
    (IHe : UP'_SP (eval_soundness_P D V F MT ME _ WFVM) e)
    (IHh : forall n, UP'_SP (eval_soundness_P D V F MT ME _ WFVM) (h n)),
    UP'_SP (eval_soundness_P D V F MT ME _ WFVM)
    (@catch' _ _ (projT1 IHe) (fun n => projT1 (IHh n))).
  Proof.
    unfold eval_soundness_P; intros; econstructor; intros.
    auto with typeclass_instances.
    unfold evalM, typeof, mfold; simpl; unfold catch'; simpl; unfold in_t.
    WF_FAlg_rewrite.
    destruct IHe as [e_UP' IHe].
    rewrite right_unit with (a := catch _ _).
    rewrite (right_unit (M := MT)).
    rewrite (left_unit (M := MT) (A := unit) tt
      (fun _ => (do te <- mfold (typeofR D MT) (fun R : Set => f_algebra (FAlgebra := Typeof_F R)) e;
        do th <- mfold (typeofR D MT) (fun R : Set => f_algebra (FAlgebra := Typeof_F R)) (h tt);
          (if eq_DType D (proj1_sig te) th then return_ te else fail)) >>=
      return_)).
    apply (inject_i (subGF := Sub_WFVM_Except_WFVM)); econstructor 2.
    intros; repeat rewrite <- left_unit, fmap_return; congruence.
    rewrite <- left_unit, <- right_unit, <- right_unit.
    apply IHe.
    intros; rewrite <- right_unit, <- left_unit, <- right_unit; destruct (IHh t) as [ht_UP' IHht].
    destruct t; eapply IHht.
  Qed.

  Global Instance ExceptE_eval_Soundness :
    DAlgebra ES_ExpName ExceptE F (UP'_SP (eval_soundness_P D V F MT ME _ WFVM)).
  Proof.
    apply ind_DAlg_ExceptE.
    apply ExceptE_Soundness_H.
    apply ExceptE_Soundness_H0.
  Qed.

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

    Section PSoundness.

      Variable P_bind : Set.
      Variable E' : Set -> Set.
      Context {Fun_E' : Functor E'}.
      Context {Sub_Except_E' : ExceptE :<: E'}.
      Context {WF_Fun_E' : WF_Functor _ _ Sub_Except_E' _ _}.

      Variable P : UP'_F F -> UP'_F E' -> P_bind -> TypContext -> Prop.

      Variable Catch_Decomp1 :
        forall e1 e2 h1 h2 e1_UP' e2_UP' e1_UP'' e2_UP'' catch1_UP' catch2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _)
              (inj (Catch _ (exist Universal_Property'_fold e2 e2_UP') h2)))) catch2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _)
              (inj (Catch _ (exist Universal_Property'_fold e1 e1_UP') h1)))) catch1_UP')
          pb Sigma ->
          P (exist _ e2 e2_UP'') (exist _ e1 e1_UP'') pb Sigma.

      Variable Catch_Decomp2 :
        forall e1 e2 h1 h2 catch1_UP' catch2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _)
              (inj (Catch _ e2 h2)))) catch2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _)
              (inj (Catch _ e1 h1)))) catch1_UP')
          pb Sigma ->
          forall t h1_UP'' h2_UP'',
            P (exist _ (proj1_sig (P := Universal_Property'_fold) (h2 t)) h2_UP'')
            (exist _ (proj1_sig (P := Universal_Property'_fold) (h1 t)) h1_UP'') pb Sigma.

    Global Instance Except_eval_soundness'
      (P_Sub : forall e e' pb Sigma Sigma',
        P e e' pb Sigma -> ConsExtension Sigma' Sigma ->
        P e e' pb Sigma')
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D MT) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_Except_E' (MAlgebra_typeof_ExceptE T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalMR V ME)
      (typeof_rec : UP'_F E' -> typeofR D MT)
      :
      P2Algebra ES'_ExpName ExceptE E' F
      (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
        _ _ _ P pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := evalM_F)))).
    Proof.
      apply ind_P2Alg_ExceptE; eauto.
      (* throw case *)
      unfold eval_soundness'_P, UP'_P2; simpl; intros;
        constructor 1 with (x := conj (proj2_sig (inject' (Throw _ n))) (proj2_sig (inject' (Throw _ n)))).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma Gamma WF_Sigma_Gamma IHa.
      repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold ExceptE_fmap; simpl.
      apply (inject_i (subGF := Sub_WFVM_Except_WFVM)); econstructor.
      (* catch case *)
      intros; destruct e as [eE eT]; destruct (h tt) as [hE hT];
        destruct IHe as [[UP'_eE UP'_eT] IHe];
          destruct (IHh tt) as [[UP'_hE UP'_hT] IHh']; simpl in *|-*.
      unfold eval_soundness'_P, UP'_P2; intros.
      assert (Universal_Property'_fold
        (fst
          (inject
            (Catch (sig Universal_Property'_fold)
              (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT)))
              (fun n : unit =>
                exist Universal_Property'_fold (fst (h n))
                (proj1 (proj1_sig (IHh n))))),
            inject
            (Catch (sig Universal_Property'_fold)
              (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT)))
              (fun n : unit =>
                exist Universal_Property'_fold (snd (h n))
                (proj2 (proj1_sig (IHh n))))))) /\
        Universal_Property'_fold
        (snd
          (inject
            (Catch (sig Universal_Property'_fold)
              (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT)))
              (fun n : unit =>
                exist Universal_Property'_fold (fst (h n))
                (proj1 (proj1_sig (IHh n))))),
            inject
            (Catch (sig Universal_Property'_fold)
              (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT)))
              (fun n : unit =>
                exist Universal_Property'_fold (snd (h n))
                (proj2 (proj1_sig (IHh n)))))))) as WF_Catch by
      (simpl; split; unfold inject; exact (proj2_sig _)).
      constructor 1 with (x := WF_Catch); simpl.
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold ExceptE_fmap.
      intros; apply eval_soundness_H0.
      generalize (IHa _ _ (exist _ _ UP'_eE, exist _ _ UP'_eT)
        (Catch_Decomp1 _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma)); simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_eE)); simpl;
        intros eE_eq WF_ref; rewrite <- eE_eq; eauto.
      apply WF_ref.
      apply IHe; eauto.
      intros n Sigma' ConsExt_Sig'_Sig; destruct n;
        generalize (IHa _ _ (exist _ _ UP'_hE, exist _ _ UP'_hT)
          (Catch_Decomp2 _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig) tt _ _)); simpl.
      generalize (typeof_rec_proj (exist _ _ UP'_hE)); simpl;
        intros hE_eq WF_ref; rewrite <- hE_eq; eauto.
      apply WF_ref.
      apply IHh'; eauto.
      apply (Catch_Decomp2 _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig) tt _ _).
    Defined.

    End PSoundness.

    Global Instance Except_eval_soundness'' typeof_rec eval_rec :
      P2Algebra ES'_ExpName ExceptE F F
      (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
        _ _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_F _)) (f_algebra (FAlgebra := evalM_F)))).
    Proof.
      eapply Except_eval_soundness'; eauto.
    Defined.

    Section Except_Sound_Sec.

    Variable WFV' : (WFValue_i D V unit -> Prop) -> WFValue_i D V unit -> Prop.
    Variable funWFV' : iFunctor WFV'.

    Variable WFVM' : (WFValueM_i D V MT ME unit -> Prop) -> WFValueM_i D V MT ME unit -> Prop.
    Variable funWFVM' : iFunctor WFVM'.

    Definition Except_Sound_P (i : WFValueM_i D V MT ME unit) :=
      forall T, fmap (@proj1_sig _ _) (wfvm_T _ _ _ _ _ i) =
        return_ (proj1_sig T) ->
        (exists v : Value,
          wfvm_v _ _ _ _ _ i = return_ (M := ME) v /\
          WFValueC D V _ WFV' tt v T) \/
        exists t, wfvm_v _ _ _ _ _ i = throw t.

    Inductive Except_Sound_Name := except_sound_name.

    Context {Reasonable_MT : Reasonable_Monad MT}.

    Context {WFV_proj1_a_WFV : iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV') WFV'}.
    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV') WFV'}.

    Global Instance Except_Sound_WFVM_base :
      iPAlgebra Except_Sound_Name Except_Sound_P (WFValueM_base D V MT ME _ WFV').
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (Monad_ME := Mon_M)
        (Fail_MT := Fail_MT) (WFV := WFV');
        try assumption; unfold Except_Sound_P; intros.
      (* WFVM_Return' *)
      left; exists v; split; simpl in *; auto.
      destruct H1 as [mt' mt'_eq]; subst.
      rewrite fmap_fusion in H2.
      destruct (fmap_exists _ _ _ _ _ H2) as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0 as [T0 T0_UP']; simpl in *.
      destruct Sigma.
      apply (WFV_proj1_b _ _ _ _ _ _ H0); simpl; auto; congruence.
      (* WFVM_Untyped' *)
      left; simpl in H0; apply sym_eq in H0.
      unfold wbind in H0; rewrite fmap_m, <- associativity, bind_fail in H0.
      apply FailMonad_Disc in H0; destruct H0; auto.
    Qed.

    Context {MT_eq_dec : forall (A : Set) (mta : MT A),
      {exists a, mta = return_ a} + {mta = fail}}.
    Context {ME_eq_dec : forall (A : Set) (mte : ME A),
      (exists a, mte = return_ a) \/ (mte = fail) \/ (mte = throw tt)}.
    Context {Inj_MT : InjMonad MT}.
    Context {Reasonable_ME : Reasonable_Monad ME}.
    Context {fail_neq_throw : forall (A B C : Set) (ma : ME A) (mb : ME B),
      (ma >>= fun _ => fail (M := ME)) <> mb >>= fun _ => throw (A := C) tt}.

    Global Instance Except_Sound_WFVM_Except' :
      iPAlgebra Except_Sound_Name Except_Sound_P (WFValueM_Except unit).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_Except with (TypContextCE := ConsExtensionUnit);
        try assumption; unfold Except_Sound_P; simpl; intros.
      (* throw case *)
      simpl; right; exists tt; reflexivity.
      (* catch case *)
      destruct (MT_eq_dec _ mte) as [[T' mte_eq] | mte_eq]; subst.
      destruct (MT_eq_dec _ mth) as [[T'' mth_eq] | mth_eq]; subst.
      repeat rewrite <- left_unit in H2.
      caseEq (eq_DType _ (proj1_sig T') T''); rewrite H3 in H2.
      destruct (H0 _ H2) as [[v' [ek'_eq WF_v'_T']] | [[] ek'_eq]].
      destruct (ME_eq_dec _ e') as [[v'' e'_eq] | [e'_eq | e'_eq]];
        subst.
      rewrite catch_return; left; exists v'; split; auto.
      failmonaddisc.
      rewrite bind_throw in ek'_eq.
      elimtype False; eapply Exception_Disc with (M := ME) (a := v') (e := tt) (mb := return_ v');
        eauto with typeclass_instances; unfold wbind; rewrite <- left_unit; auto.
      destruct (ME_eq_dec _ e') as [[v'' e'_eq] | [e'_eq | e'_eq]];
        subst.
      rewrite catch_return; right; eexists _; eauto.
      rewrite bind_fail in ek'_eq; elimtype False;
      rewrite left_unit with (a := tt) (f := fun _ => throw tt) in ek'_eq;
        rewrite left_unit with (a := tt) (f := fun _ => fail) in ek'_eq;
          eapply fail_neq_throw; eauto.
      rewrite catch_throw'.
      destruct (H1 tt Sigma (ConsExtension_id _) T) as [[v' [h_eq WF_v'_T']] | [[] h_eq]].
      rewrite rewrite_do with (m := fun U => return_ T' >>= kT U)
        (m' := fun U => kT U T') in H2; [auto |
          apply functional_extensionality; intros; repeat rewrite <- left_unit; auto].
      rewrite rewrite_do with (m := fun U => return_ T'' >>= kT U)
        (m' := fun U => kT U T''); [auto |
          apply functional_extensionality; intros; repeat rewrite <- left_unit; auto].
      rewrite <- H2; apply kt_eq; apply sym_eq; apply (eq_DType_eq _ _ _ H3).
      left; exists v'; split; auto.
      right; eauto.
      destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
      destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
      destruct (MT_eq_dec _ kT') as [[U kT'_eq] | kT'_eq]; subst; failmonaddisc.
    Qed.

    Context {Except_Sound_WFVM : iPAlgebra Except_Sound_Name Except_Sound_P WFVM'}.

    Context {eval_soundness'_Exp_F : forall (typeof_rec : UP'_F F -> typeofR D MT)
       (eval_rec : Names.Exp F -> evalMR V ME),
       P2Algebra ES'_ExpName F F F
       (UP'_P2
         (eval_soundness'_P D V F MT ME _ WFVM'
           Datatypes.unit F Fun_F
           (fun _ _ _ _ => True)
           tt typeof_rec eval_rec f_algebra
           (f_algebra (FAlgebra := evalM_F' (@Names.Exp F Fun_F)))))}.

     Context {WF_MAlg_typeof : WF_MAlgebra Typeof_F}.
     Context {WF_MAlg_eval : WF_MAlgebra evalM_F'}.

    Theorem eval_Except_Sound :
      forall (e : Exp) (T : DType D),
        fmap (@proj1_sig _ _) (typeof D F MT (proj1_sig e)) = return_ (proj1_sig T) ->
        (exists v : Value,
          evalM V F ME (proj1_sig e) = return_ (M := ME) v /\
          WFValueC D V _ WFV' tt v T) \/
        exists t, evalM V F ME (proj1_sig e) = throw (M := ME) t.
    Proof.
      intro e.
      apply (ifold_ WFVM' _ (ip_algebra (iPAlgebra := Except_Sound_WFVM)) _
        (eval_soundness (eval_soundness'_Exp_E := eval_soundness'_Exp_F) D V F MT ME WFVM' e tt)).
    Qed.

  End Except_Sound_Sec.

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
