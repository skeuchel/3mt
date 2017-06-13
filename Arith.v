Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import MonadLib.

Section Arith.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Arith (a : Set) : Set :=
  | Lit : nat -> Arith a
  | Add : a -> a -> Arith a.

  Definition Arith_fmap (B C : Set) (f : B -> C) (Aa : Arith B) : Arith C :=
    match Aa with
      | Lit n => Lit _ n
      | Add a b => Add _ (f a) (f b)
    end.

  Global Instance Arith_Functor : Functor Arith :=
    {| fmap := Arith_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Definition Exp := Exp F.
  Context {Sub_Arith_F : Arith :<: F}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_Arith_F : WF_Functor _ _ Sub_Arith_F _ _}.
  Definition lit' (n : nat) : Exp := inject' (Lit _ n).
  Definition lit  (n : nat) : Fix F := proj1_sig (lit' n).
  Global Instance UP'_lit {n : nat} :
    Universal_Property'_fold (lit n) := proj2_sig (lit' n).

  Definition add' (m n : Exp) : Exp :=  inject' (Add _ m n).

  Definition add (m n : Fix F)
    {UP'_m : Universal_Property'_fold m}
    {UP'_n : Universal_Property'_fold n}
    : Fix F := proj1_sig (add' (exist _ _ UP'_m) (exist _ _ UP'_n)).

   Global Instance UP'_add {m n : Fix F}
     {UP'_m : Universal_Property'_fold m}
     {UP'_n : Universal_Property'_fold n}
     :
     Universal_Property'_fold (add m n) :=
     proj2_sig (add' (exist _ _ UP'_m) (exist _ _ UP'_n)).

  (* Induction Principles for Arith. *)
  Definition ind_alg_Arith
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (H : forall n, UP'_P P (lit n))
    (H0 : forall m n
      (IHm : UP'_P P m)
      (IHn : UP'_P P n),
      UP'_P P (@add m n (proj1_sig IHm) (proj1_sig IHn)))
      (e : Arith (sig (UP'_P P)))
        :
        sig (UP'_P P) :=
    match e with
      | Lit n => exist _ (lit n) (H n)
      | Add m n => exist (UP'_P P) _
        (H0 (proj1_sig m) (proj1_sig n) (proj2_sig m) (proj2_sig n))
    end.

  Definition ind2_alg_Arith
    {E E' : Set -> Set}
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Arith_E : Arith :<: E}
    {Sub_Arith_E' : Arith :<: E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall n, UP'_P2 P (inject (Lit _ n), inject (Lit _ n)))
    (H0 : forall m n
      (IHm : UP'_P2 P m)
      (IHn : UP'_P2 P n),
      UP'_P2 P (inject (Add _ (exist _ _ (proj1 (proj1_sig IHm)))
        (exist _ _ (proj1 (proj1_sig IHn)))),
      inject (Add _ (exist _ _ (proj2 (proj1_sig IHm)))
        (exist _ _ (proj2 (proj1_sig IHn))))))
      (e : Arith (sig (UP'_P2 P)))
        :
        sig (UP'_P2 P) :=
    match e with
      | Lit n => exist _ _ (H n)
      | Add m n => exist (UP'_P2 P) _
        (H0 (proj1_sig m) (proj1_sig n) (proj2_sig m) (proj2_sig n))
    end.

  Lemma ind_PAlg_Arith (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (H : forall n, UP'_P P (lit n))
    (H0 : forall m n
      (IHm : UP'_P P m)
      (IHn : UP'_P P n),
      UP'_P P (@add m n (proj1_sig IHm) (proj1_sig IHn)))
    :
    PAlgebra Name Arith F (UP'_P P).
    econstructor 1 with (p_algebra := ind_alg_Arith P H H0).
    destruct e; simpl.
    unfold lit, lit'; simpl; rewrite wf_functor; reflexivity.
    unfold add, add'; simpl; rewrite wf_functor; reflexivity.
  Qed.

  Lemma ind_P2Alg_Arith (Name : Set)
    (E E' : Set -> Set)
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Arith_E : Arith :<: E}
    {Sub_Arith_E' : Arith :<: E'}
    {WF_Fun_E : WF_Functor _ _ _ _ Fun_E}
    {WF_Fun_E' : WF_Functor _ _ _ _ Fun_E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall n, UP'_P2 P (inject (Lit _ n), inject (Lit _ n)))
    (H0 : forall m n
      (IHm : UP'_P2 P m)
      (IHn : UP'_P2 P n),
      UP'_P2 P (inject (Add _ (exist _ _ (proj1 (proj1_sig IHm)))
        (exist _ _ (proj1 (proj1_sig IHn)))),
      inject (Add _ (exist _ _ (proj2 (proj1_sig IHm)))
        (exist _ _ (proj2 (proj1_sig IHn)))))) :
    P2Algebra Name Arith E E' (UP'_P2 P).
    econstructor 1 with (p2_algebra := ind2_alg_Arith P H H0);
    destruct e; simpl; unfold inject; simpl; rewrite wf_functor; reflexivity.
  Qed.

  (* Alternative Induction Principles for Arith. *)
  Definition indD_alg_Arith
    (P : forall e : Fix F, Universal_Property'_fold e -> Set)
    (H : forall n, UP'_SP P (lit n))
    (H0 : forall m n
      (IHm : UP'_SP P m)
      (IHn : UP'_SP P n),
      UP'_SP P (@add m n (projT1 IHm) (projT1 IHn)))
      (e : Arith (sigT (UP'_SP P)))
        :
        sigT (UP'_SP P) :=
    match e with
      | Lit n => existT _ (lit n) (H n)
      | Add m n => existT (UP'_SP P) _
        (H0 (projT1 m) (projT1 n) (projT2 m) (projT2 n))
    end.

  Lemma ind_DAlg_Arith (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Set)
    (H : forall n, UP'_SP P (lit n))
    (H0 : forall m n
      (IHm : UP'_SP P m)
      (IHn : UP'_SP P n),
      UP'_SP P (@add m n (projT1 IHm) (projT1 IHn)))
    :
    DAlgebra Name Arith F (UP'_SP P).
    econstructor 1 with (d_algebra := indD_alg_Arith P H H0).
    destruct e; simpl.
    unfold lit, lit'; simpl; rewrite wf_functor; reflexivity.
    unfold add, add'; simpl; rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Arithmetic Values. *)
   Inductive NatValue (A : Set) : Set :=
   | VI : nat -> NatValue A.

   Definition VI_fmap : forall (A B : Set) (f : A -> B),
     NatValue A -> NatValue B :=
     fun A B _ e => match e with
                      | VI n => VI _ n
                    end.

   Global Instance VI_Functor : Functor NatValue :=
     {| fmap := VI_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.
   Context {Sub_NatValue_V : NatValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_NatValue_F : WF_Functor _ _ Sub_NatValue_V _ _}.

  Definition vi' (n : nat) : Value := inject' (VI _ n).
  Definition vi (n : nat) : Fix V := proj1_sig (vi' n).

   Global Instance UP'_vi {n : nat} :
     Universal_Property'_fold (vi n) := proj2_sig (vi' n).

   (* Constructor Testing for Arithmetic Values. *)

   Definition isVI : Fix V -> option nat :=
     fun exp =>
       match project exp with
        | Some (VI n) => Some n
        | None        => None
       end.

    Lemma project_vi_vi : forall n,
      project (F := V) (G := NatValue) (vi n) = Some (VI _ n).
    Proof.
      intros; unfold project, vi, inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold VI_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

    Lemma project_vi'_vi : forall n,
      project (F := V) (G := NatValue) (proj1_sig (vi' n)) = Some (VI _ n).
    Proof.
      intros; unfold project, vi', inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold VI_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Definition stuck : nat -> Fix V := stuck _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

   Context {Sub_BotValue_V : BotValue :<: V}.

   (* Evaluation Algebra for Arithemetic Expressions. *)

   Definition Arith_eval (R : Set) (rec : R -> evalR V)
     (e : Arith R) : evalR V :=
       match e with
         | Lit n => (fun _ => vi' n)
         | Add m n => (fun env =>
           let m' := (rec m env) in
             let n' := (rec n env) in
               match isVI (proj1_sig m'), isVI (proj1_sig n') with
                 | Some m', Some n' => vi' (m' + n')
                 | _, _ =>
                   if @isBot _ Fun_V Sub_BotValue_V (proj1_sig m') then @bot' _ Fun_V Sub_BotValue_V else
                     if @isBot _ Fun_V Sub_BotValue_V (proj1_sig n') then @bot' _ Fun_V Sub_BotValue_V else
                       stuck' 4
               end)
       end.

  Global Instance MAlgebra_eval_Arith T :
    FAlgebra EvalName T (evalR V) Arith :=
    {| f_algebra := Arith_eval T |}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Fail_M : FailMonad ME}.

  (* Monadic Evaluation Algebra for Arithemetic Expressions. *)

  Definition Arith_evalM (R : Set) (rec : R -> evalMR V ME)
     (e : Arith R) : evalMR V ME :=
       match e with
         | Lit n => return_ (vi' n)
         | Add m n => do m' <- rec m;
                      do n' <- rec n;
                        return_
                        match isVI (proj1_sig m'), isVI (proj1_sig n') with
                          | Some m', Some n' => vi' (m' + n')
                          | _, _ => stuck' 4
                        end
       end.

  Global Instance MAlgebra_evalM_Arith T :
    FAlgebra EvalName T (evalMR V ME) Arith :=
    {| f_algebra := Arith_evalM T|}.

  Context {evalM_F : FAlgebra EvalName Exp (evalMR V ME) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ Arith F
    Sub_Arith_F (MAlgebra_evalM_Arith _) evalM_F}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.

  Global Instance MAlgebra_ExpPrint_Arith T :
    FAlgebra ExpPrintName T (ExpPrintR) Arith :=
    {| f_algebra := fun rec e => match e with
      | Lit n => fun i => String (ascii_of_nat (n + 48)) EmptyString
      | Add m n => fun i => append "(" ((rec m i) ++ " + " ++ (rec n i) ++ ")")
    end |}.

  Global Instance MAlgebra_ValuePrint_VI T :
    FAlgebra ValuePrintName T ValuePrintR NatValue :=
    {| f_algebra := fun rec e =>
      match e with
        | VI n => String (ascii_of_nat (n + 48)) EmptyString
      end |}.

  Ltac WF_FAlg_rewrite := repeat rewrite wf_functor; simpl;
    repeat rewrite out_in_fmap; simpl;
      repeat rewrite wf_functor; simpl;
        repeat rewrite wf_algebra; simpl.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Arithmetic Type. *)
  Inductive AType (A : Set) : Set :=
  | TNat : AType A.

  Definition AType_fmap : forall (A B : Set) (f : A -> B),
    AType A -> AType B := fun A B _ _ => TNat _.

  Global Instance AType_Functor : Functor AType :=
    {| fmap := AType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_AType_D  : AType :<: D}.

   (* Constructor + Universal Property. *)
  Context {WF_Sub_AType_D : WF_Functor _ _ Sub_AType_D _ _}.

  Definition tnat' : DType := inject' (TNat _).
  Definition tnat : Fix D := proj1_sig tnat'.
  Global Instance UP'_tnat :
    Universal_Property'_fold tnat := proj2_sig tnat'.

  (* Induction Principle for Nat Types. *)
  Definition ind_alg_AType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop)
    (H : UP'_P P tnat)
    (d : AType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TNat => exist _ _ H
    end.

  Lemma ind_PAlg_AType {Sub_AType_D' : AType :<: D}
    (eq_Sub_AType : forall A (d : AType A),
      inj (Sub_Functor := Sub_AType_D) d = inj (Sub_Functor := Sub_AType_D') d)
    (Name : Set)
    (P : forall e : Fix D, Universal_Property'_fold e -> Prop)
    (H : UP'_P P tnat) :
    PAlgebra (sub_F_G := Sub_AType_D') Name AType D (UP'_P P).
    econstructor 1 with (p_algebra := ind_alg_AType P H).
    destruct e; simpl; unfold tnat, tnat'; simpl;
      rewrite wf_functor; apply f_equal; eauto.
  Qed.

  (* Type Equality Section. *)
  Definition isTNat : Fix D -> bool :=
   fun typ =>
     match project typ with
      | Some TNat => true
      | None      => false
     end.

  Lemma project_tnat_tnat : project (F := D) (G := AType) tnat = Some (TNat _).
  Proof.
    intros; unfold project, tnat, inject; simpl; rewrite out_in_fmap.
    repeat rewrite wf_functor; simpl; unfold AType_fmap.
    rewrite prj_inj; reflexivity.
  Qed.

  Lemma project_tnat'_tnat :
    project (F := D) (G := AType) (proj1_sig tnat') = Some (TNat _).
  Proof.
    intros; unfold project, tnat', inject; simpl; rewrite out_in_fmap.
    repeat rewrite wf_functor; simpl; unfold AType_fmap.
    rewrite prj_inj; reflexivity.
  Qed.

  Definition AType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D)
    (e : AType R) : eq_DTypeR D :=
    match e with
      | TNat => fun t => isTNat (proj1_sig t)
    end.

  Global Instance MAlgebra_eq_DType_Arith T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) AType :=
    {| f_algebra := AType_eq_DType T|}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_AType_D (MAlgebra_eq_DType_Arith T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_DType_eq_AType {Sub_AType_D' : AType :<: D}
    (eq_Sub_AType : forall A (d : AType A),
      inj (Sub_Functor := Sub_AType_D) d = inj (Sub_Functor := Sub_AType_D') d)
    :
    PAlgebra (sub_F_G := Sub_AType_D') eq_DType_eqName AType D (UP'_P (eq_DType_eq_P D)).
  Proof.
    apply ind_PAlg_AType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tnat, tnat', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTNat in H.
    caseEq (project (subGF := Sub_AType_D) (proj1_sig d2)); rewrite H0 in H;
      try discriminate; destruct a.
    unfold project in H0.
    apply inj_prj in H0.
    unfold tnat, tnat'; simpl; rewrite wf_functor; simpl.
    unfold AType_fmap.
    generalize (f_equal (in_t_UP' _ _ ) H0); intros.
    apply (f_equal (@proj1_sig _ _)) in H1;
      rewrite in_out_UP'_inverse in H1.
    rewrite H1; simpl; rewrite wf_functor; simpl; unfold AType_fmap;
      reflexivity.
    exact (proj2_sig d2).
  Qed.

  Global Instance PAlgebra_eq_DType_neq_AType
    {Sub_AType_D' : AType :<: D}
    (eq_Sub_AType : forall A (d : AType A),
      inj (Sub_Functor := Sub_AType_D) d = inj (Sub_Functor := Sub_AType_D') d)
    :
    PAlgebra (sub_F_G := Sub_AType_D') eq_DType_neqName AType D (UP'_P (eq_DType_neq_P D)).
  Proof.
    apply ind_PAlg_AType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_neq_P; intros.
    unfold eq_DType, mfold, tnat, tnat', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTNat in H.
    caseEq (project (subGF := Sub_AType_D) (proj1_sig d2)); rewrite H0 in H;
      try (destruct a; discriminate).
    unfold not; intros; rewrite <- H1 in H0.
    unfold project, tnat, inject in H0; simpl in H0.
    rewrite out_in_fmap in H0; repeat rewrite wf_functor in H0;
      simpl in H0; rewrite prj_inj in H0; discriminate.
  Qed.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Arithmetic Expressions. *)

  Variable (MT : Set -> Set).
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.

  Definition Arith_typeof (R : Set) (rec : R -> typeofR D MT)
     (e : Arith R) : typeofR D MT :=
     match e with
       | Lit n => return_ tnat'
       | Add m n => do tm <- rec m;
                    do tn <- rec n;
                      match isTNat (proj1_sig tm), isTNat (proj1_sig tn) with
                          | true, true => return_ tnat'
                          | _, _ => fail
                        end
     end.

  Global Instance MAlgebra_typeof_Arith T:
    FAlgebra TypeofName T (typeofR D MT) Arith :=
    {| f_algebra := Arith_typeof T|}.

  (* ============================================== *)
  (* WELL-FORMED NAT VALUES                         *)
  (* ============================================== *)

  Variable TypContext : Set.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Variable funWFV : iFunctor WFV.

  (** Natural Numbers are well-formed **)

  Inductive WFValue_VI (WFV : WFValue_i D V TypContext -> Prop) : WFValue_i D V TypContext -> Prop :=
  | WFV_VI : forall Sigma n v T,
    proj1_sig v = vi n ->
    proj1_sig T = tnat ->
    WFValue_VI WFV (mk_WFValue_i D V _ Sigma v T).

  Definition ind_alg_WFV_VI (P : WFValue_i D V TypContext -> Prop)
    (H : forall Sigma n v T veq Teq, P (mk_WFValue_i _ _ _ Sigma v T))
    i (e : WFValue_VI P i) : P i :=
    match e in WFValue_VI _ i return P i with
      | WFV_VI Sigma n v T veq Teq => H Sigma n v T veq Teq
    end.

  Definition WFV_VI_ifmap (A B : WFValue_i D V TypContext -> Prop) i (f : forall i, A i -> B i)
    (WFV_a : WFValue_VI A i) : WFValue_VI B i :=
    match WFV_a in (WFValue_VI _ s) return (WFValue_VI B s)
      with
      | WFV_VI Sigma n v T veq Teq => WFV_VI B Sigma n v T veq Teq
    end.

  Global Instance iFun_WFV_VI : iFunctor WFValue_VI.
    constructor 1 with (ifmap := WFV_VI_ifmap).
    destruct a; simpl; intros; reflexivity.
    destruct a; simpl; intros; reflexivity.
  Defined.

  Variable Sub_WFV_VI_WFV : Sub_iFunctor WFValue_VI WFV.

  Global Instance WFV_proj1_a_VI :
    iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V TypContext WFV) WFValue_VI.
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WFV_proj1_a_P.
    inversion H; subst; simpl; intros.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; simpl; eauto.
    rewrite H3; eauto.
  Defined.

   Global Instance WFV_proj1_b_VI :
     iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V TypContext WFV) WFValue_VI.
     econstructor; intros.
     unfold iAlgebra; intros; unfold WFV_proj1_b_P.
     inversion H; subst; simpl; intros.
     apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; simpl; eauto.
     rewrite H3; eauto.
   Defined.

  (* Inversion principles for Well-formed natural numbers. *)
  Definition WF_invertVI_P (i : WFValue_i D V TypContext) :=
    proj1_sig (wfv_T _ _ _ i) = tnat ->
    WFValue_VI (iFix WFV) i.

  Inductive WF_invertVI_Name := wfv_invertvi_name.
  Context {WF_invertVI_WFV :
    iPAlgebra WF_invertVI_Name WF_invertVI_P WFV}.

  Global Instance WF_invertVI_VI :
    iPAlgebra WF_invertVI_Name WF_invertVI_P WFValue_VI.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertVI_P.
    inversion H; subst; simpl; intros.
    econstructor; eassumption.
  Defined.

  Definition WF_invertVI := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertVI_WFV)).

  Context {TypContextCE : ConsExtensionC TypContext}.

  Global Instance WFV_Weaken_VI :
    iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V TypContext WFV) WFValue_VI.
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WFValue_Weaken_P.
    inversion H; subst; simpl; intros.
    apply inject_i; econstructor; eassumption.
  Defined.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {WFV_proj1_a_WFV :
    iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFV}.
  Context {WFV_proj1_b_WFV :
     iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) F}.
  Context {WF_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ Arith F
    Sub_Arith_F (MAlgebra_typeof_Arith _) (Typeof_F T)}.

  Context {evalM_F' : forall T, FAlgebra EvalName T (evalMR V ME) F}.
  Context {WF_evalM_F' : forall T, @WF_FAlgebra EvalName _ _ Arith F
    Sub_Arith_F (MAlgebra_evalM_Arith _) (evalM_F' T)}.

  Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
  Context {funWFVM : iFunctor WFVM}.

  Context {Sub_WFVM_base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.

  Lemma Arith_eval_Soundness_H :
    forall n : nat,
      UP'_SP (eval_soundness_P D V F MT ME _ WFVM) (lit n).
  Proof.
    intros; econstructor.
    unfold eval_soundness_P; intros; simpl.
    unfold typeof, evalM, mfold, lit; simpl; unfold in_t; simpl.
    WF_FAlg_rewrite.
    apply (inject_i (subGF := Sub_WFVM_base_WFVM)); econstructor 1 with (T := tnat').
    apply inject_i; econstructor; unfold vi; simpl; auto.
    apply return_orn; auto.
  Defined.

  Context {wfvm_bind_alg :
    iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

  Lemma Arith_eval_soundness'_H0
   (typeof_R eval_R : Set) typeof_rec eval_rec :
   forall (m1 n1 : typeof_R) (m2 n2 : eval_R)
     (Sigma : TypContext)
     (IHm1 :  WFValueMC D V MT ME _ WFVM Sigma
       (eval_rec m2) (typeof_rec m1))
     (IHm2 : forall Sigma', ConsExtension Sigma' Sigma ->
       WFValueMC D V MT ME _ WFVM Sigma'
       (eval_rec n2) (typeof_rec n1)),
     WFValueMC D V MT ME _ WFVM Sigma
       (Arith_evalM _ eval_rec (Add _ m2 n2))
       (Arith_typeof _ typeof_rec (Add _ m1 n1)).
  Proof.
    intros; simpl.
    apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
    intros; rewrite H; reflexivity.
    intros; simpl.
    apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
    intros; rewrite H1; reflexivity.
    intros; simpl.
    rename H0 into WF_v_T.
    rename H2 into WF_v0_T0.
    unfold isTNat, isVI.
    caseEq (project (proj1_sig T0)).
    destruct a.
    caseEq (project (proj1_sig T)).
    destruct a.
    rename H0 into T0_eq; rename H2 into T_eq.
    apply project_inject in T_eq; apply project_inject in T0_eq;
      auto with typeclass_instances; try exact (proj2_sig _).
    generalize (WF_invertVI _ WF_v_T T_eq) as WF_v_T';
    generalize (WF_invertVI _ WF_v0_T0 T0_eq) as WF_v_T0'; simpl; intros.
    inversion WF_v_T0'; inversion WF_v_T'; subst.
    rewrite H3, H8, project_vi_vi, project_vi_vi.
    apply (inject_i (subGF := Sub_WFVM_base_WFVM)); econstructor 1 with (T := tnat').
    apply inject_i; econstructor.
    unfold vi; simpl; auto.
    unfold tnat; simpl; auto.
    apply return_orn; reflexivity.
    apply (inject_i (subGF := Sub_WFVM_base_WFVM)).
    eapply WFVM_Untyped_T.
    destruct (project (proj1_sig T)).
    destruct a.
    apply (inject_i (subGF := Sub_WFVM_base_WFVM)).
    eapply WFVM_Untyped_T.
    apply (inject_i (subGF := Sub_WFVM_base_WFVM)).
    eapply WFVM_Untyped_T.
  Qed.

  Section PSoundness.

    Variable P_bind : Set.
    Variable E' : Set -> Set.
    Context {Fun_E' : Functor E'}.
    Context {Sub_Arith_E' : Arith :<: E'}.
    Context {WF_Fun_E' : WF_Functor _ _ Sub_Arith_E' _ _}.

    Variable P : UP'_F F -> UP'_F E' -> P_bind -> TypContext -> Prop.

    Variable Add_Decomp1 :
      forall m1 m2 n1 n2 m1_UP' m2_UP' m1_UP'' m2_UP'' add1_UP' add2_UP' pb Sigma
        (WF_Sigma : P (exist Universal_Property'_fold
          (in_t (fmap (@proj1_sig _ _) (inj (Add _ (exist Universal_Property'_fold m2 m2_UP') n2)))) add2_UP')
        (exist Universal_Property'_fold
          (in_t (fmap (@proj1_sig _ _) (inj (Add _ (exist Universal_Property'_fold m1 m1_UP') n1)))) add1_UP')
        pb Sigma),
        P (exist _ m2 m2_UP'') (exist _ m1 m1_UP'') pb Sigma.

    Variable Add_Decomp2 :
      forall m1 m2 n1 n2 n1_UP' n2_UP' n1_UP'' n2_UP'' add1_UP' add2_UP' pb Sigma
        (WF_Sigma : P (exist Universal_Property'_fold
          (in_t (fmap (@proj1_sig _ _) (inj (Add _ m2 (exist Universal_Property'_fold n2 n2_UP'))))) add2_UP')
        (exist Universal_Property'_fold
          (in_t (fmap (@proj1_sig _ _) (inj (Add _ m1 (exist Universal_Property'_fold n1 n1_UP'))))) add1_UP')
        pb Sigma),
        P (exist _ n2 n2_UP'') (exist _ n1 n1_UP'') pb Sigma.

    Global Instance Arith_eval_soundness'
      (P_Sub : forall e e' pb Sigma Sigma',
        P e e' pb Sigma -> ConsExtension Sigma' Sigma ->
        P e e' pb Sigma')
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D MT) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_Arith_E' (MAlgebra_typeof_Arith T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalMR V ME)
      (typeof_rec : UP'_F E' -> typeofR D MT)
      :
      P2Algebra ES'_ExpName Arith E' F
      (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
        _ _ _ P pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := evalM_F)))).
    Proof.
      apply ind_P2Alg_Arith; eauto.
      (* lit n case *)
      unfold eval_soundness'_P, UP'_P2; simpl; intros;
        constructor 1 with
          (x := conj (proj2_sig (inject' (Lit _ n))) (proj2_sig (inject' (Lit _ n)))).
      unfold inject; simpl; repeat rewrite out_in_fmap;
        repeat rewrite wf_functor; intros.
      WF_FAlg_rewrite.
      apply (inject_i (subGF := Sub_WFVM_base_WFVM));
        constructor 1 with (T := tnat').
      apply inject_i; econstructor; unfold vi; simpl; eauto.
      apply return_orn; eauto.
      (* add case *)
      destruct m as [m1 m2]; destruct n as [n1 n2];
        destruct IHm as [[UP'_m1 UP'_m2] IHm];
          destruct IHn as [[UP'_n1 UP'_n2] IHn]; simpl in *|-*.
      assert (Universal_Property'_fold
    (fst
       (inject
          (Add (sig Universal_Property'_fold)
             (exist Universal_Property'_fold m1 (proj1 (conj UP'_m1 UP'_m2)))
             (exist Universal_Property'_fold n1 (proj1 (conj UP'_n1 UP'_n2)))),
       inject
         (Add (sig Universal_Property'_fold)
            (exist Universal_Property'_fold m2 (proj2 (conj UP'_m1 UP'_m2)))
            (exist Universal_Property'_fold n2 (proj2 (conj UP'_n1 UP'_n2)))))) /\
    Universal_Property'_fold
    (snd
      (inject
        (Add (sig Universal_Property'_fold)
          (exist Universal_Property'_fold m1 (proj1 (conj UP'_m1 UP'_m2)))
          (exist Universal_Property'_fold n1 (proj1 (conj UP'_n1 UP'_n2)))),
        inject
        (Add (sig Universal_Property'_fold)
          (exist Universal_Property'_fold m2 (proj2 (conj UP'_m1 UP'_m2)))
          (exist Universal_Property'_fold n2 (proj2 (conj UP'_n1 UP'_n2))))))).
      simpl; split; unfold inject; exact (proj2_sig _).
      unfold eval_soundness'_P, UP'_P2; intros.
      constructor 1 with (x := H).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Arith_fmap.
      intros; apply Arith_eval_soundness'_H0.
      intros; generalize (IHa _ _ (exist _ _ UP'_m1, exist _ _ UP'_m2)
        (Add_Decomp1 _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma)); simpl.
      rewrite typeof_rec_proj; simpl; intros H'; apply H'.
      apply IHm; eauto.
      eapply (Add_Decomp1 _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma).
      intros Sigma' ConsExt_Sig'_Sig;
        generalize (IHa _ _ (exist _ _ UP'_n1, exist _ _ UP'_n2)
          (Add_Decomp2 _ _ _ _ _ _ _ _ _ _ _ _ (P_Sub _ _ _ _ _
            WF_Sigma ConsExt_Sig'_Sig))); simpl.
      rewrite typeof_rec_proj; simpl; intros H'; apply H'.
      apply IHn; eauto.
      eapply P_Sub; try eassumption.
      eapply (Add_Decomp2 _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma).
    Defined.

  End PSoundness.

  Global Instance Arith_eval_soundness'' typeof_rec eval_rec :
    P2Algebra ES'_ExpName Arith F F
    (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
      _ _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
      (f_algebra (FAlgebra := Typeof_F _)) (f_algebra (FAlgebra := evalM_F)))).
  Proof.
    eapply Arith_eval_soundness'; eauto.
  Defined.

End Arith.

  Hint Extern 5 (iPAlgebra WF_invertVI_Name (WF_invertVI_P _ _ _ _) _) =>
    constructor; unfold iAlgebra; let H := fresh in
      intros i H; unfold WF_invertVI_P;
        inversion H; simpl;
          match goal with
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
                  apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)]
          end : typeclass_instances.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
