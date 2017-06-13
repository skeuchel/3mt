Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import MonadLib.

Section Bool.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Boolean Type. *)
  Inductive BType (A : Set) : Set :=
  | TBool : BType A.

  Definition BType_fmap : forall (A B : Set) (f : A -> B),
    BType A -> BType B := fun A B _ _ => TBool _.

  Global Instance BType_Functor : Functor BType :=
    {| fmap := BType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_BType_D  : BType :<: D}.

   (* Constructor + Universal Property. *)
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D _ _}.

  Definition tbool' : DType := inject' (TBool _).
  Definition tbool : Fix D := proj1_sig tbool'.
  Global Instance UP'_tbool :
    Universal_Property'_fold tbool := proj2_sig tbool'.

  (* Induction Principle for Nat Types. *)
  Definition ind_alg_BType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop)
    (H : UP'_P P tbool)
    (d : BType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TBot => exist _ _ H
    end.

    Lemma WF_ind_alg_BType {Sub_BType_D' : BType :<: D}
    (eq_Sub_BType : forall A (d : BType A),
      inj (Sub_Functor := Sub_BType_D) d = inj (Sub_Functor := Sub_BType_D') d)
    (Name : Set)
    (P : forall e : Fix D, Universal_Property'_fold e -> Prop)
    (H : UP'_P P tbool)
    : PAlgebra Name BType D (sub_F_G := Sub_BType_D') (UP'_P P).
      econstructor 1 with (p_algebra := ind_alg_BType P H).
      intros; destruct e; simpl;
      unfold tbool, tbool'; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.

  (* Type Equality Section. *)
  Definition isTBool : Fix D -> bool :=
   fun typ =>
     match project typ with
      | Some TBool => true
      | None      => false
     end.

  Definition BType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D)
    (e : BType R) : eq_DTypeR D :=
    match e with
      | TBool => fun t => isTBool (proj1_sig t)
    end.

  Global Instance MAlgebra_eq_DType_Bool T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) BType :=
    {| f_algebra := BType_eq_DType T|}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_BType_D (MAlgebra_eq_DType_Bool T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_DType_neq_BType {Sub_BType_D' : BType :<: D}
    (eq_Sub_BType : forall A (d : BType A),
      inj (Sub_Functor := Sub_BType_D) d = inj (Sub_Functor := Sub_BType_D') d):
    PAlgebra eq_DType_neqName BType D (sub_F_G := Sub_BType_D') (UP'_P (eq_DType_neq_P D)).
  Proof.
    apply WF_ind_alg_BType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_neq_P; intros.
    unfold eq_DType, mfold, tbool, tbool', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold not; intros; rewrite <- H0 in H.
    unfold isTBool, project, tbool, inject in H; simpl in H.
    rewrite out_in_fmap in H; repeat rewrite wf_functor in H;
      simpl in H; rewrite prj_inj in H; discriminate.
  Qed.

  Global Instance PAlgebra_eq_DType_eq_BType {Sub_BType_D' : BType :<: D}
    (eq_Sub_BType : forall A (d : BType A),
      inj (Sub_Functor := Sub_BType_D) d = inj (Sub_Functor := Sub_BType_D') d):
    PAlgebra eq_DType_eqName BType D (sub_F_G := Sub_BType_D') (UP'_P (eq_DType_eq_P D)).
  Proof.
    apply WF_ind_alg_BType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tbool, tbool', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTBool in H.
    caseEq (project (subGF := Sub_BType_D) (proj1_sig d2)); rewrite H0 in H;
      try discriminate; destruct b.
    unfold project in H0.
    apply inj_prj in H0.
    unfold tbool, tbool'; simpl; rewrite wf_functor; simpl.
    unfold BType_fmap.
    generalize (f_equal (in_t_UP' _ _ ) H0); intros.
    apply (f_equal (@proj1_sig _ _)) in H1;
      rewrite in_out_UP'_inverse in H1.
    rewrite H1; simpl; rewrite wf_functor; simpl; unfold BType_fmap;
      reflexivity.
    exact (proj2_sig d2).
  Defined.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Bool (a : Set) : Set :=
  | BLit : bool -> Bool a
  | If : a -> a -> a -> Bool a.

  Definition Bool_fmap (B C : Set) (f : B -> C) (Aa : Bool B) : Bool C :=
    match Aa with
      | BLit n => BLit _ n
      | If i t e => If _ (f i) (f t) (f e)
    end.

  Global Instance Bool_Functor : Functor Bool :=
    {| fmap := Bool_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Definition Exp := Exp F.
  Context {Sub_Bool_F : Bool :<: F}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_Bool_F : WF_Functor _ _ Sub_Bool_F _ _}.
  Definition blit' (b : bool) : Exp :=
    inject' (BLit _ b).
  Definition blit (b : bool) : Fix F := proj1_sig (blit' b).
  Global Instance UP'_blit {b : bool} :
    Universal_Property'_fold (blit b) := proj2_sig (blit' b).

  Definition cond' (i t e : Exp) : Exp :=
    inject' (If _ i t e).

  Definition cond (i t e : Fix F)
    {UP'_i : Universal_Property'_fold i}
    {UP'_t : Universal_Property'_fold t}
    {UP'_e : Universal_Property'_fold e}
    : Fix F := proj1_sig (cond' (exist _ _ UP'_i) (exist _ _ UP'_t) (exist _ _ UP'_e)).

  Global Instance UP'_cond  {i t e : Fix F }
    {UP'_i : Universal_Property'_fold i}
    {UP'_t : Universal_Property'_fold t}
    {UP'_e : Universal_Property'_fold e}
    :
    Universal_Property'_fold (cond i t e) :=
    proj2_sig (cond' (exist _ _ UP'_i) (exist _ _ UP'_t) (exist _ _ UP'_e)).

  (* Induction Principle for Bool. *)
  Definition ind_alg_Bool
    (P : forall e : Fix (F), Universal_Property'_fold e -> Prop)
    (H : forall b, UP'_P P (blit b))
    (H0 : forall i t e
      (IHi : UP'_P P i)
      (IHt : UP'_P P t)
      (IHe : UP'_P P e),
      UP'_P P (@cond i t e (proj1_sig IHi) (proj1_sig IHt) (proj1_sig IHe)))
    (e : Bool (sig (UP'_P P)))
    :
    sig (UP'_P P) :=
    match e with
      | BLit n => exist _ (blit n) (H n)
      | If i t e => exist (UP'_P P) _
        (H0 (proj1_sig i) (proj1_sig t) (proj1_sig e) (proj2_sig i) (proj2_sig t) (proj2_sig e))
    end.

  Definition ind2_alg_Bool
    {E E' : Set -> Set}
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Bool_E : Bool :<: E}
    {Sub_Bool_E' : Bool :<: E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall b, UP'_P2 P (inject (BLit _ b), inject (BLit _ b)))
    (H0 : forall i t el
      (IHi : UP'_P2 P i)
      (IHt : UP'_P2 P t)
      (IHel : UP'_P2 P el),
      UP'_P2 P (inject (If _ (exist _ _ (proj1 (proj1_sig IHi)))
        (exist _ _ (proj1 (proj1_sig IHt))) (exist _ _(proj1 (proj1_sig IHel)))),
      inject (If _ (exist _ _ (proj2 (proj1_sig IHi)))
        (exist _ _ (proj2 (proj1_sig IHt))) (exist _ _ (proj2 (proj1_sig IHel))))))
      (e : Bool (sig (UP'_P2 P)))
        :
        sig (UP'_P2 P) :=
    match e with
      | BLit b => exist _ _ (H b)
      | If i t e => exist (UP'_P2 P) _
        (H0 (proj1_sig i) (proj1_sig t) (proj1_sig e)
          (proj2_sig i) (proj2_sig t) (proj2_sig e))
    end.

  Lemma ind_PAlg_Bool {Sub_Bool_F' : Bool :<: F}
    (eq_Sub_Bool : forall A (d : Bool A),
      inj (Sub_Functor := Sub_Bool_F) d = inj (Sub_Functor := Sub_Bool_F') d)
    (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (H : forall b, UP'_P P (blit b))
    (H0 : forall i t e
      (IHi : UP'_P P i)
      (IHt : UP'_P P t)
      (IHe : UP'_P P e),
      UP'_P P (@cond i t e (proj1_sig IHi) (proj1_sig IHt) (proj1_sig IHe)))
    :
    PAlgebra Name Bool F (sub_F_G := Sub_Bool_F') (UP'_P P).
    econstructor 1 with (p_algebra := ind_alg_Bool P H H0).
    destruct e; simpl.
    unfold blit, blit'; simpl; rewrite wf_functor; rewrite eq_Sub_Bool; reflexivity.
    unfold cond, cond'; simpl; rewrite wf_functor; rewrite eq_Sub_Bool; reflexivity.
  Qed.

  Lemma ind_P2Alg_Bool (Name : Set)
    (E E' : Set -> Set)
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Bool_E : Bool :<: E}
    {Sub_Bool_E' : Bool :<: E'}
    {WF_Fun_E : WF_Functor _ _ _ _ Fun_E}
    {WF_Fun_E' : WF_Functor _ _ _ _ Fun_E'}
    (P : forall e : (Fix E) * (Fix E'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (H : forall b, UP'_P2 P (inject (BLit _ b), inject (BLit _ b)))
    (H0 : forall i t el
      (IHi : UP'_P2 P i)
      (IHt : UP'_P2 P t)
      (IHel : UP'_P2 P el),
      UP'_P2 P (inject (If _ (exist _ _ (proj1 (proj1_sig IHi)))
        (exist _ _ (proj1 (proj1_sig IHt))) (exist _ _(proj1 (proj1_sig IHel)))),
      inject (If _ (exist _ _ (proj2 (proj1_sig IHi)))
        (exist _ _ (proj2 (proj1_sig IHt))) (exist _ _ (proj2 (proj1_sig IHel))))))
    :
    P2Algebra Name Bool E E' (UP'_P2 P).
    econstructor 1 with (p2_algebra := ind2_alg_Bool P H H0);
    destruct e; simpl; unfold inject; simpl; rewrite wf_functor; reflexivity.
  Qed.

  Definition ind_dalg_Bool
    (P : forall e : Fix (F), Universal_Property'_fold e -> Set)
    (H : forall b, UP'_SP P (blit b))
    (H0 : forall i t e
      (IHi : UP'_SP P i)
      (IHt : UP'_SP P t)
      (IHe : UP'_SP P e),
      UP'_SP P (@cond i t e (projT1 IHi) (projT1 IHt) (projT1 IHe)))
    (e : Bool (sigT (UP'_SP P)))
    :
    sigT (UP'_SP P) :=
    match e with
      | BLit n => existT _ (blit n) (H n)
      | If i t e => existT (UP'_SP P) _
        (H0 (projT1 i) (projT1 t) (projT1 e) (projT2 i) (projT2 t) (projT2 e))
    end.

  Lemma ind_DAlg_Bool
    (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Set)
    (H : forall b, UP'_SP P (blit b))
    (H0 : forall i t e
      (IHi : UP'_SP P i)
      (IHt : UP'_SP P t)
      (IHe : UP'_SP P e),
      UP'_SP P (@cond i t e (projT1 IHi) (projT1 IHt) (projT1 IHe)))
    :
    DAlgebra Name Bool F (UP'_SP P).
    econstructor 1 with (d_algebra := ind_dalg_Bool P H H0).
    destruct e; simpl.
    unfold blit, blit'; simpl; rewrite wf_functor; reflexivity.
    unfold cond, cond'; simpl; rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Boolean Expressions. *)

  Variable (MT : Set -> Set). (* The Typing Monad *)
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.

  Definition Bool_typeof (R : Set) (rec : R -> typeofR D MT)
     (e : Bool R) : typeofR D MT :=
     match e with
       | BLit n => return_ tbool'
       | If i t e => do Ti <- rec i;
                     match isTBool (proj1_sig Ti) with
                       | true => do Tt <- rec t;
                                 do Te <- rec e;
                                   match eq_DType D (proj1_sig Tt) Te with
                                     | true => return_ Tt
                                     | _ => fail
                                   end
                       | _ => fail
                     end
     end.

  Global Instance MAlgebra_typeof_Bool T :
    FAlgebra TypeofName T (typeofR D MT ) Bool :=
    {| f_algebra := Bool_typeof T|}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Boolmetic Values. *)
   Inductive BoolValue (A : Set) : Set :=
   | VB : bool -> BoolValue A.

   Definition VB_fmap : forall (A B : Set) (f : A -> B),
     BoolValue A -> BoolValue B :=
     fun A B _ e => match e with
                      | VB n => VB _ n
                    end.

   Global Instance VB_Functor : Functor BoolValue :=
     {| fmap := VB_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.
   Context {Sub_BoolValue_V : BoolValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_BoolValue_F : WF_Functor _ _ Sub_BoolValue_V _ _}.

  Definition vb' (b : bool) : Value := inject' (VB _ b).
  Definition vb (b : bool) : Fix V := proj1_sig (vb' b).

  Global Instance UP'_vb {b : bool} :
    Universal_Property'_fold (vb b) := proj2_sig (vb' b).

  (* Constructor Testing for Boolmetic Values. *)

  Definition isVB : Fix V -> option bool :=
    fun exp =>
      match project exp with
       | Some (VB b) => Some b
       | None        => None
      end.

   Lemma project_vb_vb : forall b,
     project (F := V) (G := BoolValue) (vb b) = Some (VB _ b).
   Proof.
     intros; unfold project, vb, inject; simpl; rewrite out_in_fmap.
     repeat rewrite wf_functor; simpl; unfold VB_fmap.
     rewrite prj_inj; reflexivity.
   Qed.

   Lemma project_vb'_vb : forall b,
     project (F := V) (G := BoolValue) (proj1_sig (vb' b)) = Some (VB _ b).
   Proof.
     intros; unfold project, vb', inject; simpl; rewrite out_in_fmap.
     repeat rewrite wf_functor; simpl; unfold VB_fmap.
     rewrite prj_inj; reflexivity.
   Qed.

  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Definition stuck' : nat -> Value := stuck' _.
  Definition stuck : nat -> Fix V := stuck _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Context {Sub_BotValue_V : BotValue :<: V}.

  (* Evaluation Algebra for Boolemetic Expressions. *)

  Definition Bool_eval (R : Set) (rec : R -> evalR V)
    (e : Bool R) : evalR V :=
      match e with
        | BLit b => (fun _ => vb' b)
        | If i t e => (fun env =>
          let i' := (rec i env) in
            match (isVB (proj1_sig i')) with
              | Some true => rec t env
              | Some false => rec e env
              | None => if (@isBot _ Fun_V Sub_BotValue_V (proj1_sig i'))
                         then bot' V
                         else stuck' 5
            end)
      end.

  Global Instance MAlgebra_eval_Bool T :
    FAlgebra EvalName T (evalR V) Bool :=
    {| f_algebra := Bool_eval T |}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_M : Functor ME}.
  Context {Mon_M : Monad ME}.
  Context {Fail_M : FailMonad ME}.

  Definition Bool_evalM (R : Set) (rec : R -> evalMR V ME)
     (e : Bool R) : evalMR V ME :=
       match e with
         | BLit b => return_ (vb' b)
         | If i t e => do i' <- rec i;
                         match (isVB (proj1_sig i')) with
                           | Some true => rec t
                           | Some false => rec e
                           | _ => return_ (stuck' 5)
                         end
       end.

  Global Instance MAlgebra_evalM_Bool T :
    FAlgebra EvalName T (evalMR V ME) Bool :=
    {| f_algebra := Bool_evalM T |}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.

  Global Instance MAlgebra_DTypePrint_BType T:
    FAlgebra DTypePrintName T DTypePrintR BType :=
    {| f_algebra := fun rec e => append "tbool" "" |}.

  Global Instance MAlgebra_ExpPrint_Bool T :
    FAlgebra ExpPrintName T (ExpPrintR) Bool :=
    {| f_algebra := fun rec e =>
      match e with
        | BLit true => fun i => append "true" ""
        | BLit false => fun i => append "false" ""
        | If i t e => fun i' => append "(if (" ((rec i i') ++ ") then (" ++ (rec t i') ++ ") else ("++ (rec e i')++"))")
    end |}.

  Global Instance MAlgebra_ValuePrint_BType T :
    FAlgebra ValuePrintName T ValuePrintR BoolValue :=
    {| f_algebra := fun rec e =>
      match e with
        | VB true => append "true" ""
        | VB false => append "false" ""
      end |}.

  Context {eval_F : FAlgebra EvalName Exp (evalR V) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Bool) (F)
    (Sub_Bool_F) (MAlgebra_eval_Bool (Exp)) eval_F}.

  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
  Context {Dis_VB_Bot : Distinct_Sub_Functor _ Sub_BoolValue_V Sub_BotValue_V}.


  (* ============================================== *)
  (* WELL-FORMED BOOLEAN VALUES                     *)
  (* ============================================== *)

  Variable TypContext : Set.

  Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
  Variable funWFV : iFunctor WFV.

  (** Natural Number Values are well-formed **)

  Inductive WFValue_VB (WFV : WFValue_i D V TypContext -> Prop) : WFValue_i D V TypContext -> Prop :=
  | WFV_VB : forall Sigma n (v : Names.Value V) T,
    proj1_sig v = vb n ->
    proj1_sig T = tbool ->
    WFValue_VB WFV (mk_WFValue_i D V _ Sigma v T).

  Definition ind_alg_WFV_VB (P : WFValue_i D V TypContext -> Prop)
    (H : forall Sigma n v T veq Teq, P (mk_WFValue_i _ _ _ Sigma v T))
    i (e : WFValue_VB P i) : P i :=
    match e in WFValue_VB _ i return P i with
      | WFV_VB Sigma n v T veq Teq => H Sigma n v T veq Teq
    end.

  Definition WFV_VB_ifmap (A B : WFValue_i D V _ -> Prop) i (f : forall i, A i -> B i)
    (WFV_a : WFValue_VB A i) : WFValue_VB B i :=
    match WFV_a in (WFValue_VB _ s) return (WFValue_VB B s)
      with
      | WFV_VB Sigma n v T veq Teq => WFV_VB B Sigma n v T veq Teq
    end.

  Global Instance iFun_WFV_VB : iFunctor WFValue_VB.
    constructor 1 with (ifmap := WFV_VB_ifmap).
    destruct a; simpl; intros; reflexivity.
    destruct a; simpl; intros; reflexivity.
  Defined.

  Variable Sub_WFV_VB_WFV : Sub_iFunctor WFValue_VB WFV.

   Global Instance WFV_proj1_a_VB :
     iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFValue_VB.
     econstructor; intros.
     unfold iAlgebra; intros; unfold WFV_proj1_a_P.
     inversion H; subst; simpl; intros.
     apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; simpl; eauto.
     rewrite H3; eauto.
   Defined.

   Global Instance WFV_proj1_b_VB :
     iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFValue_VB.
     econstructor; intros.
     unfold iAlgebra; intros; unfold WFV_proj1_b_P.
     inversion H; subst; simpl; intros.
     apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; simpl; eauto.
     rewrite H3; eauto.
   Defined.

  (* Inversion principles for Well-formed Booleans. *)
  Definition WF_invertVB_P (i : WFValue_i D V _) :=
    proj1_sig (wfv_T _ _ _ i) = tbool -> WFValue_VB (iFix WFV) i.

  Inductive WF_invertVB_Name := wfv_invertvb_name.
  Context {WF_invertVB_WFV :
    iPAlgebra WF_invertVB_Name WF_invertVB_P WFV}.

  Global Instance WF_invertVB_VB :
    iPAlgebra WF_invertVB_Name WF_invertVB_P WFValue_VB.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertVB_P.
    inversion H; subst; simpl; intros.
    econstructor; eassumption.
  Defined.

  Ltac WF_invertVB_default :=
    constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
      inversion H; simpl;
        match goal with
          eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
            intro eq_H; rewrite eq_H in eq_H0;
              elimtype False; eapply (inject_discriminate _ _ _ eq_H0)
        end.

  Definition WF_invertVB := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertVB_WFV)).

  Context {TypContextCE : ConsExtensionC TypContext}.

  Global Instance WFV_Weaken_VB :
    iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFValue_VB.
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
    Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
    Context {eq_DType_neq_DT : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
    Context {funWFVM : iFunctor WFVM}.

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) F}.
    Context {WF_Typeof_F : forall T, @WF_FAlgebra TypeofName _ _ Bool F
      Sub_Bool_F (MAlgebra_typeof_Bool _) (Typeof_F T)}.

    Context {evalM_F' : forall T, FAlgebra EvalName T (evalMR V ME) F}.
    Context {WF_evalM_F' : forall T, @WF_FAlgebra EvalName _ _ Bool F
      Sub_Bool_F (MAlgebra_evalM_Bool _) (evalM_F' T)}.

    Context {Sub_WFVM_base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.

    Ltac WF_FAlg_rewrite := repeat rewrite wf_functor; simpl;
      repeat rewrite out_in_fmap; simpl;
        repeat rewrite wf_functor; simpl;
          repeat rewrite wf_algebra; simpl.

    Lemma Bool_eval_Soundness_H : forall b : bool,
      UP'_SP (eval_soundness_P D V F MT ME _ WFVM) (blit b).
    Proof.
      intros; econstructor.
      unfold eval_soundness_P; intros; simpl.
      unfold typeof, evalM, mfold, blit; simpl; unfold in_t; simpl.
      WF_FAlg_rewrite.
      apply (inject_i (subGF := Sub_WFVM_base_WFVM)); econstructor 1 with (T := tbool').
      apply inject_i; econstructor; unfold vb; simpl; auto.
      apply return_orn; auto.
    Defined.

    Lemma project_tbool_tbool : project (F := D) (G := BType) tbool = Some (TBool _).
    Proof.
      intros; unfold project, tbool, inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; rewrite prj_inj; reflexivity.
    Qed.

    Lemma project_tbool'_tbool : project (F := D) (G := BType) (proj1_sig tbool') = Some (TBool _).
    Proof.
      intros; unfold project, tbool', inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; rewrite prj_inj; reflexivity.
    Qed.

    Context {wfvm_bind_alg :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.

    Lemma Bool_eval_soundness'_H0
     (typeof_R eval_R : Set) typeof_rec eval_rec :
     forall (iT tT eT : typeof_R) (iE tE eE : eval_R)
       Sigma
       (IHi :  WFValueMC D V MT ME _ WFVM Sigma
         (eval_rec iE) (typeof_rec iT))
       (IHt : forall Sigma', ConsExtension Sigma' Sigma ->
         WFValueMC D V MT ME _ WFVM Sigma'
         (eval_rec tE) (typeof_rec tT))
       (IHe : forall Sigma', ConsExtension Sigma' Sigma ->
         WFValueMC D V MT ME _ WFVM Sigma'
         (eval_rec eE) (typeof_rec eT)),
       WFValueMC D V MT ME _ WFVM Sigma
         (Bool_evalM _ eval_rec (If _ iE tE eE))
         (Bool_typeof _ typeof_rec (If _ iT tT eT)).
    Proof.
      simpl; intros.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros; rewrite H; reflexivity.
      intros.
      caseEq (project (proj1_sig T)); rename H1 into T_eq.
      destruct b.
      apply project_inject in T_eq; auto with typeclass_instances; try exact (proj2_sig _).
      generalize (WF_invertVB _ H0 T_eq) as WF_v_T; intros;
        inversion WF_v_T; subst; rewrite H5.
      unfold isTBool; rewrite project_tbool_tbool.
      unfold isVB; rewrite H3, project_vb_vb.
      destruct n.
      rewrite right_unit at 1.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros; unfold eq_DType; rewrite H1.
      repeat rewrite fmap_m.
      repeat rewrite <- associativity.
      f_equal; apply functional_extensionality; intro Te.
      destruct (mfold (eq_DTypeR D) (fun R : Set => f_algebra) (proj1_sig T') Te).
      repeat rewrite <- left_unit; rewrite H1; reflexivity.
      repeat rewrite bind_fail; reflexivity.
      intros.
      apply wfvm_skip with (WFV := WFV) (Fail_MT := Fail_MT) (Monad_ME := Mon_M); auto.
      intro Te.
      caseEq (eq_DType D (proj1_sig T0) Te).
      apply (inject_i (subGF := Sub_WFVM_base_WFVM)).
      constructor 1 with (T := T0); auto.
      apply return_orn; eauto.
      apply wfvm_fail with (WFV := WFV) (Monad_ME := Mon_M); auto.
      apply wfvm_skip with (WFV := WFV) (Fail_MT := Fail_MT) (Monad_ME := Mon_M); auto.
      intro Tt.
      rewrite right_unit at 1.
      apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
      intros.
      caseEq (eq_DType D (proj1_sig Tt) T0);
        caseEq (eq_DType D (proj1_sig Tt) T');
        try reflexivity.
      apply eq_DType_eq in H2; apply eq_DType_neq in H4; auto with typeclass_instances; congruence.
      apply eq_DType_neq in H2; apply eq_DType_eq in H4; auto with typeclass_instances; congruence.
      intros.
      caseEq (eq_DType D (proj1_sig Tt) T0).
      apply eq_DType_eq in H4; auto.
      apply (inject_i (subGF := Sub_WFVM_base_WFVM)).
      constructor 1 with (T := T0); auto.
      apply return_orn; eauto.
      apply wfvm_fail with (WFV := WFV) (Monad_ME := Mon_M); auto.
      unfold isTBool.
      rewrite T_eq.
      apply wfvm_fail with (WFV := WFV) (Monad_ME := Mon_M); auto.
    Qed.

  Context {evalM_F : FAlgebra EvalName Exp (evalMR V ME) F}.
  Context {WF_eval_F' : @WF_FAlgebra EvalName _ _ Bool F
    Sub_Bool_F (MAlgebra_evalM_Bool _) evalM_F}.

    Section PSoundness.

      Variable P_bind : Set.
      Variable E' : Set -> Set.
      Context {Fun_E' : Functor E'}.
      Context {Sub_Bool_E' : Bool :<: E'}.

      Variable P : UP'_F F -> UP'_F E' -> P_bind -> TypContext -> Prop.

      Variable If_Decompi :
        forall i1 i2 e1 e2 t1 t2 i1_UP' i2_UP' i1_UP'' i2_UP'' if1_UP' if2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ (exist Universal_Property'_fold i2 i2_UP') t2 e2)))) if2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ (exist Universal_Property'_fold i1 i1_UP') t1 e1)))) if1_UP')
          pb Sigma ->
          P (exist _ i2 i2_UP'') (exist _ i1 i1_UP'') pb Sigma.

      Variable If_Decompt :
        forall i1 i2 e1 e2 t1 t2 t1_UP' t2_UP' t1_UP'' t2_UP'' if1_UP' if2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ i2 (exist Universal_Property'_fold t2 t2_UP') e2)))) if2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ i1 (exist Universal_Property'_fold t1 t1_UP') e1)))) if1_UP')
          pb Sigma ->
          P (exist _ t2 t2_UP'') (exist _ t1 t1_UP'') pb Sigma.

      Variable If_Decompe :
        forall i1 i2 e1 e2 t1 t2 e1_UP' e2_UP' e1_UP'' e2_UP'' if1_UP' if2_UP' pb Sigma,
          P (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ i2 t2 (exist Universal_Property'_fold e2 e2_UP'))))) if2_UP')
          (exist Universal_Property'_fold
            (in_t (fmap (@proj1_sig _ _) (inj (If _ i1 t1 (exist Universal_Property'_fold e1 e1_UP'))))) if1_UP')
          pb Sigma ->
          P (exist _ e2 e2_UP'') (exist _ e1 e1_UP'') pb Sigma.

    Global Instance Bool_eval_soundness'
      (P_Sub : forall e e' pb Sigma Sigma',
        P e e' pb Sigma -> ConsExtension Sigma' Sigma ->
        P e e' pb Sigma')
      {WF_Fun_E' : WF_Functor _ _ Sub_Bool_E' _ _}
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D MT) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_Bool_E' (MAlgebra_typeof_Bool T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalMR V ME)
      (typeof_rec : UP'_F E' -> typeofR D MT)
      :
      P2Algebra ES'_ExpName Bool E' F
      (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
        _ _ _ P pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := evalM_F)))).
    Proof.
      apply ind_P2Alg_Bool; eauto.
      (* blit case *)
      unfold eval_soundness'_P, UP'_P2; simpl; intros;
        constructor 1 with (x := conj (proj2_sig (inject' (BLit _ b))) (proj2_sig (inject' (BLit _ b)))).
      unfold inject; simpl; repeat rewrite out_in_fmap;
        repeat rewrite wf_functor; intros.
      WF_FAlg_rewrite.
      apply (inject_i (subGF := Sub_WFVM_base_WFVM));
        constructor 1 with (T := tbool').
      apply inject_i; econstructor; unfold vb; simpl; eauto.
      apply return_orn; eauto.
      (* if case *)
      destruct i as [iE iT]; destruct t as [tE tT]; destruct el as [eE eT];
          destruct IHi as [[UP'_iE UP'_iT] IHi];
            destruct IHt as [[UP'_tE UP'_tT] IHt];
              destruct IHel as [[UP'_eE UP'_eT] IHe];
                simpl in *|-*.
      unfold eval_soundness'_P, UP'_P2; intros.
      assert (Universal_Property'_fold
        (fst
          (inject
            (If (sig Universal_Property'_fold)
              (exist Universal_Property'_fold iE (proj1 (conj UP'_iE UP'_iT)))
              (exist Universal_Property'_fold tE (proj1 (conj UP'_tE UP'_tT)))
              (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT)))),
            inject
            (If (sig Universal_Property'_fold)
              (exist Universal_Property'_fold iT (proj2 (conj UP'_iE UP'_iT)))
              (exist Universal_Property'_fold tT (proj2 (conj UP'_tE UP'_tT)))
              (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT)))))) /\
        Universal_Property'_fold
        (snd
          (inject
            (If (sig Universal_Property'_fold)
              (exist Universal_Property'_fold iE (proj1 (conj UP'_iE UP'_iT)))
              (exist Universal_Property'_fold tE (proj1 (conj UP'_tE UP'_tT)))
              (exist Universal_Property'_fold eE (proj1 (conj UP'_eE UP'_eT)))),
            inject
            (If (sig Universal_Property'_fold)
              (exist Universal_Property'_fold iT (proj2 (conj UP'_iE UP'_iT)))
              (exist Universal_Property'_fold tT (proj2 (conj UP'_tE UP'_tT)))
              (exist Universal_Property'_fold eT (proj2 (conj UP'_eE UP'_eT))))))) as If_UP'
      by (simpl; split; unfold inject; exact (proj2_sig _)).
      constructor 1 with (x := If_UP'); simpl.
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj Sigma WF_Sigma IHa.
      repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F'));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Bool_fmap.
      intros; apply Bool_eval_soundness'_H0.
      intros; generalize (IHa _ _ (exist _ _ UP'_iE, exist _ _ UP'_iT)
        (If_Decompi _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma)); simpl.
      rewrite typeof_rec_proj; simpl; intros H'; apply H'.
      apply IHi; auto.
      eapply (If_Decompi _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma).
      intros Sigma' ConsExt_Sig'_Sig;
        generalize (IHa _ _ (exist _ _ UP'_tE, exist _ _ UP'_tT)
          (If_Decompt _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig))); simpl.
      rewrite typeof_rec_proj; simpl; intros H'; apply H'.
      apply IHt; auto.
      eapply P_Sub; try eassumption.
      eapply (If_Decompt _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma).
      intros Sigma' ConsExt_Sig'_Sig;
        generalize (IHa _ _ (exist _ _ UP'_eE, exist _ _ UP'_eT)
          (If_Decompe _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (P_Sub _ _ _ _ _ WF_Sigma ConsExt_Sig'_Sig))); simpl.
      rewrite typeof_rec_proj; simpl; intros H'; apply H'.
      apply IHe; auto.
      eapply P_Sub; try eassumption.
      eapply (If_Decompe _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF_Sigma).
    Defined.

  End PSoundness.

  Global Instance Bool_eval_soundness'' typeof_rec eval_rec :
    P2Algebra ES'_ExpName Bool F F
    (UP'_P2 (eval_soundness'_P D V F MT ME _ WFVM
      _ _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
      (f_algebra (FAlgebra := Typeof_F _)) (f_algebra (FAlgebra := evalM_F)))).
  Proof.
    eapply Bool_eval_soundness'; eauto.
  Defined.

End Bool.

    Ltac WF_invertVB_default :=
      constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
        inversion H; simpl;
          match goal with
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; eapply (inject_discriminate _ _ _ eq_H0)
          end.

  Hint Extern 5 (iPAlgebra WF_invertVB_Name (WF_invertVB_P _ _ _ _) _) =>
    constructor; unfold iAlgebra; let H := fresh in
      intros i H; unfold WF_invertVB_P;
        inversion H; simpl;
          match goal with
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
                  apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)];
                fail
          end : typeclass_instances.

(* Hint Extern 0 =>
  intros; match goal with
            |- (PAlgebra eval_Soundness_alg_Name
              (sig (UP'_P2 (eval_alg_Soundness_P _ _ _ _ _ _ _ _ _ _ _ _ _ _))) Bool) =>
            eapply Bool_eval_Soundness_alg; eauto with typeclass_instances
          end : typeclass_instances. *)

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
