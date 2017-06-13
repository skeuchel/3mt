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

Section Lambda.
  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* Function Types. *)
  Inductive LType (A : Set) : Set :=
    TArrow : A -> A -> LType A.

  Definition LType_fmap : forall (A B : Set) (f : A -> B),
    LType A -> LType B :=
    fun A B f e =>
      match e with
        | TArrow t1 t2 => TArrow _ (f t1) (f t2)
      end.

  Global Instance LType_Functor : Functor LType :=
    {| fmap := LType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Sub_LType_D  : LType :<: D}.
  Context {Fun_D : Functor D}.
  Let DType := DType D.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D _ _}.

  Definition tarrow' (t1 t2 : DType) := inject' (TArrow _ t1 t2).
  Definition tarrow (t1 t2 : Fix D)
    {UP'_t1 : Universal_Property'_fold t1}
    {UP'_t2 : Universal_Property'_fold t2}
    : Fix D := proj1_sig (tarrow' (exist _ t1 UP'_t1) (exist _ t2 UP'_t2)).

   Global Instance UP'_tarrow (t1 t2 : Fix D)
     {UP'_t1 : Universal_Property'_fold t1}
     {UP'_t2 : Universal_Property'_fold t2}
     : Universal_Property'_fold (tarrow t1 t2) :=
     proj2_sig (tarrow' (exist _ t1 UP'_t1) (exist _ t2 UP'_t2)).

  (* Induction Principle for Arrow Types. *)
  Definition ind_alg_LType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop)
    (H : forall t1 t2
      (IHt1 : UP'_P P t1)
      (IHt2 : UP'_P P t2),
      UP'_P P (@tarrow _ _ (proj1_sig IHt1) (proj1_sig IHt2)))
    (d : LType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TArrow t1 t2 => exist _ _ (H (proj1_sig t1) (proj1_sig t2) (proj2_sig t1) (proj2_sig t2))
    end.

    Lemma ind_PAlg_LType
    {Sub_LType_D' : LType :<: D}
    (eq_Sub_LType : forall A (d : LType A),
      inj (Sub_Functor := Sub_LType_D) d = inj (Sub_Functor := Sub_LType_D') d)
    (Name : Set)
    (P : forall e : Fix D, Universal_Property'_fold e -> Prop)
    (H : forall t1 t2 (IHt1 : UP'_P P t1) (IHt2 : UP'_P P t2),
      UP'_P P (@tarrow _ _ (proj1_sig IHt1) (proj1_sig IHt2)))
    :
    PAlgebra (sub_F_G := Sub_LType_D') Name LType D (UP'_P P).
    Proof.
      econstructor 1 with (p_algebra := ind_alg_LType P H).
      destruct e; simpl; unfold tarrow, tarrow'; simpl;
        rewrite wf_functor; simpl; rewrite eq_Sub_LType; eauto.
    Qed.

  (* Algebra for testing type equality. *)

  Definition isTArrow : DType -> option (_ * _) :=
    fun typ =>
      match project (proj1_sig typ) with
       | Some (TArrow t1 t2)  => Some (t1, t2)
       | None                 => None
      end.

  Definition LType_eq_DType (R : Set) (rec : R -> eq_DTypeR D)
    (e : LType R) : eq_DTypeR D :=
    match e with
    | TArrow t1 t2 => fun t' =>
        match isTArrow t' with
        | Some (t1', t2') => andb (rec t1 t1') (rec t2 t2')
        | None            => false
        end
    end.

  Global Instance MAlgebra_eq_DType_TArrow T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) LType :=
      {| f_algebra := LType_eq_DType T|}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_LType_D (MAlgebra_eq_DType_TArrow T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_TArrow_eq_LType
    {Sub_LType_D' : LType :<: D}
    (eq_Sub_LType : forall A (d : LType A),
      inj (Sub_Functor := Sub_LType_D) d = inj (Sub_Functor := Sub_LType_D') d):
    PAlgebra eq_DType_eqName LType D (sub_F_G := Sub_LType_D') (UP'_P (eq_DType_eq_P D)).
  Proof.
    eapply ind_PAlg_LType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tarrow, tarrow', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTArrow in H.
    caseEq (project (subGF := Sub_LType_D) (proj1_sig d2)); rewrite H0 in H; try discriminate.
    destruct IHt1 as [t1_UP' IHt1].
    destruct IHt2 as [t2_UP' IHt2].
    unfold eq_DType_eq_P in IHt1, IHt2.
    destruct l.
    apply project_inject in H0.
    rewrite H0.
    unfold tarrow, tarrow', inject; simpl;
      repeat rewrite wf_functor; simpl.
    caseEq (mfold (eq_DTypeR D) (fun R : Set => f_algebra) t1 s);
    rewrite H1 in H; simpl in H; try discriminate.
    unfold eq_DType in IHt1, IHt2; rewrite (IHt1 _ H1), (IHt2 _ H); auto.
    auto with typeclass_instances.
    exact (proj2_sig _).
  Qed.

  Global Instance PAlgebra_eq_TArrow_neq_LType
    {Sub_LType_D' : LType :<: D}
    (eq_Sub_LType : forall A (d : LType A),
      inj (Sub_Functor := Sub_LType_D) d = inj (Sub_Functor := Sub_LType_D') d):
    PAlgebra eq_DType_neqName LType D (sub_F_G := Sub_LType_D') (UP'_P (eq_DType_neq_P D)).
  Proof.
    eapply ind_PAlg_LType; eauto.
    unfold UP'_P; econstructor.
    unfold eq_DType_neq_P; intros.
    unfold eq_DType, mfold, tarrow, tarrow', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H.
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTArrow in H.
    caseEq (project (subGF := Sub_LType_D) (proj1_sig d2)); rewrite H0 in H; try discriminate.
    destruct IHt1 as [t1_UP' IHt1].
    destruct IHt2 as [t2_UP' IHt2].
    unfold eq_DType_neq_P in IHt1, IHt2.
    destruct l.
    apply project_inject in H0.
    rewrite H0.
    unfold tarrow, tarrow', inject; simpl;
      repeat rewrite wf_functor; simpl.
    unfold eq_DType in IHt1, IHt2; caseEq (mfold (eq_DTypeR D) (fun R : Set => f_algebra) t1 s);
    rewrite H1 in H; simpl in H; try discriminate.
    unfold not; intros; eapply (IHt2 _ H).
    generalize (in_t_UP'_inject _ _ (inj (Sub_Functor := Sub_LType_D)
      (TArrow _ (exist _ _ t1_UP') (exist _ _ t2_UP'))) (inj (Sub_Functor := Sub_LType_D) (TArrow _ s s0)));
    repeat rewrite wf_functor; simpl; intros H3; apply H3 in H2.
    apply (f_equal (prj (Sub_Functor := Sub_LType_D))) in H2;
      repeat rewrite prj_inj in H2; injection H2; auto.
    unfold not; intros; eapply (IHt1 _ H1).
    generalize (in_t_UP'_inject _ _
      (inj (Sub_Functor := Sub_LType_D) (TArrow _ (exist _ _ t1_UP') (exist _ _ t2_UP')))
      (inj (Sub_Functor := Sub_LType_D) (TArrow _ s s0))); repeat rewrite wf_functor;
    simpl; intros H3; apply H3 in H2.
    apply (f_equal (prj (Sub_Functor := Sub_LType_D))) in H2;
      repeat rewrite prj_inj in H2; injection H2; auto.
    auto with typeclass_instances.
    exact (proj2_sig _).
    unfold not; intros; rewrite <- H1 in H0.
    unfold project, tarrow, inject in H0; simpl in H0.
    rewrite out_in_fmap in H0; repeat rewrite wf_functor in H0;
      simpl in H0; rewrite prj_inj in H0; discriminate.
  Qed.

  (* End type equality section. *)


  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Lambda Expressions *)
  Inductive Lambda (A E : Set) : Set :=
  | Var : A -> Lambda A E
  | App : E -> E -> Lambda A E
  | Lam : DType -> (A -> E) -> Lambda A E.

  (** Functor Instance **)

  Definition fmapLambda {A} : forall (X Y: Set), (X -> Y) -> (Lambda A X -> Lambda A Y):=
    fun _ _ f e =>
      match e with
       | Var a      => Var _ _ a
       | App e1 e2  => App _ _ (f e1) (f e2)
       | Lam t g    => Lam _ _ t (fun a => f (g a))
      end.

  Global Instance LambdaFunctor A : Functor (Lambda A) :=
  {| fmap := fmapLambda
   |}.
  (* fmap fusion *)
  intros. destruct a; unfold fmapLambda; reflexivity.
  (* fmap id *)
  intros; destruct a; unfold fmapLambda.
     reflexivity. reflexivity. unfold id. unfold id.
     assert ((fun x => a x) = a).
       apply functional_extensionality; intro. reflexivity.
    rewrite H. reflexivity.
  Defined.

  Variable F : Set -> Set -> Set.
  Context {Sub_Lambda_F : forall A : Set, Lambda A :<: F A}.
  Context {Fun_F : forall A, Functor (F A)}.
  Definition Exp (A : Set) := Exp (F A).

  (* Constructors + Universal Property. *)

  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_F A) _ _}.

  Definition var' {A : Set} (a : A) : Exp A := inject' (Var _ _ a).
  Definition var {A : Set} (a : A) : Fix (F A) := proj1_sig (var' a).
  Global Instance UP'_var {A : Set} (a : A) :
    Universal_Property'_fold (var a) := proj2_sig (var' a).

  Definition app' {A : Set} (e1 e2 : Exp A) :=
    inject' (App _ _ e1 e2).
  Definition app {A : Set}
    (e1 e2 : Fix (F A))
    {e1_UP' : Universal_Property'_fold e1}
    {e2_UP' : Universal_Property'_fold e2}
    :
    Fix (F A) := proj1_sig (app' (exist _ _ e1_UP') (exist _ _ e2_UP')).

  Global Instance UP'_app {A : Set} (e1 e2 : Fix (F A))
    {e1_UP' : Universal_Property'_fold e1}
    {e2_UP' : Universal_Property'_fold e2}
    :
    Universal_Property'_fold (app e1 e2) :=
    proj2_sig (app' (exist _ _ e1_UP') (exist _ _ e2_UP')).

  Definition lam' {A : Set}
    (t1 : DType)
    (f : A -> sig (Universal_Property'_fold (F := F A)))
    :
    Exp A := inject' (Lam _ _ t1 f).
  Definition lam {A : Set}
    (t1 : DType)
    (f : A -> Fix (F A))
    {f_UP' : forall a, Universal_Property'_fold (f a)}
    :
    Fix (F A) := proj1_sig (lam' t1 (fun a => exist _ _ (f_UP' a))).

   Global Instance UP'_lam {A : Set}
     (t1 : DType)
     (f : A -> Fix (F A))
     {f_UP' : forall a, Universal_Property'_fold (f a)}
     :
     Universal_Property'_fold (lam t1 f) := proj2_sig (lam' t1 (fun a => exist _ _ (f_UP' a))).

  (* Induction Principle for Lambda. *)
  Definition ind_alg_Lambda {A : Set}
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop)
    (H : forall x, UP'_P P (var x))
    (H0 : forall e1 e2
      (IHe1 : UP'_P P e1)
      (IHe2 : UP'_P P e2),
      UP'_P P (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)))
    (H1 : forall t1 f
      (IHf : forall a, UP'_P P (f a)),
      UP'_P P (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))))
    (e : Lambda A (sig (UP'_P P))) : sig (UP'_P P) :=
    match e with
      | Var x => exist _ _ (H x)
      | App e1 e2 =>
        exist _ _ (H0 (proj1_sig e1) (proj1_sig e2) (proj2_sig e1) (proj2_sig e2))
      | Lam t1 f => exist _ _ (H1 t1 (fun a => proj1_sig (f a)) (fun a => proj2_sig (f a)))
    end.

  Lemma ind_PAlg_Lambda {A : Set} (Name : Set)
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop)
    (H : forall x, UP'_P P (var x))
    (H0 : forall e1 e2
      (IHe1 : UP'_P P e1)
      (IHe2 : UP'_P P e2),
      UP'_P P (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)))
    (H1 : forall t1 f
      (IHf : forall a, UP'_P P (f a)),
      UP'_P P (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))))
    :
    PAlgebra Name (Lambda A) (F A) (UP'_P P).
  Proof.
    econstructor 1 with (p_algebra := ind_alg_Lambda P H H0 H1).
    destruct e; simpl.
    unfold var, var'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold app, app'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold lam, lam'; simpl; intros; rewrite wf_functor; reflexivity.
  Qed.

  Definition indD_alg_Lambda {A : Set}
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop)
    (H : forall x, UP'_SP P (var x))
    (H0 : forall e1 e2
      (IHe1 : UP'_SP P e1)
      (IHe2 : UP'_SP P e2),
      UP'_SP P (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)))
    (H1 : forall t1 f
      (IHf : forall a, UP'_SP P (f a)),
      UP'_SP P (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))))
    (e : Lambda A (sigT (UP'_SP P))) : sigT (UP'_SP P) :=
    match e with
      | Var x => existT _ _ (H x)
      | App e1 e2 =>
        existT _ _ (H0 (projT1 e1) (projT1 e2) (projT2 e1) (projT2 e2))
      | Lam t1 f => existT _ _ (H1 t1 (fun a => projT1 (f a)) (fun a => projT2 (f a)))
    end.

  Lemma ind_DAlg_Lambda {A : Set} (Name : Set)
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop)
    (H : forall x, UP'_SP P (var x))
    (H0 : forall e1 e2
      (IHe1 : UP'_SP P e1)
      (IHe2 : UP'_SP P e2),
      UP'_SP P (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)))
    (H1 : forall t1 f
      (IHf : forall a, UP'_SP P (f a)),
      UP'_SP P (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))))
    :
    DAlgebra Name (Lambda A) (F A) (UP'_SP P).
  Proof.
    econstructor 1 with (d_algebra := indD_alg_Lambda P H H0 H1).
    destruct e; simpl.
    unfold var, var'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold app, app'; simpl; intros; rewrite wf_functor; reflexivity.
    unfold lam, lam'; simpl; intros; rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing for Lambda Expressions. *)

  Variable MT : Set -> Set.
  Context {Fun_MT : Functor MT}.
  Context {Mon_MT : Monad MT}.
  Context {Fail_MT : FailMonad MT}.
  Context {Inj_MT : InjMonad MT}.
  Context {Reasonable_MT : Reasonable_Monad MT}.
  Context {MT_eq_dec : forall (A : Set) (mta : MT A),
    {exists a, mta = return_ a} + {mta = fail}}.


  Definition Lambda_typeof (R : Set) (rec : R -> typeofR D MT) (e : Lambda DType R) : typeofR D MT:=
  match e with
    | Var v => return_ v
    | App e1 e2 =>
      do t1 <- rec e1 ;
      do t3 <- rec e2 ;
      match (isTArrow t1) with
        | Some (t1, t2) =>
          if (eq_DType (eq_DType_DT := eq_DType_DT) D (proj1_sig t1) t3) then return_ t2 else fail
        | _ => fail
      end
    | Lam t1 f =>
      do t2 <- rec (f t1) ;
      return_ (inject' (TArrow _ t1 t2))
  end.

  Global Instance MAlgebra_typeof_Lambda T:
    FAlgebra TypeofName T (typeofR D MT) (Lambda DType) :=
    {| f_algebra := Lambda_typeof T|}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Function Values. *)

  Inductive ClosValue (A : Set) : Set :=
  | Clos : Exp nat -> Env A -> ClosValue A.

  Definition Clos_fmap : forall (A B : Set) (f : A -> B),
    ClosValue A -> ClosValue B := fun A B f e =>
      match e with
        | Clos f' env => Clos _ f' (map f env)
      end.

   Global Instance Clos_Functor : Functor ClosValue :=
     {| fmap := Clos_fmap |}.
     destruct a; simpl.
     assert (map g (map f e0) = map (fun e1 : A => g (f e1)) e0) as eq_map by
       (clear; induction e0; simpl; eauto; erewrite IHe0; reflexivity).
     rewrite eq_map; reflexivity.
     (* fmap_id *)
     destruct a. unfold Clos_fmap. rewrite map_id. reflexivity.
   Defined.

  Variable V : Set -> Set.
  Context {Sub_ClosValue_V : ClosValue :<: V}.
  Context {Fun_V : Functor V}.
  Definition Value := Value V.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_ClosValue_V : WF_Functor _ _ (Sub_ClosValue_V) _ _}.

  Definition closure' f env : Value := inject' (Clos _ f env).
  Definition closure
    (f : Fix (F nat))
    {f_UP' : Universal_Property'_fold f}
    (env : Env (sig (Universal_Property'_fold (F := V))))
      :
      Fix V := proj1_sig (closure' (exist _ _ f_UP') env).

  Global Instance UP'_closure
    (f : Fix (F nat))
    {f_UP' : Universal_Property'_fold f}
    (env : Env (sig (Universal_Property'_fold (F := V))))
     :
     Universal_Property'_fold (closure f env) :=
     proj2_sig (closure' (exist _ _ f_UP') env).

  (* Constructor Testing for Function Values. *)

  Definition isClos : Fix V -> option _ :=
    fun exp =>
     match project exp with
      | Some (Clos f env)  => Some (f, env)
      | None             => None
     end.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Context {Sub_BotValue_V : BotValue :<: V}.
   Definition bot' : Value := bot' _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Definition Lambda_eval : Mixin (Exp nat) (Lambda nat) (evalR V) :=
    fun rec e =>
     match e with
       | Var v => fun env =>
         match lookup env v with
           | Some y => y
           | None => stuck' 20
         end
       | App e1 e2 => fun env =>
         let reced := (rec e1 env) in
           match isClos (proj1_sig reced) with
             | Some (f, env') => rec f (insert _ (rec e2 env) env')
             | None => if isBot _ (proj1_sig reced) then bot' else stuck' 5
           end
       | Lam t1 f => fun env => closure' (f (length env)) env
     end.

  Global Instance MAlgebra_eval_Lambda :
    FAlgebra EvalName (Exp nat) (evalR V) (Lambda nat) :=
    {| f_algebra := Lambda_eval|}.

  Variable (ME : Set -> Set). (* Evaluation Monad. *)
  Context {Fun_ME : Functor ME}.
  Context {Mon_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.
  Context {Environment_ME : Environment ME (Env Value)}.

  (* Monadic Evaluation Algebra for Lambda Expressions. *)

  Definition Lambda_evalM : Mixin (Exp nat) (Lambda nat) (evalMR V ME) :=
    fun rec e =>
    match e with
      | Var v =>
        do env <- ask ;
        match lookup env v with
          | None   => return_ (stuck' 20)
          | Some v => return_ v
        end
      | App e1 e2 =>
        do reced <- rec e1;
        do a <- rec e2;
        match isClos (proj1_sig reced) with
          | Some (f, env')  => local (fun _ => insert _ a env') (rec f)
          | None => return_ (stuck' 5)
        end
      | Lam t1 f => do env <- ask; return_ (closure' (f (length env)) env)
    end.

  Global Instance MAlgebra_evalM_Lambda :
    FAlgebra EvalName (Names.Exp (F nat)) (evalMR V ME) (Lambda nat) :=
    {| f_algebra := Lambda_evalM|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import String.
  Require Import Ascii.

  Global Instance MAlgebra_DTypePrint_AType T:
    FAlgebra DTypePrintName T DTypePrintR LType :=
    {| f_algebra := fun rec e =>
      match e with
        TArrow t1 t2 => append "(" ((rec t1) ++ " -> " ++ (rec t2) ++ ")")
      end
      |}.

  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR D}.

   Definition Lambda_ExpPrint (R : Set) (rec : R -> ExpPrintR)
     (e : Lambda nat R) : ExpPrintR :=
     match e with
       | Var v => fun n => append "x" (String (ascii_of_nat (v)) EmptyString)
       | App e1 e2 => fun n => append "(" ((rec e1 n) ++ ") @ (" ++ (rec e2 n) ++ ")")
       | Lam t1 f => fun n => append "\x" ((String (ascii_of_nat n) EmptyString) ++
         " : " ++ (DTypePrint _ (proj1_sig t1)) ++ ". " ++
         (rec (f n) (S n)) ++ ")")
     end.

   Global Instance MAlgebra_Print_Lambda T :
     FAlgebra ExpPrintName T ExpPrintR (Lambda nat) :=
     {| f_algebra := Lambda_ExpPrint T|}.

   Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR (F nat)}.

    Global Instance MAlgebra_ValuePrint_AType T:
    FAlgebra ValuePrintName T ValuePrintR ClosValue :=
    {| f_algebra := fun rec e =>
      match e with
        | Clos f _ => append "\x0. " (ExpPrint _ (proj1_sig f))
      end |}.

  (* ============================================== *)
  (* EQUIVALENCE OF EXPRESSIONS                     *)
  (* ============================================== *)


    Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
    Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Lambda nat) (F nat)
      (Sub_Lambda_F nat) (MAlgebra_eval_Lambda) (eval_F)}.

    Context {evalM_F : FAlgebra EvalName (Exp nat) (evalMR V ME) (F nat)}.
    Context {WF_evalM_F : @WF_FAlgebra EvalName _ _ (Lambda nat) (F nat)
      (Sub_Lambda_F nat) (MAlgebra_evalM_Lambda) (evalM_F)}.

    (** SuperFunctor for Equivalence Relation. **)

    Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
    Definition E_eqv A B := iFix (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' :=
      E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').
    Variable funEQV_E : forall A B, iFunctor (EQV_E A B).

    (* Projection doesn't affect Equivalence Relation.*)

    Inductive Lambda_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
    | Var_eqv : forall (gamma : Env _) gamma' n a b e e',
      lookup gamma n = Some a -> lookup gamma' n = Some b ->
      proj1_sig e = var a ->
      proj1_sig e' = var b ->
      Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' e e')
    | App_eqv : forall (gamma : Env _) gamma' a b a' b' e e',
      E (mk_eqv_i _ _ _ gamma gamma' a a') ->
      E (mk_eqv_i _ _ _ gamma gamma' b b') ->
      proj1_sig e = proj1_sig (app' a b) ->
      proj1_sig e' = proj1_sig (app' a' b') ->
      Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' e e')
    | Lam_eqv : forall (gamma : Env _) gamma' f g t1 t2 e e',
      (forall (a : A) (b : B), E (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))) ->
      proj1_sig t1 = proj1_sig t2 ->
      proj1_sig e = proj1_sig (lam' t1 f) ->
      proj1_sig e' = proj1_sig (lam' t2 g) ->
      Lambda_eqv _ _ E (mk_eqv_i _ _ _ gamma gamma' e e').

    Definition ind_alg_Lambda_eqv
      (A B : Set)
      (P : eqv_i F A B -> Prop)
      (H : forall gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq,
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (H0 : forall gamma gamma' a b a' b' e e'
        (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b'))
        e_eq e'_eq,
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (H1 : forall gamma gamma' f g t1 t2 e e'
        (IHf : forall a b, P (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b)))
        t1_eq e_eq e'_eq,
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      i (e : Lambda_eqv A B P i) : P i :=
      match e in Lambda_eqv _ _ _ i return P i with
        | Var_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq =>
          H gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | App_eqv gamma gamma' a b a' b' e e'
          eqv_a_a' eqv_b_b' e_eq e'_eq =>
          H0 gamma gamma' a b a' b' e e'
          eqv_a_a' eqv_b_b' e_eq e'_eq
        | Lam_eqv gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq =>
          H1 gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq
      end.

    Definition Lambda_eqv_ifmap (A B : Set)
      (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i)
      (eqv_a : Lambda_eqv A B A' i) : Lambda_eqv A B B' i :=
      match eqv_a in Lambda_eqv _ _ _ i return Lambda_eqv _ _ _ i with
        | Var_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq =>
          Var_eqv _ _ _ gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | App_eqv gamma gamma' a b a' b' e e'
          eqv_a_a' eqv_b_b' e_eq e'_eq =>
          App_eqv _ _ _ gamma gamma' a b a' b' e e'
          (f _ eqv_a_a') (f _ eqv_b_b') e_eq e'_eq
        | Lam_eqv gamma gamma' f' g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq =>
          Lam_eqv _ _ _ gamma gamma' f' g t1 t2 e e'
          (fun a b => f _ (eqv_f_g a b)) t1_eq e_eq e'_eq
      end.

    Global Instance iFun_Lambda_eqv A B : iFunctor (Lambda_eqv A B).
      constructor 1 with (ifmap := Lambda_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; unfold id; eauto.
    Defined.

    Variable Sub_Lambda_eqv_EQV_E : forall A B,
      Sub_iFunctor (Lambda_eqv A B) (EQV_E A B).

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D MT) (F DType)}.

     Global Instance EQV_proj1_Lambda_eqv :
       forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (Lambda_eqv _ _).
       econstructor; intros.
       unfold iAlgebra; intros; apply ind_alg_Lambda_eqv;
         unfold EQV_proj1_P; simpl; intros; subst.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor; simpl; eauto.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
       destruct a; destruct a'; eapply IHa; eauto.
       destruct b; destruct b'; eapply IHb; eauto.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor 3; simpl; eauto.
       intros; caseEq (f a); caseEq (g b); apply IHf; eauto.
       rewrite H2; simpl; eauto.
       rewrite H3; simpl; eauto.
       apply H.
     Qed.

  Section WFValue_Sec.

    (* ============================================== *)
    (* WELL-FORMED FUNCTION VALUES                    *)
    (* ============================================== *)

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.
    Context {GammaTypContext : GammaTypContextC D TypContext}.
    Context {TypContext_GCE : GammaConsExtensionC D TypContext _ _}.

    Variable WFV : (WFValue_i D V TypContext -> Prop) -> WFValue_i D V TypContext -> Prop.
    Variable funWFV : iFunctor WFV.

    (** Functions are well-formed **)

    Inductive WFValue_Clos
      (WFV : WFValue_i D V TypContext -> Prop) : WFValue_i D V TypContext -> Prop :=
    | WFV_Clos : forall (fE : nat -> Names.Exp _)
                        (fT : DType -> Names.Exp _)
                        (env : Env Value)
                        (Sigma : TypContext)
                        (gammaE : Env nat)
                        (gammaT : Env DType)
                        fE_UP
                        (t1 t2 t3 t4 : DType) v T
                        (*WF_Sigma : Gamma _ Sigma = gammaT*),
      proj1_sig v = proj1_sig (closure' (exist _ (proj1_sig (fE (List.length env))) fE_UP) env) ->
      proj1_sig T = proj1_sig (tarrow' t1 t2) ->
      (forall a b, E_eqvC (insert _ a gammaE) (insert _ b gammaT) (fE a) (fT b)) ->
      (forall n b, lookup gammaE n = Some b ->
        exists T, lookup gammaT b = Some T) ->
      List.length gammaE = List.length gammaT ->
      P2_Env (fun v T => WFV (mk_WFValue_i _ _ _ Sigma v T)) env gammaT ->
      (forall n b, lookup gammaE n = Some b -> b = n) ->
      typeof D (F DType) MT (proj1_sig (fT t4)) = return_ t3 ->
      proj1_sig t2 = proj1_sig t3 ->
      proj1_sig t4 = proj1_sig t1 ->
      WFValue_Clos WFV (mk_WFValue_i D V _ Sigma v T).

    Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
      (Sub_Lambda_F _) (MAlgebra_typeof_Lambda T) (Typeof_F _)}.

    Definition ind_alg_WFV_Clos
      (P : WFValue_i D V TypContext -> Prop)
      (P' : TypContext -> Env Value -> Env DType -> Prop)
      (H : forall fE fT env Sigma gammaE gammaT fE_UP t1 t2 t3 t4 v T
        (*WF_Sigma *) v_eq T_e1 eqv_fE_fT lookup_gammaE len_gammaE_gammaT
        P2_env lookup_gammaE' typeof_fT t3_eq t4_eq,
        P' Sigma env gammaT ->
        P (mk_WFValue_i _ _ _ Sigma v T))
      (H0 : forall Sigma, P' Sigma nil nil)
      (H1 : forall Sigma a b env env',
        P (mk_WFValue_i _ _ _ Sigma a b) ->
        P' Sigma env env' ->
        P' Sigma (a :: env) (b :: env'))
      i (e : WFValue_Clos  P i) : P i :=
      match e in WFValue_Clos _ i return P i with
        | WFV_Clos fE fT env Sigma gammaE gammaT fE_UP t1 t2 t3 t4 v T
          (*WF_Sigma *) v_eq T_e1 eqv_fE_fT lookup_gammaE len_gammaE_gammaT
          P2_env lookup_gammaE' typeof_fT t3_eq t4_eq =>
          H fE fT env Sigma gammaE gammaT fE_UP t1 t2 t3 t4 v T
          (*WF_Sigma *) v_eq T_e1 eqv_fE_fT lookup_gammaE len_gammaE_gammaT
          P2_env lookup_gammaE' typeof_fT t3_eq t4_eq
          ((fix P_Env_ind' (env : Env Value) (env' : Env DType)
            (P_env_env' : P2_Env (fun v T => P (mk_WFValue_i _ _ _ Sigma v T)) env env') :=
            match P_env_env' in P2_Env _ As Bs return P' Sigma As Bs with
              | P2_Nil => H0 Sigma
              | P2_Cons a b As Bs P_a_b P_As_Bs =>
                H1 Sigma a b As Bs P_a_b (P_Env_ind' _ _ P_As_Bs)
            end) env gammaT P2_env)
      end.

    Definition WFV_Clos_ifmap
      (A B : WFValue_i D V TypContext -> Prop) i
      (g : forall i, A i -> B i)
      (WFV_a : WFValue_Clos  A i) : WFValue_Clos  B i :=
      match WFV_a in (WFValue_Clos _ s) return (WFValue_Clos  B s)
        with
        | WFV_Clos fE fT env Sigma gammaE gammaT fE_UP t1 t2 t3 t4 v T
          (*WF_Sigma *) v_eq T_e1 eqv_fE_fT lookup_gammaE len_gammaE_gammaT
          P2_env lookup_gamma'' type_of_f t3_eq t4_eq =>
          WFV_Clos _ fE fT env Sigma gammaE gammaT fE_UP t1 t2 t3 t4 v T
          (*WF_Sigma *) v_eq T_e1 eqv_fE_fT lookup_gammaE len_gammaE_gammaT
          ((fix P_Env_ind' (env : Env _) (env' : Env _)
            (P_env_env' : P2_Env (fun v T => A (mk_WFValue_i _ _ _ Sigma v T)) env env') :=
            match P_env_env' in P2_Env _ As Bs return
              P2_Env (fun v T => B (mk_WFValue_i _ _ _ Sigma v T)) As Bs with
              | P2_Nil => P2_Nil _
              | P2_Cons a b As Bs P_a_b P_As_Bs =>
                P2_Cons (fun v T => B (mk_WFValue_i _ _ _ Sigma v T))
                a b As Bs (g (mk_WFValue_i _ _ _ Sigma a b) P_a_b) (P_Env_ind' _ _ P_As_Bs)
            end) _ _ P2_env)
          lookup_gamma'' type_of_f t3_eq t4_eq
      end.

    Global Instance iFun_WFV_Clos
      : iFunctor (WFValue_Clos ).
      constructor 1 with (ifmap := WFV_Clos_ifmap ).
      destruct a; simpl; intros;
        apply (f_equal (fun G => WFV_Clos C fE fT env Sigma gammaE gammaT fE_UP
          t1 t2 t3 t4 v T (*WF_Sigma *) e e0 e1 e2 e3 G e4 e5 e6 e7)).
      generalize gammaT p; clear; induction env; dependent inversion p; subst.
      reflexivity.
      rewrite IHenv.
      apply (f_equal (fun G => P2_Cons
        (fun (v : Names.Value V) (T : Names.DType D) => C (mk_WFValue_i _ _ _ Sigma v T)
        ) a b env Bs G (((fix P_Env_ind' (env0 : Env (Names.Value V))
          (env' : Env (Names.DType D))
          (P_env_env' : P2_Env
            (fun (v : Names.Value V)
              (T : Names.DType D) => A (mk_WFValue_i _ _ _ Sigma v T)) env0 env') {struct P_env_env'} :
          P2_Env
          (fun (v : Names.Value V) (T : Names.DType D) => C (mk_WFValue_i _ _ _ Sigma v T)) env0 env' :=
          match
            P_env_env' in (P2_Env _ As Bs0)
            return
            (P2_Env
              (fun (v : Names.Value V) (T : Names.DType D) => C (mk_WFValue_i _ _ _ Sigma v T)) As Bs0)
            with
            | P2_Nil =>
              P2_Nil
              (fun (v : Names.Value V) (T : Names.DType D) => C (mk_WFValue_i _ _ _ Sigma v T))
            | P2_Cons a0 b0 As Bs0 P_a_b P_As_Bs =>
              P2_Cons
              (fun (v : Names.Value V) (T : Names.DType D) => C (mk_WFValue_i _ _ _ Sigma v T)) a0 b0 As Bs0
              (g (mk_WFValue_i _ _ _ Sigma a0 b0) (f (mk_WFValue_i _ _ _ Sigma a0 b0) P_a_b))
              (P_Env_ind' As Bs0 P_As_Bs)
          end) env Bs p0)))).
      auto.
      destruct a; simpl; intros;
        apply (f_equal (fun G => WFV_Clos _ fE fT env Sigma gammaE gammaT fE_UP
          t1 t2 t3 t4 v T (*WF_Sigma *) e e0 e1 e2 e3 G e4 e5 e6 e7)).
      generalize gammaT p; clear; induction env; dependent inversion p; subst.
      reflexivity.
      rewrite IHenv.
      reflexivity.
    Defined.

    Variable Sub_WFV_Clos_WFV : Sub_iFunctor WFValue_Clos WFV.

     Global Instance WFV_proj1_a_Clos  :
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) (WFValue_Clos ).
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_a_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_Clos_WFV )); econstructor; simpl; eauto.
       rewrite H11; rewrite H0; simpl; reflexivity.
       rewrite H1; simpl; reflexivity.
       remember (Gamma D Sigma).
       generalize gammaT H5; clear; induction env; intros; inversion H5;
         subst; constructor.
       unfold WFV_proj1_a_P in H1; unfold WFValueC, WFValue in H1;
         destruct a; eapply H1; eauto.
       eauto.
     Defined.

     Global Instance WFV_proj1_b_Clos  :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) (WFValue_Clos ).
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_Clos_WFV )); econstructor; simpl; eauto.
       rewrite H11; rewrite H1; reflexivity.
       remember (Gamma D Sigma).
       generalize gammaT H5; clear; induction env; intros; inversion H5;
         subst; constructor.
       unfold WFV_proj1_b_P in H1; unfold WFValueC, WFValue in H1.
         destruct b; eapply H1; eauto.
       eauto.
     Defined.

     Global Instance WFValue_Weaken_Clos  :
       iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFValue_Clos.
     Proof.
       econstructor; intros.
       unfold iAlgebra; intros; apply ind_alg_WFV_Clos with
         (P' := fun Sigma env gamma =>
           forall Sigma' : TypContext,
             ConsExtension Sigma' Sigma ->
             WF_Environment D V _ WFV Sigma' env gamma);
         try eassumption.
       unfold WFValue_Weaken_P; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_Clos_WFV )); econstructor; simpl; eauto.
       eapply H0; eauto.
       intros; constructor.
       intros; constructor; eauto.
       apply H1; eauto.
     Qed.

    Definition WF_invertClos_P  (i : WFValue_i D V TypContext) :=
      WFValue _ _ _ WFV i /\
      forall t1 t2, proj1_sig (wfv_T _ _ _ i) = proj1_sig (tarrow' t1 t2) ->
      WFValue_Clos  (iFix WFV) i.

    Inductive WF_invertClos_Name := wfv_invertclosure_name.
    Context {WF_invertClos_WFV :
      iPAlgebra WF_invertClos_Name (WF_invertClos_P ) WFV}.

    Global Instance WF_invertClos_Clos  :
      iPAlgebra WF_invertClos_Name (WF_invertClos_P ) (WFValue_Clos ).
      econstructor; intros.
      unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
        fun Sigma => P2_Env (fun v T => WFValueC _ _ _ WFV Sigma v T)).
      inversion H; subst; simpl; intros; split.
      eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
        econstructor 1 with (fE_UP := fE_UP0); simpl in *|-*; eauto.
      econstructor 1 with (fE_UP := fE_UP0); simpl in *|-*; eauto; try congruence.
      rewrite T_e1 in H11; apply (f_equal out_t) in H11;
        repeat rewrite out_in_inverse in H11.
      repeat rewrite wf_functor in H11; simpl in H11;
      apply (f_equal prj) in H11; repeat rewrite prj_inj in H11;
        injection H11; intros.
      congruence.
      rewrite T_e1 in H11; apply (f_equal out_t) in H11;
        repeat rewrite out_in_inverse in H11.
      repeat rewrite wf_functor in H11; simpl in H11;
      apply (f_equal prj) in H11; repeat rewrite prj_inj in H11;
        injection H11; intros.
      congruence.
      constructor.
      constructor.
      destruct b; destruct H0; eauto.
      eassumption.
      exact H.
    Defined.

    Definition WF_invertClos  := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertClos_WFV )).

    Definition WF_invertClos'_P  (i : WFValue_i D V TypContext) :=
      WFValue _ _ _ WFV i /\
      forall v : ClosValue _, proj1_sig (wfv_v _ _ _ i) = inject v ->
      WFValue_Clos  (iFix WFV) i.

    Inductive WF_invertClos'_Name := wfv_invertclosure'_name.
    Context {WF_invertClos'_WFV :
      iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) WFV}.

    Global Instance WF_invertClos'_Clos  :
      iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) (WFValue_Clos ).
      econstructor; intros.
      unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
        fun Sigma => P2_Env (fun v T => WFValueC _ _ _ WFV Sigma v T)).
      inversion H; subst; simpl; intros; split.
      eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
        econstructor 1 with (fE_UP := fE_UP0);
        simpl in *|-*; eauto.
      intros; econstructor 1 with (fE_UP := fE_UP0); simpl in *|-*; eauto.
      left; econstructor; simpl in *|-*; eauto; try congruence.
      intros; constructor; auto.
      destruct b; destruct H0; auto.
      assumption.
    Defined.

    Definition WF_invertClos'  :=
      ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertClos'_WFV )).

  (* ============================================== *)
  (* WELL-FORMED MONADIC STATE VALUES               *)
  (* ============================================== *)

     (** SuperFunctor for Well-Formed Monadic Value Relation with
        Typing Environment. **)

     Variable WFVM : (WFValueM_i D V MT ME TypContext -> Prop) -> WFValueM_i D V MT ME TypContext -> Prop.
     Definition WFValueM := iFix WFVM.
     Definition WFValueMC Sigma v T:= WFValueM (mk_WFValueM_i D V MT ME _ Sigma v T).
     Variable funWFVM : iFunctor WFVM.


    Context {Sub_WFVM_Base_WFVM : Sub_iFunctor (WFValueM_base D V MT ME _ WFV) WFVM}.
    Context {Sub_WFVM_Environment_WFVM : Sub_iFunctor (WFValueM_Environment D MT V ME _ WFV) WFVM}.

    Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P D V _ WFV) WFV}.

    Context {TypContextCE' : ConsExtensionC TypContext}.
    Context {WFV_Weaken_WFV' : iPAlgebra WFValue_Weaken_Name (WFValue_Weaken_P (TypContextCE := TypContextCE') D V _ WFV) WFV}.

    Context {WFV_Weaken'_WFV : iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V _ WFV) WFV}.

    Global Instance WF_Weaken'_Clos  :
      iPAlgebra WFValue_Weaken'_Name (WFValue_Weaken'_P D V _ WFV) (WFValue_Clos ).
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros. apply (ind_alg_WFV_Clos ) with (P' :=
      fun Sigma => P2_Env (fun v T => forall env1, WFValueC _ _ _ WFV (GammaSet D Sigma env1) v T));
      try eassumption.
      inversion H; subst; simpl; intros.
      unfold WFValue_Weaken'_P; intros.
      eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
        econstructor 1 with (fE_UP := fE_UP0);
        simpl in *|-*; simpl; eauto.
      eapply P2_Env_P_P'; try eassumption; simpl; intros; eauto.
      simpl in H11; apply H11.
      intros; econstructor.
      intros; constructor; auto.
    Defined.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

    Context {wfvm_bind_alg :
      iPAlgebra wfvm_bind_Name (wfvm_bind_P D V MT ME _ WFV WFVM (TypContextCE := TypContextCE)) WFVM}.
    Context {EQV_proj1_alg :
      forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (EQV_E _ _)}.
    Context {WFV_proj1_a_WFV :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V _ WFV) WFV}.
     Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V _ WFV) WFV}.
     Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName D D (UP'_P (eq_DType_eq_P D))}.
     Context {eq_DType_neq_D : PAlgebra eq_DType_neqName D D (UP'_P (eq_DType_neq_P D))}.

    Context {TypContextGCE' : GammaConsExtension'C D TypContext TypContextCE' GammaTypContext}.

    Global Instance eqv_soundness_X'_Lambda_eqv eval_rec :
      iPAlgebra soundness_X'_Name
      (soundness_X'_P D V F MT ME _ EQV_E WFVM (fun e => typeof _ _ MT (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_F _))
        (f_algebra (FAlgebra := evalM_F))) (Lambda_eqv _ _).
    Proof.
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_Lambda_eqv; try eassumption;
        unfold soundness_X'_P, eval_soundness'_P; unfold bevalM; simpl; intros.
      (* var case *)
      split; intros.
      apply inject_i; econstructor; eauto.
      rewrite e_eq, e'_eq; intros; unfold var, var'; simpl.
      simpl; repeat erewrite out_in_fmap;
        repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_evalM_F)); simpl.
      unfold typeof, mfold, in_t;
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)); simpl.
      apply (inject_i (subGF := Sub_WFVM_Environment_WFVM)); constructor.
      destruct WF_Gamma as [e_eqv [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]]; subst.
      intros; rewrite (WF_gamma' _ _ lookup_a) in *|-*.
      destruct (WF_gamma _ _ lookup_a) as [T lookup_b'].
      unfold WF_EnvG in H0; rewrite Sub_Gamma_gamma' in H0.
      destruct (P2_Env_lookup' _ _ _ _ _ H0 _ _ lookup_b) as [v [lookup_v WF_v]].
      intros; rewrite (WF_gamma' _ _ lookup_a) in *|-*.
        unfold Value; rewrite lookup_v.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor; eauto.
      generalize (return_orn MT _
        (fun T => proj1_sig b = proj1_sig T) b); simpl; intros;
      unfold Names.DType, UP'_F; auto.
    (* app case *)
       destruct (IHa IH) as [eqv_a _];
         destruct (IHb IH) as [eqv_b _].
       split.
       apply inject_i; econstructor 2; simpl; try apply e_eq; try apply e'_eq; eauto.
       intros; rewrite e_eq, e'_eq; simpl; repeat erewrite out_in_fmap;
        repeat rewrite wf_functor; simpl.
       rewrite (wf_algebra (WF_FAlgebra := WF_evalM_F)); simpl.
       unfold typeof, mfold, in_t;
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)); simpl.
       apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
       intros; unfold isTArrow; rewrite H0; reflexivity.
       generalize in_out_UP'_inverse; intro H'; simpl in H';
         rewrite H'; clear H'.
       unfold typeof, mfold in IHa.
       eapply IH; eauto.
       instantiate (1 := (gamma, gamma')).
       split; eauto.
       destruct WF_Gamma as [e_eqv WF_Gamma]; subst; auto.
       eapply eqv_a.
       exact (proj2_sig _).
       intros.
       apply wfvm_bind with (WFV := WFV) (TypContextCE := TypContextCE); auto.
       intros; apply f_equal; destruct (isTArrow T); auto; destruct p.
       caseEq ( eq_DType D (proj1_sig s) T0);
         caseEq (eq_DType D (proj1_sig s) T'); auto.
       elimtype False; apply (eq_DType_neq _ _ _ H4);
         generalize (eq_DType_eq _ _ _ H3); intros; congruence.
       elimtype False; apply (eq_DType_neq _ _ _ H3);
         generalize (eq_DType_eq _ _ _ H4); intros; congruence.
       generalize in_out_UP'_inverse; intro H'; simpl in H';
         rewrite H'; clear H'.
       unfold typeof, mfold in IH.
       eapply IH with (pb := (gamma, gamma')); eauto.
       destruct WF_Gamma as [e_eqv WF_Gamma]; auto.
       split; eauto.
       eapply WF_eqv_environment_P_Sub with (TypContextCE := TypContextCE); eauto.
       exact (proj2_sig _).
       intros; unfold isTArrow.
       caseEq (project (proj1_sig T)).
       destruct l.
       apply project_inject in H4; unfold inject in H4; simpl in H4;
         eauto with typeclass_instances.
       generalize (proj2 (WF_invertClos _ H1) _ _ H4); simpl; intros WF_v_T;
         inversion WF_v_T; subst.
       rewrite H8; simpl.
       unfold isClos, project; rewrite out_in_fmap;
         repeat rewrite wf_functor; simpl; rewrite prj_inj.
       caseEq (eq_DType D (proj1_sig s) T0).
       rewrite (right_unit (M := ME) (local _ _)).
       apply (inject_i (subGF := Sub_WFVM_Environment_WFVM)).
       eapply WFVM_Local with (Gamma' := (insert _ t4 gammaT)).
       (* apply ConsExtension_GammaInsert.*)
       unfold WF_EnvG; intros; rewrite (Gamma_GammaSet);
         apply P2_Env_insert; auto.
       (*rewrite <- (ConsExtension_Gamma _ _ _ H2).*)
       remember gammaT; rewrite Heqe0 at -1; rewrite Heqe0 in H13.
       revert WFV_Weaken_WFV WFV_Weaken'_WFV WFV_proj1_a_WFV funWFV H13 H2; clear; intros; induction H13;
         simpl; constructor; auto.
       apply (WFV_proj1_a D V _ WFV _ _
         (WFV_Weaken' D V _ WFV _ (WFV_Weaken D V _ WFV _ _ H _ H2) (insert _ t4 e0))); simpl; auto.
       generalize in_out_UP'_inverse; simpl; intros H4; apply H4.
       exact (proj2_sig _).
       destruct t4 as [t4 t4_UP'].
       eapply (WFV_Weaken' D V _ WFV (mk_WFValue_i _ _ _ Sigma'0 _ _)); simpl; auto.
       apply (WFV_proj1_b D V _ WFV _ _ H3); simpl; auto.
       rewrite <- (eq_DType_eq _ _ _ H5).
       rewrite H4 in H9; simpl in H9; apply in_t_UP'_inject in H9;
         repeat rewrite wf_functor in H9; apply (f_equal prj) in H9;
           repeat rewrite prj_inj in H9; simpl in H9; injection H9; intros; auto.
       simpl in *; rewrite H18, H17; reflexivity.
       instantiate (1 := t3).
       unfold DType in H15; simpl; rewrite <- H15; rewrite  eval_rec_proj;
         eapply IH with (pb := (insert _ (Datatypes.length gammaE) gammaE, insert _ t4 gammaT));
           eauto.
       split; simpl; auto.
       unfold PNames.E_eqvC, PNames.E_eqv.
       unfold E_eqvC, E_eqv in H10.
       generalize (@EQV_proj1 F _ EQV_E _ _ _ _ _ (H10 (Datatypes.length gammaE) t4)).
       unfold EQV_proj1_P; simpl; intros.
       unfold DType in H6.
       destruct (fT t4); apply H6; simpl; auto.
       rewrite H12; auto.
       unfold DType; rewrite <- (P2_Env_length _ _ _ _ _ H13); auto.
      unfold WF_eqv_environment_P; simpl in *|-*; repeat split; auto.
      rewrite H12.
      revert H11; clear; simpl; induction gammaE;
        destruct m; simpl; intros; try discriminate.
      injection H; intros; subst.
      clear; induction gammaT; simpl; eauto; eexists.
      injection H; intros; subst.
      generalize b (H11 0 _ (eq_refl _)); clear; induction gammaT; simpl; intros b H;
        destruct H as [T' lookup_T']; try discriminate.
      destruct b; eauto.
      eapply IHgammaE.
      intros n0 b0 H0; eapply (H11 (S n0) _ H0).
      eassumption.
      repeat rewrite length_insert; eauto.
      intro; caseEq (beq_nat m (Datatypes.length gammaE)).
      assert (exists m', m' = Datatypes.length gammaE) as ex_m' by
        (eexists _; reflexivity); destruct ex_m' as [m' m'_eq];
          rewrite <- m'_eq in H7 at 1.
      rewrite (beq_nat_true _ _ H6).
      rewrite (beq_nat_true _ _ H6), m'_eq in H7.
      rewrite lookup_insert in H7; congruence.
      eapply H14.
      rewrite <- H7; apply sym_eq; apply lookup_insert_lt.
      eapply lookup_Some_lt in H7.
      rewrite length_insert in H7; inversion H7; auto.
      apply beq_nat_false in H6; elimtype False; eauto.
      apply Gamma_GammaSet.
       unfold PNames.E_eqvC, PNames.E_eqv.
       unfold E_eqvC, E_eqv in H10.
       generalize (@EQV_proj1 F _ EQV_E _ _ _ _ _ (H10 (Datatypes.length gammaE) t4)).
       unfold EQV_proj1_P; simpl; intros.
       unfold DType in *|-*; simpl.
       destruct (fT t4); simpl; apply H6; simpl; auto.
       rewrite H12; auto.
       unfold DType; rewrite <- (P2_Env_length _ _ _ _ _ H13); auto.
       intros; apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor; eauto.
       generalize (return_orn MT); simpl; intro RO; apply RO.
       rewrite H4 in H9; simpl in H9; apply in_t_UP'_inject in H9;
         repeat rewrite wf_functor in H9; apply (f_equal prj) in H9;
           repeat rewrite prj_inj in H9; simpl in H9; injection H9; intros; auto.
       simpl in *; rewrite H18, H16; reflexivity.
       apply (wfvm_fail _ _ _ _ _ _ WFVM).
       exact (proj2_sig _).
       apply (wfvm_fail _ _ _ _ _ _ WFVM).
      (* lam case *)
      split; intros.
      generalize (fun a b => proj1 (IHf a b IH)); intro IHf';
        apply inject_i; econstructor 3; eauto.
      generalize (fun a b => proj1 (IHf a b IH)); intro IHf';
        rewrite e_eq, e'_eq.
      intros; simpl; repeat erewrite out_in_fmap;
        repeat rewrite wf_functor; simpl.
      rewrite (wf_algebra (WF_FAlgebra := WF_evalM_F)); simpl.
      unfold typeof, mfold, in_t;
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)); simpl.
      apply (inject_i (subGF := Sub_WFVM_Environment_WFVM)); constructor.
      destruct (MT_eq_dec _ (mfold (typeofR D MT) (fun R : Set => f_algebra) (proj1_sig (g t2))))
               as [[d d_eq] | d_eq].
      intros.
      apply (inject_i (subGF := Sub_WFVM_Base_WFVM)); econstructor 1.
      instantiate (1 := (inject' (TArrow DType t2 d))).
      apply inject_i; econstructor 1 with (fE := fun n =>
        (in_t_UP' (F nat) (Fun_F nat)
          (out_t_UP' (F nat) (Fun_F nat)
             (proj1_sig (f n))))) (fT := g)
        (env := env) (Sigma := Sigma) (gammaE := gamma) (gammaT := gamma')
        (fE_UP := proj2_sig _).
      destruct WF_Gamma as [e_eqv [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]]; eauto.
      reflexivity.
      (* unfold tarrow'; reflexivity.*)
      intros; caseEq (g b); caseEq (f a);
        apply (@EQV_proj1 F _ EQV_E _ _ _ _ _ (IHf' a b)); simpl.
      rewrite H2; generalize in_out_UP'_inverse; simpl.
      intro H3; apply H3; auto.
      rewrite H1; auto.
      destruct WF_Gamma as [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]; auto.
      destruct WF_Gamma as [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]; auto.
      destruct WF_Gamma as [_ [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]]; subst; auto.
      unfold WF_EnvG in H0; rewrite Sub_Gamma_gamma' in H0; auto.
      destruct WF_Gamma as [_ [WF_gamma [WF_gamma2 [WF_gamma' Sub_Gamma_gamma']]]]; subst; auto.
      apply d_eq.
      auto.
      auto.
      intros; generalize in_out_UP'_inverse; intro H'; simpl in H';
        rewrite H'; auto.
      unfold mfold in d_eq; rewrite d_eq.
      rewrite <- left_unit.
      generalize (return_orn MT); simpl; intro RO; apply RO.
      reflexivity.
      exact (proj2_sig _).
      intros; generalize in_out_UP'_inverse; intro H'; simpl in H';
        rewrite H'; auto.
      unfold mfold in d_eq; rewrite d_eq.
      rewrite bind_fail.
      apply (wfvm_fail _ _ _ _ _ _ WFVM).
      exact (proj2_sig _).
  Defined.

  End WFValue_Sec.

End Lambda.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
