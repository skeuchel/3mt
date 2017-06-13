Require Import Functors.
Require Import List.
Require Import FunctionalExtensionality.
Require Import MonadLib.

Section Names.

  (* ============================================== *)
  (* ENVIRONMENTS                                   *)
  (* ============================================== *)

  Definition Env (A : Set) := list A.

  Fixpoint lookup {A: Set} (As : Env A) (i : nat) : option A :=
    match As, i with
      | nil, _  => None
      | cons _ As', S i' => lookup As' i'
      | cons a _, 0 => Some a
    end.

  Fixpoint insert (A : Set) (e : A) (env : Env A) : Env A :=
    match env in list _ return Env A with
      | nil => cons e (nil)
      | cons e' env' => cons e' (@insert _ e env')
    end.

  Definition empty A : Env A := nil.

  Lemma length_insert {A : Set} :
    forall (a : A) (As : Env A), length (insert _ a As) = S (length As).
  Proof.
    induction As; simpl; auto.
  Qed.

  Lemma lookup_insert {A : Set} :
    forall (a : A) (As : Env A),
      lookup (insert _ a As) (length As) = Some a.
  Proof.
    induction As; simpl; auto.
  Qed.

  Lemma lookup_insert_lt {A : Set} :
    forall (a : A) (As : Env A) (i : nat),
      i < (length As) -> lookup (insert _ a As) i = lookup As i.
  Proof.
    induction As; destruct i; simpl; intros; auto with arith.
    inversion H.
  Qed.

  Lemma lookup_Some_lt {A : Set} :
    forall (a : A) (i : nat) (As : Env A),
      lookup As i = Some a -> i < (length As).
  Proof.
    induction i; destruct As; simpl; intros; try discriminate;
      auto with arith.
  Qed.

  Lemma lookup_Some_insert {A : Set} :
    forall (a : A) (i : nat) (As : Env A),
      lookup As i = Some a ->
      forall (a' : A), lookup (insert _ a' As) i = lookup As i.
  Proof.
    intros; apply lookup_insert_lt.
    eapply lookup_Some_lt; eauto.
  Qed.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)


  (** SuperFunctor for Types. **)
  Variable DT : Set -> Set.
  Context {Fun_DT : Functor DT}.
  Definition DType := UP'_F DT.


  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)


  (** SuperFunctor for Values. **)

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Definition Value := UP'_F V.

  (** ERROR VALUES **)

   Inductive StuckValue (A : Set) : Set :=
    | Stuck : nat -> StuckValue A.

   Context {Sub_StuckValue_V : StuckValue :<: V}.

   Definition Stuck_fmap : forall (A B : Set) (f : A -> B),
     StuckValue A -> StuckValue B := fun A B _ e =>
       match e with
         | Stuck n => Stuck _ n
       end.

   Global Instance Stuck_Functor : Functor StuckValue :=
     {| fmap := Stuck_fmap |}.
     destruct a; reflexivity.
     (* fmap_id *)
     destruct a; reflexivity.
   Defined.

   (* Constructor + Universal Property. *)
   Context {WF_SubStuckValue_V : WF_Functor _ _ Sub_StuckValue_V _ _}.

   Definition stuck' (n : nat) : Value := inject' (Stuck _ n).
   Definition stuck (n : nat) : Fix V := proj1_sig (stuck' n).

   Global Instance UP'_stuck {n : nat} :
     Universal_Property'_fold (stuck n) := proj2_sig (stuck' n).

   (* Induction Principle for Stuckor Values. *)

  Definition ind_alg_Stuck (P : Fix V -> Prop)
    (H : forall n, P (stuck n))
      (e : StuckValue (sig P)) : sig P :=
    match e with
      | Stuck n => exist P (stuck n) (H n)
    end.

  Definition ind_palg_Stuck (Name : Set) (P : Fix V -> Prop) (H : forall n, P (stuck n)) :
    PAlgebra Name StuckValue V P.
  Proof.
    econstructor 1 with (p_algebra := ind_alg_Stuck P H).
    destruct e; simpl; unfold stuck, stuck'; simpl;
      rewrite wf_functor; reflexivity.
  Qed.

   (** BOTTOM VALUES **)

   Inductive BotValue (A : Set) : Set :=
   | Bot : BotValue A.

   Context {Sub_BotValue_V : BotValue :<: V}.

   Definition Bot_fmap : forall (A B : Set) (f : A -> B),
     BotValue A -> BotValue B := fun A B _ _ => Bot _.

   Global Instance Bot_Functor : Functor BotValue :=
     {| fmap := Bot_fmap |}.
     destruct a; reflexivity.
     (* fmap_id *)
     destruct a. reflexivity.
   Defined.

   (* Constructor + Universal Property. *)
   Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V _ _}.

   Definition bot' : Value := inject' (Bot _).
   Definition bot : Fix V := proj1_sig bot'.
   Global Instance UP'_bot : Universal_Property'_fold bot :=
     proj2_sig bot'.

  Definition ind_alg_Bot (P : Fix V -> Prop)
    (H : P bot)
      (e : BotValue (sig P)) : sig P :=
    match e with
      | Bot => exist P bot H
    end.

  (* Constructor Testing for Bottom Values. *)

  Definition isBot : Fix V -> bool :=
    fun exp =>
      match project exp with
       | Some Bot  => true
       | None      => false
      end.

  Definition ind_palg_Bot (Name : Set) (P : Fix V -> Prop) (H : P bot) :
    PAlgebra Name BotValue V P.
  Proof.
    econstructor 1 with (p_algebra := ind_alg_Bot P H).
    destruct e; simpl; unfold bot, bot'; simpl;
      rewrite wf_functor; reflexivity.
  Qed.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Definition Exp := UP'_F E.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)


  (** TYPING **)

  Variable MT : Set -> Set.

  Definition typeofR  := MT DType.
  Inductive TypeofName : Set := typeofname.
  Context {Typeof_E : forall T,
    FAlgebra TypeofName T typeofR E}.
  Definition typeof :=
    mfold _ (fun _ => @f_algebra _ _ _ _ (Typeof_E _)).

  (** EVALUATION **)

  Definition evalR : Set := Env Value -> Value.

  Inductive EvalName := evalname.

  Context {eval_E : forall T, FAlgebra EvalName T evalR E}.
  Definition eval := mfold _ (fun _ => @f_algebra _ _ _ _ (eval_E _)).

  Context {beval_E : FAlgebra EvalName Exp evalR E}.

  Definition beval (n: nat) :=
    boundedFix_UP n (@f_algebra _ _ _ _ beval_E) (fun _ => bot').

  Variable ME : Set -> Set.
  Context {Functor_ME : Functor ME}.
  Context {Monad_ME : Monad ME}.
  Context {Fail_ME : FailMonad ME}.

  Definition evalMR := ME Value.

  Context {evalM_E : forall T, FAlgebra EvalName T evalMR E}.
  Definition evalM := mfold _ (fun _ => @f_algebra _ _ _ _ (evalM_E _)).

  Context {bevalM_E : FAlgebra EvalName Exp evalMR E}.

  Definition bevalM (n: nat) :=
    boundedFix_UP n (@f_algebra _ _ _ _ bevalM_E) fail.

  (** DTYPE EQUALITY **)

  Definition eq_DTypeR := DType -> bool.
  Inductive eq_DTypeName := eq_dtypename.
  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T eq_DTypeR DT}.
  Definition eq_DType := mfold _ (fun _ => @f_algebra _ _ _ _ (eq_DType_DT _)).

  Definition eq_DType_eq_P (d : Fix DT) (d_UP' : Universal_Property'_fold d) := forall d2,
    eq_DType d d2 = true -> d = proj1_sig d2.
  Inductive eq_DType_eqName := eq_dtype_eqname.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName DT DT (UP'_P eq_DType_eq_P)}.
  Lemma eq_DType_eq : forall (d1 : DType), eq_DType_eq_P (proj1_sig d1) (proj2_sig d1).
    intro; eapply (proj2_sig (Ind (P := UP'_P eq_DType_eq_P) (proj1_sig d1) (proj2_sig d1))).
  Qed.

  Definition eq_DType_neq_P (d : Fix DT) (d_UP' : Universal_Property'_fold d) := forall d2,
    eq_DType d d2 = false -> d <> proj1_sig d2.
  Inductive eq_DType_neqName := eq_dtype_neqname.
  Context {eq_DType_neq_D : PAlgebra eq_DType_neqName DT DT (UP'_P eq_DType_neq_P)}.
  Lemma eq_DType_neq : forall (d1 : DType), eq_DType_neq_P (proj1_sig d1) (proj2_sig d1).
    intro; eapply (proj2_sig (Ind (P := UP'_P eq_DType_neq_P) (proj1_sig d1) (proj2_sig d1))).
  Qed.

  (** PRETTY PRINTING **)

  Require Import String.
  Require Import Ascii.

  Definition DTypePrintR := string.
  Inductive DTypePrintName := dtypeprintname.
  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR DT}.
  Definition DTypePrint := mfold _ (fun _ => @f_algebra _ _ _ _ (DTypePrint_DT _)).

  Definition ExpPrintR := nat -> string.
  Inductive ExpPrintName := expprintname.
  Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR E}.
  Definition ExpPrint e := mfold _ (fun _ => @f_algebra _ _ _ _ (ExpPrint_E _)) e 48.

  Definition ValuePrintR := string.
  Inductive ValuePrintName := valueprintname.
  Context {ValuePrint_V : forall T, FAlgebra ValuePrintName T ValuePrintR V}.
  Definition ValuePrint := mfold _ (fun _ => @f_algebra _ _ _ _ (ValuePrint_V _)).

  (* Printers for Bot and Stuck *)
   Global Instance MAlgebra_ValuePrint_BotValue T : FAlgebra ValuePrintName T ValuePrintR BotValue :=
     {| f_algebra :=  fun _ _ => append "bot" "" |}.

   Global Instance MAlgebra_ValuePrint_StuckValue T : FAlgebra ValuePrintName T ValuePrintR StuckValue :=
     {| f_algebra :=
       fun _ e => match e with
                      | Stuck n => append "Stuck " (String (ascii_of_nat (n + 48)) EmptyString)
                    end|}.

  (* ============================================== *)
  (* PREDICATE LIFTERS FOR LISTS                    *)
  (* ============================================== *)

    (* Unary Predicates.*)
    Inductive P_Env {A : Set} (P : A -> Prop) : forall (env : Env A), Prop :=
    | P_Nil : P_Env P nil
    | P_Cons : forall a (As : Env _), P a -> P_Env P As ->
      P_Env P (cons a As).

    Lemma P_Env_lookup : forall A (env : Env A) P,
      P_Env P env ->
      forall n v,
        lookup env n = Some v -> P v.
      intros A env P P_env; induction P_env;
        destruct n; simpl; intros; try discriminate.
      injection H0; intros; subst; eauto.
      eauto.
    Qed.

    Lemma P_Env_Lookup : forall A (env : Env A) (P : A -> Prop),
      (forall n v,
        lookup env n = Some v -> P v) ->
      P_Env P env.
      intros A env P H; induction env; constructor.
      eapply (H 0); eauto.
      apply IHenv; intros; eapply (H (S n)); eauto.
    Qed.

    Lemma P_Env_insert : forall A (env : Env A) (P : A -> Prop),
      P_Env P env -> forall a, P a -> P_Env P (insert _ a env).
      induction env; simpl; intros; constructor; eauto.
      inversion H; subst; eauto.
      eapply IHenv; inversion H; eauto.
    Qed.

    (* Binary Predicates.*)
    Inductive P2_Env {A B : Set} (P : A -> B -> Prop) : forall (env : Env A) (env : Env B), Prop :=
    | P2_Nil : P2_Env P nil nil
    | P2_Cons : forall a b (As : Env _) (Bs : Env _), P a b -> P2_Env P As Bs ->
      P2_Env P (cons a As) (cons b Bs).

    Lemma P2_Env_lookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n v,
        lookup env n = Some v -> exists v', lookup env' n = Some v' /\
          P v v'.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      exists b; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.

    Lemma P2_Env_lookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n v,
        lookup env' n = Some v -> exists v', lookup env n = Some v' /\
          P v' v.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      eexists; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.

    Lemma P2_Env_Nlookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n,
        lookup env n = None -> lookup env' n = None.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate; auto.
    Qed.

    Lemma P2_Env_Nlookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n,
        lookup env' n = None -> lookup env n = None.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate; auto.
    Qed.

    Lemma P2_Env_length : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> List.length env = List.length env'.
      intros; induction H; simpl; congruence.
    Qed.

    Lemma P2_Env_insert : forall A B (env : Env A) (env' : Env B) (P : A -> B -> Prop),
      P2_Env P env env' ->
      forall a b, P a b -> P2_Env P (insert _ a env) (insert _ b env').
      intros; induction H; simpl; constructor; eauto.
      constructor.
    Qed.

    Fixpoint replace_el {A : Set} (n : nat) (a : A) (l : list A) :=
      match n, l with
        | 0, cons _ l' => cons a l'
        | S n', cons a' l' => cons a' (replace_el n' a l')
        | _, _ => nil
      end.

    Lemma P2_Env_replace_el : forall (A B : Set) (P : A -> B -> Prop) (n : nat)
      (env : Env A) (env' : Env B),
      P2_Env P env env' ->
      forall a b, P a b -> (lookup env' n = Some b) ->
        P2_Env P (replace_el n a env) env'.
    Proof.
      induction n; intros; destruct H; simpl in *; try discriminate.
      injection H1; intros; subst; constructor; auto.
      constructor; eauto.
    Qed.

    (* Need this better induction principle when we're reasoning about
       Functors that use P2_Envs. *)
    Definition P2_Env_ind' :=
    fun (A B : Set) (P : A -> B -> Prop) (P0 : forall As Bs, P2_Env P As Bs -> Prop)
      (f : P0 _ _ (P2_Nil _))
      (f0 : forall (a : A) (b : B) (As : Env A) (Bs : Env B) (ABs : P2_Env P As Bs)
        (P_a_b : P a b), P0 _ _ ABs -> P0 _ _ (P2_Cons P a b As Bs P_a_b ABs)) =>
        fix F (env : Env A) (env0 : Env B) (p : P2_Env P env env0) {struct p} :
        P0 env env0 p :=
        match p in (P2_Env _ env1 env2) return (P0 env1 env2 p) with
        | P2_Nil => f
        | P2_Cons a b As Bs y p0 => f0 a b As Bs p0 y (F As Bs p0)
      end.

    Lemma P2_Env_P_P' : forall A B (env : Env A) (env' : Env B) (P P' : A -> B -> Prop),
      P2_Env P env env' ->
      (forall a b, P a b -> P' a b) ->
      P2_Env P' env env'.
    Proof.
      intros until P'; intro P_env_env'.
      induction P_env_env'; constructor; eauto.
    Qed.

    Context {Fun_MT : Functor MT}.
    Context {Mon_MT : Monad MT}.
    Context {Fail_MT : FailMonad MT}.

    Section WFValue_Sec.

  (* ============================================== *)
  (* WELL-FORMED VALUES RELATION                     *)
  (* ============================================== *)

      Variable TypContext : Set.

      Record WFValue_i : Set := mk_WFValue_i
        { wfv_S : TypContext;
          wfv_v : Value;
          wfv_T : DType}.

    (** SuperFunctor for Well-Formed Value Relation. **)

      Variable WFV : (WFValue_i -> Prop) -> WFValue_i -> Prop.
      Definition WFValue := iFix WFV.
      Definition WFValueC Sigma V T:= WFValue (mk_WFValue_i Sigma V T).
      Variable funWFV : iFunctor WFV.

      Definition WF_Environment Sigma env env' :=
        P2_Env (WFValueC Sigma) env env'.

    (* Projection doesn't affect WFValue Relation.*)

      Definition WFV_proj1_a_P (i :WFValue_i) :=
        forall a' H, a' = proj1_sig (wfv_v i) ->
          WFValueC (wfv_S i) (exist _ a' H) (wfv_T i).

      Inductive WFV_proj1_a_Name := wfv_proj1_a_name.
      Context {WFV_proj1_a_WFV :
        iPAlgebra WFV_proj1_a_Name WFV_proj1_a_P WFV}.

      Definition WFV_proj1_a :=
        ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_proj1_a_WFV)).

      Definition WFV_proj1_b_P (i :WFValue_i) :=
        forall b' H, b' = proj1_sig (wfv_T i) ->
          WFValueC (wfv_S i) (wfv_v i) (exist _ b' H).

      Inductive WFV_proj1_b_Name := wfv_proj1_b_name.
      Context {WFV_proj1_b_WFV :
        iPAlgebra WFV_proj1_b_Name WFV_proj1_b_P WFV}.

      Definition WFV_proj1_b :=
        ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_proj1_b_WFV)).

      Inductive eval_Soundness_alg_Name := eval_soundness_algname.

      Class ConsExtensionC (TypContext : Set) : Type :=
        { ConsExtension : TypContext -> TypContext -> Prop;
          ConsExtension_id : forall Sigma : TypContext, ConsExtension Sigma Sigma;
          ConsExtension_trans : forall (Sigma Sigma' Sigma'' : TypContext),
            ConsExtension Sigma' Sigma ->
            ConsExtension Sigma'' Sigma' ->
            ConsExtension Sigma'' Sigma
        }.

      Context {TypContextCE : ConsExtensionC TypContext}.

      Definition WFValue_Weaken_P (i : WFValue_i) :=
        forall Sigma', ConsExtension Sigma' (wfv_S i) ->
          WFValueC Sigma' (wfv_v i) (wfv_T i).

      Inductive WFValue_Weaken_Name := wfvalue_weaken_name.

      Context {WFV_Weaken_WFV : iPAlgebra WFValue_Weaken_Name WFValue_Weaken_P WFV}.

      Definition WFV_Weaken := ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_Weaken_WFV)).

  (* ============================================== *)
  (* WELL-FORMED MONADIC VALUES RELATION            *)
  (* ============================================== *)

      Record WFValueM_i : Set := mk_WFValueM_i
        { wfvm_S : TypContext;
          wfvm_v : ME Value;
          wfvm_T : MT DType}.

    (** SuperFunctor for Well-Formed Value Relation. **)

      Variable WFVM : (WFValueM_i -> Prop) -> WFValueM_i -> Prop.
      Definition WFValueM := iFix WFVM.
      Definition WFValueMC Sigma v T:= WFValueM (mk_WFValueM_i Sigma v T).
      Variable funWFVM : iFunctor WFVM.

      Inductive WFValueM_base (A : WFValueM_i -> Prop) : WFValueM_i -> Prop :=
      | WFVM_Return : forall Sigma v (T : DType) (mt : MT DType),
        WFValueC Sigma v T ->
        {mt' : MT {T' : DType | proj1_sig T = proj1_sig T'} &
          fmap (@proj1_sig _ _) mt' = mt} ->
        WFValueM_base A (mk_WFValueM_i Sigma (return_ v) mt)
      | WFVM_Untyped : forall B Sigma me (mt : MT B),
        WFValueM_base A (mk_WFValueM_i Sigma me (mt >> fail)).

      Definition ind_alg_WFVM_base (P : WFValueM_i -> Prop)
        (H_Return : forall Sigma v T mt,
          WFValueC Sigma v T ->
          {mt' : MT {T' : DType | proj1_sig T = proj1_sig T'} &
            fmap (@proj1_sig _ _) mt' = mt} ->
          P (mk_WFValueM_i Sigma (return_ v) mt))
        (H_Untyped : forall B Sigma me mt,
          P (mk_WFValueM_i Sigma me (mt >> fail)))
        (i : WFValueM_i)
        (e : WFValueM_base P i)
        :
        P i :=
        match e in WFValueM_base _ i return P i with
          | WFVM_Return Sigma v T mt WF_v_T WF_mt => H_Return Sigma v T mt WF_v_T WF_mt
          | WFVM_Untyped B Sigma me mt => H_Untyped B Sigma me mt
        end.

      Definition WFVM_base_ifmap
        (A B : WFValueM_i -> Prop)
        (i : WFValueM_i)
        (f : forall i, A i -> B i)
        (wfvm_v : WFValueM_base A i)
        :
        WFValueM_base B i :=
        match wfvm_v in WFValueM_base _ i return WFValueM_base B i with
          | WFVM_Return Sigma v T mt WF_v_T WF_mt => WFVM_Return B Sigma v T mt WF_v_T WF_mt
          | WFVM_Untyped C Sigma me mt => WFVM_Untyped B C Sigma me mt
        end.

      Global Instance iFun_WFVM_base : iFunctor WFValueM_base.
      constructor 1 with (ifmap := WFVM_base_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; auto.
    Defined.

    Lemma WFVM_Return_T : forall A Sigma v T,
      WFValueC Sigma v T ->
      WFValueM_base A (mk_WFValueM_i Sigma (return_ v) (return_ T)).
    Proof.
      intros; constructor 1 with (T := T); auto.
      exists (return_ (exist (fun T' => proj1_sig T = proj1_sig T')
        T (refl_equal (proj1_sig T)))).
      rewrite fmap_m, <- left_unit; reflexivity.
    Qed.

    Lemma WFVM_Untyped_T : forall A Sigma v,
      WFValueM_base A (mk_WFValueM_i Sigma (return_ v) fail).
    Proof.
      simpl; intros.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      intros; constructor 2.
    Qed.

    Definition eval_soundness_P (e : Fix E) (e_UP' : Universal_Property'_fold e) :=
      forall Sigma, WFValueMC Sigma (evalM e) (typeof e).

    Inductive ES_ExpName := es_expname.

    Definition eval_soundness'_P
      (P_bind : Set)
      (E' : Set -> Set)
      (Fun_E' : Functor E')
      (P : UP'_F E -> UP'_F E' -> P_bind -> TypContext -> Prop)
      (pb : P_bind)
      (typeof_rec : UP'_F E' -> typeofR)
      (eval_rec : Exp -> evalMR)
      (typeof_F : Mixin (UP'_F E') E' typeofR)
      (eval_F : Mixin Exp E evalMR)
      (e : (Fix E') * (Fix E))
      (e_UP' : Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e)) :=
      forall
        (eval_rec_proj : forall e, eval_rec e = eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e))))
        (typeof_rec_proj : forall e, typeof_rec e = typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e))))
        Sigma (WF_Gamma : P (exist _ _ (proj2 e_UP')) (exist _ _ (proj1 e_UP')) pb Sigma)
          (IHa : forall pb Sigma (a : (UP'_F E' * Exp))
            (WF_Gamma : P (snd a) (fst a) pb Sigma),
            (WFValueMC Sigma  (eval_F eval_rec (out_t_UP' _ _ (proj1_sig (snd a))))
              (typeof_F typeof_rec (out_t_UP' _ _ (proj1_sig (fst a)))) ->
              WFValueMC Sigma (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig (snd a)))))
              (typeof_rec (fst a)))),
          WFValueMC Sigma (eval_F eval_rec (out_t_UP' _ _ (snd e)))
          (typeof_F typeof_rec (out_t_UP' _ _ (fst e))).

  End WFValue_Sec.

  Section EvalSoundness.

    Variable WFVM : (WFValueM_i unit -> Prop) -> WFValueM_i unit -> Prop.
    Variable funWFVM : iFunctor WFVM.

    Inductive ES'_ExpName := es'_expname.

    Context {WF_MAlg_typeof : WF_MAlgebra Typeof_E}.
    Context {WF_MAlg_eval : WF_MAlgebra evalM_E}.

    Context {eval_soundness_Exp_E : DAlgebra ES_ExpName E E (UP'_SP (eval_soundness_P unit WFVM))}.
    Context {eval_soundness'_Exp_E : forall typeof_rec eval_rec,
      P2Algebra ES'_ExpName E E E
      (UP'_P2 (eval_soundness'_P unit WFVM unit _ _ (fun _ _ _ _ => True) tt typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _)) (f_algebra (FAlgebra := evalM_E _))))}.

    Lemma eval_soundness : forall (e : Exp) Sigma,
      (WFValueMC unit WFVM Sigma (evalM (proj1_sig e)) (typeof (proj1_sig e))).
    Proof.
      intro; rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig e)).
      simpl; unfold typeof, evalM, fold_, mfold, in_t.
      repeat rewrite wf_malgebra; unfold mfold.
      destruct (Ind2 (Ind_Alg := eval_soundness'_Exp_E
        (fun e => typeof (proj1_sig e)) (fun e => evalM (proj1_sig e)))
        _ (proj2_sig e)) as [e' eval_e'].
      unfold eval_soundness'_P in eval_e'.
      intros; eapply eval_e'; intros; auto; try constructor.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig (fst a)) (proj2_sig _)).
      unfold typeof, evalM, mfold; simpl; unfold in_t;
        repeat rewrite wf_malgebra; unfold mfold; apply H; auto.
    Qed.

    Global Instance ConsExtensionUnit : ConsExtensionC unit :=
      { ConsExtension := fun _ _ => True }.
    Proof.
      (* ConsExtension_id *)
      eauto.
      (* ConsExtension_trans *)
      eauto.
    Qed.

  End EvalSoundness.

  Section BindRule.

    Variable TypContext : Set.
    Context {TypContextCE : ConsExtensionC TypContext}.

    Variable WFV : (WFValue_i TypContext -> Prop) -> WFValue_i TypContext -> Prop.
    Variable funWFV : iFunctor WFV.

    Variable WFVM : (WFValueM_i TypContext -> Prop) -> WFValueM_i TypContext -> Prop.
    Variable funWFVM : iFunctor WFVM.

    Inductive wfvm_bind_Name : Set := wfvm_bind_name.

    Definition wfvm_bind_P (i : WFValueM_i TypContext) :=
      forall ke kt
        (kt_proj1_eq : forall T T' : DType,
          proj1_sig T = proj1_sig T' -> fmap (@proj1_sig _ _) (kt T) = fmap (@proj1_sig _ _) (kt T'))
        (WFVM_ke_kt : forall Sigma' v T,
          ConsExtension Sigma' (wfvm_S _ i) ->
          WFValueC _ WFV Sigma' v T ->
          WFValueMC _ WFVM Sigma' (ke v) (kt T)),
        WFValueMC _ WFVM (wfvm_S _ i) (wfvm_v _ i >>= ke) (wfvm_T _ i >>= kt).

    Context {wfvm_bind_alg : iPAlgebra wfvm_bind_Name wfvm_bind_P WFVM}.

    Lemma wfvm_bind Sigma (mv : ME Value) (mT : MT DType)
          (ke : Value -> ME Value) (kt : DType -> MT DType)
          (kt_proj1_eq : forall T T' : DType,
            proj1_sig T = proj1_sig T' -> fmap (@proj1_sig _ _) (kt T) = fmap (@proj1_sig _ _) (kt T'))
          (WFVM_mv_mT : WFValueMC _ WFVM Sigma mv mT)
          (WFVM_ke_kt : forall Sigma' v T,
            ConsExtension Sigma' Sigma ->
            WFValueC _ WFV Sigma' v T -> WFValueMC _ WFVM Sigma' (ke v) (kt T)) :
       WFValueMC _ WFVM Sigma (mv >>= ke) (mT >>= kt).
    Proof.
      eapply (ifold_ WFVM _ (ip_algebra (iPAlgebra := wfvm_bind_alg)) (mk_WFValueM_i _ Sigma mv mT) WFVM_mv_mT);
        eauto.
    Qed.

    Context {MT_eq_dec : forall (A : Set) (mta : MT A),
      {exists a, mta = return_ a} + {mta = fail}}.
    Context {Inj_MT : InjMonad MT}.
    Context {Reasonable_MT : Reasonable_Monad MT}.

    Context {WFV_proj1_b_WFV : iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P _ WFV) WFV}.
    Context {Sub_WFVM_Base'_WFVM : Sub_iFunctor (WFValueM_base _ WFV) WFVM}.

    Lemma wfvm_skip Sigma (me : ME Value) (mt : MT DType) (kt : DType -> MT DType)
         (WFVM_me_kt : forall T, WFValueMC _ WFVM Sigma me (kt T)) :
      WFValueMC _ WFVM Sigma me (mt >>= kt).
    Proof.
      destruct (MT_eq_dec _ mt) as [[T mt_eq] | mt_eq]; subst.
      rewrite <- left_unit.
      apply WFVM_me_kt.
      rewrite bind_fail.
      apply inject_i.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      constructor 2.
    Qed.

    Lemma wfvm_fail : forall Sigma ke,
      WFValueM _ WFVM (mk_WFValueM_i _ Sigma ke fail).
    Proof.
      intros.
      apply inject_i.
      rewrite left_unit with (a := tt) (f := fun _ => fail).
      constructor 2.
    Qed.

    Global Instance wfvm_bind_base' :
      iPAlgebra wfvm_bind_Name wfvm_bind_P (WFValueM_base _ WFV).
    Proof.
      econstructor.
      unfold iAlgebra; intros; apply ind_alg_WFVM_base with (WFV := WFV);
        try assumption; unfold wfvm_bind_P; simpl; intros.
      (* WFVM_Return' *)
      destruct (MT_eq_dec _ mt) as [[T0 mt_eq] | mt_eq]; subst.
      repeat rewrite <- left_unit; eapply WFVM_ke_kt; eauto.
      apply ConsExtension_id.
      destruct H1 as [mt' mt'_eq']; subst.
      destruct (MT_eq_dec _ mt') as [[T' mt'_eq] | mt'_eq]; subst.
      rewrite fmap_return in mt'_eq'.
      apply inj_return in mt'_eq'; subst.
      destruct T'.
      destruct x.
      apply (WFV_proj1_b TypContext WFV _ _ H0); simpl; auto.
      destruct (fmap_exists _ _ _ _ _ mt'_eq') as [[T' T_eq] T'_eq].
      simpl in *; subst; auto.
      destruct T0.
      apply (WFV_proj1_b TypContext WFV _ _ H0); simpl; auto.
      rewrite bind_fail.
      apply wfvm_fail.
      (* WFVM_Untyped' *)
      destruct (MT_eq_dec _ mt) as [[T0 mt_eq] | mt_eq]; subst.
      unfold wbind; rewrite <- left_unit.
      rewrite bind_fail.
      apply wfvm_fail.
      unfold wbind.
      rewrite <- associativity.
      rewrite bind_fail.
      apply wfvm_fail.
    Qed.

  End BindRule.

End Names.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
