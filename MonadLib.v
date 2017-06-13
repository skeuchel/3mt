(* Set Implicit Arguments. *)
Require Import FunctionalExtensionality.
Require Import Functors.
Require Import Coq.Program.Basics.

(***********************************************************************
 ***********************************************************************

   INFRASTRUCTURE

 ***********************************************************************
 ***********************************************************************)


(*-----------------------------------------------------------------------
  MONADS
  -----------------------------------------------------------------------*)

Class Monad (M : Set -> Set) `{functor : Functor M} := {
  return_: forall {A: Set}, A -> M A;
  bind: forall {A: Set}, M A -> forall {B : Set}, (A -> M B) -> M B;
  (* laws *)
  right_unit: forall {A : Set} (a : M A), a = bind a (return_);
  left_unit: forall {A : Set} (a: A) {B : Set} (f: A -> M B),
             f a = bind (return_ a) f;
  associativity: forall (A : Set) (ma: M A) (B : Set) f (C : Set) (g: B -> M C),
                 bind ma (fun x => bind (f x) g) = bind (bind ma f) g;
  fmap_m: forall (A B: Set) (f: A -> B) (m: M A),
    fmap f m = bind m (fun v => return_ (f v))
}.

Lemma fmap_return {M} `{Monad M} {A B: Set} (f: A -> B) (v: A):
  fmap f (return_ v) = return_ (f v).
Proof.
  rewrite fmap_m.
  rewrite <- left_unit.
  reflexivity.
Qed.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).

(* We exploit injectivity of return in a lot of our inversion lemmas. *)
Class InjMonad (M : Set -> Set) `{Mon_M : Monad M} := {
  inj_return : forall {A : Set} (a b : A), return_ a = return_ b -> a = b
}.

Section monadic_functions.

 Definition wbind {M} `{Monad M} {A : Set} (ma: M A) {B: Set} (mb: M B) :=
 ma >>= fun _ => mb.

 Definition liftM {M} `{Monad M} {A B : Set} (f: A -> B) (ma: M A): M B :=
 ma >>= (fun a => return_ (f a)).

 Definition join {M} `{Monad M} {A: Set} (mma: M (M A)): M A :=
 mma >>= (fun ma => ma).

End monadic_functions.

Notation "a >> f" := (wbind a f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

Lemma rewrite_do : forall (M : Set -> Set)
  {Fun_M : Functor M}
  {Monad_M : Monad M},
  forall (A B : Set) (n : M A) (m m' : A -> M B),
    m = m' -> (do o <- n; m o) = (do o <- n; m' o).
intros; rewrite H; reflexivity.
Qed.

Lemma eq_bind_fmap : forall M `{Monad M} (A B C : Set)
  (ma : M A) (f : A -> M B) (f' : C -> M B) (g : A -> C),
  (forall a, f a = f' (g a)) ->
  do x <- ma; f x = do x <- fmap g ma; f' x.
  intros; rewrite fmap_m; rewrite <- associativity.
  apply f_equal; apply functional_extensionality; intros.
  rewrite H0; rewrite <- left_unit; auto.
Qed.

(* Need to assume eta-equality (assumed in FunctionalExtensionality.v)*)
Definition Eta : forall A (B: A -> Set) (f: forall a, B a), f = fun a => f a :=
  @eta_expansion_dep.

(* Rules for building ornamented monads. *)
Lemma return_orn M `{Monad M} : forall (A : Set) (PA : A -> Prop) (a : A),
  PA a -> {mt' : M {a | PA a} & fmap (@proj1_sig _ _) mt' = return_ a}.
Proof.
  intros A PA a PA_a; exists (return_ (exist (fun a => PA a) _ PA_a));
    simpl; rewrite fmap_m; rewrite <- left_unit; reflexivity.
Qed.

Lemma bind_orn M `{Monad M} : forall (A B : Set)
  (PA : A -> Prop) (PB : B -> Prop)
  (mt : M {a | PA a})
  (k : A -> M B)
  (k' : forall a : {a | PA a},
    {mb : M {b | PB b} &
      fmap (@proj1_sig _ _) mb = k (proj1_sig a)}),
  {mt' : M {b | PB b} &
    fmap (@proj1_sig _ _) mt' = fmap (@proj1_sig _ _) mt >>= k}.
Proof.
  intros.
  exists (mt >>= fun T => (projT1 (k' T))).
  rewrite (right_unit (do T <- mt; projT1 (k' T))),
    <- associativity, (Eta _ _ (return_ (M := M))),
    fmap_m, <- associativity.
  rewrite rewrite_do with
    (m := fun T => do v0 <- do a <- projT1 (k' T); return_ a; return_ (proj1_sig v0))
    (m' := fun T => k (proj1_sig T)).
  rewrite eq_bind_fmap with (g := @proj1_sig _ _) (f' := k); auto.
  apply functional_extensionality_dep; intros.
  rewrite <- associativity,
    rewrite_do with (m := fun x0 => do v0 <- return_ x0; return_ (proj1_sig v0))
    (m' := fun v0 => return_ (proj1_sig v0)).
  rewrite <- fmap_m; auto.
  destruct (k' x) as [mb mb_eq]; simpl; auto.
  apply functional_extensionality_dep; intros; rewrite <- left_unit;
    auto.
Qed.

Lemma bind_orn' M `{Monad M} : forall (A B : Set)
  (PB : B -> Prop)
  (mt : M A)
  (k : A -> M B)
  (k' : forall a : A, {mb : M {b | PB b} &
    fmap (@proj1_sig _ _) mb = k a}),
  {mt' : M {b | PB b} &
    fmap (@proj1_sig _ _) mt' = mt >>= k}.
Proof.
  intros.
  exists (mt >>= fun T => (projT1 (k' T))).
  rewrite (right_unit (do T <- mt; projT1 (k' T))),
    <- associativity, (Eta _ _ (return_ (M := M))),
    fmap_m, <- associativity.
  rewrite rewrite_do with
    (m := fun T => do v0 <- do a <- projT1 (k' T); return_ a; return_ (proj1_sig v0))
    (m' := fun T => k T).
  rewrite (Eta _ _ k); auto.
  apply functional_extensionality_dep; intros.
  rewrite <- associativity,
    rewrite_do with (m := fun x0 => do v0 <- return_ x0; return_ (proj1_sig v0))
    (m' := fun v0 => return_ (proj1_sig v0)).
  rewrite <- fmap_m; auto.
  destruct (k' x) as [mb mb_eq]; simpl; auto.
  apply functional_extensionality_dep; intros; rewrite <- left_unit;
    auto.
Qed.

Class Reasonable_Monad M `{Monad_M : Monad M} := (* This attempts to capture the parametericity *)
  { fmap_exists : forall (A B : Set)             (* of fmap. *)
    (ma : M A) (f : A -> B) (b : B),
    fmap f ma = return_ b ->
    exists a, f a = b}.

(*-----------------------------------------------------------------------
  MONAD TRANSFORMERS
  -----------------------------------------------------------------------*)

(**** Monad Transformers ****)

Class Transformer (T : (Set -> Set) -> Set -> Set) := {
  lift: forall {A} {M} `{mm: Monad M}, M A -> T M A;
  transformed_functor:
    forall {M} `{mm: Monad M}, @Functor (T M);
  transformed_monad:
    forall {M} `{mm: Monad M}, @Monad (T M) transformed_functor;
  lift_return:
    forall (A: Set) (M: Set -> Set) `{mm: Monad M} (x: A),
      lift (return_ x) = return_ x;
  lift_bind:
    forall A B M `{mm: Monad M} (m: M A) (f: A -> M B),
      lift (m >>= (fun x => f x)) = lift m >>= (fun x => lift (f x))
}.

  (* The composition of 2 transformers is a transformer *)

Instance TransformerTransformer (T1 T2 : (Set -> Set) -> Set -> Set)
  {Transformer_T1 : Transformer T1} {Transformer_T2 : Transformer T2} :
  Transformer (fun M => T1 (T2 M)).
Proof.
  econstructor 1 with (lift := fun A M Fun_M Monad_M MA =>
    @lift T1 Transformer_T1 _ _
    (@transformed_functor T2 Transformer_T2 _ _ Monad_M)
    (@transformed_monad T2 Transformer_T2 _ _ Monad_M)
    (@lift T2 Transformer_T2 A M Fun_M Monad_M MA))
  (transformed_functor := fun M Fun_M Monad_M =>
    @transformed_functor T1 Transformer_T1 _
    (@transformed_functor T2 Transformer_T2 M Fun_M Monad_M)
    (@transformed_monad T2 Transformer_T2 M Fun_M Monad_M))
  (transformed_monad := fun M Fun_M Monad_M =>
    @transformed_monad T1 Transformer_T1 _
    (@transformed_functor T2 Transformer_T2 M Fun_M Monad_M)
    (@transformed_monad T2 Transformer_T2 M Fun_M Monad_M)).
  (* lift_return *)
  intros; simpl; repeat rewrite lift_return; reflexivity.
  (* lift_bind *)
  intros; simpl; repeat rewrite lift_bind; reflexivity.
Defined.

(***********************************************************************
 ***********************************************************************

   INSTANCES

 ***********************************************************************
 ***********************************************************************)

(*-----------------------------------------------------------------------
  MONAD PAIRS (FOR REASONING)
  -----------------------------------------------------------------------*)

Definition Pair (F G : Set -> Set) (A : Set) : Set := prod (F A) (G A).

Global Instance FunctorPair {F G : Set -> Set} `{Functor F} `{Functor G} :
  Functor (Pair F G) := {|
    fmap := fun A B h x =>
      match x with
        (f, g) => (fmap h f, fmap h g)
      end
|}.
Proof.
  (* fmap_fusion *)
  intros; destruct a; simpl.
  repeat rewrite fmap_fusion; reflexivity.
  (* fmap_id *)
  intros; destruct a; simpl.
  repeat rewrite fmap_id; reflexivity.
Defined.

Global Instance MonadPair {F G : Set -> Set} `{Monad F} `{Monad G}: Monad (Pair F G) :=
{| return_ := fun A x => (return_ x, return_ x);
   bind := fun A x B f => (bind (fst x) (fun a => fst (f a)), bind (snd x) (fun a => snd (f a)))
|}.
(* Checking the 3 laws *)
 (* right_unit *)
 intros; destruct a; simpl.
 repeat rewrite (functional_extensionality (fun a : A => return_ a) return_); auto.
 repeat rewrite <- right_unit.
 reflexivity.
 (* left_unit *)
 intros; simpl.
 repeat rewrite <- left_unit; simpl.
 destruct (f a); reflexivity.
 (* associativity *)
 intros; simpl.
 repeat rewrite associativity; reflexivity.
 (* fmap_m *)
 intros; destruct m; unfold fmap; simpl.
 repeat rewrite fmap_m; reflexivity.
Defined.

(*-----------------------------------------------------------------------
  IDENTITY MONADS
  -----------------------------------------------------------------------*)


(**** Identity monad ****)

Definition Id (A : Set) := A.

Global Instance idFunctor : Functor Id := {|
  fmap := fun A B f x => f x
|}.
(* Checking the fusion law *)
  intros.
  reflexivity.
  (* fmap id *)
  intros; reflexivity.
Defined.

Global Instance idMonad: Monad Id :=
{| return_ := fun _ x => x;
   bind := fun A x B f => f x
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 intros; reflexivity.
 (* unit_right *)
 intros; reflexivity.
 (* associativity *)
 intros; reflexivity.
 (* fmap_m *)
 intros; unfold fmap; simpl; reflexivity.
Defined.

Global Instance Reasonable_Id : Reasonable_Monad Id.
Proof.
  constructor; simpl; intros; eexists ma; auto.
Qed.

Global Instance inj_idMonad : InjMonad Id.
  constructor; simpl; intros; auto.
Qed.

Section IdT_Section.
(**** Identity transformer ****)

Definition IdT (M: Set -> Set) (A : Set) := M A.

Instance idTFunctor M `{FM: Functor M} : Functor (IdT M) :=
  {|
     fmap := fun A B f x => @fmap M FM A B f x
  |}.
  (* fusion law *)
  intros; rewrite fmap_fusion; reflexivity.
  (* fmap id *)
  intros; rewrite fmap_id ; reflexivity.
Defined.

Instance idTMonad M {functorM : Functor M} {monadM : Monad M} : Monad (IdT M) :=
{| return_ := fun A x => @return_ M functorM monadM A x;
   bind := fun A (m : M A) B f => m >>= f
|}.
(* Check 3 monad laws *)
  (* right_unit *)
  intros. unfold IdT in a. simpl.
  rewrite <- (eta_expansion_dep ( @return_ M functorM monadM A)).
  rewrite <- right_unit.
  reflexivity.
  (* left_unit *)
  intros. unfold IdT in f.
  rewrite <- left_unit.
  reflexivity.
  (* bind_associativity *)
  intros.
  unfold IdT in ma, f, g.
  rewrite associativity.
  reflexivity.
  (* fmap_m *)
  intros. rewrite <- fmap_m. reflexivity.
Defined.

Instance inj_idTMonad M `{InjMonad M} : InjMonad (IdT M).
  constructor; simpl; intros; auto.
  apply inj_return.
  assumption.
Qed.

Instance idTTransformer : Transformer IdT :=
  {|
     lift := fun A M FunctorM MonadM MA => MA
  |}.
(* Checking the 2 lift laws *)
  (* lift_return *)
  intros. reflexivity.
  (* lift_bind *)
  intros. reflexivity.
Defined.

End IdT_Section.

(*-----------------------------------------------------------------------
  Failure MONADS
  -----------------------------------------------------------------------*)

(**** FailMonad Class ****)

Class FailMonad (M : Set -> Set) `{monad: Monad M} := {
  fail: forall {A: Set}, M A;
  bind_fail:
    forall (A B : Set) (f : A -> M B),
      fail >>= f = fail;
  fmap_fail :
    forall (A B : Set) (f : A -> B),
      fmap f fail = fail
}.

Lemma FailMonad_Disc (M : Set -> Set) `{FailMonad M} {Reasonable_M : Reasonable_Monad M} :
  forall (A B : Set) (a : A) (mb : M B), return_ a <> mb >> fail.
Proof.
  intros.
  assert {mb' : M {a' : A | False} &
    fmap (@proj1_sig _ _) mb' = do x <- mb; fail} as mb' by
  (apply bind_orn'; intros; exists fail; rewrite fmap_fail; auto).
  destruct mb' as [mb' mb'_eq].
  unfold not; intros.
  unfold wbind in H0; rewrite <- H0 in mb'_eq.
  apply fmap_exists in mb'_eq; destruct mb'_eq as [[x []] _].
Qed.

Lemma FailMonad_Disc' (M : Set -> Set) `{FailMonad M} {Reasonable_M : Reasonable_Monad M} :
  forall (A : Set) (a : A), return_ a <> fail.
Proof.
  intros; rewrite <- bind_fail at 1.
  apply FailMonad_Disc with (M := M) (a := a) (mb := fail (A := A)); auto.
Qed.

Ltac failmonaddisc :=
  repeat match goal with
    | [ H : context[bind (return_ _) _]  |- _ ] => rewrite <- left_unit in H
    | [ H : context[bind fail _]         |- _ ] => rewrite bind_fail in H
    | [ H : context[fmap _ fail]         |- _ ] => rewrite fmap_fail in H
    | [ H : return_ _ = fail             |- _ ] => apply FailMonad_Disc' in H; tauto
    | [ H : fail = return_ _             |- _ ] => apply sym_eq, FailMonad_Disc' in H; tauto
  end.

(*-----------------------------------------------------------------------
  EXCEPTION MONADS
  -----------------------------------------------------------------------*)

(**** Exception Class ****)

Class Exception (M : Set -> Set) (E : Set) `{monad: Monad M} := {
  throw: forall {A: Set}, E -> M A;
  catch: forall {A: Set}, M A -> (E -> M A) -> M A;
  catch_throw:
    forall A (m : M A),
      catch m (@throw _) = m;
  catch_throw':
    forall A (h : E -> M A) e,
      catch (@throw _ e) h = h e;
  bind_throw:
    forall (A B : Set) (e : E) (f : A -> M B),
      (@throw A e) >>= f = @throw B e;
  catch_return:
    forall (A : Set) (x: A) (h: E -> M A),
       catch (return_ x) h = return_ x;
  fmap_catch :
    forall (A B : Set) (m : M A) (h : E -> M A)
      (f : A -> B), fmap f (catch m h) = catch (fmap f m) (fun e => fmap f (h e));
  fmap_throw :
    forall (A B : Set) (e : E)
      (f : A -> B), fmap f (throw e) = throw e;
  throwsnot1:
    forall (A: Set) (m : M A),
    (forall (B : Set) (f : A -> M B) h, catch (m >>= f) h = m >>= f) ->
      (forall h, catch m h = m);
  throwsnot2:
    forall (A B: Set) (f: A -> M B),
      (forall (m : M A) h, (forall h', catch m h' = m) ->
        catch (m >>= f) h = m >>= f) ->
      (forall h x, catch (f x) h = f x)
}.

Lemma Exception_Disc (M : Set -> Set) (E : Set) `{Exception M E} {Reasonable_M : Reasonable_Monad M} :
  forall (A B : Set) (a : A) (e : E) (mb : M B), return_ a <> mb >> throw e.
Proof.
  intros.
  assert {mb' : M {a' : A | False} &
    fmap (@proj1_sig _ _) mb' = do x <- mb; throw e} as mb' by
  (apply bind_orn'; intros; exists (throw e); rewrite fmap_throw; auto).
  destruct mb' as [mb' mb'_eq].
  unfold not; intros.
  unfold wbind in H0; rewrite <- H0 in mb'_eq.
  apply fmap_exists in mb'_eq; destruct mb'_eq as [[x []] _].
Qed.

Definition throwsnot {E} {M} `{Exception M E} {A} (m : M A) :=
  (forall h, catch m h = m).

(**** Option monad ****)

Definition MaybeT (M : Set -> Set) (A : Set) := M (option A).

Definition Maybe := MaybeT Id.

Instance maybeTFunctor M {functorM : Functor M} : Functor (MaybeT M) := {|
  fmap :=
    fun A B f =>
      fmap  (fun x =>
                match x with
                   None   => None
                 | Some a => Some (f a)
                end)
|}.
(* Checking the fusion law *)
  intros.
  rewrite fmap_fusion.
  apply equal_f.
  apply f_equal.
  apply functional_extensionality.
  intro x.
  case x.
    intros; reflexivity.
    reflexivity.
  (* fmap id *)
  intros.
  assert ((fun x : option A =>
   match x with
   | Some a0 => Some (id a0)
   | None => None
   end) = id ).
    apply functional_extensionality; intro.
    unfold id. destruct x; reflexivity.
  rewrite H. rewrite fmap_id; reflexivity.
Defined.

Instance maybeMonad M {functorM : Functor M} {monadM : Monad M} :
Monad (functor := maybeTFunctor M (functorM := functorM)) (MaybeT M) :=
{| return_ := fun A x => return_ (Some x);
   bind    :=
     fun A (m : M (option A)) B f =>
        m >>= (fun x => match x with
                           None   => return_ None
                         | Some a => f a
                        end)
|}.

(* right_unit *)
  Require Setoid.
  intros.
  unfold MaybeT in a.
  rewrite right_unit at 1.
  assert (return_ (A := option A) = fun (x : option A) => return_ x).
  apply functional_extensionality. intros; reflexivity.
  rewrite H at 1.
  apply f_equal.
  apply functional_extensionality.
  intro x. case x; reflexivity.
(* left_unit *)
  intros. unfold MaybeT in f.
  rewrite <- left_unit. reflexivity.
(* associativity *)
  unfold MaybeT.
  intros.
  rewrite <- associativity.
  apply f_equal. apply functional_extensionality.
  intro x; case x.
  intros. reflexivity.
  rewrite <- left_unit. reflexivity.
  (* fmap_m *)
  intros. unfold fmap.  simpl. rewrite -> fmap_m.
  assert (forall v, (return_ match v with
                   | Some a => Some (f a)
                   | None => None
                   end ) = (match v with
| Some a => return_ (Some (f a))
| None => return_ None
end)).
    intro.
    destruct v; reflexivity.
  assert ((fun v => return_ match v with
                   | Some a => Some (f a)
                   | None => None
                   end) = (fun x => match x with
| Some a => return_ (Some (f a))
| None => return_ None
end)).
  apply functional_extensionality.
  intro.
    rewrite H. reflexivity.
  rewrite H0.
  reflexivity.
Defined.

Instance inj_maybeMonad M `{InjMonad M} : InjMonad (MaybeT M).
  constructor; simpl; intros; auto.
  generalize (inj_return (Some a) (Some b) H0); congruence.
Qed.

Instance MaybeT_FailMonad M `{Monad M} :
  FailMonad (MaybeT M) :=
{|
   fail := fun A => return_ None
|}.
Proof.
  (* fail_bind *)
  intros.
  simpl. rewrite <- left_unit. reflexivity.
  (* fmap_fail *)
  simpl; intros.
  rewrite fmap_m, <- left_unit; auto.
Defined.

Instance MaybeT_Reasonable_Monad M `{ReasonableM : Reasonable_Monad M} :
  Reasonable_Monad (MaybeT M).
Proof.
  (* fmap_exists *)
  constructor; simpl; intros.
  destruct (fmap_exists _ _ _ _ _ H).
  destruct x; [exists a; congruence | discriminate].
Qed.

Instance MaybeT_Exception M
  {functorM : Functor M}
  {monadM : Monad M}
  : Exception (MaybeT M) unit :=
{|
   throw := fun A e => return_ None;
   catch := fun A (m : M (option A)) h =>
     bind m (fun x => match x with None => h tt | Some a => return_ (Some a) end)
|}.
(* Proof of catch_throw law *)
  unfold MaybeT.
  intros.
  rewrite right_unit.
  assert (return_ (A := option A) = fun (x : option A) => return_ x).
  apply functional_extensionality. intros; reflexivity.
  rewrite H at 1. apply f_equal. apply functional_extensionality.
  intros.
  case x.
  auto.
  auto.
(* Proof of catch_throw' law *)
  unfold MaybeT.
  intros.
  rewrite <- left_unit; destruct e; reflexivity.
(* Proof of bind_throw law*)
  unfold MaybeT.
  intros.
  simpl.
  erewrite <- left_unit.
  reflexivity.
(* catch_return *)
  simpl.
  intros.
  rewrite <- (@left_unit M functorM monadM).
  reflexivity.
  (* fmap catch *)
  simpl; intros.
  rewrite fmap_m; rewrite <- associativity.
  rewrite fmap_m; rewrite <- associativity.
  apply f_equal; apply functional_extensionality; intro.
  destruct x; repeat rewrite <- left_unit; auto.
  rewrite fmap_m; auto.
  (* fmap throw *)
  simpl; intros; rewrite fmap_return; auto.
(* throwsnot 1 *)
  intros.
  rewrite (@right_unit (MaybeT M) _ _ (A) m).
  exact (H (A) (return_) h).
(* throwsnot 2 *)
  intros.
  rewrite (@left_unit (MaybeT M) _ _ _ x).
  apply (H (return_ x) h).
  intros; simpl; rewrite <- left_unit; reflexivity.
Defined.

(**** Exc monad ****)

Definition ExcT (X : Set) (M : Set -> Set) (A : Set) := M (sum X A).

Definition Exc (X : Set) (A : Set) := ExcT X Id A.

Instance excTFunctor X M {functorM : Functor M} : Functor (ExcT X M) :=
  {| fmap := fun _ _ f e =>
              fmap (fun s => match s with
                     | inl x => inl _ x
                     | inr a => inr _ (f a)
                     end) e
   |}.
   (* fmap fusion *)
   intros. rewrite fmap_fusion.
   assert ((fun e : X + A =>
   match match e with
         | inl x => inl B x
         | inr a0 => inr X (f a0)
         end with
   | inl x => inl C x
   | inr a0 => inr X (g a0)
   end) = (fun s : X + A =>
   match s with
   | inl x => inl C x
   | inr a0 => inr X (g (f a0))
   end)).
    apply functional_extensionality; intro; destruct x; reflexivity.
  rewrite H. reflexivity.
  (* fmap id *)
  unfold id. intros.
  assert ((fun s : X + A => match s with
                    | inl x => inl A x
                    | inr a0 => inr X a0
                    end) = id).
    apply functional_extensionality; intro; destruct x; reflexivity.
  rewrite H. rewrite fmap_id. reflexivity.
  Defined.

Instance excMonad X M {functorM : Functor M} {monadM : Monad M} : Monad (ExcT X M) :=
  {| return_ := fun A a => return_ (inr X a);

     bind := fun A m B f =>
              @bind M _ _ (sum X A) m (sum X B) (fun a =>
                        match a with
                         | inl x  =>  return_ (inl B x)
                         | inr y  =>  f y
                        end)
   |}.
Proof.
  (* left unit *)
  intros.
  assert ((fun a0 => match a0 with
                       |  inl x => return_ (inl A x)
                       | inr y => return_ (inr X y)
                     end) = return_).
  apply functional_extensionality; intro s; destruct s; reflexivity.
  rewrite H. rewrite <- right_unit. reflexivity.
  (* right unit *)
  intros. rewrite <- left_unit. reflexivity.
  (* associativity *)
  intros.
  rewrite <- associativity.
  assert ((fun (a : sum X A) =>
    match a with
      | inl x => return_ (inl C x)
      | inr y =>
        @bind M _ _ _ (f y) _ (fun (a0 : sum X B) =>
          match a0 with
            | inl x => return_ (inl C x)
            | inr y0 => g y0
          end)
    end) = (fun (x : sum X A) => do a <- match x with
                                           | inl x0 => return_ (inl B x0)
                                           | inr y => f y
                                         end; match a with
                                                | inl x0 => return_ (inl C x0)
                                                | inr y => g y
                                              end)).
  apply functional_extensionality; intro.
  destruct x.
  rewrite <- left_unit. reflexivity.
  reflexivity.
  rewrite H. reflexivity.
  (* fmap_m *)
  intros. unfold fmap. simpl.
  rewrite fmap_m.
  assert ((fun v => return_ match v with
                   | inl x => inl B x
                   | inr a => inr X (f a)
                   end) = (fun a => match a with
| inl x => return_ (inl B x)
| inr y => return_ (inr X (f y))
end)).
    apply functional_extensionality. intro.
    destruct x ; reflexivity.
  rewrite H.
  reflexivity.
Defined.

Instance inj_excMonad X M `{InjMonad M} : InjMonad (ExcT X M).
Proof.
  constructor; simpl; intros.
  eapply (inj_return (inr X a)) in H0; congruence.
Qed.

Instance excT_Reasonable_Monad X M
  {functorM : Functor M}
  {monadM : Monad M}
  {ReasonableM : Reasonable_Monad M}
  : Reasonable_Monad (ExcT X M).
Proof.
  (* fmap_exists *)
  constructor; simpl; intros.
  destruct (fmap_exists _ _ _ _ _ H).
  destruct x; [discriminate | exists a; congruence].
Qed.

Instance excTransformer X : Transformer (ExcT X) :=
  {| lift :=
       fun A M Fun_M MonadM ma =>
         bind ma (fun x => return_ (inr X x))
  |}.
Proof.
  (* lift return *)
  intros. rewrite <- left_unit. unfold return_ at 2.
  simpl. reflexivity.
  (* lift bind *)
  simpl; intros.
  repeat rewrite <- associativity.
  cut ((fun x => do x0 <- f x; return_ (inr X x0)) = fun x =>
    do a <- return_ (inr X x);
   match a with
   | inr y => do x0 <- f y; return_ (inr X x0)
   | inl x0 => return_ (inl B x0)
   end).
  intros.
  rewrite H at 1; reflexivity.
  apply functional_extensionality; intros.
  rewrite <- left_unit; reflexivity.
Defined.

Instance excException X M
  {functorM : Functor M}
  {monadM : Monad M}
  : Exception (ExcT X M) X :=
{|
   throw := fun A e => return_ (inl A e);
   catch := fun A (m : M (sum X A)) h =>
     bind m (fun x => match x with (inl e) => h e | inr a => return_ (inr X a) end)
|}.
(* Proof of catch_throw law *)
  unfold ExcT.
  intros.
  rewrite right_unit.
  assert (return_ (A := sum X A) = fun (x : sum X A) => return_ x).
  apply functional_extensionality. intros; reflexivity.
  rewrite H at 1. apply f_equal. apply functional_extensionality.
  intros.
  case x.
  auto.
  auto.
(* Proof of catch_throw' law *)
  unfold ExcT.
  intros.
  rewrite <- left_unit; auto.
(* Proof of bind_throw law*)
  unfold ExcT.
  intros.
  simpl.
  erewrite <- left_unit.
  reflexivity.
(* catch_return *)
  simpl.
  intros.
  rewrite <- (@left_unit M functorM monadM).
  reflexivity.
(* fmap_catch *)
  simpl; intros; repeat rewrite fmap_m, <- associativity.
  apply f_equal; apply functional_extensionality; intros.
  rewrite <- left_unit; destruct x; simpl.
  rewrite fmap_m; auto.
  rewrite <- left_unit; auto.
(* fmap_bind *)
  simpl; intros; rewrite fmap_return; auto.
(* throwsnot1 *)
  intros.
  rewrite (@right_unit (ExcT X M) _ _ (A) m).
  exact (H (A) (return_) h).
(* throwsnot2 *)
  intros.
  rewrite (@left_unit (ExcT X M) _ _ _ x).
  apply (H (return_ x) h).
  intros; simpl; rewrite <- left_unit; reflexivity.
Defined.

(*-----------------------------------------------------------------------
  PRODUCT MONADS
  -----------------------------------------------------------------------*)

Definition Product (M N : Set -> Set) (A : Set) := prod (M A) (N A).

Instance Product_Functor (M N : Set -> Set) `{Functor M} `{Functor N} :
  Functor (Product M N) :=
  {fmap A B f a := (fmap f (fst a), fmap f (snd a))}.
Proof.
   (*fmap fusion *)
  intros; destruct a; simpl; repeat rewrite fmap_fusion; auto.
  (*fmap id *)
  intros; destruct a; simpl; repeat rewrite fmap_id; auto.
Defined.

Instance Product_Monad (M N : Set -> Set) `{Monad M} `{Monad N} :
  Monad (Product M N) :=
  {return_ A a := (return_ a, return_ a);
    bind A mna B k := (bind (fst mna) (fun a => fst (k a)),
                       bind (snd mna) (fun a => snd (k a)))}.
Proof.
(* right unit *)
  intros; destruct a; simpl.
  rewrite right_unit with (a := m) at 1.
  rewrite right_unit with (a := n) at 1.
  reflexivity.
(* left unit *)
  simpl; intros.
  repeat rewrite <- (left_unit a); destruct (f a); reflexivity.
(* associativity *)
  intros; simpl; repeat rewrite <- associativity; auto.
(* fmap_m *)
  intros; destruct m; simpl; repeat rewrite fmap_m; auto.
Defined.


(*-----------------------------------------------------------------------
  WRITER MONADS
  -----------------------------------------------------------------------*)


(**** Monoid Class ****)

Class Monoid (A : Set) := {
  munit: A;
  mappend: A -> A -> A;
  monoid_left :
    forall x : A,
      mappend munit x = x;
  monoid_right :
    forall x : A,
      mappend x munit = x;
  monoid_assoc :
    forall (x y z : A),
      mappend (mappend x y) z = mappend x (mappend y z)
}.

(**** MonadPlus Class ****)

Class MonadPlus (M : Set -> Set) `{Monad M} := {
  monoid_A :> forall A, Monoid (M A);
  left_zero : forall (A B : Set) (k : A -> M B), (munit >>= k) = munit;
  left_dist : forall (A B : Set) (a b : M A) (k : A -> M B),
    (mappend a b) >>= k = mappend (a >>= k) (b >>= k)}.

Require Import List.

Definition ListT (M : Set -> Set) (A : Set) := M (list A).

Instance ListT_Functor M `{Functor_M : Functor M} : Functor (ListT M) :=
  {fmap := fun (A B : Set) (f : A -> B) => fmap (map f)}.
Proof.
(* fmap_fusion *)
  simpl; intros; rewrite fmap_fusion.
  apply (@f_equal _ _ (fun b : list A -> list C => fmap b a)).
  apply functional_extensionality; intros b; induction b;
    simpl; congruence.
  (* fmap_id*)
  simpl; intros.
  assert (map (fun x : A => x) = id) by
    (apply functional_extensionality; intros; rewrite map_id; auto).
  unfold id; rewrite H; rewrite fmap_id; auto.
Defined.

Definition sequence M `{Monad M} {A : Set} (ms : list (M A)) : M (list A) :=
  fold_right (fun m m' => do x <- m; do x' <- m'; return_ (x :: x')) (return_ nil) ms.

Definition mapM M `{Monad M} {A B : Set} (f : A -> M B) (la : list A) : M (list B) :=
  sequence M (map f la).

(* Instance List_Monad M `{Monad_M : Monad M} : Monad (functor := ListT_Functor M) (ListT M) :=
  {return_ := fun (A : Set) (a : A) => (return_ (cons a nil));
  bind := fun (A : Set) (la : ListT M A) (B : Set)
    (k : A -> ListT M B) =>
      bind la (M := M) ( fun a =>
      do b <- mapM M k a;
      return_ (fold_right (@app _) nil b))}.
      Proof.
(* left_unit *)
   unfold ListT.
   intros; rewrite (right_unit a) at 1.
   apply f_equal; apply functional_extensionality; intros.
   induction x; simpl.
   unfold mapM, sequence; simpl; rewrite <- left_unit; auto.
   unfold mapM, sequence; simpl; rewrite <- left_unit.
   repeat rewrite <- associativity.
   simpl.
   unfold mapM, sequence in IHx.
Abort. *)

Instance List_Monoid : forall A : Set, Monoid (list A) :=
  {munit := nil;
  mappend := @app A}.
Proof.
  (* monoid_left *)
  simpl; auto.
  (* monoid_right *)
  intros; rewrite app_nil_r; auto.
  (* fmap_id*)
  intros; rewrite app_assoc; auto.
Defined.

(**** Writer Monad Class ****)

Class WriterM (M : Set -> Set) (S : Set) `{Monoid S} `{Monad M} := {
  tell: S -> M unit;
  listen: forall {A : Set}, M A -> M (prod A S);
  tell_tell:
    forall m1 m2,
      tell m1 >> tell m2 = tell (mappend m1 m2);
  tell_munit:
      tell munit = return_ tt;
  listen_tell:
    forall m,
      listen (tell m) = tell m >> return_ (pair tt m);
  listen_return:
    forall (A : Set) (x:A),
      listen (return_ x) = return_ (pair x munit);
  listen_bind:
    forall (A B : Set) (m: M A) (f: A -> M B),
      listen (m >>= f) =
        listen m >>=
          (fun p1 =>
             let (x, m1) := p1
             in listen (f x) >>=
                  ( fun p2 =>
                      let (y, m2) := p2
                      in return_ (pair y (mappend m1 m2))
                  )
          );
  listen_listen:
    forall (A: Set) (m:M A),
      listen (listen m) =
      listen m >>= (fun p => let (x,w) := p in return_ ((x,w),w))
}.


(**** Writer Transformer ****)

Definition WriterT (S : Set) (M : Set -> Set) (A : Set) := M (prod A S).

Definition Writer (S A : Set) := WriterT S Id A.

Instance writerTFunctor S M {functorM : Functor M} : Functor (WriterT S M) := {|
  fmap := fun A B f => fmap (fun x => match x with pair x y => pair (f x) y end)
|}.
(* Checking the fusion law *)
  unfold WriterT.
  intros. rewrite fmap_fusion.
  apply equal_f.
  apply f_equal.
  apply functional_extensionality.
  intros; destruct x; reflexivity.
  (* fmap id *)
  intros.
  assert ((fun x : A * S => let (x0, y) := x in (id x0, y)) = id).
    apply functional_extensionality; intro. unfold id.
    destruct x; reflexivity.
  rewrite H. rewrite fmap_id; reflexivity.
Defined.

Instance writerMonad (S : Set) M {monoid : Monoid S} {functorM : Functor M} {monadM : Monad M} : Monad (WriterT S M) :=
{| return_ := fun A x => return_ (x, munit);
   bind := fun A (m : M (prod A S)) B (f : A -> M (prod B S)) =>
     m >>= (fun m' =>
       let (x,s1) := m' in
         f x >>= (fun fx =>
           let (y, s2) := fx in
             return_ (y, mappend s1 s2)))
|}.
Proof.
(* left_unit *)
  unfold WriterT. intros.
  rewrite right_unit at 1.
  apply f_equal.
  apply functional_extensionality.
  intros.
  case x; intros; rewrite <- left_unit; rewrite monoid_right; reflexivity.
  (* right_unit *)
  unfold WriterT. intros.
  rewrite <- left_unit.
  rewrite right_unit at 1.
  apply f_equal.
  apply functional_extensionality.
  intros; destruct x; rewrite monoid_left; reflexivity.
  (* associativity *)
  unfold WriterT. intros.
  rewrite <- associativity.
  apply f_equal. apply functional_extensionality. intros.
  destruct x. rewrite <- associativity. rewrite <- associativity.
  apply f_equal. apply functional_extensionality. intros.
  destruct x. rewrite <- associativity. rewrite <- left_unit.
  apply f_equal. apply functional_extensionality. intros.
  destruct x. rewrite <- left_unit. rewrite monoid_assoc.
  reflexivity.
  (* fmap_m *)
  intros.
  unfold fmap; simpl.
  rewrite fmap_m.
  assert ((fun (v : (prod A S)) => return_ (let (x, y) := v in (f x, y)))
         = (fun m' => (let (x, s1) := m' in
 do fx <- return_ (f x, munit);
 (let (y, s2) := fx in return_ (y, mappend s1 s2))))).
  apply functional_extensionality.
  intro. destruct x.
    rewrite <- left_unit. rewrite monoid_right. reflexivity.
  rewrite H. reflexivity.
Defined.

Instance inj_writerMonad (S : Set) M `{Monoid S} `{InjMonad M}: InjMonad (WriterT S M).
Proof.
  constructor.
  simpl.
  intros.
  apply (inj_return (a,munit)) in H1.  congruence.
Qed.

Instance WriterT_Reasonable_Monad S `{Monoid S} M
  {functorM : Functor M}
  {monadM : Monad M}
  {ReasonableM : Reasonable_Monad M}
  : Reasonable_Monad (WriterT S M).
Proof.
  (* fmap_exists *)
  constructor; simpl; intros.
  destruct (fmap_exists _ _ _ _ _ H0).
  destruct x; exists a; congruence.
Qed.

Instance WriterTTransformer (S : Set) {Monoid_S : Monoid S} : Transformer (WriterT S):=
  {|
     lift := fun A M Fun_M MonadM ma => bind ma (* (A * S) *) (fun x => return_ (x, munit))
   |}.
  simpl; intros; rewrite <- left_unit; reflexivity.
  simpl; intros.
  repeat rewrite <- associativity.
  assert ((fun x => do x0 <- f x; return_ (x0, munit)) = fun x =>
    do m' <- return_ (x, munit);
      (let (x0, s1) := m' in
        do fx <- do x1 <- f x0; return_ (x1, munit);
          (let (y, s2) := fx in return_ (y, mappend s1 s2)))) as H by
  (apply functional_extensionality; intros;
    rewrite <- left_unit; rewrite <- associativity;
      assert ((fun x0 => return_ (x0, munit)) = (fun x0 : B =>
        do fx <- return_ (x0, munit);
          let (y, s2) := fx in return_ (y, mappend munit s2))) as H by
      (apply functional_extensionality; intros;
        rewrite <- left_unit; rewrite monoid_left; reflexivity);
      rewrite H; reflexivity).
  rewrite H; reflexivity.
Defined.


Instance writerM (S : Set) (M : Set -> Set) `{monoid: Monoid S} {functorM : Functor M} {monadM : Monad M} : @WriterM (WriterT S M) S _ _ _ :=
{| tell := fun x => return_ (tt, x);
   listen := fun A (m : M (prod A S)) => bind m (fun p => let (x,s1) := p in return_ ((x,s1), s1))
|}.
Proof.
  (* tell_tell *)
  intros. simpl.
  rewrite <- left_unit.
  rewrite <- left_unit.
  reflexivity.
  (* tell_munit *)
  simpl; reflexivity.
  (* listen_tell *)
  intros. simpl.
  rewrite <- left_unit. rewrite <- left_unit. rewrite <- left_unit.
  rewrite monoid_right. reflexivity.
  (* listen_return *)
  intros. simpl. rewrite <- left_unit. reflexivity.
  (* listen_bind *)
  unfold WriterT.
  intros. simpl.
  rewrite <- associativity.
  rewrite <- associativity.
  f_equal. apply functional_extensionality. intros. destruct x.
  rewrite <- left_unit. rewrite <- associativity. rewrite <- associativity. rewrite <- associativity.
  f_equal. apply functional_extensionality. intros. destruct x.
  rewrite <- left_unit. rewrite <- left_unit. rewrite <- left_unit. rewrite <- left_unit.
  rewrite monoid_right; reflexivity.
  (* listen_listen *)
  unfold WriterT.
  intros. simpl.
  rewrite <- associativity. rewrite <- associativity.
  f_equal. apply functional_extensionality. intros. destruct x.
  rewrite <- left_unit. rewrite <- left_unit. rewrite <- left_unit.
  rewrite monoid_right. reflexivity.
Qed.

(*-----------------------------------------------------------------------
  READER MONADS
  -----------------------------------------------------------------------*)


(**** Environment class ****)

Class Environment (M : Set -> Set) (R : Set) `{monad: Monad M} := {
  ask: M R;
  local: forall {A: Set}, (R -> R) -> M A -> M A;
  ask_query :
    forall (A : Set) (m: M A),
      ask >> m = m;
  ask_ask :
    forall (A : Set) (f: R -> R -> M A),
      ask >>= (fun e1 => ask >>= (fun e2 => f e1 e2))
      =
      ask >>= (fun e1 => f e1 e1);
  ask_bind :
    forall (A B : Set) (m: M A) (f: A -> R -> M B),
      m >>= (fun x => ask >>= (fun e => f x e))
      =
      ask >>= (fun e => m >>= (fun x => f x e));
  local_return :
    forall (A : Set) (x: A) (f: R -> R),
      local f (return_ x) = return_ x;
  local_bind :
    forall (A B : Set) (m: M A) (g: A -> M B) (f: R -> R),
      local f (m >>= g) = local f m >>= (fun x => local f (g x));
  local_ask :
    forall (f: R -> R),
      local f ask = ask >>= (fun e => return_ (f e));
  local_local :
    forall (f g: R -> R) (A : Set) (m: M A),
      local f (local g m) = local (compose g f) m
}.


(**** Reader Monad ****)

Definition ReaderT (E : Set) (M : Set -> Set) (A : Set) := E -> M A.

Definition Reader e := (ReaderT e Id).

Definition runReader (E A : Set) (r : Reader E A) : E -> A := r.

Global Instance readerFunctor (E : Set) (M : Set -> Set) {functorM : Functor M} : Functor (ReaderT E M) := {|
    fmap := fun A B f g x => fmap f (g x)
|}.
intros.
apply functional_extensionality. intro.
apply fmap_fusion.
  (* fmap id *)
  intros.
  apply functional_extensionality; intro.
  rewrite fmap_id; reflexivity.
Defined.

Global Instance readerMonad (E : Set) M {functorM : Functor M} {monadM : Monad M} : Monad (ReaderT E M) :=
{| return_ := fun A (a: A) e => return_ a;
   bind    := fun A m B f e => m e >>= (fun a => f a e)
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 intros.
 apply functional_extensionality. intro.
 rewrite <- right_unit.
 reflexivity.
 (* right_unit *)
 intros.
 apply functional_extensionality. intro.
 rewrite <- left_unit.
 reflexivity.
 (* associativity *)
 intros.
 apply functional_extensionality. intro.
 rewrite associativity.
 reflexivity.
  (* fmap_m *)
  intros.
  unfold fmap; simpl.
  apply functional_extensionality.
  intro. rewrite fmap_m. reflexivity.
Defined.

Class Inhabited (S : Set) := {witness : S}.

Global Instance inj_readerMonad (E : Set) M `{Inhabited E} `{InjMonad M} : InjMonad (ReaderT E M).
Proof.
  constructor; simpl; intros.
  apply inj_return; apply (f_equal (fun f => f witness) H1).
Qed.

Instance ReaderT_Reasonable_Monad E `{Inhabited E} M
  {functorM : Functor M}
  {monadM : Monad M}
  {ReasonableM : Reasonable_Monad M}
  : Reasonable_Monad (ReaderT E M).
Proof.
  (* fmap_exists *)
  constructor; simpl; intros.
  destruct (fmap_exists _ _ _ _ _ (f_equal (fun f => f witness) H0)).
  exists x; congruence.
Qed.

Global Instance readerTTransformer (E : Set) : Transformer (ReaderT E):=
  {|
     lift := fun A M Fun_M MonadM ma =>
       fun (_:E) => ma
   |}.
(* lift_return *)
  intros.
  unfold return_ at 2. unfold readerMonad. reflexivity.
(* lift_bind *)
  intros.
  unfold bind at 2. unfold readerMonad. reflexivity.
Defined.

Global Instance readerEnvironment {R : Set} M {functorM : Functor M} {monadM : Monad M} :
  Environment (ReaderT R M) R :=
{|
   ask := fun e => return_ e;
   local := fun A f m e => m (f e)
|}.
(* Checking the laws *)
  (* ask_query *)
  intros; apply functional_extensionality; intro; simpl;
  (rewrite <- left_unit); reflexivity.
  (* ask_ask *)
  intros; apply functional_extensionality; intro; simpl.
  repeat (rewrite <- left_unit); reflexivity.
  (* ask_bind *)
  intros; apply functional_extensionality; intro; simpl.
  repeat (rewrite <- left_unit).
  assert ((fun a => do a0 <- return_ x; f a a0 x) =
          (fun a => f a x x)).
   apply functional_extensionality. intro.
   rewrite <- left_unit.
   reflexivity.
  rewrite H.
  reflexivity.
  (* local_return *)
  intros. apply functional_extensionality; intro; simpl.
  reflexivity.
  (* local_bind *)
  intros; apply functional_extensionality; intro; simpl.
  reflexivity.
  (* local_ask *)
  intros; apply functional_extensionality; intro; simpl.
  rewrite <- left_unit.
  reflexivity.
  (* local_local *)
  intros; apply functional_extensionality; intro; simpl.
  unfold compose.
  reflexivity.
Defined.

Class FailEnvironmentMonad (R : Set) (M : Set -> Set) `{FailM : FailMonad M}
  {EnvM : Environment M R} := {
    local_fail : forall {A : Set} (f : R -> R),
      local f fail = fail (A := A)
  }.

(*-----------------------------------------------------------------------
  STATE MONADS
  -----------------------------------------------------------------------*)

(**** State monad class ****)

Class StateM (M : Set -> Set) (S : Set) `{monad: Monad M} := {
  get: M S;
  put: S -> M unit;
  get_query:
    forall A (m: M A),
      get >> m = m;
  get_get:
    forall A (f: S -> S -> M A),
    get >>= (fun s1 => get >>= (fun s2 => f s1 s2))
     = get >>= (fun s => f s s);
  put_put:
    forall s1 s2,
      put s1 >> put s2 = put s2;
  put_get:
    forall s,
      put s >> get = put s >> return_ s;
  get_put:
    get >>= put = return_ tt
}.

Class InjStateMonad (S : Set) (M : Set -> Set) `{StateM M S} := {
  inj_put : forall {A : Set} (s s' : S) (a b : A),
    put s >> return_ a = put s' >> return_ b -> a = b /\ s = s'
}.

Class FailStateMonad_Disc (S : Set) (M : Set -> Set) `{FailM : FailMonad M}
  {StateM : StateM M S} := {
  inj_put_fail : forall {A : Set} (s s' : S) (b : A),
    put s >> fail <> put s' >> return_ b
  }.

(**** State Monad ****)

Definition StateT (S : Set) (M : Set -> Set) (A : Set) := S -> M (prod A S).

Definition State (S A : Set) := StateT S Id A.

Instance stateFunctor (S : Set) (M: Set -> Set) (functorM: Functor M):
  Functor (StateT S M) :=
  {|
     fmap := fun A B f m =>
               (fun s0 => fmap (fun a_s => match a_s with
                                  pair a s => pair (f a) s
                                end) (m s0))
  |}.
 intros. apply functional_extensionality. intro. rewrite (fmap_fusion).
 assert ((fun a_s : A * S =>
     let (a0, s) :=
       let (a0, s) := a_s
       in (f a0, s)
     in (g a0, s)) = (fun a_s : A * S =>
     let (a0, s) := a_s
     in (g (f a0), s))).
 apply functional_extensionality.
 intro. induction x0. trivial.
 rewrite H. auto.
  (* fmap id *)
  intros.
  apply functional_extensionality; intro. unfold id.
  assert ((fun a_s : A * S => let (a0, s) := a_s in (a0, s)) = id ).
    apply functional_extensionality; intro. unfold id.
    destruct x0; reflexivity.
  rewrite H. rewrite fmap_id; reflexivity.
Defined.

Instance stateMonad (S: Set) (M: Set -> Set) {functorM : Functor M} {monadM : Monad M} : Monad (StateT S M) :=
{| return_ := fun A (a: A) s => return_ (a, s);
   bind := fun A m B f s =>
            do a_s <- m s ;
               (let (a, s) := a_s
                in f a s)
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 intros. apply functional_extensionality.
 intros.
 assert (forall (a_s: prod A S), (let (a0, s) := a_s in return_ (a0, s)) = return_ a_s) by
   (intros; induction a_s; reflexivity).
 assert ((fun (a_s : prod A S) => (let (a0, s) := a_s in return_ (a0, s))) =
         (fun (a_s : prod A S) => return_ a_s)) by
 (apply functional_extensionality; apply H).
 rewrite H0, <- right_unit.
 reflexivity.
 (* unit_right *)
 intros.
 apply functional_extensionality. intro x.
 rewrite <- (@left_unit M functorM monadM (prod A S) (a,x)).
 reflexivity.
 (* associativity *)
 intros.
 apply functional_extensionality. intro.
 rewrite <- associativity.
 assert ((fun (a_s: prod A S) => (let (a, s) := a_s in
   do a_s0 <- f a s;
   (let (a0, s0) := a_s0
    in g a0 s0))) =
   (fun (x0: prod A S) => do a_s <- let (a, s) := x0 in f a s;
                         (let (a, s) := a_s in g a s))) by
 (apply functional_extensionality; intro;
   induction x0; reflexivity).
 rewrite H.
 reflexivity.
  (* fmap_m *)
  intros.
  unfold fmap; simpl.
  apply functional_extensionality.
  intro.
  rewrite fmap_m.
  assert ((fun (v:(prod A S)) => return_ (let (x0, y) := v in (f x0, y)))
         = (fun a_s => (let (a, s) := a_s in return_ (f a, s)))) by
  (apply functional_extensionality; intro; destruct x0; reflexivity).
  rewrite H.
 reflexivity.
Defined.

Instance inj_stateMonad (S: Set) (M: Set -> Set) `{Inhabited S} `{InjMonad M} : InjMonad (StateT S M).
Proof.
  constructor; simpl; intros.
  generalize (inj_return _ _ (f_equal (fun f => f witness) H1)); congruence.
Qed.

Instance StateT_Reasonable_Monad S `{Inhabited S} M
  {functorM : Functor M}
  {monadM : Monad M}
  {ReasonableM : Reasonable_Monad M}
  : Reasonable_Monad (StateT S M).
Proof.
  (* fmap_exists *)
  constructor; simpl; intros.
  destruct (fmap_exists _ _ _ _ _ (f_equal (fun f => f witness) H0)).
  destruct x as [a x]; exists a; congruence.
Qed.

Instance stateTTransformer (S : Set) : Transformer (StateT S):=
  {|
     lift := fun A M Fun_M MonadM ma =>
       fun (s:S) => bind ma (* (prod A S) *) (fun (x:A) => return_ (pair x s))
   |}.
(* lift_return *)
  intros.
  unfold return_ at 3. unfold stateMonad.
  apply functional_extensionality. intro.
  rewrite <- left_unit.
  reflexivity.
(* lift_bind *)
  intros.
  unfold bind at 3. unfold stateMonad.
  apply functional_extensionality. intro.
  rewrite <- associativity.
  rewrite <- associativity.
  assert ((fun x0 => bind (return_ (x0,x)) (fun a_s => (let (a, s) := a_s in do x1 <- f a; return_ (x1, s)))) =
  (fun x0 => do x1 <- f x0; return_ (x1, x))).
     apply functional_extensionality. intro.
     rewrite <- left_unit.
     reflexivity.
  rewrite H.
  reflexivity.
Defined.

Instance stateM (S : Set) (M : Set -> Set) {functorM : Functor M} {monadM : Monad M} : @StateM (StateT S M) S _ _ :=
{| get := fun s => return_ (s, s);
   put := fun s1 => (fun s0 => return_ (tt, s1))
|}.
(* get_query *)
  intros. apply functional_extensionality. intro.
  unfold wbind. simpl.
  rewrite <- left_unit. reflexivity.

(* get_get *)
  intros. apply functional_extensionality. intro.
  simpl. repeat (rewrite <- left_unit).
  reflexivity.

(* put_put *)
  intros. apply functional_extensionality. intro.
  simpl.
  rewrite <- left_unit.
  reflexivity.
(* put_get *)
  intros. apply functional_extensionality. intro.
  simpl.
  rewrite <- left_unit. rewrite <- left_unit.
  reflexivity.
(* get_put *)
  intros. apply functional_extensionality. intro.
  simpl.
  rewrite <- left_unit.
  reflexivity.
Defined.

Instance InjState_stateMonad (S: Set) (M: Set -> Set) `{InjMonad M} :
  InjStateMonad S (StateT S M).
Proof.
  constructor; simpl; intros.
  repeat rewrite <- left_unit in H0.
  assert (forall (A B : Set) (f g : A -> B) (a : A), f = g ->
    f a = g a) as equal_f by (intros; rewrite H1; auto).
  generalize (equal_f _ _ _ _ s H0).
  intros.
  apply inj_return in H1; injection H1; intros; subst; auto.
Qed.

(*-----------------------------------------------------------------------
  CROSS INSTANCES
  -----------------------------------------------------------------------*)

(**** ReaderT Cross Instances ****)

Tactic Notation "elimReaderT":=
  unfold lift;
  unfold wbind;
  unfold bind;
  unfold return_;
  unfold readerMonad;
  unfold readerTTransformer;
  apply functional_extensionality; intro.

Instance readerTstateM (E S : Set) (M : Set -> Set)
  {functorM : Functor M}
  {monadM : Monad M}
  {stateM: StateM M S}: @StateM (ReaderT E M) S _ _ :=
{| get := lift get;
   put := fun s1 => lift (put s1)
|}.
Proof.
  (* get_query *)
  intros; elimReaderT.
  fold (@wbind M _ _ S get A (m x)).
  rewrite get_query;
  reflexivity.
  (* get_get *)
  intros; elimReaderT.
  rewrite get_get;
  reflexivity.
  (* put_put *)
  intros; elimReaderT.
  fold (@wbind M _ _ unit (put s1) unit (put s2));
  rewrite put_put;
  reflexivity.
  (* put_get *)
  intros;
  elimReaderT.
  fold (@wbind M _ _ unit (put s) S get);
  fold (@wbind M _ _ unit (put s) S (return_ s));
  rewrite put_get;
  reflexivity.
  (* get_put *)
  intros;
  elimReaderT.
  rewrite get_put;
  reflexivity.
Defined.

Instance MaybeT_Transformer : Transformer (MaybeT):=
  {|
     lift := fun A M Fun_M MonadM ma =>
       bind ma (* (prod A S) *) (fun (x:A) => return_ (Some x))
   |}.
(* lift_return *)
  intros.
  simpl.
  rewrite <- left_unit.
  reflexivity.
(* lift_bind *)
  intros.
  simpl.
  repeat rewrite <- associativity.
  apply f_equal; apply functional_extensionality; intros.
  rewrite <- left_unit; reflexivity.
Defined.

Instance MaybeT_stateM (S : Set) (M : Set -> Set)
  {functorM : Functor M}
  {monadM : Monad M}
  {stateM: StateM M S}: @StateM (MaybeT M) S _ _ :=
{| get := lift get;
   put := fun s1 => lift (put s1)
|}.
Proof.
  (* get_query *)
  intros; simpl; repeat rewrite <- associativity.
  rewrite (functional_extensionality (fun x : S => do x0 <- return_ (M := M) (Some x);
    match x0 with
      | Some _ => m
      | None => return_ None
    end) (fun x : S => m)).
  unfold MaybeT in m; apply (get_query _ m).
  intros; rewrite <- left_unit; auto.
  (* get_get *)
  simpl; intros.
  repeat rewrite <- associativity.
  unfold MaybeT in f.
  rewrite (functional_extensionality (fun x => do x0 <- return_ (M := M) (Some x);
   match x0 with
   | Some a =>
       do x1 <- do x1 <- get; return_ (M := M) (Some x1);
       match x1 with
       | Some a0 => f a a0
       | None => return_ None
       end
   | None => return_ None
   end) (fun x => do x0 <- get (M := M); f x x0)).
  rewrite (functional_extensionality (fun x => do x0 <- return_ (M := M) (Some x);
     match x0 with
   | Some a => f a a
   | None => return_ None
   end) (fun x => f x x)).
  apply (get_get _ f).
  intros; rewrite <- left_unit; auto.
  intros; rewrite <- left_unit.
  rewrite <- associativity.
  apply f_equal; apply functional_extensionality; intros.
  rewrite <- left_unit; auto.
  (* put_put *)
  simpl; intros.
  assert ( do x <- put s2; return_ (Some x) =
    do x <- (put s1 >> put s2); return_ (Some x)) as eq_put_s2 by
  (rewrite (put_put s1 s2); auto).
  assert (exists b, b =   do x <- do x <- put s1; return_ (Some x);
    match x with
      | Some _ => do x0 <- put s2; return_ (Some x0)
      | None => return_ None
    end ) as eq_s1 by (eexists _; reflexivity);
  destruct eq_s1 as [b eq_s1]; rewrite <- eq_s1.
  rewrite eq_put_s2.
  rewrite eq_s1.
  rewrite <- associativity.
  rewrite (functional_extensionality (fun x : unit => do x0 <- return_ (M := M) (Some x);
    match x0 with
      | Some _ => do x1 <- put s2; return_ (M := M) (Some x1)
      | None => return_ (M := M) None
    end) (fun x : unit => do x0 <- put s2; return_ (Some x0))).
  unfold wbind.
  rewrite <- associativity; reflexivity.
  intros; rewrite <- left_unit; auto.
  (* put_get *)
  simpl.
  intros; repeat rewrite <- associativity.
  rewrite (functional_extensionality
    (fun x : unit => do x0 <- return_ (Some x);
      match x0 with
        | Some _ => do x1 <- get; return_ (Some x1)
        | None => return_ None
      end) (fun x => do x1 <- get; return_ (Some x1))).
  rewrite (functional_extensionality
    (fun x : unit => do x0 <- return_ (Some x);
      match x0 with
        | Some _ => return_ (Some s)
        | None => return_ None
      end) (fun x => return_ (Some s))).
  generalize (put_get s).
  unfold wbind; intros.
  rewrite associativity, H, <- associativity.
  apply f_equal; apply functional_extensionality; intros;
    rewrite <- left_unit; auto.
  intros; rewrite <- left_unit; auto.
  intros; rewrite <- left_unit; auto.
  (* get_put *)
  simpl; intros.
  rewrite <- associativity.
  rewrite (functional_extensionality
    (fun x : S => do x0 <- return_ (M := M) (Some x);
      match x0 with
        | Some a => do x1 <- put a; return_ (Some x1)
        | None => return_ None
      end) (fun x : S => do x1 <- put x; return_ (Some x1))).
  rewrite (left_unit tt (fun u => return_ (Some u))), <- get_put,
    <- associativity; auto.
  intros; rewrite <- left_unit; auto.
Defined.

Instance InjState_readerT (E S : Set) (M : Set -> Set)
  {Inhabited_E : Inhabited E}
  {functorM : Functor M}
  {monadM : Monad M}
  {stateM: StateM M S}
  {InjState: InjStateMonad S M} : InjStateMonad S (ReaderT E M).
Proof.
  constructor; simpl; intros.
  assert (forall (A B : Set) (f g : A -> B) (a : A), f = g ->
    f a = g a) as equal_f by (intros; rewrite H0; auto).
  apply inj_put.
  apply (equal_f _ _ _ _ witness H); intros.
Defined.

Instance InjState_MaybeT (S : Set) (M : Set -> Set)
  {functorM : Functor M}
  {monadM : Monad M}
  {stateM: StateM M S}
  {InjState: InjStateMonad S M} : InjStateMonad S (MaybeT M).
Proof.
  constructor; simpl; intros.
  repeat rewrite <- associativity in H.
  rewrite (functional_extensionality
    (fun x : unit => do x0 <- return_ (M := M) (Some x);
      match x0 with
      | Some _ => return_ (Some a)
      | None => return_ None
      end) (fun x => return_ (M := M) (Some a))) in H.
  rewrite (functional_extensionality
    (fun x : unit => do x0 <- return_ (M := M) (Some x);
      match x0 with
      | Some _ => return_ (Some b)
      | None => return_ None
      end) (fun x => return_ (M := M) (Some b))) in H.
  destruct (inj_put _ _ _ _ H); split; congruence.
  intros; rewrite <- left_unit; auto.
  intros; rewrite <- left_unit; auto.
Defined.

Lemma decompBindEq:
  forall A B M {functorM: Functor M} {monadM: Monad M}
    (m1 m2: M A) (f1 f2: A -> M B),
  (m1 = m2) /\ (f1 = f2) -> (m1 >>= f1) = (m2 >>= f2).
Proof.
  intros.
  elim H.
  intros.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Tactic Notation "decompBind" :=
  apply decompBindEq;
  split;
  [ reflexivity
  | apply functional_extensionality;
    intro
  ].

Instance readerTException E X M
  {functorM : Functor M}
  {monadM : Monad M}
  {exceptionM: Exception M X}
  : Exception (ReaderT E M) X :=
{|
   throw := fun A x => lift (throw x);
   catch := fun A (m : ReaderT E M A) h =>
     fun e => catch (m e) (fun x => h x e)
 |}.
Proof.
  (* catch_throw *)
  intros; elimReaderT.
  rewrite catch_throw; reflexivity.
  (* catch_throw' *)
  intros; elimReaderT.
  rewrite catch_throw'; reflexivity.
  (* throw_bind *)
  intros; elimReaderT.
  rewrite bind_throw; reflexivity.
  (* catch_return *)
  intros; elimReaderT.
  rewrite catch_return; reflexivity.
  (* fmap_catch *)
  simpl; intros.
  apply functional_extensionality.
  intros; rewrite fmap_catch; reflexivity.
  (* fmap_throw *)
  simpl; intros; rewrite fmap_throw; auto.
  (* throwsnot1 *)
  intros; elimReaderT.
   rewrite throwsnot1.
    reflexivity.
  intros.
  unfold bind in H. unfold readerMonad in H.
  assert (forall (B : Set) (f : A -> ReaderT E M B) (h : X -> ReaderT E M B) (e: E),
    (catch (do a <- m e; f a e) (fun x : X => h x e)) =
    (do a <- m e; f a e)).
    intros.
    generalize e.
    apply equal_f.
    exact (H B0 f0 h1).
  assert (f = (fun a => (fun (a0: A) (_ : E) => f a0) a x)).
    apply functional_extensionality; intro; reflexivity.
  rewrite H1.
  assert (h0 = (fun x0 : X => (fun (x : X) (_ : E) => h0 x) x0 x)).
    apply functional_extensionality; intro; reflexivity.
  rewrite H2.
  exact (H0 B (fun a e => f a) (fun x e => h0 x) x).
  (* throwsnot2 *)
  intro; intro; intro. intro. intro h. intro x. elimReaderT.
  apply (@throwsnot2 M X functorM monadM exceptionM A B (fun x => f x x0)).
    (* precondition of throwsnot2 for M *)
    intros. unfold bind in H. unfold readerMonad in H.
    assert (forall (m: ReaderT E  M A) (h : X -> ReaderT E M B) (e : E),
             (forall e h', catch (m e) (fun x : X => h' x e) = m e) ->
             (catch (do a <- m e; f a e) (fun x : X => h x e)) =
             (do a <- m e ; f a e)).
      intros. generalize e. apply equal_f.
      apply (H m0 h1).
      intros.
      apply functional_extensionality; intros.
      apply H1.
      assert (h0 = (fun x2 : X => (fun (x : X) (_ : E) => h0 x) x2 x0)).
    apply functional_extensionality; intro; reflexivity.
    rewrite H2.
    apply (H1 (fun e => m) (fun x e => h0 x) x0).
    intros; apply H0.
Qed.

Instance readerTWriterM
  (E W : Set)
  (M : Set -> Set)
  `{monoid: Monoid W}
  {functorM : Functor M}
  {monadM  : Monad M}
  {writerM : @WriterM M W _ _ _} : @WriterM (ReaderT E M) W _ _ _
 :=
{| tell   := fun x => lift (tell x);
   listen :=
     fun A (m : ReaderT E M A) =>
       fun e => listen (m e)
|}.
Proof.
  (* tell_tell GENERIC PROOF *)
  intros.
  rewrite <- tell_tell.
  unfold wbind.
  rewrite lift_bind.
  reflexivity.
  (* tell_munit GENERIC PROOF *)
  intros.
  rewrite tell_munit.
  rewrite lift_return.
  reflexivity.
  (* listen_tell *)
  intro; elimReaderT.
  rewrite listen_tell.
  unfold wbind.
  reflexivity.
  (* listen_return *)
  intros; elimReaderT.
  rewrite listen_return.
  reflexivity.
  (* listen_bind *)
  intros; elimReaderT.
  rewrite listen_bind.
  decompBind.
   induction x0.
   decompBind.
     induction x0.
     reflexivity.
  (* listen_listen *)
  intros; elimReaderT.
  rewrite listen_listen.
  decompBind.
  induction x0; reflexivity.
Qed.

(**** WriterT Cross Instances ****)

Instance writerTstateM (W S : Set) (M : Set -> Set) `{monoidW: Monoid W} {functorM : Functor M} {monadM : Monad M} {stateM: StateM M S}: @StateM (WriterT W M) S _ _ :=
{| get := lift get;
   put := fun s1 => lift (put s1)
|}.
Proof.
  (* get_query GENERIC PROOF *)
  intros.
  rewrite (left_unit tt (fun _ => m)).
  unfold wbind.
  rewrite associativity.
  apply decompBindEq.
  split.
  assert ((fun _ : S => @return_ (WriterT W M) _ _ unit tt) =
          (fun _ : S => lift (return_ tt))).
    apply functional_extensionality; intro.
    rewrite lift_return.
    reflexivity.
  rewrite H.
  assert ((@return_ (WriterT W M) _ _ unit tt) = (lift (return_ tt))).
    rewrite lift_return.
    reflexivity.
  rewrite H0.
  assert ((return_ tt) = (get >> return_ tt)).
    rewrite get_query.
    reflexivity.
  rewrite H1 at 1.
  unfold wbind.
  rewrite lift_bind.
  reflexivity.
  reflexivity.
(* get_get *)
  Admitted.


  Lemma catch_fail : forall (M : Set -> Set) `{FailMonad M} (E : Set) {Exc_M : Exception M E}
    (A B : Set) (f : A -> B) (e : E) (h : E -> M B),
    fail (A := A) = throw (A := A) e ->
      catch (fail (A := B)) h = h e.
  Proof.
    intros.
    assert (fmap f fail (A := A) = fmap f (throw (A := A) e)) by
      (rewrite H0; reflexivity).
    rewrite <- (@fmap_fail _ _ _ _ _ _ f), H1, fmap_throw, catch_throw'; auto.
  Qed.


(***********************************************************************
 ***********************************************************************

   INFRASTRUCTURE

 ***********************************************************************
 ***********************************************************************)

Example prog1 A : Reader A nat :=
  return_ 67.

Eval compute in (prog1 nat 0).

Example prog A : Reader A A :=
 (do x    <- ask;
  do y    <- ask;
  return_ x).

Example prog2 : Reader nat nat :=
 (do x  <- ask;
  do y  <- ask;
  return_ (x + y)).

Example prog3 : Reader nat nat :=
  (do x    <- ask;
   return_ (x + x)).

Lemma example_lemma : prog2 = prog3.
  unfold prog2, prog3.
  simpl. reflexivity.
Qed.

Example prog4 M {functorM: Functor M} {monadM: Monad M} {envM: Environment M nat} f : (M nat) :=
 (do x    <- ask;
  do y    <- ask;
  return_ (f x y)).

(* Sections are handy when we have a lot of context (specially when shared by multiple programs) *)

Section monadic_programs.
  Variable M : Set -> Set.
  Context {functorM : Functor M}.
  Context {monadM : Monad M}.

  Example prog5 {envM: Environment M nat} : (M nat) :=
    (do x    <- ask;
     do y    <- ask;
     return_ (x + y)).

  Example prog6 {envM : Environment M nat} {exc : Exception M unit} : M nat :=
    (do x <- ask;
     match x with 0 => throw tt | S n => return_ (S n) end).

  Example prog7 A {envM : Environment M A} : M A :=
    (do x <- ask;
     return_ x).

End monadic_programs.

Definition test : nat -> nat := prog5 (Reader nat).

Definition test2 := prog7 (Reader nat).

Check test2.

Eval compute in test 10.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
