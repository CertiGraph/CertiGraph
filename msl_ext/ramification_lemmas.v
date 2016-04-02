Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import VST.msl.base.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.ramification_lemmas.

Local Open Scope logic.

Section Ramification_P.

Context {A Env : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.
Context {CoSL: CorableSepLog A}.

Variable M: Env -> Env -> Prop.
Context {EqM: Equivalence M}.

Definition EnvironBox (P: Env -> A) : Env -> A :=
  fun rho: Env => (ALL rho': Env, !! M rho rho' --> P rho').

Definition EnvironStable (P: Env -> A) : Prop :=
  forall rho rho', M rho rho' -> P rho = P rho'.

Lemma EnvironStable_sepcon: forall P Q,
  EnvironStable P ->
  EnvironStable Q ->
  EnvironStable (P * Q).
Proof.
  unfold EnvironStable.
  intros.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  simpl.
  f_equal; auto.
Qed.

Lemma EnvironBox_EnvironStable: forall P, EnvironStable (EnvironBox P).
(* This lemma is the reason why EqM is required. *)
Proof.
  intros.
  unfold EnvironBox, EnvironStable; intros.
  apply pred_ext; apply allp_right; intro rho''; apply (allp_left _ rho'');
  apply imp_andp_adjoint; normalize; rewrite prop_imp; auto.
  + rewrite H; auto.
  + rewrite <- H; auto.
Qed.

Lemma EnvironBox_T: forall P, EnvironBox P |-- P.
Proof.
  intros P rho.
  apply (allp_left _ rho).
  rewrite prop_imp by reflexivity.
  auto.
Qed.

Lemma EnvironBox_derives: forall P Q, P |-- Q -> EnvironBox P |-- EnvironBox Q.
Proof.
  intros P Q ? rho.
  apply allp_right; intro rho'.
  apply (allp_left _ rho').
  apply imp_andp_adjoint.
  apply derives_extract_prop'; intro.
  rewrite prop_imp by auto.
  auto.
Qed.

Lemma EnvironBox_sepcon: forall P Q, EnvironBox P * EnvironBox Q |-- EnvironBox (P * Q).
Proof.
  intros.
  unfold EnvironBox; simpl; intro rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint; normalize.
  apply sepcon_derives; apply (allp_left _ rho'); 
  rewrite prop_imp by auto; auto.
Qed.

Lemma EnvironBox_andp: forall P Q, EnvironBox (P && Q) = EnvironBox P && EnvironBox Q.
Proof.
  intros.
  unfold EnvironBox; apply pred_ext; simpl; intro rho.
  + apply andp_right.
    - apply allp_right; intro rho'.
      apply -> imp_andp_adjoint; normalize.
      apply (allp_left _ rho'); 
      rewrite prop_imp by auto.
      apply andp_left1; auto.
    - apply allp_right; intro rho'.
      apply -> imp_andp_adjoint; normalize.
      apply (allp_left _ rho'); 
      rewrite prop_imp by auto.
      apply andp_left2; auto.
  + apply allp_right; intro rho'.
    apply -> imp_andp_adjoint; normalize.
    apply andp_derives; apply (allp_left _ rho'); 
    rewrite prop_imp by auto; auto.
Qed.

Lemma EnvironStable_allp: forall {T} P, (forall a: T, EnvironStable (P a)) -> EnvironStable (allp P).
Proof.
  intros.
  unfold EnvironStable in *.
  intros.
  simpl.
  apply allp_congr; intro a.
  apply H; auto.
Qed.

Lemma EnvironBox_TT: EnvironBox TT = TT.
Proof.
  intros.
  apply pred_ext.
  + apply TT_right.
  + unfold EnvironBox; intro rho.
    apply allp_right; intro rho'.
    apply imp_andp_adjoint.
    simpl; apply TT_right.
Qed.

Lemma EnvironStable_EnvironBox: forall P, EnvironStable P -> EnvironBox P = P.
Proof.
  intros.
  apply pred_ext; [apply EnvironBox_T |].
  unfold EnvironBox; intro rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint; normalize.
  rewrite (H _ _ H0).
  auto.
Qed.

Lemma sepcon_EnvironBox_weaken: forall P Q R R', R |-- R' -> P |-- Q * EnvironBox R -> P |-- Q * EnvironBox R'.
Proof.
  intros.
  eapply derives_trans; [apply H0 |].
  apply sepcon_derives; auto.
  apply EnvironBox_derives; auto.
Qed.

Lemma EnvironBox_corable: forall P, corable P -> corable (EnvironBox P).
Proof.
  intros.
  simpl in H |- *.
  intro.
  unfold EnvironBox.
  auto.
Qed.

Lemma solve_ramify_P: forall (g l g' l' F: Env -> A),
  EnvironStable F ->
  g |-- l * F ->
  F * l' |-- g' ->
  g |-- l * EnvironBox (l' -* g').
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  unfold EnvironBox; simpl; intros rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  normalize.
  rewrite (H rho rho' H2).
  apply wand_sepcon_adjoint.
  apply H1.
Qed.

Lemma ramify_P_frame: forall g l g' l' F,
  EnvironStable F ->
  g |-- l * EnvironBox (l' -* g') ->
  g * F |-- l * EnvironBox (l' -* g' * F).
Proof.
  intros.
  apply solve_ramify_P with (EnvironBox (l' -* g') * F).
  + apply EnvironStable_sepcon; auto.
    apply EnvironBox_EnvironStable.
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    apply sepcon_derives; [| auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    apply EnvironBox_T.
Qed.

Lemma split_ramify_P: forall g1 g2 l1 l2 g1' g2' l1' l2',
  g1 |-- l1 * EnvironBox (l1' -* g1') ->
  g2 |-- l2 * EnvironBox (l2' -* g2') ->
  g1 * g2 |-- (l1 * l2) * EnvironBox (l1' * l2' -* g1' * g2').
Proof.
  intros.
  apply solve_ramify_P with (EnvironBox (l1' -* g1') * EnvironBox (l2' -* g2')).
  + apply EnvironStable_sepcon;
    apply EnvironBox_EnvironStable.
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + apply wand_sepcon_adjoint.
    eapply derives_trans; [apply EnvironBox_sepcon |].
    eapply derives_trans; [apply EnvironBox_T |].
    apply wand_sepcon_wand.
Qed.

Lemma go_lower_ramify_P: forall (g l g' l': A),
  g |-- l * (l' -* g') ->
  @Basics.const A Env g |-- Basics.const l * EnvironBox (Basics.const l' -* Basics.const g').
Proof.
  intros.
  intro rho; unfold EnvironBox, Basics.const; simpl.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  apply andp_left1.
  auto.
Qed.

Lemma ramify_PQ_reduce0: forall {B} g l (g' l': B -> Env -> A),
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g |-- l * EnvironBox (exp l' -* exp g').
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply EnvironBox_derives.
  apply wand_sepcon_adjoint.
  rewrite exp_sepcon2.
  apply exp_left; intro x; apply (exp_right x).
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  auto.
Qed.

Lemma ramify_PQ_reduce1: forall {B} g l g0 l0 (g' l': B -> Env -> A),
  corable l0 ->
  g0 |-- l0 ->
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g0 && g |-- (l0 && l) * EnvironBox (allp (l' -* g')).
Proof.
  intros.
  rewrite corable_andp_sepcon1 by auto.
  apply andp_derives; auto.
Qed.

Lemma ramify_PQ_reduce2: forall {B} g l g0 g' l' g0',
  corable g0 ->
  EnvironStable g0 ->
  (forall x: B, g0 |-- g0' x) ->
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g0 && g |-- l * EnvironBox (allp (l' -* g0' && g')).
Proof.
  intros.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H2] |].
  rewrite <- corable_sepcon_andp1 by auto.
  apply sepcon_derives; [auto |].
  rewrite <- (EnvironStable_EnvironBox g0) at 1 by auto.
  rewrite <- EnvironBox_andp.
  apply EnvironBox_derives.
  apply allp_right; intro x.
  rewrite (andp_comm g0).
  apply imp_andp_adjoint.
  apply (allp_left _ x).
  apply imp_andp_adjoint.
  apply wand_sepcon_adjoint.
  rewrite corable_andp_sepcon2 by auto.
  change ((g0' && g') x) with (g0' x && g' x).
  change ((l' -* g') x) with (l' x -* g' x).
  apply andp_derives; auto.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma ramify_PQ_reduce3: forall {B} g l g' l' g0 l0 p,
  (forall x: B, corable (l0 x)) ->
  (forall x: B, l0 x |-- g0 x) ->
  (forall x: B, l0 x |-- p x) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))) ->
  g |-- l * EnvironBox (allp (l0 && l' -* g0 && g')).
Proof.
  intros.
  apply derives_trans with (l * EnvironBox (allp (p --> (l' -* g')))).
  + auto.
  + apply sepcon_derives; auto.
    apply EnvironBox_derives.
    apply allp_right; intro x.
    apply (allp_left _ x).
    change ((l0 && l' -* g0 && g') x) with (l0 x && l' x -* g0 x && g' x).
    change ((p --> (l' -* g')) x) with (p x --> (l' x -* g' x)).
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, corable_andp_sepcon1, <- corable_sepcon_andp1 by auto.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl |] |].
    - apply andp_right; [apply andp_left1; apply derives_refl |].
      eapply derives_trans; [apply andp_derives; [apply H1 | apply derives_refl] |].
      apply modus_ponens.
    - rewrite corable_sepcon_andp1 by auto.
      apply andp_derives; auto.
      apply modus_ponens_wand.
Qed.

Lemma solve_ramify_PQ: forall {B} g l p g' l' F,
  EnvironStable F ->
  (forall x: B, corable (p x)) ->
  g |-- l * F ->
  (forall x: B, p x && (F * l' x) |-- g' x) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))).
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  unfold EnvironBox; simpl; intros rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  normalize.
  rewrite (H rho rho' H3).
  clear rho H3; rename rho' into rho.
  apply allp_right; intro x.
  apply imp_andp_adjoint, wand_sepcon_adjoint.
  rewrite corable_andp_sepcon2 by apply (H0 x rho).
  apply (H2 x rho).
Qed.

Lemma ramify_PQ_frame: forall {B} g l p g' l' F,
  EnvironStable F ->
  (forall x: B, corable (p x)) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))) ->
  g * F |-- l * EnvironBox (allp (p --> (l' -* g' * Basics.const F))).
Proof.
  intros.
  eapply derives_trans with (l * EnvironBox (allp (p --> (l' -* g'))) * F).
  + apply sepcon_derives; auto.
  + rewrite sepcon_assoc.
    apply sepcon_derives; auto.
    rewrite <- (EnvironStable_EnvironBox F) at 1 by auto.
    eapply derives_trans; [apply EnvironBox_sepcon |].
    apply EnvironBox_derives.
    apply allp_right; intro x.
    apply wand_sepcon_adjoint.
    apply (allp_left _ x).
    apply wand_sepcon_adjoint.
    change ((p --> (l' -* g' * Basics.const F)) x) with (p x --> (l' x -* g' x * F)).
    change ((p --> (l' -* g')) x) with (p x --> (l' x -* g' x)).
    apply imp_andp_adjoint.
    rewrite andp_comm, <- corable_andp_sepcon1 by auto.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply modus_ponens |].
    rewrite wand_wand_comm.
    apply wand_derives; auto.
    apply wand_sepcon_adjoint; auto.
Qed.

Lemma split_ramify_PQ: forall {B} g1 g2 l1 l2 p g1' g2' l1' l2',
  (forall x: B, corable (p x)) ->
  g1 |-- l1 * EnvironBox (allp (p --> (l1' -* g1'))) ->
  g2 |-- l2 * EnvironBox (allp (p --> (l2' -* g2'))) ->
  g1 * g2 |-- (l1 * l2) * EnvironBox (allp (p --> (l1' * l2' -* g1' * g2'))).
Proof.
  intros.
  apply solve_ramify_PQ with (EnvironBox (allp (p --> (l1' -* g1'))) * EnvironBox (allp (p --> (l2' -* g2')))).
  + apply EnvironStable_sepcon;
    apply EnvironBox_EnvironStable.
  + auto.
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + intros x.
    change ((l1' * l2') x) with (l1' x * l2' x).
    rewrite <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l1' x)), (sepcon_comm _ (l1' x)), <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l2' x)).
    rewrite <- (andp_dup (p x)), andp_assoc.
    rewrite <- corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
    rewrite <- !corable_sepcon_andp1 by auto.
    apply sepcon_derives.
    - apply wand_sepcon_adjoint; (eapply derives_trans; [apply EnvironBox_T |]).
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
    - apply wand_sepcon_adjoint; (eapply derives_trans; [apply EnvironBox_T |]).
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
Qed.

Lemma go_lower_ramify_PQ: forall {B} g l (p g' l': B -> A),
  g |-- l * (allp (p --> (l' -* g'))) ->
  Basics.const g |-- Basics.const l *
    EnvironBox (allp ((fun (x: B) (rho: Env) => p x) -->
      ((fun x _ => l' x) -* (fun x _ => g' x)))).
Proof.
  intros.
  intro rho; unfold EnvironBox, Basics.const; simpl.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  apply andp_left1.
  auto.
Qed.
  
End Ramification_P.

Lemma EnvironBox_allp: forall {A B Env : Type} {ND : NatDed A} (M: Env -> Env -> Prop) P, EnvironBox M (@allp _ _ B P) = ALL x: B, (EnvironBox M (P x)).
Proof.
  intros.
  unfold EnvironBox; apply pred_ext; simpl; intro rho.
  + apply allp_right; intro b.
    apply allp_right; intro rho'.
    apply imp_andp_adjoint; normalize.
    apply (allp_left _ rho').
    rewrite prop_imp by auto.
    apply (allp_left _ b).
    auto.
  + apply allp_right; intro rho'.
    apply imp_andp_adjoint; normalize.
    apply allp_right; intro b.
    apply (allp_left _ b).
    apply (allp_left _ rho').
    rewrite prop_imp by auto.
    auto.
Qed.

Lemma EnvironBox_weaken: forall {A Env : Type} {ND : NatDed A} (M1 M2: Env -> Env -> Prop) P, inclusion _ M1 M2 -> EnvironBox M2 P |-- EnvironBox M1 P.
Proof.
  intros.
  unfold EnvironBox.
  intro rho.
  apply allp_right; intro rho'.
  apply (allp_left _ rho').
  apply imp_andp_adjoint.
  apply derives_extract_prop'; intro.
  rewrite prop_imp by auto.
  auto.
Qed.

Lemma EnvironBox_EnvironStable_weaken: forall {A Env : Type} {ND : NatDed A} (M1 M2: Env -> Env -> Prop) {EqM2: Equivalence M2} P, inclusion _ M1 M2 -> EnvironStable M1 (EnvironBox M2 P).
(* This lemma is the reason why EqM is required. *)
Proof.
  intros.
  unfold EnvironBox, EnvironStable; intros.
  apply pred_ext; apply allp_right; intro rho''; apply (allp_left _ rho'');
  apply imp_andp_adjoint; normalize; rewrite prop_imp; auto.
  + apply H in H0.
    rewrite H0; auto.
  + apply H in H0.
    rewrite <- H0; auto.
Qed.

Ltac solve_ramify_Q_with Fr :=
  match goal with
  | |- @derives ?Pred _ ?g (?l * @allp ?Pred _ ?T ?Func) =>
      let p := fresh "p" in evar (p: T -> Pred);
      let g' := fresh "g'" in evar (g': T -> Pred);
      let l' := fresh "l'" in evar (l': T -> Pred);
      let x := fresh "x" in
      let H := fresh "H" in
      assert (Func = p --> (l' -* g'));
      [
        extensionality x; cbv beta;
        match goal with
        | |- ?P --> (?L' -* ?G') = _ =>
             super_pattern P x; super_pattern L' x; super_pattern G' x
        end;
        match goal with
        | |- ?P _ --> (?L' _ -* ?G' _) = _ =>
             instantiate (1 := P) in (Value of p);
             instantiate (1 := L') in (Value of l');
             instantiate (1 := G') in (Value of g')
        end;
        subst p g' l';
        reflexivity
      | subst p g' l'; rewrite H; clear H]
  end;
  apply RAMIF_Q'.solve with Fr.

Section Ramification_PredSepCon.

(******************************************

The purpose of these lemmas are specifying ramification premises, such that
spatial predicates and items (or pure predicates) can be modified from the
left side to the right side.

However, the frame part should be part-wise equivalent, i.e. spatial predicates
must be equivalent and items (or pure predicates) must be equivalent. E.g. 
F = G and a = b is acceptable but only F a = G b is not. To prove a ramification
premise of latter situation should use iter_sepcon_map/pred_sepcon_map first.

******************************************)

Context {A : Type}.
Context {B : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.
Context {ClS: ClassicalSep A}.
Context {CoSL: CorableSepLog A}.

(******************************************

Ramification Premises with iter_sepcon

******************************************)

Lemma iter_sepcon_ramif_1Q: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (P': T -> B -> A) (g: list B) (g': T -> list B) (x: B) (x': T -> B),
  (exists f,
    Permutation g (x :: f) /\
    (forall a, Pure a -> Permutation (g' a) (x' a :: f)) /\
    (forall a, Pure a -> forall x, In x f -> P x = (P' a) x)) ->
  iter_sepcon g P |-- P x *
    (ALL a: T, !! Pure a -->
      ((P' a) (x' a) -* iter_sepcon (g' a) (P' a))).
Proof.
  intros.
  destruct H as [f [? [? ?]]].
  RAMIF_Q'.formalize.
  apply RAMIF_Q'.solve with (iter_sepcon f P).
  + simpl; auto.
  + rewrite H; simpl; auto.
  + intros a; normalize.
    specialize (H0 _ H2).
    specialize (H1 _ H2).
    rewrite H0.
    rewrite sepcon_comm.
    apply derives_refl'; simpl; f_equal.
    apply iter_sepcon_func_strong; auto.
Qed.

Lemma iter_sepcon_ramif_xQ: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (P': T -> B -> A) (g l: list B) (g' l': T -> list B),
  (exists f,
    Permutation g (l ++ f) /\
    (forall a, Pure a -> Permutation (g' a) (l' a ++ f)) /\
    (forall a, Pure a -> forall x, In x f -> P x = (P' a) x)) ->
  iter_sepcon g P |-- iter_sepcon l P *
    (ALL a: T, !! Pure a -->
      (iter_sepcon (l' a) (P' a) -* iter_sepcon (g' a) (P' a))).
Proof.
  intros.
  destruct H as [f [? [? ?]]].
  RAMIF_Q'.formalize.
  apply RAMIF_Q'.solve with (iter_sepcon f P).
  + simpl; auto.
  + rewrite H.
    apply derives_refl'.
    apply iter_sepcon_app_sepcon.
  + intros a; normalize.
    specialize (H0 _ H2).
    specialize (H1 _ H2).
    rewrite H0.
    rewrite sepcon_comm.
    apply derives_refl'.
    rewrite iter_sepcon_app_sepcon; f_equal.
    apply iter_sepcon_func_strong; auto.
Qed.

Lemma iter_sepcon_ramif_item_1Q: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (g: list B) (g': T -> list B) (x: B) (x': T -> B),
  (exists f,
    Permutation g (x :: f) /\
    (forall a, Pure a -> Permutation (g' a) (x' a :: f))) ->
  iter_sepcon g P |-- P x *
    (ALL a: T, !! Pure a -->
      (P (x' a) -* iter_sepcon (g' a) P)).
Proof.
  intros.
  apply (iter_sepcon_ramif_1Q Pure P (fun _ => P)).
  destruct H as [f [? ?]].
  exists f; split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_item_xQ: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (g l: list B) (g' l': T -> list B),
  (exists f,
    Permutation g (l ++ f) /\
    (forall a, Pure a -> Permutation (g' a) (l' a ++ f))) ->
  iter_sepcon g P |-- iter_sepcon l P *
    (ALL a: T, !! Pure a -->
      (iter_sepcon (l' a) P -* iter_sepcon (g' a) P)).
Proof.
  intros.
  apply (iter_sepcon_ramif_xQ Pure P (fun _ => P)).
  destruct H as [f [? ?]].
  exists f; split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_pred_1Q: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (P': T -> B -> A) (g: list B) (x: B),
  (exists f,
    Permutation g (x :: f) /\
    (forall a, Pure a -> forall x, In x f -> P x = (P' a) x)) ->
  iter_sepcon g P |-- P x *
    (ALL a: T, !! Pure a -->
      ((P' a) x -* iter_sepcon g (P' a))).
Proof.
  intros.
  apply (iter_sepcon_ramif_1Q _ _ _ g (fun _ => g) x (fun _ => x)).
  destruct H as [f [? ?]].
  exists f; split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_pred_xQ: forall {T: Type} (Pure: T -> Prop) (P: B -> A) (P': T -> B -> A) (g l: list B),
  (exists f,
    Permutation g (l ++ f) /\
    (forall a, Pure a -> forall x, In x f -> P x = (P' a) x)) ->
  iter_sepcon g P |-- iter_sepcon l P *
    (ALL a: T, !! Pure a -->
      (iter_sepcon l (P' a) -* iter_sepcon g (P' a))).
Proof.
  intros.
  apply (iter_sepcon_ramif_xQ _ _ _ g l (fun _ => g) (fun _ => l)).
  destruct H as [f [? ?]].
  exists f; split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_1: forall P P' (g g': list B) (x x': B),
  (exists f,
    Permutation g (x :: f) /\
    Permutation g' (x' :: f) /\
    (forall x, In x f -> P x = P' x)) ->
  iter_sepcon g P |-- P x * (P' x' -* iter_sepcon g' P').
Proof.
  intros.
  pose proof iter_sepcon_ramif_1Q (fun x: unit => True) P (fun _ => P') g (fun _ => g') x (fun _ => x').
  rewrite allp_unit in H0.
  rewrite prop_imp in H0 by auto.
  apply H0.
  destruct H as [f [? [? ?]]]; exists f.
  split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_x: forall P P' (g g' l l': list B),
  (exists f,
    Permutation g (l ++ f) /\
    Permutation g' (l' ++ f) /\
    (forall x, In x f -> P x = P' x)) ->
  iter_sepcon g P |-- iter_sepcon l P * (iter_sepcon l' P' -* iter_sepcon g' P').
Proof.
  intros.
  pose proof iter_sepcon_ramif_xQ (fun x: unit => True) P (fun _ => P') g l (fun _ => g') (fun _ => l').
  rewrite allp_unit in H0.
  rewrite prop_imp in H0 by auto.
  apply H0.
  destruct H as [f [? [? ?]]]; exists f.
  split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_item_1: forall P (g g': list B) (x x': B),
  (exists f,
    Permutation g (x :: f) /\
    Permutation g' (x' :: f)) ->
  iter_sepcon g P |-- P x * (P x' -* iter_sepcon g' P).
Proof.
  intros.
  apply iter_sepcon_ramif_1.
  destruct H as [f [? ?]]; exists f.
  split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_item_x: forall P (g g' l l': list B),
  (exists f,
    Permutation g (l ++ f) /\
    Permutation g' (l' ++ f)) ->
  iter_sepcon g P |-- iter_sepcon l P * (iter_sepcon l' P -* iter_sepcon g' P).
Proof.
  intros.
  apply iter_sepcon_ramif_x.
  destruct H as [f [? ?]]; exists f.
  split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_pred_1: forall P P' (g: list B) (x: B),
  (exists f,
    Permutation g (x :: f) /\
    (forall x, In x f -> P x = P' x)) ->
  iter_sepcon g P |-- P x * (P' x -* iter_sepcon g P').
Proof.
  intros.
  apply iter_sepcon_ramif_1.
  destruct H as [f [? ?]]; exists f.
  split; [| split]; intros; auto.
Qed.

Lemma iter_sepcon_ramif_pred_x: forall P P' (g l: list B),
  (exists f,
    Permutation g (l ++ f) /\
    (forall x, In x f -> P x = P' x)) ->
  iter_sepcon g P |-- iter_sepcon l P * (iter_sepcon l P' -* iter_sepcon g P').
Proof.
  intros.
  apply iter_sepcon_ramif_x.
  destruct H as [f [? ?]]; exists f.
  split; [| split]; intros; auto.
Qed.

(******************************************

Ramification Premises with pred_sepcon

******************************************)

(* A better way to prove it is using RAMIF_Q'.solve and sepcon properties of pred_sepcon.
Unfolding into iter_sepcon needs handling quatifiers, which is in convenient. The following
proof script only shows that it is doable. *)
Lemma pred_sepcon_ramif_1Q: forall {T: Type} (Pure: T -> Prop) (P: B -> Prop) (P': T -> B -> Prop) (p: B -> A) (p': T -> B -> A) (x: B) (x' : T -> B),
  (exists Pf,
    Prop_join (eq x) Pf P /\
    (forall a, Pure a -> Prop_join (eq (x' a)) Pf (P' a)) /\
    (forall a, Pure a -> (forall y, Pf y -> p y = (p' a) y))) ->
  pred_sepcon P p |-- p x *
    (ALL a: T, !! Pure a -->
      ((p' a) (x' a) -* pred_sepcon (P' a) (p' a))).
Proof.
  intros.
  unfold pred_sepcon.
  normalize; intros; normalize; rename x0 into g.
  destruct H as [Pf [? [? ?]]].
  destruct (Permutation_spec_Prop_join g P Pf x H (conj H0 H1)) as [f [? [? ?]]].
  RAMIF_Q'.formalize.
  apply (RAMIF_Q'.exp_right (fun a => x' a :: f)); [simpl; auto |].
  pose proof iter_sepcon_ramif_1Q Pure p p' g (fun a => x' a :: f) x x'.
  spec H7; [clear H7 |].
  + exists f.
    split; auto.
    split; intros.
    - reflexivity.
    - apply (H3 _ H7).
      rewrite <- H5; auto.
  + eapply derives_trans; [exact H7 |]; clear H7.
    apply sepcon_derives; auto.
    apply allp_right; intros a.
    apply (allp_left _ a).
    simpl.
    apply imp_andp_adjoint; normalize.
    unfold TT; rewrite prop_imp by auto.
    apply wand_derives; auto.
    apply andp_right; auto.
    specialize (H2 _ H7).
    specialize (H3 _ H7).
    apply andp_right; apply prop_right.
    - intro y.
      rewrite H5.
      destruct H2 as [? _].
      symmetry; apply H2.
    - apply NoDup_cons; auto.
      destruct H2 as [_ ?].
      specialize (H2 (x' a) eq_refl).
      rewrite H5; auto.
Qed.

Lemma pred_sepcon_ramif_xQ: forall {T: Type} (Pure: T -> Prop) (G L: B -> Prop) (L' G': T -> B -> Prop) (p: B -> A) (p': T -> B -> A),
  (exists Pf,
    Prop_join L Pf G /\
    (forall a, Pure a -> Prop_join (L' a) Pf (G' a)) /\
    (forall a, Pure a -> (forall y, Pf y -> p y = (p' a) y))) ->
  pred_sepcon G p |-- pred_sepcon L p *
    (ALL a: T, !! Pure a -->
      (pred_sepcon (L' a) (p' a) -* pred_sepcon (G' a) (p' a))).
Proof.
  intros.
  destruct H as [Pf [? [? ?]]].
  RAMIF_Q'.formalize.
  apply RAMIF_Q'.solve with (pred_sepcon Pf p).
  + simpl; auto.
  + apply derives_refl'; symmetry.
    apply pred_sepcon_sepcon; auto.
  + intros.
    normalize.
    specialize (H0 _ H2).
    specialize (H1 _ H2).
    apply derives_refl'.
    rewrite (pred_sepcon_strong_proper Pf Pf p (p' x)) by (auto; intros; tauto).
    rewrite sepcon_comm; apply pred_sepcon_sepcon; auto.
Qed.

Lemma pred_sepcon_ramify1: forall {EqB: EqDec B eq} (P1 P2: B -> Prop) p1 p2 x,
  P1 x ->
  (forall y, P1 y <-> P2 y) ->
  (forall y, y <> x -> p1 y = p2 y) ->
  pred_sepcon P1 p1 |-- p1 x * (p2 x -* pred_sepcon P2 p2).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with (pred_sepcon (fun u => P1 u /\ u <> x) p1).
  + rewrite sepcon_comm,  <- pred_sepcon_sepcon1 with (P' := P1); [auto | |tauto].
    intros.
    destruct_eq_dec x0 x; try subst; tauto.
  + replace (pred_sepcon (fun u : B => P1 u /\ u <> x) p1)
      with (pred_sepcon (fun u : B => P1 u /\ u <> x) p2).
    - assert (pointwise_relation _ iff P1 P2) by auto.
      rewrite <- H2.
      rewrite <- pred_sepcon_sepcon1 with (P' := P1); [auto | | tauto].
      intros.
      destruct_eq_dec x0 x; try subst; tauto.
    - apply pred_sepcon_strong_proper.
      * intros; reflexivity.
      * intros.
        symmetry; apply H1.
        tauto.
Qed.

Lemma pred_sepcon_ramify1_simpl: forall {EqB: EqDec B eq} (P: B -> Prop) p1 p2 x,
  P x ->
  (forall y, y <> x -> p1 y = p2 y) ->
  pred_sepcon P p1 |-- p1 x * (p2 x -* pred_sepcon P p2).
Proof.
  intros.
  apply pred_sepcon_ramify1; auto.
  intros; reflexivity.
Qed.

Lemma pred_sepcon_ramify_pred: forall (Pg1 Pl1 Pg2 Pl2 PF: B -> Prop) p1 p2,
  Prop_join Pl1 PF Pg1 ->
  Prop_join Pl2 PF Pg2 ->
  (forall x, PF x -> p1 x = p2 x) ->
  pred_sepcon Pg1 p1 |-- pred_sepcon Pl1 p1 * (pred_sepcon Pl2 p2 -* pred_sepcon Pg2 p2).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with (pred_sepcon PF p1).
  + rewrite pred_sepcon_sepcon with (R := Pg1); auto.
  + replace (pred_sepcon PF p1) with (pred_sepcon PF p2).
    - rewrite sepcon_comm, pred_sepcon_sepcon with (R := Pg2); auto.
    - apply pred_sepcon_strong_proper.
      * intros; reflexivity.
      * intros; symmetry; apply H1; auto.
Qed.

Lemma pred_sepcon_ramify_pred_Q: forall {C: Type} (Pg1 Pl1 PF: B -> Prop) (PureF: C -> Prop) (Pg2 Pl2: C -> B -> Prop) (p1: B -> A) (p2: C -> B -> A),
  Prop_join Pl1 PF Pg1 ->
  (forall c, PureF c -> Prop_join (Pl2 c) PF (Pg2 c)) ->
  (forall c x, PureF c -> PF x -> p1 x = p2 c x) ->
  pred_sepcon Pg1 p1 |-- pred_sepcon Pl1 p1 * 
    (ALL c: C, !! PureF c -->
      (pred_sepcon (Pl2 c) (p2 c) -*
       pred_sepcon (Pg2 c) (p2 c))).
Proof.
  intros.
  solve_ramify_Q_with (pred_sepcon PF p1).
  + intro; simpl; apply corable_prop.
  + rewrite pred_sepcon_sepcon with (R := Pg1); auto.
  + intro c.
    normalize.
    replace (pred_sepcon PF p1) with (pred_sepcon PF (p2 c)).
    - rewrite sepcon_comm, pred_sepcon_sepcon with (R := Pg2 c); auto.
    - apply pred_sepcon_strong_proper.
      * intros; reflexivity.
      * intros; symmetry; apply H1; auto.
Qed.

Lemma existential_pred_sepcon_ramify_pred': forall {C: Type} (Pg1 Pl1 PF: B -> Prop) (PureF PureF': C -> Prop)
                                                   (Pg2 Pl2: C -> B -> Prop) (p1: B -> A) (p2: C -> B -> A),
  (forall x, Pg1 x -> {Pl1 x} + {PF x}) ->
  (forall x, Pg1 x <-> Pl1 x \/ PF x) ->
  (forall x, Pl1 x -> PF x -> False) ->
  (forall c x, PureF c -> (Pg2 c x <-> Pl2 c x \/ PF x)) ->
  (forall c x, PureF c -> Pl2 c x -> PF x -> False) ->
  (forall c x, PureF c -> PF x -> p1 x = p2 c x) ->
  (forall c, PureF c -> PureF' c) ->
  pred_sepcon Pg1 p1 |-- pred_sepcon Pl1 p1 *
   ((EX c: C, !! PureF c && pred_sepcon (Pl2 c) (p2 c)) -*
    (EX c: C, !! PureF' c && pred_sepcon (Pg2 c) (p2 c))).
Proof.
  intros.
  unfold pred_sepcon.
  normalize.
  assert (Enumerable _ Pg1) by (exists l; auto).
  pose proof EnumSplit _ Pg1 Pl1 PF.
  spec X1; [auto |].
  spec X1; [split; auto |].
  spec X1; [auto |].
  destruct X1 as [[l0 [? ?]] [lF [? ?]]]; clear X0; unfold Ensembles.In in *.
  apply (exp_right l0).
  normalize.
  apply RAMIF_PLAIN.solve with (iter_sepcon lF p1).
  + rewrite <- iter_sepcon_app_sepcon.
    erewrite iter_sepcon_permutation; [apply derives_refl |].
    apply NoDup_Permutation; auto.
    - apply NoDup_app_inv; auto.
      intro x; rewrite H8, H10.
      exact (H0 x).
    - intro x; rewrite in_app_iff, H5, H8, H10.
      apply H.
  + normalize.
    intros l' ?.
    normalize.
    apply (exp_right c); normalize.
    apply (exp_right (lF ++ l')); apply andp_right.
    apply prop_right. apply H4; auto.
    apply andp_right; [apply andp_right; apply prop_right|].
    - intro x; rewrite in_app_iff, H10, H12.
      specialize (H1 c x H11); tauto.
    - apply NoDup_app_inv; auto.
      intro x; rewrite H10, H12.
      specialize (H2 c x H11); tauto.
    - replace (iter_sepcon lF p1) with (iter_sepcon lF (p2 c)).
      * rewrite <- iter_sepcon_app_sepcon; auto.
      * apply iter_sepcon_func_strong.
        intros.
        symmetry; apply H3; auto.
        rewrite <- H10; auto.
Qed.

Lemma existential_pred_sepcon_ramify_pred: forall {C: Type} (Pg1 Pl1 PF: B -> Prop) (PureF: C -> Prop) (Pg2 Pl2: C -> B -> Prop) (p1: B -> A) (p2: C -> B -> A),
  (forall x, Pg1 x -> {Pl1 x} + {PF x}) ->
  (forall x, Pg1 x <-> Pl1 x \/ PF x) ->
  (forall x, Pl1 x -> PF x -> False) ->
  (forall c x, PureF c -> (Pg2 c x <-> Pl2 c x \/ PF x)) ->
  (forall c x, PureF c -> Pl2 c x -> PF x -> False) ->
  (forall c x, PureF c -> PF x -> p1 x = p2 c x) ->
  pred_sepcon Pg1 p1 |-- pred_sepcon Pl1 p1 *
   ((EX c: C, !! PureF c && pred_sepcon (Pl2 c) (p2 c)) -*
    (EX c: C, !! PureF c && pred_sepcon (Pg2 c) (p2 c))).
Proof. intros. eapply existential_pred_sepcon_ramify_pred'; eauto. Qed.

End Ramification_PredSepCon.
