Require Import VST.floyd.proofauto.

Definition def_float (x: val) : Prop :=
 match x with
 | Vfloat x' => Binary.is_finite 53 1024 x' = true
 | _ => False
 end.

Definition f_cmp op x y :=
 match x, y with
 | Vfloat x', Vfloat y' => Float.cmp op x' y' = true
 | _, _ => False
 end.

Lemma float_cmp_eq_refl:
  forall x, def_float x -> f_cmp Ceq x x.
Proof.
intros.
destruct x; try contradiction.
simpl in *.
pose proof (Binary.Bcompare_correct _ _ _ _ H H).
change (cmp_of_comparison Ceq (Float.compare f f) = true).
simpl.
unfold Float.compare.
rewrite H0.
rewrite Raux.Rcompare_Eq; auto.
Qed.

Lemma f_le_refl: forall x, def_float x -> f_cmp Cle x x.
intros.
destruct x; try contradiction; simpl in *.
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff; right.
pose proof (Binary.Bcompare_correct _ _ _ _ H H).
change (cmp_of_comparison Ceq (Float.compare f f) = true).
simpl.
unfold Float.compare.
rewrite H0.
rewrite Raux.Rcompare_Eq; auto.
Qed.

Lemma f_cmp_false:
  forall op a b, def_float (Vfloat a) -> def_float (Vfloat b) -> 
     Float.cmp op a b = false ->
     f_cmp (negate_comparison op) (Vfloat a) (Vfloat b).
Proof.
intros.
simpl in *.
Transparent Float.cmp.
unfold Float.cmp in *.
Opaque Float.cmp.
unfold cmp_of_comparison in *.
pose proof (Binary.Bcompare_correct _ _ _ _ H H0).
set (c := Raux.Rcompare (Binary.B2R 53 1024 a) (Binary.B2R 53 1024 b)) in *.
change (Binary.Bcompare 53 1024 a b) with (Float.compare a b) in H2.
rewrite H2 in *.
destruct op; inv H1; simpl; auto;
destruct c; inv H4; auto.
Qed.

Lemma f_lt_irrefl:
   forall a, f_cmp Clt a a -> False.
Proof.
intros.
destruct a; simpl in H; auto.
Transparent Float.cmp.
unfold Float.cmp in *.
Opaque Float.cmp.
simpl in H.
unfold Float.compare in *.
destruct (Binary.Bcompare 53 1024 f f) eqn:?; inv H.
destruct c; inv H1.
pose proof (Binary.Bcompare_swap 53 1024 f f).
rewrite Heqo in H. inv H.
Qed.

Lemma is_float_middle:
  forall (before: list val) (bl: list val) (after: list val) i,
       Forall def_float bl ->
       Zlength before <= i < Zlength before + Zlength bl ->
       val_lemmas.is_float (Znth i (before ++ bl ++ after)).
Proof.
intros.
rewrite app_Znth2 by rep_omega.
rewrite app_Znth1 by (autorewrite with sublist; rep_omega).
eapply Forall_Znth; eauto.
rep_omega.
eapply Forall_impl; try eassumption.
intros. destruct a; try contradiction; simpl; auto.
Qed.

Lemma f_cmp_lt_ge_false:
  forall a b, f_cmp Clt a b -> f_cmp Cge a b -> False.
Proof.
intros.
hnf in *.
destruct a; try contradiction.
destruct b; try contradiction.
rewrite Float.cmp_ge_gt_eq in H0.
rewrite orb_true_iff in H0; destruct H0.
eapply Float.cmp_lt_gt_false; eauto.
eapply Float.cmp_lt_eq_false; eauto.
Qed.

Lemma float_cmp_gt_le_false:
  forall a b, f_cmp Cgt a b -> f_cmp Cle a b -> False.
Proof.
intros.
hnf in *.
destruct a; try contradiction.
destruct b; try contradiction.
rewrite Float.cmp_le_lt_eq in H0.
rewrite orb_true_iff in H0; destruct H0.
eapply Float.cmp_lt_gt_false; eauto.
eapply Float.cmp_gt_eq_false; eauto.
Qed.

Lemma both_float_cmp_true:
  forall op a b,
    def_float a -> def_float b ->
   typed_true tint (force_val 
     (both_float (fun n1 n2 : float => Some (Val.of_bool (Float.cmp op n1 n2)))
        sem_cast_f2f sem_cast_f2f a b)) ->
   f_cmp op a b.
Proof.
intros.
destruct a; try contradiction.
destruct b; try contradiction.
apply typed_true_of_bool in H1.
apply H1.
Qed.

Lemma both_float_cmp_false:
  forall op a b,
    def_float a -> def_float b ->
   typed_false tint (force_val 
     (both_float (fun n1 n2 : float => Some (Val.of_bool (Float.cmp op n1 n2)))
        sem_cast_f2f sem_cast_f2f a b)) ->
   f_cmp (negate_comparison op) a b.
Proof.
intros.
destruct a; try contradiction.
destruct b; try contradiction.
apply typed_false_of_bool in H1.
apply f_cmp_false; auto.
Qed.

Lemma f_cmp_swap:
  forall op a b, f_cmp op a b -> f_cmp (swap_comparison op) b a.
Proof.
intros.
destruct a,b; try contradiction; simpl in *.
rewrite Float.cmp_swap; auto.
Qed.

Lemma f_cmp_ge_gt_eq:
  forall a b, f_cmp Cge a b <-> (f_cmp Cgt a b \/ f_cmp Ceq a b).
Proof.
intros.
unfold f_cmp.
destruct a,b; simpl; try solve [split; [intro; contradiction | intros [?|?]; auto]].
rewrite Float.cmp_ge_gt_eq.
rewrite orb_true_iff. split; auto.
Qed.

Lemma f_cmp_le_lt_eq:
  forall a b, f_cmp Cle a b <-> (f_cmp Clt a b \/ f_cmp Ceq a b).
Proof.
intros.
unfold f_cmp.
destruct a,b; simpl; try solve [split; [intro; contradiction | intros [?|?]; auto]].
rewrite Float.cmp_le_lt_eq.
rewrite orb_true_iff. split; auto.
Qed.

Lemma def_float_f2f:
 forall a, def_float a -> force_val (sem_cast_f2f a) = a.
Proof.
intros. destruct a; simpl in *; try contradiction; reflexivity.
Qed.

Lemma f_cmp_le_ge:
  forall a b, f_cmp Cle a b -> f_cmp Cge a b -> f_cmp Ceq a b.
Proof.
intros.
rewrite f_cmp_le_lt_eq in H.
destruct H; auto.
contradiction (f_cmp_lt_ge_false _ _ H H0).
Qed.

Lemma f_cmp_le_trans:
   transitive val (f_cmp Cle).
Proof.
intros.
intros a b c ? ?.
destruct a,b; try contradiction.
destruct c; try contradiction.
simpl in *.
Transparent Float.cmp.
unfold Float.cmp in *.
Opaque Float.cmp.
simpl in *.
unfold Float.compare in *.
unfold Binary.Bcompare in *.
destruct f,f0,f1; simpl in *; auto; try discriminate;
destruct s,s0,s1; simpl in *; auto; try discriminate;
destruct (e ?= e1) eqn:?H;
destruct (e1 ?= e3) eqn:?H;
auto; try discriminate.
-
apply Z.compare_eq_iff in H1. apply Z.compare_eq_iff in H2.
subst.
rewrite Z.compare_refl.
destruct (Pos.compare_cont Eq m m0) eqn:?H; simpl in H; try discriminate.
apply Pcompare_Eq_eq in H1. subst m0. auto.
destruct (Pos.compare_cont Eq m0 m1) eqn:?H; simpl in H; try discriminate.
apply Pcompare_Eq_eq in H2. subst m0. rewrite H1. auto.
apply nat_of_P_gt_Gt_compare_morphism in H1.
apply nat_of_P_gt_Gt_compare_morphism in H2.
rewrite nat_of_P_gt_Gt_compare_complement_morphism.
auto.
omega.
-
apply Z.compare_eq_iff in H1.
subst e1.
rewrite H2.
auto.
-
apply Z.compare_eq_iff in H2.
subst e1.
rewrite H1.
auto.
-
rewrite (Zcompare_Gt_trans _ _ _ H1 H2).
auto.
-
apply Z.compare_eq_iff in H1. apply Z.compare_eq_iff in H2.
subst.
rewrite Z.compare_refl.
destruct (Pos.compare_cont Eq m m0) eqn:?H; simpl in H; try discriminate.
apply Pcompare_Eq_eq in H1. subst m0. auto.
destruct (Pos.compare_cont Eq m0 m1) eqn:?H; simpl in H; try discriminate.
apply Pcompare_Eq_eq in H2. subst m0. rewrite H1. auto.
apply nat_of_P_lt_Lt_compare_morphism in H1.
apply nat_of_P_lt_Lt_compare_morphism in H2.
rewrite nat_of_P_lt_Lt_compare_complement_morphism.
auto.
omega.
-
apply Z.compare_eq_iff in H1.
subst e1.
rewrite H2.
auto.
-
apply Z.compare_eq_iff in H2.
subst e1.
rewrite H1.
auto.
-
rewrite (Zcompare_Lt_trans _ _ _ H1 H2).
auto.
Qed.

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  induction 1; simpl; intros; auto.
  inv H0; constructor; auto.
  inv H. inv H3. constructor; auto.
Qed.

Lemma Exists_app:
  forall {A} (P: A->Prop) (l1 l2: list A),
     Exists P (l1++l2) <-> Exists P l1 \/ Exists P l2.
Proof.
intros.
induction l1; simpl; auto.
split; intros. right; auto. destruct H; auto. inv H.
split; intro.
inv H. left. left. auto.
rewrite IHl1 in H1.
destruct H1; auto. 
destruct H.
inv H. left; auto.
right. rewrite IHl1; auto.
right. rewrite IHl1; auto.
Qed.

Inductive sorted {A} (le: A -> A -> Prop): list A -> Prop := 
| sorted_nil:
    sorted le nil
| sorted_1: forall x,
    sorted le (x::nil)
| sorted_cons: forall x y l,
     le x y -> sorted le (y::l) -> sorted le (x::y::l).

Lemma sorted_app:
  forall {A} {le: A->A->Prop} (TRANS: transitive A le)
    pivot al bl,
    sorted le al -> sorted le bl ->
    Forall (fun x => le x pivot) al ->
    Forall (le pivot) bl ->
    sorted le (al++bl).
Proof.
intros.
induction H.
simpl; auto.
simpl.
inv H1. inv H5.
inv H0.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor; auto.
simpl.
constructor; auto.
apply IHsorted.
inv H1; auto.
Qed.

Lemma sorted_app_e3:
  forall {A} {le: A->A->Prop} (TRANS: transitive A le)
    pivot al bl,
    sorted le (al++[pivot]++bl) ->
    sorted le al /\ sorted le bl /\ 
    Forall (fun x => le x pivot) al /\
    Forall (le pivot) bl.
Proof.
 intros.
 induction al.
 simpl in *.
 split. constructor.
 induction bl; inv  H. repeat constructor.
 spec IHbl. destruct bl; inv H4; constructor; auto. 
 eapply TRANS; eassumption.
 split3; auto. destruct IHbl as [? [? ?]]; constructor; auto.
 inv H. destruct al; inv H2. destruct al; inv H1.
 simpl in IHal. spec IHal; auto.
 destruct IHal as [_ [? [_ ?]]].
 split3. constructor. auto. split; auto.
 spec IHal; auto.
 destruct IHal as [? [? [? ?]]].
 split3; auto. constructor; auto.
 split; auto.
 constructor; auto.
 apply TRANS with a0; auto.
 inv H1; auto.
Qed.

Lemma Permutation_Zlength:
  forall {A} {al bl: list A}, Permutation al bl -> Zlength al = Zlength bl.
Proof.
intros. rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
Qed.
