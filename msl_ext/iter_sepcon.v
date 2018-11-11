Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Export Coq.Classes.Morphisms.

Local Open Scope logic.

Set Implicit Arguments.

Definition sepcon_unique1 {X A} `{SepLog A} (P: X -> A): Prop :=
  forall x, P x * P x |-- FF.

Definition sepcon_unique2 {X Y A} `{SepLog A} (P: X -> Y -> A): Prop :=
  forall x y1 y2, P x y1 * P x y2 |-- FF.

Section IterSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  (* Context {PSL : PreciseSepLog A}. *)
  Context {CoSL: CorableSepLog A}.
  (* Context {OSL: OverlapSepLog A}. *)
  (* Context {DSL : DisjointedSepLog A}. *)

Fixpoint iter_sepcon (l : list B) (p : B -> A) : A :=
  match l with
    | nil => emp
    | x :: xl => p x * iter_sepcon xl p
  end.

Lemma iter_sepcon_app_sepcon:
  forall (l1 l2 : list B) (p : B -> A), iter_sepcon (l1 ++ l2) p = iter_sepcon l1 p * iter_sepcon l2 p.
Proof.
  induction l1; intros; simpl. rewrite emp_sepcon; auto. rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Lemma iter_sepcon_app_comm: forall (l1 l2 : list B) (p : B -> A), iter_sepcon (l1 ++ l2) p = iter_sepcon (l2 ++ l1) p.
Proof. intros. do 2 rewrite iter_sepcon_app_sepcon. rewrite sepcon_comm. auto. Qed.

Lemma iter_sepcon_permutation: forall  (l1 l2 : list B) (p : B -> A), Permutation l1 l2 -> iter_sepcon l1 p = iter_sepcon l2 p.
Proof.
  intros. induction H; simpl; auto.
  + rewrite IHPermutation. auto.
  + do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm (p y)). auto.
  + rewrite IHPermutation1. auto.
Qed.

(*
Lemma precise_iter_sepcon: forall (p : B -> A), (forall z, precise (p z)) -> forall (l : list B), precise (iter_sepcon l p).
Proof. intros; induction l; simpl. apply precise_emp. apply precise_sepcon; auto. Qed.
 *)

Lemma iter_sepcon_in_true: forall (p : B -> A) (l : list B) x, In x l -> iter_sepcon l p |-- p x * TT.
Proof.
  intros. apply in_split in H. destruct H as [l1 [l2 ?]]. subst.
  rewrite iter_sepcon_app_comm. rewrite <- app_comm_cons. simpl.
  apply sepcon_derives; auto. apply TT_right.
Qed.

Lemma iter_sepcon_incl_true: forall (p : B -> A) (l s: list B),
    NoDup s -> incl s l -> iter_sepcon l p |-- iter_sepcon s p * TT.
Proof.
  intros. destruct (incl_Permutation l s H H0) as [l' ?].
  apply (iter_sepcon_permutation p) in H1. rewrite H1, iter_sepcon_app_sepcon.
  apply sepcon_derives; auto. apply TT_right.
Qed.

Lemma iter_sepcon_unique_nodup: forall (p : B -> A) (l : list B), sepcon_unique1 p -> iter_sepcon l p |-- !!(NoDup l).
Proof.
  intros. induction l.
  + apply prop_right. constructor.
  + simpl.
    assert (p a * iter_sepcon l p |-- !!(~ In a l)). {
      apply not_prop_right.
      intros. apply (iter_sepcon_in_true p) in H0.
      apply derives_trans with (p a * p a * TT).
      + rewrite sepcon_assoc. apply sepcon_derives. apply derives_refl. auto.
      + specialize (H a). apply derives_trans with (FF * TT).
        apply sepcon_derives; auto. rewrite sepcon_comm, sepcon_FF. apply derives_refl.
    }
  apply derives_trans with (!!(NoDup l) && !!(~ In a l)).
  - apply andp_right; auto. apply sepcon_left2_corable_right; auto with norm.
  - normalize. constructor; auto.
Qed.

(*

Definition joinable (p : B -> A): Prop := forall x y, x <> y -> disjointed (p x) (p y).

Lemma iter_sepcon_joinable:
  forall (p : B -> A) (l : list B) (x : B), joinable p -> (~ In x l) -> disjointed (p x) (iter_sepcon l p).
Proof.
  intros. induction l; simpl.
  + apply disj_emp.
  + apply disj_sepcon_right.
    - apply H. intro. apply H0. subst. apply in_eq.
    - apply IHl. intro; apply H0. apply in_cons; auto.
Qed.

Lemma iter_sepcon_app_joinable:
  forall (p : B -> A) (l1 l2 : list B),
    joinable p -> (forall x, In x l1 -> ~ In x l2) -> disjointed (iter_sepcon l1 p) (iter_sepcon l2 p).
Proof.
  intros; induction l1; simpl; auto.
  + apply disj_comm, disj_emp.
  + apply disj_comm, disj_sepcon_right.
    - apply disj_comm, iter_sepcon_joinable; auto. apply H0, in_eq.
    - apply disj_comm, IHl1. intros; apply H0, in_cons; auto.
Qed.

*)

(*
Fixpoint iter_ocon (l : list B) (p : B -> A) : A :=
  match l with
    | nil => emp
    | x :: xl => p x ⊗ iter_ocon xl p
  end.

Lemma iter_sepcon_iter_ocon: forall l p, iter_sepcon l p |-- iter_ocon l p.
Proof.
  induction l; intro; simpl.
  + apply derives_refl.
  + eapply derives_trans; [| apply sepcon_ocon].
    apply sepcon_derives; [apply derives_refl | apply IHl].
Qed.

Lemma iter_ocon_app_ocon:
  forall (l1 l2 : list B) (p : B -> A), iter_ocon (l1 ++ l2) p = ocon (iter_ocon l1 p) (iter_ocon l2 p).
Proof.
  induction l1; intros; simpl. rewrite emp_ocon; auto. rewrite (IHl1 l2). rewrite ocon_assoc. auto.
Qed.


Lemma iter_sepcon_ocon' (eq_dec: forall x y : B, {x = y} + {x <> y}):
  forall l l1 l2 p,
    NoDup l -> NoDup l1 -> NoDup l2 ->
    (forall x, precise (p x)) -> joinable p ->
    (forall x, In x l <-> In x l1 \/ In x l2) ->
    iter_sepcon l p = iter_sepcon l1 p ⊗ iter_sepcon l2 p.
Proof.
  intros until p.
  intros NoDupl NoDupl1 NoDupl2 PRECISE EQUIV JOINABLE.
  assert (l ~= (l1 ++ l2)) by (apply eq_as_set_spec; intros; rewrite in_app_iff; auto).
  apply pred_ext.
  + destruct (tri_list_split eq_dec NoDupl NoDupl1 NoDupl2 H) as [i1 [i2 [i3 [? [? ?]]]]].
    rewrite (iter_sepcon_permutation _ H0).
    rewrite (iter_sepcon_permutation _ H1).
    rewrite (iter_sepcon_permutation _ H2).
    rewrite !iter_sepcon_app_sepcon. rewrite <- sepcon_assoc.
    apply tri_sepcon_ocon.
  + destruct (double_list_split eq_dec NoDupl1 NoDupl2) as [i1 [i2 [i3 [? [? ?]]]]].
    rewrite (iter_sepcon_permutation _ H0).
    rewrite (iter_sepcon_permutation _ H1).
    rewrite !iter_sepcon_app_sepcon.
    eapply derives_trans; [apply ocon_derives; apply sepcon_ocon |].
    rewrite ocon_assoc.
    rewrite <- (ocon_assoc (iter_sepcon i2 p)).
    rewrite <- precise_ocon_self by (apply precise_iter_sepcon; auto).
    assert (Permutation l (i1 ++ i2 ++ i3)).
    1: {
      apply NoDup_Permutation; auto.
      intros. rewrite JOINABLE. rewrite !in_app_iff.
      pose proof (Permutation_in x H0).
      pose proof (Permutation_in x H1).
      pose proof (Permutation_in x (Permutation_sym H0)).
      pose proof (Permutation_in x (Permutation_sym H1)).
      rewrite in_app_iff in *. tauto.
    }
    rewrite (iter_sepcon_permutation _ H3).
    rewrite !iter_sepcon_app_sepcon.
    eapply derives_trans;
    [ apply ocon_sepcon; apply disj_ocon_right
    | apply sepcon_derives; [auto | apply ocon_sepcon]];
    apply iter_sepcon_app_joinable; auto; intros;
    apply NoDup_app_iff in H2; destruct H2 as [? [? ?]];
    generalize (NoDup_app_not_in _ _ _  H5 x); intro; specialize (H6 x); auto;
    specialize (H6 H4); intro; apply H6; apply in_or_app; auto.
Qed.

Lemma iter_sepcon_ocon (eq_dec: forall x y : B, {x = y} + {x <> y}):
  forall l1 l2 p,
    NoDup l1 -> NoDup l2 ->
    (forall x, precise (p x)) -> joinable p ->
    iter_sepcon l1 p ⊗ iter_sepcon l2 p = iter_sepcon (nodup eq_dec (l1 ++ l2)) p.
Proof.
  intros.
  symmetry; apply iter_sepcon_ocon'; auto.
  + apply NoDup_nodup; auto.
  + intros.
    rewrite nodup_In.
    rewrite in_app_iff.
    tauto.
Qed.

Lemma precise_exp_iter_sepcon: forall (P : B -> A) (Q: list B -> Prop),
  sepcon_unique1 P ->
  (exists x : list B, Q x /\ NoDup x) \/ ~ (exists x : list B, Q x /\ NoDup x) ->
  (forall l, precise (P l)) ->
  (forall l l', Q l -> Q l' -> NoDup l -> NoDup l' -> Permutation l l') ->
  precise (EX l: list B, !! (Q l) && iter_sepcon l P).
Proof.
  intros.
  replace (EX  l : list B, !!Q l && iter_sepcon l P) with (EX  l : list B, !! (Q l /\ NoDup l) && iter_sepcon l P).
  2: {
    f_equal.
    extensionality l.
    rewrite (add_andp _ _ (iter_sepcon_unique_nodup l H)) at 2.
    rewrite (andp_comm _ (!! NoDup l)), <- andp_assoc, prop_and.
    reflexivity.
  }
  apply precise_exp_prop_andp.
  1: assumption.
  1: apply precise_iter_sepcon; auto.
  intros l l'. specialize (H2 l l').
  intros.
  apply iter_sepcon_permutation.
  tauto.
Qed.

*)
Lemma iter_sepcon_func: forall l P Q, (forall x, P x = Q x) -> iter_sepcon l P = iter_sepcon l Q.
Proof. intros. induction l; simpl; [|f_equal]; auto. Qed.

Lemma iter_sepcon_func_derives: forall l P Q, (forall x, In x l -> P x |-- Q x) ->
                                              iter_sepcon l P |-- iter_sepcon l Q.
Proof.
  intros. induction l.
  - apply derives_refl.
  - simpl. apply sepcon_derives.
    + apply H. simpl; auto.
    + apply IHl. intros; apply H. simpl; auto.
Qed.

Lemma iter_sepcon_func_strong: forall l P Q,
    (forall x, In x l -> P x = Q x) -> iter_sepcon l P = iter_sepcon l Q.
Proof.
  intros. apply pred_ext; apply iter_sepcon_func_derives; intros; rewrite H; auto.
Qed.

Lemma iter_sepcon_pointwise_eq: forall (l1 l2: list B) (P Q: B -> A) (x y: B),
    length l1 = length l2 ->
    (forall i, i < length l1 -> P (nth i l1 x) = Q (nth i l2 y)) ->
    iter_sepcon l1 P = iter_sepcon l2 Q.
Proof.
  induction l1; intros.
  - destruct l2. 2: simpl in H; inversion H. simpl. reflexivity.
  - destruct l2. 1: simpl in H; inversion H. simpl. f_equal.
    + specialize (H0 O). simpl in H0. apply H0. apply NPeano.Nat.lt_0_succ.
    + simpl in H. apply (IHl1 _ _ _ x y); eauto. intros. specialize (H0 (S i)).
      simpl in H0. apply H0. apply Lt.lt_n_S. assumption.
Qed.

Instance iter_sepcon_permutation_proper : Proper ((@Permutation B) ==> (pointwise_relation B eq) ==> eq) iter_sepcon.
Proof.
  repeat intro. transitivity (iter_sepcon x y0).
  + apply iter_sepcon_func.
    exact H0.
  + apply iter_sepcon_permutation. auto.
Qed.

Lemma iter_sepcon_emp: forall (p : B -> A) (l l' : list B), (forall x, p x |-- emp) -> NoDup l' -> incl l' l -> iter_sepcon l p |-- iter_sepcon l' p.
Proof.
  intros.
  revert l H1; induction l'; intros.
  + simpl; clear H1.
    induction l; simpl; auto.
    rewrite <- (emp_sepcon emp).
    apply sepcon_derives; auto.
  + inversion H0; subst.
    spec IHl'; [auto |].
    assert (In a l) by (specialize (H1 a); simpl in H1; auto).
    apply in_split in H2.
    destruct H2 as [l1 [l2 ?]].
    specialize (IHl' (l1 ++ l2)).
    spec IHl'.
    1: {
      clear - H2 H1 H4.
      intros x ?H.
      specialize (H1 x).
      spec H1; [simpl; auto |].
      subst.
      rewrite in_app_iff in H1; simpl in H1.
      rewrite in_app_iff.
      assert (a = x -> False) by (intros; subst; tauto).
      tauto.
    }
    subst.
    rewrite iter_sepcon_app_sepcon in *.
    simpl.
    rewrite (sepcon_comm (p a)), <- sepcon_assoc, (sepcon_comm _ (p a)).
    apply sepcon_derives; auto.
Qed.

Lemma iter_sepcon_nil: forall (p : B -> A), iter_sepcon nil p = emp.
Proof. intros; reflexivity. Qed.

End IterSepCon.

Lemma iter_sepcon_map: forall {A B C: Type} {ND : NatDed A} {SL : SepLog A} (l : list C) (f : B -> A) (g: C -> B),
                         iter_sepcon l (fun x : C => f (g x)) = iter_sepcon (map g l) f.
Proof. intros. induction l; simpl; [|f_equal]; auto. Qed.

Global Existing Instance iter_sepcon_permutation_proper.

Section IterPredSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.

Definition pred_sepcon (P: B -> Prop) (p: B -> A): A :=
  EX l: list B, !! (forall x, In x l <-> P x) && !! NoDup l && iter_sepcon l p.

Lemma pred_sepcon_eq: forall (P: B -> Prop) (p: B -> A),
    pred_sepcon P p =
    (EX l: list B, !! ((forall x, In x l <-> P x) /\ NoDup l) && iter_sepcon l p).
Proof.
  intros. unfold pred_sepcon. f_equal. extensionality l. rewrite prop_and. auto.
Qed.

Lemma pred_sepcon_strong_proper: forall P1 P2 p1 p2,
  (forall x, P1 x <-> P2 x) ->
  (forall x, P1 x -> P2 x -> p1 x = p2 x) ->
  pred_sepcon P1 p1 = pred_sepcon P2 p2.
Proof.
  assert (forall P1 P2 p1 p2,
    (forall x, P1 x <-> P2 x) ->
    (forall x, P1 x -> P2 x -> p1 x = p2 x) ->
    pred_sepcon P1 p1 |-- pred_sepcon P2 p2).
  2: intros; apply pred_ext; apply H; [auto | auto | symmetry; auto | symmetry; auto].
  intros.
  unfold pred_sepcon.
  apply exp_left; intro l; apply (exp_right l).
  normalize.
  assert (forall x : B, In x l <-> P2 x) by (intros; rewrite H1, H; reflexivity).
  normalize.
  erewrite iter_sepcon_func_strong; [apply derives_refl |].
  intros.
  specialize (H1 x); specialize (H3 x).
  apply H0; tauto.
Qed.

Instance pred_sepcon_proper: Proper (pointwise_relation B iff ==> pointwise_relation B eq ==> eq) pred_sepcon.
Proof.
  intros.
  do 2 (hnf; intros).
  apply pred_sepcon_strong_proper; intros; auto.
Defined.

Global Existing Instance pred_sepcon_proper.

Lemma pred_sepcon1: forall p x0,
  pred_sepcon (fun x => x = x0) p = p x0.
Proof.
  intros.
  unfold pred_sepcon.
  apply pred_ext.
  + apply exp_left; intro l.
    normalize.
    destruct l as [| ? [|]].
    - specialize (H x0); simpl in H.
      tauto.
    - specialize (H x0); simpl in H.
      assert (b = x0) by tauto; subst b.
      simpl.
      rewrite sepcon_emp; auto.
    - pose proof proj1 (H b) as HH; simpl in HH.
      spec HH; [auto |].
      subst b.
      pose proof proj1 (H b0) as HH; simpl in HH.
      spec HH; [auto |].
      subst b0.
      clear - H0.
      inversion H0; subst.
      simpl in H2; tauto.
  + apply (exp_right (x0 :: nil)).
    repeat apply andp_right.
    - apply prop_right.
      intros.
      simpl.
      split; [intros [? | ?]; [congruence | tauto] | left; congruence].
    - apply prop_right.
      constructor; [simpl; tauto | constructor].
    - simpl.
      rewrite sepcon_emp; auto.
Qed.

(* TODO: change this name to pred_sepcon_sepcon_xx. *)
Lemma pred_sepcon_sepcon: forall (P Q R: B -> Prop) p,
  Prop_join P Q R ->
  pred_sepcon P p * pred_sepcon Q p = pred_sepcon R p.
Proof.
  intros.
  destruct H.
  unfold pred_sepcon; apply pred_ext.
  + rewrite exp_sepcon1. apply exp_left; intro lP.
    rewrite exp_sepcon2. apply exp_left; intro lQ.
    normalize.
    apply (exp_right (lP ++ lQ)).
    apply andp_right; [apply andp_right |].
    - apply prop_right.
      intros.
      rewrite in_app_iff.
      firstorder.
    - apply prop_right.
      apply NoDup_app_inv; auto.
      firstorder.
    - rewrite <- iter_sepcon_app_sepcon; auto.
  + apply exp_left; intro l.
    rewrite andp_assoc.
    do 2 (apply derives_extract_prop; intro).
    destruct (spec_list_split l P Q R H2 H1 (conj H H0)) as [lp [lq [? [? [? [? ?]]]]]].
    rewrite exp_sepcon1. apply (exp_right lp).
    rewrite exp_sepcon2. apply (exp_right lq).
    normalize.
    rewrite H7, iter_sepcon_app_sepcon; auto.
Qed.

(* TODO: change this name to pred_sepcon_sepcon_x1. *)
(* TODO: add a lemma pred_sepcon_sepcon_1x. *)
Lemma pred_sepcon_sepcon1: forall (P P': B -> Prop) p x0,
  (forall x, P' x <-> P x \/ x = x0) ->
  ~ P x0 ->
  pred_sepcon P' p = pred_sepcon P p * p x0.
Proof.
  intros.
  rewrite <- pred_sepcon_sepcon with (Q := fun x => x = x0) (P := P).
  + f_equal.
    apply pred_sepcon1.
  + split; intros.
    - specialize (H a).
      assert (a = x0 -> ~ P a) by (intro; subst; auto).
      tauto.
    - subst.
      specialize (H x0).
      tauto.
Qed.

(* TODO: Maybe delete this one, this is not general enough.
  it only requires p x0 to be conflict with q x0. *)
Lemma pred_sepcon_unique_sepcon1: forall (P: B -> Prop) p x0,
  sepcon_unique1 p ->
  pred_sepcon P p * p x0 |-- !! (~ P x0).
Proof.
  intros.
  apply not_prop_right; intro.
  unfold pred_sepcon; normalize.
  rewrite <- H1 in H0.
  eapply derives_trans; [apply sepcon_derives; [apply iter_sepcon_in_true; eauto| apply derives_refl] |].
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply H | apply derives_refl] |].
  normalize.
Qed.

Lemma prop_forall_allp: forall (P: B -> Prop),
  !! (forall x, P x) = ALL x: B, !! P x.
Proof.
  intros.
  apply pred_ext.
  + apply allp_right; intros.
    apply prop_derives; intros.
    auto.
  + apply allp_prop_left.
Qed.

Lemma prop_impl_imp: forall (P Q: Prop),
  !! (P -> Q) = !! P --> !! Q.
Proof.
  intros.
  apply pred_ext.
  + apply imp_andp_adjoint.
    normalize.
  + apply prop_imp_prop_left.
Qed.

Lemma neg_pure_from_pred_sepcon: forall (P Q: B -> Prop) p,
  (forall x, Q x -> p x |-- FF) ->
  pred_sepcon P p |-- !! (Disjoint _ P Q).
Proof.
  intros.
  unfold pred_sepcon; normalize; intros.
  rename x into l.
  normalize.
  eapply derives_trans with (!! (forall x, P x -> Q x -> False)).
  2: apply prop_derives; rewrite Disjoint_spec; auto.
  rewrite prop_forall_allp.
  apply allp_right; intro x.
  rewrite !prop_impl_imp.
  apply imp_andp_adjoint; normalize.
  apply imp_andp_adjoint; normalize.
  rewrite <- H0 in H2.
  eapply derives_trans; [eapply iter_sepcon_in_true; eauto |].
  eapply derives_trans; [apply sepcon_derives; [apply H; auto | apply derives_refl] |].
  normalize.
Qed.

(* TODO: Maybe delete this one, this is not general enough.
  it only requires p x0 to be conflict with q x0. *)
Lemma pred_sepcon_unique_sepcon_seg: forall (P Q: B -> Prop) p,
  sepcon_unique1 p ->
  pred_sepcon P p * pred_sepcon Q p |-- !! (Disjoint _ P Q).
Proof.
  intros.
  unfold pred_sepcon; normalize; intros; normalize.
  rename l into lQ, x into lP.
  eapply derives_trans with (!! (forall x, P x -> Q x -> False)).
  2: apply prop_derives; rewrite Disjoint_spec; auto.
  rewrite prop_forall_allp.
  apply allp_right; intro x.
  rewrite !prop_impl_imp.
  apply imp_andp_adjoint; normalize.
  apply imp_andp_adjoint; normalize.
  rewrite <- H2 in H4.
  rewrite <- H0 in H5.
  eapply derives_trans; [apply sepcon_derives; [apply iter_sepcon_in_true; eauto| apply iter_sepcon_in_true; eauto] |].
  rewrite sepcon_assoc, (sepcon_comm TT), sepcon_assoc.
  rewrite TT_sepcon_TT, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply H | apply derives_refl] |].
  normalize.
Qed.

Lemma pred_sepcon_prop_true: forall (P: B -> Prop) p x,
  P x ->
  pred_sepcon P p |-- p x * TT.
Proof.
  intros.
  unfold pred_sepcon; normalize.
  intros.
  normalize.
  rename x0 into l.
  rewrite <- H0 in H.
  eapply iter_sepcon_in_true; auto.
Qed.

Lemma pred_sepcon_prop_true_weak:
  forall (P Q: B -> Prop) (qdec: forall x, Decidable (Q x)) p,
    (forall x, Q x -> P x) -> pred_sepcon P p |-- pred_sepcon Q p * TT.
Proof.
  intros. unfold pred_sepcon. normalize.
  apply (exp_right (filter (fun x => if (qdec x) then true else false) l)).
  rewrite <- prop_and, sepcon_andp_prop'.
  remember (filter (fun x0 : B => if qdec x0 then true else false) l) as l'.
  assert (forall x : B, In x l' <-> Q x). {
    intros. subst l'. rewrite filter_In. destruct (qdec x); split; intros; auto.
    - split; auto. apply H in H2. rewrite H0. auto.
    - destruct H2; inversion H3.
    - exfalso; auto.
  } assert (NoDup l') by (subst l'; apply NoDup_filter; auto). apply andp_right.
  - apply prop_right. split; auto.
  - apply iter_sepcon_incl_true; auto. intro. rewrite H0, H2. apply H.
Qed.

Lemma pred_sepcon_False: forall p,
  pred_sepcon (fun _ => False) p = emp.
Proof.
  intros.
  unfold pred_sepcon.
  apply pred_ext.
  + apply exp_left; intros.
    normalize.
    destruct x; [simpl; auto |].
    specialize (H b); simpl in H; tauto.
  + apply (exp_right nil).
    normalize. simpl.
    apply andp_right; auto.
    apply prop_right; constructor.
Qed.

Lemma pred_sepcon_Empty: forall p,
  pred_sepcon (Empty_set _) p = emp.
Proof.
  intros.
  rewrite <- pred_sepcon_False with p.
  apply pred_sepcon_proper; [| reflexivity].
  intros ?.
  rewrite Empty_set_spec; tauto.
Qed.

End IterPredSepCon.

(*

Section OconIterSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  Context {PSL : PreciseSepLog A}.
  Context {CoSL: CorableSepLog A}.
  Context {OSL: OverlapSepLog A}.
  Context {DSL : DisjointedSepLog A}.

  Lemma pred_sepcon_ocon:
    forall (P Q R: B -> Prop) p (eq_dec : forall x y : B, {x = y} + {x <> y}),
      (forall x, Decidable (P x)) -> (forall x, Decidable (Q x)) ->
      (forall a, P a \/ Q a <-> R a) ->
      (forall x : B, precise (p x)) ->
      joinable p ->
      pred_sepcon P p ⊗ pred_sepcon Q p = pred_sepcon R p.
  Proof.
    intros. unfold pred_sepcon. apply pred_ext.
    + normalize_overlap; intro lP.
      do 2 normalize_overlap. rename x into lQ.
      apply (exp_right (nodup eq_dec (lP ++ lQ))).
      rewrite (iter_sepcon_ocon eq_dec); auto. rewrite <- prop_and.
      apply andp_right; auto. apply prop_right. split; intros.
      2: apply NoDup_nodup. split; intros.
      - rewrite nodup_In in H6. rewrite <- H.
        rewrite in_app_iff in H6. rewrite H2 in H6. rewrite H4 in H6. auto.
      - rewrite nodup_In. rewrite <- H in H6.
        rewrite in_app_iff. rewrite H2. rewrite H4. auto.
    + normalize. intro lR; intros. normalize. normalize_overlap.
      assert (forall a, In a lR <-> P a \/ Q a) by (clear -H H2; firstorder).
      destruct (or_dec_prop_list_split _ _ _ H3 X X0 H4) as [lP [lQ [? [? [? [? ?]]]]]].
      apply (exp_right lP). normalize_overlap. apply (exp_right lQ).
      rewrite <- prop_and. normalize_overlap. apply andp_right.
      - apply prop_right. intuition.
      - rewrite <- iter_sepcon_ocon' with (l := lR); auto.
  Qed.

  Lemma pred_sepcon_ocon1:
    forall (Q R: B -> Prop) p z (eq_dec : forall x y : B, {x = y} + {x <> y}),
      (forall x, Decidable (Q x)) ->
      (forall a, a = z \/ Q a <-> R a) ->
      (forall x : B, precise (p x)) ->
      joinable p ->
      p z ⊗ pred_sepcon Q p = pred_sepcon R p.
  Proof.
    intros. rewrite <- (pred_sepcon_ocon (fun x => x = z) Q R); auto.
    + f_equal. rewrite pred_sepcon1. auto.
    + intros. apply eq_dec.
  Qed.

End OconIterSepCon.
 *)
