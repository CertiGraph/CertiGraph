Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Export Coq.Classes.Morphisms.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Set Implicit Arguments.

Section IterSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  Context {PSL : PreciseSepLog A}.
  Context {CoSL: CorableSepLog A}.
  Context {OSL: OverlapSepLog A}.
  Context {DSL : DisjointedSepLog A}.

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

Lemma precise_iter_sepcon: forall (p : B -> A), (forall z, precise (p z)) -> forall (l : list B), precise (iter_sepcon l p).
Proof. intros; induction l; simpl. apply precise_emp. apply precise_sepcon; auto. Qed.

Lemma iter_sepcon_in_true: forall (p : B -> A) (l : list B) x, In x l -> iter_sepcon l p |-- p x * TT.
Proof.
  intros. apply in_split in H. destruct H as [l1 [l2 ?]]. subst.
  rewrite iter_sepcon_app_comm. rewrite <- app_comm_cons. simpl.
  apply sepcon_derives; auto. apply TT_right.
Qed.

Definition sepcon_unique (p : B -> A) :Prop := forall x, p x * p x |-- FF.

Lemma iter_sepcon_unique_nodup: forall (p : B -> A) (l : list B), sepcon_unique p -> iter_sepcon l p |-- !!(NoDup l).
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
*)

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
    Focus 1. {
      apply eq_as_set_permutation; auto.
      rewrite H.
      apply eq_as_set_spec; intro x.
      unfold eq_as_set, Sublist.
      pose proof (Permutation_in x H0).
      pose proof (Permutation_in x H1).
      pose proof (Permutation_in x (Permutation_sym H0)).
      pose proof (Permutation_in x (Permutation_sym H1)).
      pose proof (in_app_iff i1 i2 x).
      pose proof (in_app_iff i2 i3 x).
      pose proof (in_app_iff i1 (i2 ++ i3) x).
      pose proof (in_app_iff l1 l2 x).
      tauto.
    } Unfocus.
    rewrite (iter_sepcon_permutation _ H3).
    rewrite !iter_sepcon_app_sepcon.
    eapply derives_trans;
    [ apply ocon_sepcon; apply disj_ocon_right
    | apply sepcon_derives; [auto | apply ocon_sepcon]];
    apply iter_sepcon_app_joinable; auto; intros;
    apply NoDup_app_eq in H2; destruct H2 as [? [? ?]];
    generalize (NoDup_app_not_in _ _ _  H5 x); intro; specialize (H6 x); auto;
    specialize (H6 H4); intro; apply H6; apply in_or_app; auto.
Qed.

Lemma iter_sepcon_ocon (eq_dec: forall x y : B, {x = y} + {x <> y}):
  forall l1 l2 p,
    NoDup l1 -> NoDup l2 ->
    (forall x, precise (p x)) -> joinable p ->
    iter_sepcon l1 p ⊗ iter_sepcon l2 p = iter_sepcon (remove_dup eq_dec (l1 ++ l2)) p.
Proof.
  intros.
  symmetry; apply iter_sepcon_ocon'; auto.
  + apply remove_dup_nodup; auto.
  + intros.
    rewrite <- remove_dup_in_inv.
    rewrite in_app_iff.
    tauto.
Qed.

Lemma precise_exp_iter_sepcon: forall (P : B -> A) (Q: list B -> Prop),
  sepcon_unique P ->
  (exists x : list B, Q x /\ NoDup x) \/ ~ (exists x : list B, Q x /\ NoDup x) ->
  (forall l, precise (P l)) ->
  (forall l l', Q l -> Q l' -> NoDup l -> NoDup l' -> Permutation l l') ->
  precise (EX l: list B, !! (Q l) && iter_sepcon l P).
Proof.
  intros.
  replace (EX  l : list B, !!Q l && iter_sepcon l P) with (EX  l : list B, !! (Q l /\ NoDup l) && iter_sepcon l P).
  Focus 2. {
    f_equal.
    extensionality l.
    rewrite (add_andp _ _ (iter_sepcon_unique_nodup l H)) at 2.
    rewrite (andp_comm _ (!! NoDup l)), <- andp_assoc, prop_and.
    reflexivity.
  } Unfocus.
  apply precise_exp_prop_andp.
  1: assumption.
  1: apply precise_iter_sepcon; auto.
  intros l l'. specialize (H2 l l').
  intros.
  apply iter_sepcon_permutation.
  tauto.
Qed.

Lemma iter_sepcon_ramification: forall P g g' l l',
  (exists f, Permutation g (l ++ f) /\ Permutation g' (l' ++ f)) ->
  iter_sepcon g P |-- iter_sepcon l P * (iter_sepcon l' P -* iter_sepcon g' P).
Proof.
  intros.
  destruct H as [f [? ?]].
  rewrite (iter_sepcon_permutation _ H).
  rewrite (iter_sepcon_permutation _ H0).
  rewrite !iter_sepcon_app_sepcon.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  auto.
Qed.

Lemma exists_iter_sepcon_ramification:
  forall (T: Type) (PureF: T -> Prop) P g l (g' l': T -> list B),
  (exists f, Permutation g (l ++ f) /\
     forall t, PureF t -> Permutation (g' t) ((l' t) ++ f)) ->
  iter_sepcon g P |-- iter_sepcon l P *
   ((EX t: T, !! PureF t && iter_sepcon (l' t) P) -*
    (EX t: T, !! PureF t && iter_sepcon (g' t) P)).
Proof.
  intros.
  destruct H as [f [? ?]].
  rewrite (iter_sepcon_permutation _ H).
  rewrite iter_sepcon_app_sepcon.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  normalize.
  apply (exp_right t).
  normalize.
  apply H0 in H1.
  rewrite (iter_sepcon_permutation _ H1).
  rewrite iter_sepcon_app_sepcon.  
  rewrite sepcon_comm.
  auto.
Qed.

Lemma iter_sepcon_func: forall l P Q, (forall x, P x = Q x) -> iter_sepcon l P = iter_sepcon l Q.
Proof. intros. induction l; simpl; [|f_equal]; auto. Qed.

Lemma iter_sepcon_func_strong: forall l P Q, (forall x, In x l -> P x = Q x) -> iter_sepcon l P = iter_sepcon l Q.
Proof.
  intros. induction l.
  + reflexivity.
  + simpl.
    f_equal.
    - apply H.
      simpl; auto.
    - apply IHl.
      intros; apply H.
      simpl; auto.
Qed. 

Instance iter_sepcon_permutation_proper : Proper ((@Permutation B) ==> (pointwise_relation B eq) ==> eq) iter_sepcon.
Proof.
  repeat intro. transitivity (iter_sepcon x y0).
  + apply iter_sepcon_func.
    exact H0.
  + apply iter_sepcon_permutation. auto.
Qed.

Lemma iter_sepcon_emp: forall (p : B -> A) (l l' : list B), (forall x, p x |-- emp) -> NoDup l' -> Sublist l' l -> iter_sepcon l p |-- iter_sepcon l' p.
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
    Focus 1. {
      clear - H2 H1 H4.
      intros x ?H.
      specialize (H1 x).
      spec H1; [simpl; auto |].
      subst.
      rewrite in_app_iff in H1; simpl in H1.
      rewrite in_app_iff.
      assert (a = x -> False) by (intros; subst; tauto).
      tauto.
    } Unfocus.
    subst.
    rewrite iter_sepcon_app_sepcon in *.
    simpl.
    rewrite (sepcon_comm (p a)), <- sepcon_assoc, (sepcon_comm _ (p a)).
    apply sepcon_derives; auto.
Qed.

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

Lemma pred_sepcon_ramify1: forall {EqB: EqDec B eq} (P1 P2: B -> Prop) p1 p2 x,
  P1 x ->
  (forall y, P1 y <-> P2 y) ->
  (forall y, y <> x -> p1 y = p2 y) ->
  pred_sepcon P1 p1 |-- p1 x * (p2 x -* pred_sepcon P2 p2).
Proof.
  intros.
  unfold pred_sepcon.
  normalize.
  intros l ?.
  normalize.
  apply solve_ramify with (iter_sepcon (remove equiv_dec x l) p2);
   [replace (iter_sepcon (remove equiv_dec x l) p2) with (iter_sepcon (remove equiv_dec x l) p1) |].
  + change (p1 x * iter_sepcon (remove equiv_dec x l) p1) with
      (iter_sepcon (x :: remove equiv_dec x l) p1).
    erewrite iter_sepcon_permutation; [apply derives_refl |].
    apply nodup_remove_perm; auto.
    firstorder.
  + apply iter_sepcon_func_strong.
    intros.
    rewrite remove_in_3 in H4.
    apply H1; tauto.
  + apply (exp_right l).
    assert (forall x0 : B, In x0 l <-> P2 x0) by firstorder.
    normalize.
    rewrite sepcon_comm.
    change (p2 x * iter_sepcon (remove equiv_dec x l) p2) with
      (iter_sepcon (x :: remove equiv_dec x l) p2).
    erewrite iter_sepcon_permutation; [apply derives_refl |].
    symmetry.
    apply nodup_remove_perm; auto.
    firstorder.
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

Lemma pred_sepcon_ramify_pred: forall (Pg1 Pl1 Pg2 Pl2: B -> Prop) p1 p2,
  (forall x, {Pl1 x} + {~ Pl1 x}) ->
  (forall x, Pl1 x -> Pg1 x) ->
  (forall x, Pg2 x <-> (Pg1 x /\ ~ Pl1 x) \/ Pl2 x) ->
  (forall x, Pg1 x /\ ~ Pl1 x -> p1 x = p2 x) ->
  pred_sepcon Pg1 p1 |-- pred_sepcon Pl1 p1 * (pred_sepcon Pl2 p2 -* pred_sepcon Pg2 p2).
Proof.
  intros.
  unfold pred_sepcon.
  normalize.
Admitted.
(*
  apply (exp_right (
*)

End IterPredSepCon.