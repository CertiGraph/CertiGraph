Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.List_Func_ext.
Require Export RamifyCoq.lib.Relation_ext.

(* TODO: define a general pointwise relation on list *)
Inductive same_relation_list {A: Type}: list (relation A) -> list (relation A) -> Prop :=
  | same_relation_list_nil :
      same_relation_list nil nil
  | same_relation_list_cons :
      forall x xs y ys,
      same_relation A x y ->
      same_relation_list xs ys -> 
      same_relation_list (x :: xs) (y :: ys).

Lemma same_relation_list_refl: forall {A} (rs: list (relation A)), same_relation_list rs rs.
Proof.
  intros.
  induction rs; constructor; auto.
  reflexivity.
Qed.

Lemma same_relation_list_symm: forall {A} (rs1 rs2: list (relation A)),
  same_relation_list rs1 rs2 -> same_relation_list rs2 rs1.
Proof.
  intros.
  induction H; constructor.
  + symmetry; auto.
  + auto.
Qed.

Lemma same_relation_list_trans: forall {A} (rs1 rs2 rs3: list (relation A)),
  same_relation_list rs1 rs2 ->
  same_relation_list rs2 rs3 ->
  same_relation_list rs1 rs3.
Proof.
  intros.
  rename H0 into HH.
  revert rs3 HH; induction H; intros;
  inversion HH; subst; constructor.
  + rewrite H; auto.
  + auto.
Qed.

Instance Equivalence_same_relation_list {A}: Equivalence (@same_relation_list A).
Proof.
  split.
  + exact same_relation_list_refl.
  + exact same_relation_list_symm.
  + exact same_relation_list_trans.
Defined.

Instance cons_relation_proper {A}: Proper (same_relation A ==> same_relation_list ==> same_relation_list) (@cons (relation A)).
Proof.
  do 2 (hnf; intros).
  apply same_relation_list_cons; auto.
Defined.

Definition relation_list {A: Type} (R: list (relation A)) : relation A := fold_left compond_relation R eq.
    
Lemma relation_list_app: forall {A: Type} (R R': list (relation A)),
  same_relation _ (relation_list (R ++ R')) (compond_relation (relation_list R) (relation_list R')).
Proof.
  intros.
  apply monoid_fold_left_app.
  + apply compond_eq_left.
  + apply compond_eq_right.
  + apply compond_assoc.
Qed.

Lemma relation_list_head: forall {A: Type} a (l: list (relation A)),
  same_relation _ (relation_list (a :: l)) (compond_relation a (relation_list l)).
Proof.
  intros.
  apply monoid_fold_left_head.
  + apply compond_eq_left.
  + apply compond_eq_right.
  + apply compond_assoc.
Qed.

Lemma relation_list_tail: forall {A: Type} (l: list (relation A)) a,
  same_relation _ (relation_list (l ++ a :: nil)) (compond_relation (relation_list l) a).
Proof.
  intros.
  apply monoid_fold_left_tail.
Qed.

Lemma relation_list_nil: forall {A}, same_relation A (relation_list nil) eq.
Proof.
  intros.
  reflexivity.
Qed.

Lemma eq_relation_list: forall {A B} {R: relation A} {EqRA: Equivalence R} (l: list B),
  inclusion _ (relation_list (map (fun _ => R) l)) R.
Proof.
  intros.
  induction l.
  + simpl; rewrite relation_list_nil.
    hnf; intros.
    subst; reflexivity.
  + simpl map.
    rewrite relation_list_head.
    hnf; intros.
    inversion H; subst.
    transitivity y0.
    - auto.
    - apply IHl; auto.
Qed.

Lemma relation_list_weaken_ind: forall {A B} (R R': B -> relation A) l a1 a2,
  (forall bs_done b0 a2 a3,
     In (bs_done, b0) (cprefix l) ->
     relation_list (map R bs_done) a1 a2 ->
     R b0 a2 a3 ->
     R' b0 a2 a3) ->
  relation_list (map R l) a1 a2 ->
  relation_list (map R' l) a1 a2.
Proof.
  intros.
  revert a2 H0; rev_induction l; intros.
  + simpl in H0 |- *; auto.
  + revert H1.
    rewrite !map_app; simpl.
    erewrite !(app_same_relation (relation_list _)) by apply relation_list_tail.
    intro.
    destruct H1.
    apply compond_intro with y.
    - apply H; auto.
      clear - H0.
      intros; apply (H0 bs_done); auto.
      rewrite combine_prefixes_app_1.
      apply in_app_iff.
      left; auto.
    - apply (H0 l); auto.
      rewrite combine_prefixes_app_1.
      apply in_app_iff.
      right; simpl; auto.
Qed.

Lemma relation_list_weaken_ind': forall {A B} (R R': B -> relation A) l a1 a2,
  (forall bs_done b0 a2 a3,
     In (bs_done, b0) (cprefix l) ->
     relation_list (map R bs_done) a1 a2 ->
     relation_list (map R' bs_done) a1 a2 ->
     R b0 a2 a3 ->
     R' b0 a2 a3) ->
  relation_list (map R l) a1 a2 ->
  relation_list (map R' l) a1 a2.
Proof.
  intros.
  revert a2 H0; rev_induction l; intros.
  + simpl in H0 |- *; auto.
  + revert H1.
    rewrite !map_app; simpl.
    erewrite !(app_same_relation (relation_list _)) by apply relation_list_tail.
    intro.
    destruct H1.
    assert (relation_list (map R' l) x0 y).
    - apply H; auto.
      clear - H0.
      intros; apply (H0 bs_done); auto.
      rewrite combine_prefixes_app_1.
      apply in_app_iff.
      left; auto.
    - apply compond_intro with y; auto.
      apply (H0 l); auto.
      rewrite combine_prefixes_app_1.
      apply in_app_iff.
      right; simpl; auto.
Qed.

Lemma relation_list_inclusion: forall {A B} (R R': B -> relation A) l,
  (forall b, In b l -> inclusion _ (R b) (R' b)) ->
  inclusion _ (relation_list (map R l)) (relation_list (map R' l)).
Proof.
  intros.
  induction l.
  + simpl.
    hnf; auto.
  + simpl map.
    rewrite relation_list_head.
    rewrite relation_list_head.
    apply compond_relation_inclusion.
    - apply H; simpl; auto.
    - apply IHl; intros.
      apply H; simpl; auto.
Qed.

Lemma relation_list_conjunction: forall {A B} (R R': B -> relation A) l,
  inclusion _ (relation_list (map (fun b => relation_conjunction (R b) (R' b)) l)) (relation_conjunction (relation_list (map R l)) (relation_list (map R' l))).
Proof.
  intros.
  simpl.
  induction l.
  - simpl.
    rewrite relation_list_nil.
    hnf; intros.
    rewrite relation_conjunction_iff.
    auto.
  - simpl map.
    rewrite !relation_list_head.
    hnf; intros.
    inv H.
    apply IHl in H1.
    rewrite relation_conjunction_iff.
    destruct H0, H1.
    split; apply compond_intro with y0; auto.
Qed.

Lemma respectful_relation_list: forall {B A} (f: B -> A) (l: list (relation A)),
  inclusion _
   (relation_list (map (respectful_relation f) l))
   (respectful_relation f (relation_list l)).
Proof.
  intros; hnf; intros.
  revert x y H; induction l; intros.
  + unfold relation_list in H.
    simpl in *.
    subst.
    reflexivity.
  + simpl.
    erewrite app_same_relation by (rewrite relation_list_head; reflexivity).
    apply respectful_compond_relation.
    simpl in H.
    erewrite app_same_relation in H by (rewrite relation_list_head; reflexivity).
    inversion H; subst.
    apply compond_intro with y0; auto.
Qed.

Lemma relation_list_singleton: forall {A} (R: relation A), same_relation _ (relation_list (R :: nil)) R.
Proof.
  intros.
  unfold relation_list; simpl.
  apply compond_eq_left.
Qed.

Instance relation_list_proper {A: Type}: Proper (same_relation_list ==> same_relation A) relation_list.
Proof.
  hnf; intros.
  induction H.
  + reflexivity.
  + rewrite !relation_list_head.
    rewrite H.
    rewrite IHsame_relation_list.
    reflexivity.
Qed.

Ltac split_relation_list L :=
  match goal with
  | |- relation_list _ ?x ?z =>
         match L with
         | nil =>
            try rewrite ((proj1 (same_relation_spec _ _) (relation_list_singleton _)) x z)
         | ?y :: ?L0 =>
            rewrite ((proj1 (same_relation_spec _ _) (relation_list_head _ _)) x z);
            apply compond_intro with y; [| split_relation_list L0]
         end
  end.

Ltac destruct_relation_list_aux cont H x z L := 
  match L with
  | ?A :: ?L0 =>
     match L0 with
     | _ :: _ =>
         fun y =>
         destruct_relation_list_aux ltac:(cont;
           rewrite ((proj1 (same_relation_spec _ _) (relation_list_head _ _)) x z) in H;
           let HH := fresh "H" in
           apply compond_relation_spec in H; destruct H as [y [HH H]]) H y z L0
     | _ => cont;
         try rewrite ((proj1 (same_relation_spec _ _) (relation_list_singleton _)) x z) in H
     end
  | _ => cont
  end.

Ltac destruct_relation_list' H :=
  match type of H with
  | relation_list ?L ?x ?z => destruct_relation_list_aux idtac H x z L
  end.

Tactic Notation "destruct_relation_list" ident(x0) "in" hyp(H) := destruct_relation_list' H x0.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) "in" hyp(H) := destruct_relation_list' H x0 x1.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) "in" hyp(H) := destruct_relation_list' H x0 x1 x2.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4 x5.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4 x5 x6.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4 x5 x6 x7.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4 x5 x6 x7 x8.
Tactic Notation "destruct_relation_list" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) "in" hyp(H) := destruct_relation_list' H x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
