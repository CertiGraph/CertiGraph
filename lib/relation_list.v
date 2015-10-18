Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.List_Func_ext.
Require Export RamifyCoq.lib.Relation_ext.

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

Lemma eq_relation_list: forall {A B} {R: relation A} {EqRA: Equivalence R} (l: list B),
  inclusion _ (relation_list (map (fun _ => R) l)) R.
Proof.
  intros.
  unfold relation_list.
  induction l.
  + simpl.
    hnf; intros.
    subst; reflexivity.
  + simpl map.
    rewrite monoid_fold_left_head.
    2: apply compond_eq_left.
    2: apply compond_eq_right.
    2: apply compond_assoc.
    hnf; intros.
    inversion H; subst.
    transitivity y0.
    - auto.
    - apply IHl; auto.
Qed.
