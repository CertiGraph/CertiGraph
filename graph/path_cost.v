Require Import VST.floyd.proofauto.
Require Import Coq.Classes.EquivDec.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.

Local Open Scope Z_scope.

Section PathCost.

  Context {V E DV DG : Type}.

  Context {V_EqDec : EqDec V eq}. 
  Context {E_EqDec : EqDec E eq}.
  
  Definition path_cost (g: LabeledGraph V E DV Z DG) (path: @path V E) : Z :=
    fold_left Z.add (map (elabel g) (snd path)) 0.

  Lemma path_cost_zero:
    forall (g: LabeledGraph V E DV Z DG) src,
      path_cost g (src, []) = 0.
  Proof.
    intros. unfold path_cost; trivial.
  Qed.

  Lemma one_step_path_Znth:
    forall (g: LabeledGraph V E DV Z DG) s e,
      path_cost g (s, e :: nil) = elabel g e.
  Proof.
    intros. unfold path_cost; simpl.
    apply Z.add_0_l.
  Qed.

  Lemma acc_pos: forall (g: LabeledGraph V E DV Z DG) l z,
      (forall e : E, In e l -> 0 <= elabel g e) ->
      0 <= z ->
      0 <= fold_left Z.add (map (elabel g) l) z.
  Proof.
    intro. induction l; intros; simpl; auto. apply IHl.
    - intros. apply H. now apply in_cons.
    - assert (In a (a :: l)) by apply in_eq.
      specialize (H _ H1). lia.
  Qed.

  Lemma path_cost_init:
    forall l init s,
      fold_left Z.add l (init + s) =
      init + (fold_left Z.add l s).
  Proof.
    intros.
    generalize dependent s.
    induction l.
    - intros; simpl. trivial. 
    - intros; simpl.
      rewrite <- Z.add_assoc.
      rewrite IHl. lia.
  Qed.

  Lemma path_cost_path_glue:
    forall (g: LabeledGraph V E DV Z DG) p1 p2,
      path_cost g (path_glue p1 p2) =
      path_cost g p1 + path_cost g p2.
  Proof.
    intros.
    unfold path_cost at 1, path_glue at 1.
    simpl. rewrite map_app.
    rewrite fold_left_app.
    assert ((fold_left Z.add (map (elabel g) (snd p1)) 0) = (path_cost g p1))
      by now unfold path_cost.
    rewrite H. 
    unfold path_cost at 3.
    remember (map (elabel g) (snd p2)) as l2.
    remember (path_cost g p1) as c1.
    replace c1 with (c1 + 0) at 1 by lia.
    rewrite path_cost_init; trivial.
  Qed.
 
End PathCost.
