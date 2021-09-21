Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
(* for ufgraph *)
Require Import CertiGraph.graph.path_lemmas.
(*for unionfind*)
Require Export CertiGraph.graph.UnionFind.
Require Import CertiGraph.msl_application.ArrayGraph.
Require Import CertiGraph.unionfind.env_unionfind_arr.
(*spanning tree definition*)
Require Import CertiGraph.graph.undirected_graph.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.
Local Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Lemma reachable_uf_equiv_connected:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    reachable g1 u v ->
    connected g2 u v.
Proof.
  intros.
  pose proof (reachable_foot_valid _ _ _ H0).
  pose proof (reachable_head_valid _ _ _ H0).
  destruct H.
  assert (EnumEnsembles.EnumCovered Z (evalid g2)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  assert (EnumEnsembles.EnumCovered Z (evalid g1)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  assert (vvalid g2 u). {
    apply H; trivial.
  }
  assert (vvalid g2 v). {
    apply H; trivial.
  }
  pose proof (uf_root_always_exists g1 (liGraph g1) u X0 H2).
  pose proof (uf_root_always_exists g1 (liGraph g1) v X0 H1).
  pose proof (uf_root_always_exists g2 (liGraph g2) u X H4).
  pose proof (uf_root_always_exists g2 (liGraph g2) v X H5).
  destruct H6 as [ur1 ?].
  destruct H7 as [vr1 ?].
  destruct H8 as [ur2 ?].
  destruct H9 as [vr2 ?].
  pose proof (H3 _ _ _ H6 H8).
  pose proof (H3 _ _ _ H7 H9).
  pose proof (uf_root_reachable _ _ _ _ H0 H7).
  pose proof (uf_root_unique _ _ _ _ _ H6 H12).
  subst ur1. subst vr1. subst vr2.
  clear H6 H7.
  destruct H8 as [? _].
  destruct H9 as [? _].
  apply reachable_implies_connected in H6.
  apply reachable_implies_connected in H7.
  apply connected_symm in H7.
  apply (connected_trans _ _ _ _ H6 H7).
Qed.

Lemma uf_equiv_adjacent_connected:
  forall (g1 g2 : UFGraph) u v,
    uf_equiv g1 g2 ->
    adjacent g1 u v ->
    connected g2 u v.
Proof.
  intros.
  apply adjacent_reachable in H0.
  destruct H0.
  - apply (reachable_uf_equiv_connected g1); trivial.
  - apply connected_symm.
    apply (reachable_uf_equiv_connected g1); trivial.
Qed.

Lemma uf_equiv_connected':
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    connected g1 u v ->
    connected g2 u v.
Proof.
  intros.
  rewrite connected_exists_path in H0.
  destruct H0 as [p [? [? ?]]].
  generalize dependent u.
  induction p.
  - intros. inversion H1.
  - destruct p.
    + intros. simpl in H1, H2.
      inversion H1. inversion H2.
      subst.
      apply connected_refl; trivial.
      simpl in H0. destruct H. apply H; trivial.
    + destruct H0.
      rewrite last_error_cons in H2.
      2: unfold not; inversion 1.
      specialize (IHp H1 H2).
      intros.
      simpl in H3. inversion H3; subst a; clear H3.
      assert (connected g2 z v). {
        apply adjacent_requires_vvalid in H0.
        destruct H0.
        apply IHp; trivial.
      }
      apply (uf_equiv_adjacent_connected _ g2) in H0; trivial.
      apply (connected_trans _ _ _ _ H0 H3).
Qed.

Lemma uf_equiv_connected:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    connected g1 u v <-> connected g2 u v.
Proof.
  intros. split; intros.
  - apply (uf_equiv_connected' g1); trivial.
  - apply uf_equiv_sym in H.
    apply (uf_equiv_connected' g2); trivial.
Qed.

Lemma adjacent_ufroot_same:
  forall (g: UFGraph) u v,
    adjacent g u v ->
    ufroot_same g u v.
Proof.
  intros.
  apply adjacent_reachable in H.
  destruct H.
  - apply (reachable_ufroot_same _ (liGraph g)); trivial. 
  - apply ufroot_same_symm, (reachable_ufroot_same _ (liGraph g)); trivial.
Qed.

Lemma connected_ufroot_same:
  forall (g: UFGraph) u v,
    connected g u v ->
    ufroot_same g u v.
Proof.
  intros.
  rewrite connected_exists_path in H.
  destruct H as [p [? [? ?]]].
  generalize dependent u.
  induction p.
  - intros. inversion H1.
  - destruct p.
    + intros. simpl in H1, H0.
      inversion H1. inversion H0.
      subst. apply (ufroot_same_refl _ (liGraph g)).
      simpl in H; trivial.
    + destruct H.
      rewrite last_error_cons in H1.
      2: unfold not; inversion 1.
      specialize (IHp H0 H1).
      intros.
      simpl in H2. inversion H2; subst a; clear H2.
      apply adjacent_ufroot_same in H.
      apply (ufroot_same_trans _ (liGraph g) _ z); trivial.
      apply IHp. trivial.
Qed.

Lemma ufroot_same_connected:
  forall (g: UFGraph) u v,
    ufroot_same g u v ->
    connected g u v.
Proof.
  intros.
  destruct H as [r [[? _] [? _]]].
  apply reachable_implies_connected in H.
  apply reachable_implies_connected in H0.
  apply connected_symm in H0.
  apply (connected_trans _ _ _ _ H H0).
Qed.

Lemma connected_ufroot_same_iff:
  forall (g: UFGraph) u v,
    connected g u v <-> ufroot_same g u v. 
Proof.
  intros. split; intros.
  apply connected_ufroot_same; trivial.
  apply ufroot_same_connected; trivial.
Qed.

Lemma uf_equiv_ufroot_same:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    ufroot_same g1 u v <-> ufroot_same g2 u v.
Proof.
intros. do 2 rewrite <- connected_ufroot_same_iff. apply uf_equiv_connected. auto.
Qed.