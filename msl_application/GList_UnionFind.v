Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GList.

Local Open Scope logic.

Section GList_UnionFind.

  Context {pSGG: pSpatialGraph_GList}.
  Context {sSGG: sSpatialGraph_GList nat unit}.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Notation Graph := (@Graph pSGG nat unit unit).

  Lemma uf_root_vgamma: forall (g: Graph) v n, vvalid g v -> vgamma g v = (n, v) -> uf_root g v v.
  Proof.
    intros. split.
    - apply reachable_refl; auto.
    - intros. apply (parent_loop g _ n); auto.
  Qed.

  Lemma vgamma_not_reachable': forall (g: Graph) x r pa y, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> reachable g pa y -> ~ reachable g y x.
  Proof. intros. apply (dst_not_reachable _ (liGraph g) _ pa); auto. simpl in H0. destruct (SGBA_VE (dst g (x, tt)) null); inversion H0; [exfalso |]; auto. Qed.

  Lemma vgamma_not_reachable: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> ~ reachable g pa x.
  Proof. intros. assert (vvalid g pa) by (apply valid_parent in H0; auto). apply (vgamma_not_reachable' g x r pa pa); auto. apply reachable_refl; auto. Qed.

  Lemma findS_preserves_vgamma: forall (g1 g2: Graph) x r pa, vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> findS g1 pa g2 -> vgamma g2 x = (r, pa).
  Proof.
    intros. assert (Hr: ~ reachable g1 pa x) by (apply vgamma_not_reachable with r; auto). simpl in *. destruct (SGBA_VE (dst g1 (x, tt)) null). 1: inversion H0; exfalso; auto.
    unfold complement, Equivalence.equiv in c. rewrite <- H0. destruct H2 as [? [[? ?] ?]]. f_equal.
    - assert (vvalid g2 x) by (rewrite <- H3; auto). specialize (H5 x H H6). unfold Graph_LGraph. rewrite H5. auto.
    - assert (evalid (predicate_partialgraph (lg_gg g1) (fun n : addr => ~ reachable (lg_gg g1) pa n)) (x, tt)). {
        simpl. hnf. assert ((x, tt) = (x, tt)) by auto. pose proof (@only_one_edge _ _ _ _ g1 _ (liGraph g1) x (x, tt) H). simpl in H7. rewrite <- H7 in H6.
        clear H7. unfold Graph_LGraph in H6. destruct H6. rewrite H6. split; auto. 
      } destruct H2 as [_ [? [_ ?]]]. pose proof H6. rewrite H2 in H8. clear H2. specialize (H7 _ H6 H8). simpl in H7. unfold Graph_LGraph. rewrite <- H7.
      destruct (SGBA_VE (dst (lg_gg g1) (x, tt)) null); [exfalso |]; auto.
  Qed.

  Lemma graph_ramify_aux_parent: forall {RamUnit: Type} (g: Graph) x r pa,
      vvalid g x -> vgamma g x = (r, pa) ->
      (reachable_vertices_at x g: pred) |-- reachable_vertices_at pa g *
      (ALL a : RamUnit * addr * Graph, !! (findS g pa (snd a) /\
                                           reachable (snd a) pa (snd (fst a)) /\
                                           (forall y : addr, reachable (snd a) (snd (fst a)) y -> snd (fst a) = y)) -->
                                          (vertices_at (reachable g pa) (snd a) -* vertices_at (reachable g x) (snd a))).
  Proof.
    intros. eapply vertices_at_ramif_xQ; auto. eexists; split; [|split].
    - eapply Prop_join_reachable_parent; auto. apply H0.
    - intros. eapply Prop_join_reachable_parent; auto. apply H0.
    - intros. destruct a as [[? rt] g']. rewrite vertices_identical_spec. intros y ?.
      rewrite Intersection_spec in H2. unfold Complement, Ensembles.In in H2.
      destruct H2. simpl in *. destruct H1 as [? [? ?]]. destruct (SGBA_VE (dst g (x, tt))); inversion H0.
      + subst pa. exfalso; auto.
      + pose proof (lst_out_edge_only_one g (liGraph g) x pa y). simpl in H6. specialize (H6 H8 H2 H3). subst y. destruct H1 as [? [[? ?] ?]]. f_equal.
        * assert (vvalid g' x) by (rewrite <- H6; auto). specialize (H10 x H H11). unfold Graph_LGraph. rewrite H10. auto.
        * assert (evalid (predicate_partialgraph (lg_gg g) (fun n : addr => ~ reachable (lg_gg g) pa n)) (x, tt)). {
            simpl. hnf. assert ((x, tt) = (x, tt)) by auto. pose proof (@only_one_edge _ _ _ _ g _ (liGraph g) x (x, tt) H). simpl in H12. rewrite <- H12 in H11.
            clear H12. unfold Graph_LGraph in H11. destruct H11. rewrite H11. auto.
          } destruct H1 as [? [? [? ?]]]. pose proof H11. rewrite H12 in H11. specialize (H14 _ H15 H11). clear H1 H12 H13 H11 H15. simpl in H14.
          unfold Graph_LGraph. rewrite <- H14. auto.
  Qed.

  Lemma graph_gen_redirect_parent_ramify: forall (g1 g2: Graph) x r pa pa' (H: weak_valid g2 pa') (Hv: vvalid g2 x) (Hn: ~ reachable g2 pa' x),
      vvalid g1 x -> vgamma g2 x = (r, pa) -> pa' <> null ->
      (vertices_at (reachable g1 x) g2: pred)
        |-- vertex_at x (r, pa) * (vertex_at x (r, pa') -* vertices_at (reachable g1 x) (Graph_gen_redirect_parent g2 x pa' H Hv Hn)).
  Proof.
    intros. assert (vgamma (Graph_gen_redirect_parent g2 x pa' H Hv Hn) x = (r, pa')). {
      simpl in *. remember (updateEdgeFunc (dst (lg_gg g2)) (x, tt) pa' (x, tt)).
      inversion H1. f_equal. unfold updateEdgeFunc in Heqy. destruct (equiv_dec (x, tt) (x, tt)).
      2: compute in c; exfalso; apply c; auto. subst y. destruct (SGBA_VE pa' null); [exfalso| ]; auto.
    } apply vertices_at_ramif_1; auto. eexists. split; [|split].
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. apply reachable_by_refl; auto.
      + intros; destruct_eq_dec x x0; auto.
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. apply reachable_by_refl; auto.
      + intros; destruct_eq_dec x x0; auto.
    - rewrite vertices_identical_spec. simpl. intros. change (lg_gg g2) with (g2: LGraph).
      rewrite Intersection_spec in H4. destruct H4. unfold Complement, In in H5. unfold updateEdgeFunc.
      destruct (equiv_dec (x, tt) (x0, tt)); auto. compute in e. exfalso. inversion e. auto.
  Qed.

  Lemma graph_gen_redirect_parent_findS: forall (g1 g2: Graph) x r pa pa' (H: weak_valid g2 pa') (Hv: vvalid g2 x) (Hn: ~ reachable g2 pa' x),
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> findS g1 pa g2 -> findS g1 x (Graph_gen_redirect_parent g2 x pa' H Hv Hn).
  Proof.
    intros. hnf. simpl. split; [|split].
    - hnf. simpl. split; [|split; [|split]].
      + intros. unfold predicate_vvalid. simpl.
  Abort.

End GList_UnionFind.
