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

  Lemma vgamma_not_dst: forall (g: Graph) x r pa, vgamma g x = (r, pa) -> pa <> x -> dst g (x, tt) = pa.
  Proof. intros. simpl in H. destruct (SGBA_VE (dst g (x, tt)) null); inversion H; [exfalso |]; auto. Qed.

  Lemma vgamma_not_edge: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> g |= x ~> pa.
  Proof.
    intros. assert (vvalid g pa) by (apply valid_parent in H0; auto). hnf. split; [|split]; auto.
    apply (vgamma_not_dst g x r) in H1; auto. rewrite step_spec. exists (x, tt).
    pose proof (vvalid_src_evalid _ (liGraph g) _ H). destruct H3. split; auto.
  Qed.

  Lemma vgamma_not_reachable': forall (g: Graph) x r pa y, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> reachable g pa y -> ~ reachable g y x.
  Proof. intros. apply (dst_not_reachable _ (liGraph g) _ pa); auto. apply (vgamma_not_dst g x r); auto. Qed.

  Lemma vgamma_not_reachable: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> pa <> x -> ~ reachable g pa x.
  Proof. intros. assert (vvalid g pa) by (apply valid_parent in H0; auto). apply (vgamma_not_reachable' g x r pa pa); auto. apply reachable_refl; auto. Qed.

  Instance fml : FML_General addr (addr * unit) nat unit unit LiMaFin (fun x => (x, tt)) is_null_SGBA. Proof. constructor; intros; destruct X; auto. Defined.

  Global Existing Instance fml.

  Lemma findS_preserves_vgamma: forall (g1 g2: Graph) x r pa, vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> findS g1 pa g2 -> vgamma g2 x = (r, pa).
  Proof.
    intros. assert (Hr: ~ reachable g1 pa x) by (apply vgamma_not_reachable with r; auto). simpl in *. destruct (SGBA_VE (dst g1 (x, tt)) null). 1: inversion H0; exfalso; auto.
    unfold complement, Equivalence.equiv in c. rewrite <- H0. destruct H2 as [? [[? ?] ?]]. f_equal.
    - assert (vvalid g2 x) by (rewrite <- H3; auto). specialize (H5 x H H6). unfold Graph_LGraph. rewrite H5. auto.
    - assert (evalid (predicate_partialgraph (lg_gg g1) (fun n : addr => ~ reachable (lg_gg g1) pa n)) (x, tt)). {
        simpl. hnf. pose proof (vvalid_src_evalid _ (liGraph g1) _ H). unfold Graph_LGraph in H6. destruct H6. rewrite H6. split; auto. 
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
            simpl. hnf. pose proof (vvalid_src_evalid _ (liGraph g) _ H). unfold Graph_LGraph in H11. destruct H11. rewrite H11. auto.
          } destruct H1 as [? [? [? ?]]]. pose proof H11. rewrite H12 in H11. specialize (H14 _ H15 H11). clear H1 H12 H13 H11 H15. simpl in H14.
          unfold Graph_LGraph. rewrite <- H14. auto.
  Qed.

  Lemma graph_gen_redirect_parent_ramify: forall (g: Graph) x r pa root (H: weak_valid g root) (Hv: vvalid g x) (Hn: ~ reachable g root x),
      vgamma g x = (r, pa) -> root <> null ->
      (vertices_at (vvalid g) g: pred)
        |-- vertex_at x (r, pa) * (vertex_at x (r, root) -* vertices_at (vvalid g) (Graph_gen_redirect_parent g x root H Hv Hn)).
  Proof.
    intros. assert (vgamma (Graph_gen_redirect_parent g x root H Hv Hn) x = (r, root)). {
      simpl in *. remember (updateEdgeFunc (dst (lg_gg g)) (x, tt) root (x, tt)).
      inversion H0. f_equal. unfold updateEdgeFunc in Heqy. destruct (equiv_dec (x, tt) (x, tt)).
      2: compute in c; exfalso; apply c; auto. subst y. destruct (SGBA_VE root null); [exfalso| ]; auto.
    } apply vertices_at_ramif_1; auto. eexists. split; [|split].
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - rewrite vertices_identical_spec. simpl. intros. change (lg_gg g) with (g: LGraph).
      rewrite Intersection_spec in H3. destruct H3. unfold Complement, In in H4. unfold updateEdgeFunc.
      destruct (equiv_dec (x, tt) (x0, tt)); auto. compute in e. exfalso. inversion e. auto.
  Qed.

  Lemma graph_gen_redirect_parent_findS: forall (g1 g2: Graph) x r pa pa' (H: weak_valid g2 pa') (Hv: vvalid g2 x) (Hn: ~ reachable g2 pa' x),
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> vgamma g2 x = (r, pa) -> findS g1 pa g2 -> uf_root g2 pa pa' -> findS g1 x (Graph_gen_redirect_parent g2 x pa' H Hv Hn).
  Proof.
    intros. hnf. simpl. destruct H4 as [? [? ?]]. hnf in H4. simpl in H4. unfold predicate_vvalid, predicate_weak_evalid in H4. split; [|split].
    - assert (forall v, ~ reachable (lg_gg g1) x v -> ~ reachable (lg_gg g1) pa v). {
        intros. intro. apply H8. pose proof (gamma_parent_reachable_included g1 x r pa H0 H1). apply H10. auto. }
      assert (forall v, ~ reachable (lg_gg g1) pa v <-> ~ reachable (lg_gg g1) x v \/ x = v). {
        intros. split; intros.
        - destruct_eq_dec x v; [right | left]; auto. intro. apply H9. apply reachable_ind.reachable_ind in H11. destruct H11. 1: exfalso; auto.
          destruct H11 as [z [[_ [_ ?]] [? ?]]]. rewrite (dst_step g1 (liGraph g1) x pa) in H11; auto; [subst pa | apply (vgamma_not_dst g1 x r)]; auto.
        - destruct H9.
          + apply H8; auto.
          + subst v. apply vgamma_not_reachable with r; auto.
      } hnf. simpl. unfold predicate_vvalid, predicate_weak_evalid. simpl. destruct H4 as [? [? [? ?]]]. split; [|split; [|split]]; intros.
      + split; intros; destruct H13; split; auto; apply H8 in H14; pose proof (conj H13 H14); [rewrite H4 in H15 | rewrite <- H4 in H15]; destruct H15; auto.
      + split; intros; destruct H13.
        * pose proof (H8 _ H14). pose proof (conj H13 H15). rewrite H10 in H16. destruct H16. rewrite H9 in H17. destruct H17. 1: split; auto. symmetry in H17.
          pose proof (conj H17 H16). rewrite (@only_one_edge _ _ _ _ g2 _ (liGraph g2)) in H18; auto. subst e. pose proof (vvalid_src_evalid _ (liGraph g1) _ H0).
          destruct H18 as [? _]. unfold Graph_LGraph in H18. rewrite H18 in H14. exfalso. apply H14. apply reachable_refl. auto.
        * pose proof (H8 _ H14). pose proof (conj H13 H15). rewrite <- H10 in H16. destruct H16. rewrite H9 in H17. destruct H17. 1: split; auto. symmetry in H17.
          pose proof (conj H17 H16). rewrite (@only_one_edge _ _ _ _ g1 _ (liGraph g1)) in H18; auto. subst e. pose proof (vvalid_src_evalid _ (liGraph g2) _ Hv).
          destruct H18 as [? _]. unfold Graph_LGraph in H18. rewrite H18 in H14. exfalso. apply H14. apply reachable_refl. auto.
      + destruct H13, H14. apply H8 in H15. apply H8 in H16. apply H11; auto.
      + unfold updateEdgeFunc. destruct (equiv_dec (x, tt) e).
        * unfold Equivalence.equiv in e0. subst e. pose proof (vvalid_src_evalid _ (liGraph g1) _ H0).
          destruct H15. unfold Graph_LGraph in H15. destruct H13. exfalso. apply H17. rewrite H15. apply reachable_refl; auto.
        * destruct H13, H14. apply H8 in H15. apply H8 in H16. apply H12; auto.
    - hnf. simpl. split; intro y; destruct H6. 1: apply H6. intros. assert (vvalid (lg_gg g1) y) by (destruct H9 as [? _]; apply reachable_head_valid in H9; auto).
      assert (Decidable (reachable g2 y x)). (apply Graph_reachable_dec; left; rewrite <- H6; auto). apply decidable_prop_decidable in H12. destruct H12.
      + assert (uf_root g2 x pa') by (apply (uf_root_edge g2 (liGraph g2) x pa); auto; apply (vgamma_not_dst g2 x r); auto).
        pose proof (uf_root_gen_dst g2 (liGraph g2) _ _ _ H13 Hn H12). simpl in H14.
        pose proof (uf_root_unique _ (gen_dst_preserve_lst g2 (liGraph g2) _ _ Hn Hv) _ _ _ H10 H14). subst pa'. apply (H8 y); auto.
        apply uf_root_reachable with x; auto.
      + assert (uf_root (lg_gg g2) y r2). {
          pose proof (vvalid_src_evalid _ (liGraph g2) _ Hv). destruct H13 as [? _]. unfold Graph_LGraph in H13. destruct H10.
          assert (reachable (lg_gg g2) y r2) by (rewrite <- (not_reachable_gen_dst_equiv (lg_gg g2) y (x, tt) pa'); auto; rewrite H13; auto). split; auto; intros.
          apply H14. rewrite not_reachable_gen_dst_equiv; auto. rewrite H13. intro. apply H12. apply reachable_trans with r2; auto.
        } apply (H8 y); auto.
    - apply H7. 
  Qed.

  Lemma the_same_root_union: forall (g g1 g2: Graph) x y root,
      vvalid g x -> vvalid g y -> findS g x g1 -> findS g1 y g2 -> uf_root g1 x root -> uf_root g2 y root -> uf_union g x y g2.
  Proof. intros. apply (same_root_union g g1 g2 x y root); auto. Qed.

End GList_UnionFind.
