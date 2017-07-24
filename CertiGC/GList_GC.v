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

  Lemma the_same_root_union: forall (g g1 g2: Graph) x y root,
      vvalid g x -> vvalid g y -> uf_equiv g g1 -> uf_equiv g1 g2 -> uf_root g1 x root -> uf_root g2 y root -> uf_union g x y g2.
  Proof. intros. apply (same_root_union g g1 g2 x y root); auto. Qed.

  Lemma uf_equiv_root_the_same: forall (g1 g2: Graph) x root, uf_equiv g1 g2 -> uf_root g1 x root <-> uf_root g2 x root.
  Proof. intros. pose proof (@uf_equiv_the_same_root _ _ _ _ _ _ _ _ (fun x: addr => (x, tt)) is_null_SGBA fml g1 g2 x root H). apply H0. Qed.

  Lemma uf_equiv_not_reachable: forall (g1 g2: Graph) x r pa root,
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> uf_equiv g1 g2 -> uf_root g2 pa root -> ~ reachable g2 root x.
  Proof.
    intros. pose proof H3. rewrite <- (uf_equiv_root_the_same _ _ pa root H2) in H4. destruct H3. intro. apply H5 in H6. subst x.
    pose proof (vgamma_not_reachable g1 root r pa H H0 H1). destruct H4. auto.
  Qed.

  Lemma graph_gen_redirect_parent_equiv: forall (g1 g2: Graph) x r pa root (Hv: vvalid g2 x) (Hn: ~ reachable g2 root x),
      vvalid g1 x -> vgamma g1 x = (r, pa) -> pa <> x -> uf_equiv g1 g2 -> uf_root g2 pa root -> uf_equiv g1 (pregraph_gen_dst g2 (x, tt) root).
  Proof.
    intros. apply (@uf_equiv_trans _ _ _ _ g2 _ (liGraph g2) _ (maGraph g2) (finGraph g2)); auto. split; intro y; simpl; [intuition |]. intros.
    assert (Decidable (reachable g2 y x)) by (apply Graph_reachable_dec; left; destruct H4; apply reachable_head_valid in H4; auto).
    apply decidable_prop_decidable in H6. destruct H6.
    - assert (uf_root g2 x root). {
        rewrite <- (uf_equiv_root_the_same g1); auto.
        apply (uf_root_edge g1 (liGraph g1) x pa); [| apply (vgamma_not_dst g1 x r) | rewrite (uf_equiv_root_the_same g1 g2)]; auto.
      } pose proof (uf_root_gen_dst_same g2 (liGraph g2) _ _ _ H7 Hn H6). simpl in H8.
      pose proof (uf_root_unique _ (gen_dst_preserve_lst g2 (liGraph g2) _ _ Hn Hv) _ _ _ H5 H8). subst r2.
      pose proof (uf_root_reachable _ _ _ _ H6 H7). apply (uf_root_unique g2 (liGraph g2) _ _ _ H4 H9).
    - apply (uf_root_unique _ (gen_dst_preserve_lst g2 (liGraph g2) _ _ Hn Hv) y); auto. apply (uf_root_gen_dst_preserve g2 (liGraph g2)); auto.
  Qed.

  Lemma graph_gen_redirect_parent_findS: forall (g1 g2: Graph) x r1 r2 pa pa' (H: weak_valid g2 pa') (Hv: vvalid g2 x) (Hn: ~ reachable g2 pa' x),
      vvalid g1 x -> vgamma g1 x = (r1, pa) -> pa <> x -> vgamma g2 x = (r2, pa) -> findS g1 pa g2 -> uf_root g2 pa pa' ->
      findS g1 x (Graph_gen_redirect_parent g2 x pa' H Hv Hn).
  Proof.
    intros. hnf. simpl. destruct H4 as [? [? ?]]. hnf in H4. simpl in H4. unfold predicate_vvalid, predicate_weak_evalid in H4. split; [|split].
    - assert (forall v, ~ reachable (lg_gg g1) x v -> ~ reachable (lg_gg g1) pa v). {
        intros. intro. apply H8. pose proof (gamma_parent_reachable_included g1 x r1 pa H0 H1). apply H10. auto. }
      assert (forall v, ~ reachable (lg_gg g1) pa v <-> ~ reachable (lg_gg g1) x v \/ x = v). {
        intros. split; intros.
        - destruct_eq_dec x v; [right | left]; auto. intro. apply H9. apply reachable_ind.reachable_ind in H11. destruct H11. 1: exfalso; auto.
          destruct H11 as [z [[_ [_ ?]] [? ?]]]. rewrite (dst_step g1 (liGraph g1) x pa) in H11; auto; [subst pa | apply (vgamma_not_dst g1 x r1)]; auto.
        - destruct H9.
          + apply H8; auto.
          + subst v. apply vgamma_not_reachable with r1; auto.
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
    - apply (graph_gen_redirect_parent_equiv _ _ _ r1 pa); auto.
    - apply H7.
  Qed.

  Lemma diff_root_union_1: forall (g g1 g2: Graph) x y x_root y_root,
      uf_equiv g g1 -> uf_root g1 x x_root -> uf_equiv g1 g2 -> uf_root g2 y y_root -> x_root <> y_root ->
      (@weak_valid _ _ _ _ g2 _ (maGraph g2) y_root) -> vvalid g2 x_root ->
      ~ reachable g2 y_root x_root -> uf_union g x y (pregraph_gen_dst g2 (x_root, tt) y_root).
  Proof.
    intros. assert (uf_equiv g g2) by (apply (@uf_equiv_trans _ _ _ _ g1 _ (liGraph g1) _ (maGraph g1) (finGraph g1)); auto).
    pose proof (uf_equiv_union g g2 (Graph_gen_redirect_parent g2 x_root y_root H4 H5 H6) x y H7). simpl in H8. apply H8.
    apply (@diff_root_union _ _ _ _ _ _ _ _ (fun x: addr => (x, tt)) is_null_SGBA fml); auto. apply (uf_equiv_root_the_same g1); auto.
  Qed.

  Lemma diff_root_union_2: forall (g g1 g2: Graph) x y x_root y_root,
      uf_equiv g g1 -> uf_root g1 x x_root -> uf_equiv g1 g2 -> uf_root g2 y y_root -> x_root <> y_root -> (@weak_valid _ _ _ _ g2 _ (maGraph g2) x_root) -> vvalid g2 y_root ->
      ~ reachable g2 x_root y_root -> uf_union g x y (pregraph_gen_dst g2 (y_root, tt) x_root).
  Proof.
    intros. assert (uf_equiv g g2) by (apply (@uf_equiv_trans _ _ _ _ g1 _ (liGraph g1) _ (maGraph g1) (finGraph g1)); auto).
    pose proof (uf_equiv_union g g2 (Graph_gen_redirect_parent g2 y_root x_root H4 H5 H6) y x H7). simpl in H8. apply uf_union_sym. apply H8.
    apply (@diff_root_union _ _ _ _ _ _ _ _ (fun x: addr => (x, tt)) is_null_SGBA fml); auto. apply (uf_equiv_root_the_same g1); auto.
  Qed.

  Lemma graph_gen_redirect_parent_vgamma: forall (g1 g2: Graph) x r pa y (H: weak_valid g1 x) (Hv: vvalid g1 y) (Hn: ~ reachable g1 x y),
      vgamma g1 x = (r, pa) -> g2 = (Graph_gen_redirect_parent g1 y x H Hv Hn) -> vgamma g2 x = (r, pa).
  Proof.
    intros. rewrite H1. clear H1. simpl in *. inversion H0. f_equal. unfold updateEdgeFunc.
    destruct (equiv_dec (y, tt) (x, tt)); [hnf in e; inversion e; subst; exfalso; apply Hn; apply reachable_refl|]; auto.
  Qed.

  Lemma graph_vgen_ramify: forall (g: Graph) x r1 r2 pa,
      vvalid g x -> vgamma g x = (r1, pa) -> (vertices_at (vvalid g) g: pred) |-- vertex_at x (r1, pa) * (vertex_at x (r2, pa) -* vertices_at (vvalid g) (Graph_vgen g x r2)).
  Proof.
    intros. assert (vgamma (Graph_vgen g x r2) x = (r2, pa)). {
      simpl in *. inversion H0. f_equal. unfold update_vlabel. destruct (equiv_dec x x); auto. compute in c. exfalso; auto.
    } apply vertices_at_ramif_1; auto. eexists. split; [|split].
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - rewrite vertices_identical_spec. simpl. intros. change (lg_gg g) with (g: LGraph).
      rewrite Intersection_spec in H2. destruct H2. unfold Complement, In in H3. unfold update_vlabel. f_equal. destruct (equiv_dec x x0); auto. hnf in e. exfalso; auto.
  Qed.

  Lemma uf_under_bound_redirect_parent: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      uf_root g x root -> uf_under_bound id g -> uf_under_bound id (Graph_gen_redirect_parent g x root Hw Hv Hr).
  Proof.
    intros. hnf in H0 |-* . simpl. unfold uf_bound, id in *. intros. destruct p as [p l]. destruct H. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H4 H2 H3).
    - destruct H5. apply H0; auto.
    - destruct H5 as [? [l1 [? ?]]]. subst l. subst v. simpl. destruct H as [l2 ?]. destruct l2 as [? l2]. assert (a = x) by (destruct H as [[? _] ?]; simpl in H; auto).
      subst a. destruct l2. 1: destruct H as [[_ ?] ?]; simpl in H; subst root; exfalso; apply Hr; apply reachable_refl; auto.
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H7 H). unfold path_glue in H5. simpl in H5. destruct H5 as [[_ ?] [? _]]. pose proof (H0 _ H1 _ H6 H5). simpl in H8.
      clear -H8. rewrite app_length in *. simpl in *. intuition.
  Qed.

  Lemma uf_under_bound_redirect_parent_lt: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      vlabel g x < vlabel g root -> (forall y, reachable g root y -> root = y) -> uf_under_bound id g -> uf_under_bound id (Graph_gen_redirect_parent g x root Hw Hv Hr).
  Proof.
    intros. hnf in H1 |-* . simpl. unfold uf_bound, id in *. intros. destruct p as [p l]. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H0 H3 H4).
    - destruct H5; apply H1; auto.
    - destruct H5 as [? [l1 [? ?]]]. subst l. subst v. simpl. destruct H7 as [[_ ?] [? _]]. specialize (H1 _ Hv _ H6 H5). simpl in H1. rewrite app_length. simpl.
      clear - H H1. unfold Graph_LGraph in H. intuition.
  Qed.

  Lemma uf_under_bound_redirect_parent_eq: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      vlabel g x = vlabel g root -> (forall y, reachable g root y -> root = y) -> uf_under_bound id g ->
      uf_under_bound id (Graph_vgen (Graph_gen_redirect_parent g x root Hw Hv Hr) root (vlabel g root + 1)).
  Proof.
    intros. hnf in H1 |-* . simpl. unfold uf_bound, id, update_vlabel in *. intros. destruct p as [p l]. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H0 H3 H4).
    - destruct H5. specialize (H1 _ H2 _ H5 H6). simpl in H1 |-* . clear -H1. destruct (equiv_dec root v); [hnf in e; subst v |]; intuition.
    - destruct H5 as [? [l1 [? ?]]]. subst l. subst v. destruct (equiv_dec root root). 2: compute in c; exfalso; apply c; auto. simpl. destruct H7 as [[_ ?] [? _]].
      specialize (H1 _ Hv _ H6 H5). simpl in H1. rewrite app_length. simpl. clear -H H1. unfold Graph_LGraph in *. intuition.
  Qed.

End GList_UnionFind.
