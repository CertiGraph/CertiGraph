Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.GList.

Local Open Scope logic.

Section GList_UnionFind.

  Context {pSGG: pPointwiseGraph_GList}.
  Context {sSGG: sPointwiseGraph_GList nat unit}.

  Definition SGraph := (PointwiseGraph addr (addr * unit) (nat * addr) unit).

  Definition LGraph := (@LGraph addr (addr * unit) _ _ nat unit unit).
  Definition Graph := (@Graph addr (addr * unit) _ _ is_null_SGBA (fun x => (x, tt)) nat unit unit).

  Definition UGraph_LGraph (G: Graph): LGraph := lg_gg G.
  Definition LGraph_SGraph (G: LGraph): SGraph := Graph_PointwiseGraph G.

  Local Coercion UGraph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  
  Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
  Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.
  Local Identity Coercion SGraph_SpatialGraph: SGraph >-> PointwiseGraph.

  Global Existing Instance fml.

  Instance maGraph(G: Graph): MathGraph G is_null_SGBA := maGraph G.
  Instance finGraph (G: Graph): FiniteGraph G := finGraph G.
  Instance liGraph (G: Graph):  LstGraph G (fun x => (x, tt)) := liGraph G.

  Definition vgamma := (@vgamma addr (addr * unit) SGBA_VE SGBA_EE is_null_SGBA (fun x => (x, tt)) nat unit unit).

  Definition Graph_gen_redirect_parent (g: Graph) (x: addr) (pa: addr) (H: weak_valid g pa) (Hv: vvalid g x) (Hn: ~ reachable g pa x): Graph :=
    Graph_gen_redirect_parent g x pa H Hv Hn.

  Lemma graph_gen_redirect_parent_ramify: forall (g: Graph) x r pa root (H: weak_valid g root) (Hv: vvalid g x) (Hn: ~ reachable g root x),
      vgamma g x = (r, pa) -> root <> null -> 
      (vertices_at (vvalid g) g: pred) 
        |-- vertex_at x (r, pa) * (vertex_at x (r, root) -* vertices_at (vvalid g) (Graph_gen_redirect_parent g x root H Hv Hn)).
  Proof.
    intros. assert (vgamma (Graph_gen_redirect_parent g x root H Hv Hn) x = (r, root)). {
      simpl in *. remember (updateEdgeFunc (dst (lg_gg g)) (x, tt) root (x, tt)).
      inversion H0. unfold vgamma, UnionFindGraph.vgamma. simpl. f_equal. unfold updateEdgeFunc in *. destruct (equiv_dec (x, tt) (x, tt)).
      2: compute in c; exfalso; apply c; auto. subst a. destruct (SGBA_VE root null); [exfalso| ]; auto.
    } apply vertices_at_ramif_1; auto. eexists. split; [|split].
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - rewrite vertices_identical_spec. simpl. intros. change (lg_gg g) with (g: LGraph).
      rewrite Intersection_spec in H3. destruct H3. unfold Complement, In in H4. unfold vgamma, UnionFindGraph.vgamma. simpl. unfold updateEdgeFunc.
      destruct (equiv_dec (x, tt) (x0, tt)); auto. compute in e. exfalso. inversion e. auto.
  Qed.

  Definition ggrp_rel (g : Graph) (x root : addr) (g' : Graph) : Prop :=
    exists H1 H2 H3, g' = Graph_gen_redirect_parent g x root H1 H2 H3.

  Lemma graph_gen_redirect_parent_ramify_rel: forall (g: Graph) x r pa root g',
      ggrp_rel g x root g' ->
      vgamma g x = (r, pa) -> root <> null -> 
      (vertices_at (vvalid g) g: pred) 
        |-- vertex_at x (r, pa) * (vertex_at x (r, root) -* vertices_at (vvalid g) g').
  Proof. intros g x r pa root g' [Ha [Hb [Hc Heq]]] ? ?. subst g'. apply graph_gen_redirect_parent_ramify; auto. Qed. 

  Definition Graph_vgen (G: Graph) (x: addr) (d: nat) : Graph := Graph_vgen G x d.

  Lemma graph_vgen_ramify: forall (g: Graph) x r1 r2 pa,
      vvalid g x -> vgamma g x = (r1, pa) -> (vertices_at (vvalid g) g: pred) |-- vertex_at x (r1, pa) * (vertex_at x (r2, pa) -* vertices_at (vvalid g) (Graph_vgen g x r2)).
  Proof.
    intros. assert (vgamma (Graph_vgen g x r2) x = (r2, pa)). {
      simpl in *. inversion H0. unfold vgamma, UnionFindGraph.vgamma. simpl. f_equal. unfold update_vlabel. destruct (equiv_dec x x); auto. compute in c. exfalso; auto.
    } apply vertices_at_ramif_1; auto. eexists. split; [|split].
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - apply Ensemble_join_Intersection_Complement.
      + unfold Included, In; intro y. intros. subst. auto.
      + intros; destruct_eq_dec x x0; auto.
    - rewrite vertices_identical_spec. simpl. intros. change (lg_gg g) with (g: LGraph).
      rewrite Intersection_spec in H2. destruct H2. unfold Complement, In in H3. unfold vgamma, UnionFindGraph.vgamma. simpl.
      unfold update_vlabel. f_equal. destruct (equiv_dec x x0); auto. hnf in e. exfalso; auto.
  Qed.

  Lemma uf_under_bound_redirect_parent: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      uf_root g x root -> uf_under_bound id g -> uf_under_bound id (Graph_gen_redirect_parent g x root Hw Hv Hr).
  Proof.
    intros. hnf in H0 |-* . simpl. unfold uf_bound, id in *. intros. destruct p as [p l]. destruct H. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H4 H2 H3).
    - destruct H5. apply H0; auto.
    - destruct H5 as [? [l1 [? ?]]]. subst l. subst v. simpl. destruct H as [l2 ?]. destruct l2 as [? l2]. assert (a = x) by (destruct H as [[? _] ?]; simpl in H; auto).
      subst a. destruct l2. 1: destruct H as [[_ ?] ?]; simpl in H; subst root; exfalso; apply Hr; apply reachable_refl; auto.
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H7 H). unfold path_glue in H3. simpl in H3. destruct H3 as [[_ ?] [? _]].
      rewrite <- H5 in H3. pose proof (H0 _ H1 _ H6 H3). simpl in H8.
      clear -H8. rewrite app_length in *. simpl in *. intuition.
  Qed.

  Lemma uf_under_bound_redirect_parent_lt: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      vlabel g x < vlabel g root -> (forall y, reachable g root y -> root = y) -> uf_under_bound id g -> uf_under_bound id (Graph_gen_redirect_parent g x root Hw Hv Hr).
  Proof.
    intros. hnf in H1 |-* . simpl. unfold uf_bound, id in *. intros. destruct p as [p l]. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H0 H3 H4).
    - destruct H5; apply H1; auto.
    - destruct H5 as [? [l1 [? ?]]]. subst l. clear H4. subst v. simpl. destruct H7 as [[_ ?] [? _]]. specialize (H1 _ Hv _ H5 H4). simpl in H1. rewrite app_length. simpl length.
      clear - H H1. unfold Graph_LGraph in H. assert (vlabel (lg_gg g) x < vlabel (lg_gg g) root) by intuition. intuition.
  Qed.

  Lemma uf_under_bound_redirect_parent_eq: forall (g: Graph) root x (Hw : weak_valid g root) (Hv : vvalid g x) (Hr: ~ reachable g root x),
      vlabel g x = vlabel g root -> (forall y, reachable g root y -> root = y) -> uf_under_bound id g ->
      uf_under_bound id (Graph_vgen (Graph_gen_redirect_parent g x root Hw Hv Hr) root (vlabel g root + 1)).
  Proof.
    intros. hnf in H1 |-* . simpl. unfold uf_bound, id, update_vlabel in *. intros. destruct p as [p l]. destruct (redirect_to_root g (liGraph g) _ _ _ _ _ Hv Hr H0 H3 H4).
    - destruct H5. specialize (H1 _ H2 _ H5 H6). simpl in H1 |-* . clear -H1. destruct (equiv_dec root v); [hnf in e; subst v |]; intuition.
    - destruct H5 as [? [l1 [? ?]]]. subst l. clear H4. subst v. destruct (equiv_dec root root). 2: compute in c; exfalso; apply c; auto. simpl. destruct H7 as [[_ ?] [? _]].
      specialize (H1 _ Hv _ H5 H4). simpl in H1. rewrite app_length. simpl. clear -H H1. unfold Graph_LGraph in *. assert (vlabel (lg_gg g) x = vlabel g root) by intuition. intuition.
  Qed.

  Definition make_set_Graph (default_dv: nat) (default_de: unit) (default_dg: unit) (v: addr) (g: Graph) (Hn: v <> null) (Hi: ~ vvalid g v) : Graph := make_set_Graph default_dv default_de default_dg v g Hn Hi.
End GList_UnionFind.
