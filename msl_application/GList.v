Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
Require Export RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.Graph.

Local Open Scope logic.

Class pSpatialGraph_GList: Type :=
  {
    addr: Type;
    null: addr;
    pred: Type;
    SGBA: SpatialGraphBasicAssum addr (addr * unit)
  }.

Existing Instance SGBA.

Definition is_null_SGBA {pSGG: pSpatialGraph_GList} : DecidablePred addr := (existT (fun P => forall a, {P a} + {~ P a}) (fun x => x = null) (fun x => SGBA_VE x null)).

Class sSpatialGraph_GList {pSGG_Bi: pSpatialGraph_GList} (DV DE: Type): Type :=
  {
    SGP: SpatialGraphPred addr (addr * unit) (DV * addr) unit pred;
    SGA: SpatialGraphAssum SGP;
    SGAvs: SpatialGraphAssum_vs SGP;
    SGAvn: SpatialGraphAssum_vn SGP null
  }.

Existing Instances SGP SGA SGAvs.

Section GRAPH_GList.

  Context {pSGG: pSpatialGraph_GList}.
  Context {DV DE DG: Type}.

  Class LiMaFin (g: PreGraph addr (addr * unit)) :=
    {
      li: LstGraph g (fun x => (x, tt));
      ma: MathGraph g is_null_SGBA;
      fin: FiniteGraph g
    }.

  Definition Graph := (GeneralGraph addr (addr * unit) DV DE DG (fun g => LiMaFin (pg_lg g))).
  Definition LGraph := (LabeledGraph addr (addr * unit) DV DE DG).
  Definition SGraph := (SpatialGraph addr (addr * unit) (DV * addr) unit).

  Instance SGC_GList: SpatialGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_SpatialGraphConstructor _ _ _ _ _ _ _ SGBA _ _).
    + exact (fun G v => (vlabel G v, let target := dst (pg_lg G) (v, tt) in if (SGBA_VE target null) then v else target)).
    + exact (fun _ _ => tt).
  Defined.

  Instance L_SGC_GList: Local_SpatialGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_Local_SpatialGraphConstructor
              _ _ _ _ _ _ _ SGBA SGC_GList
              (fun G v => evalid (pg_lg G) (v, tt) /\ src (pg_lg G) (v, tt) = v) _
              (fun _ _ => True) _).
    - intros. simpl. destruct H as [? ?], H0 as [? ?]. f_equal; auto. pose proof (H3 _ H H5 H0 H6). rewrite <- !H7. clear H7.
      destruct (SGBA_VE (dst (pg_lg G1) (x, tt)) null); auto.
    - intros; simpl. auto.
  Defined.

  Global Existing Instances SGC_GList L_SGC_GList.

  Definition Graph_LGraph (G: Graph): LGraph := lg_gg G.
  Definition LGraph_SGraph (G: LGraph): SGraph := Graph_SpatialGraph G.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Instance maGraph(G: Graph): MathGraph G is_null_SGBA := @ma G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance finGraph (G: Graph): FiniteGraph G := @fin G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance liGraph (G: Graph):  LstGraph G (fun x => (x, tt)) := @li G (@sound_gg _ _ _ _ _ _ _ _ G).

  Instance RGF (G: Graph): ReachableFiniteGraph G.
  Proof.
    apply Build_ReachableFiniteGraph.
    intros.
    apply finite_reachable_computable with (is_null := is_null_SGBA) in H.
    - destruct H as [l [? ?]]. exists l; auto.
    - apply maGraph.
    - apply (LocalFiniteGraph_FiniteGraph G), finGraph.
    - apply (FiniteGraph_EnumCovered G), finGraph.
  Defined.

  Definition single_uf_pregraph (v: addr) : PreGraph addr (addr * unit) :=
    pregraph_add_edge (single_vertex_pregraph v) (v, tt) v null.

  Lemma single_uf_is_uf: forall v, v <> null -> uf_graph (single_uf_pregraph v).
  Proof.
    intros. hnf. intros. hnf. exists (v, nil). split.
    - hnf. auto.
    - intros. hnf in H0. subst v. destruct H1 as [[v p] [[? ?] [? ?]]]. simpl in H0. subst v. destruct p.
      + simpl in *. subst y. exists (x, nil). split.
        * split; [split; split|]; simpl; auto. intros. destruct H0 as [[? ?] [? ?]]. destruct x'. simpl in H0. subst a. destruct l; auto. clear H5. exfalso.
          destruct H4 as [_ ?]. simpl in H0. assert (strong_evalid (single_uf_pregraph x) p) by (destruct l; intuition). clear H0. rename H4 into H0.
          hnf in H0. simpl in H0. unfold updateEdgeFunc in H0. destruct H0 as [? [_ ?]]. unfold addValidFunc in H0. destruct H0; auto. subst p.
          destruct (equiv_dec (x, tt) (x, tt)); [| compute in c]; intuition.
        * apply Subpath_refl.
      + exfalso. clear H3. simpl in H2. destruct H2 as [_ ?]. assert (strong_evalid (single_uf_pregraph x) p) by (destruct p0; intuition). clear H0. rename H2 into H0.
        hnf in H0. simpl in H0. unfold updateEdgeFunc in H0. destruct H0 as [? [_ ?]]. unfold addValidFunc in H0. destruct H0; auto. subst p.
        destruct (equiv_dec (x, tt) (x, tt)); [| compute in c]; intuition.
  Qed.

  Lemma reachabel_single_uf: forall x y, x <> null -> reachable (single_uf_pregraph x) x y <-> x = y.
  Proof.
    intros. split; intros.
    - destruct H0 as [[? ?] [[? ?] [? _]]]. simpl in H0. subst a. destruct l.
      + simpl in H1. auto.
      + destruct H2. simpl in H2. assert (strong_evalid (single_uf_pregraph x) p) by (destruct l; intuition). clear H2. exfalso.
        hnf in H3. simpl in H3. unfold updateEdgeFunc in H3. destruct H3 as [? [_ ?]]. unfold addValidFunc in H2. destruct H2; auto. subst p.
        destruct (equiv_dec (x, tt) (x, tt)); [|compute in c]; auto.
    - subst y. apply reachable_refl. simpl. auto.
  Qed.

  Definition single_uf_LabeledGraph (v: addr) (default_dv: DV) (default_de: DE) (default_dg: DG) : LGraph :=
    Build_LabeledGraph _ _ _ (single_uf_pregraph v) (fun v => default_dv) (fun e => default_de) default_dg.

  Definition single_uf_MathGraph (v: addr) (H: v <> null): MathGraph (single_uf_pregraph v) is_null_SGBA.
  Proof.
    apply (Build_MathGraph _ is_null_SGBA).
    - intros. simpl. unfold updateEdgeFunc.
      destruct (equiv_dec (v, tt) e); intuition.
    - intros. hnf in *. subst v. intuition.
  Defined.

  Definition single_uf_FiniteGraph (v: addr): FiniteGraph (single_uf_pregraph v).
  Proof.
    constructor; hnf.
    - exists (v :: nil). split.
      + constructor. intro. inversion H. constructor.
      + intros. simpl. unfold In. intuition.
    - exists ((v, tt) :: nil). split.
      + constructor. intro. inversion H. constructor.
      + intros. simpl. unfold In, addValidFunc. intuition.
  Defined.

  Definition single_uf_LstGraph (v: addr) (H: v <> null): LstGraph (single_uf_pregraph v) (fun x => (x, tt)).
  Proof.
    constructor; simpl; intros; unfold updateEdgeFunc.
    - unfold addValidFunc. subst. destruct (equiv_dec (x, tt) e); intuition.
    - destruct H0 as [[? _] [? _]]. destruct p as [p l]. simpl in *. subst p.
      destruct l; auto. destruct H1. clear H0. simpl in H1. assert (strong_evalid (single_uf_pregraph v) p) by (destruct l; [|destruct H1]; auto). clear H1.
      hnf in H0. simpl in H0. unfold addValidFunc, updateEdgeFunc in H0. destruct H0 as [? [_ ?]]. exfalso. destruct H0; auto. subst p.
      destruct (equiv_dec (v, tt) (v, tt)); auto. compute in c. apply c; auto.
  Defined.

  Definition single_sound (v: addr) (H: v <> null) : LiMaFin (single_uf_pregraph v) :=
    Build_LiMaFin _ (single_uf_LstGraph v H) (single_uf_MathGraph v H) (single_uf_FiniteGraph v).
    
  Definition single_Graph (v: addr) (H: v <> null) (default_dv: DV) (default_de: DE) (default_dg: DG): Graph :=
    Build_GeneralGraph _ _ _ _ (single_uf_LabeledGraph v default_dv default_de default_dg) (single_sound v H).

  Lemma valid_parent: forall (g: Graph) v n p, vvalid g v -> vgamma g v = (n, p) -> vvalid g p.
  Proof.
    intros. unfold vgamma in H0. simpl in H0. inversion H0. clear H0 H2. destruct (SGBA_VE (dst g (v, tt)) null); auto.
    unfold complement, Equivalence.equiv in c. pose proof (only_one_edge v (v, tt) H). simpl in H0. assert ((v, tt) = (v, tt)) by auto. rewrite <- H0 in H1. destruct H1.
    pose proof (valid_graph _ _ H2). destruct H4 as [_ [? | ?]]; auto. simpl in H4. exfalso; auto.
  Qed.

  Lemma parent_loop: forall (g: Graph) v n y, vgamma g v = (n, v) -> reachable g v y -> v = y.
  Proof.
    intros. unfold vgamma in H. simpl in H. destruct (SGBA_VE (dst g (v, tt)) null).
    - unfold Equivalence.equiv in e. assert (~ reachable g null y) by (intro; apply reachable_head_valid in H1; apply (valid_not_null g null H1); simpl; auto).
      apply (lst_out_edge_only_one g _ v null y); auto.
    - apply (lst_self_loop _ (liGraph g)) in H0; auto. inversion H. rewrite H3. auto.
  Qed.

  Lemma gamma_parent_reachable_included: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> Included (reachable g pa) (reachable g x).
  Proof.
    intros. intro y; intros. unfold vgamma in H0. simpl in H0. destruct (SGBA_VE (dst g (x, tt)) null).
    - inversion H0. auto.
    - apply edge_reachable_by with pa; auto. split; auto. split.
      + apply reachable_head_valid in H1; auto.
      + inversion H0. rewrite H4. rewrite (dst_step _ (liGraph g) _ _ H H4). auto.
  Qed.

  Lemma Prop_join_reachable_parent: forall (g: Graph) x r pa,
      vvalid g x ->
      vgamma g x = (r, pa) ->
      Prop_join
        (reachable g pa)
        (Intersection _ (reachable g x) (Complement addr (reachable g pa)))
        (reachable g x).
  Proof.
    intros.
    apply Ensemble_join_Intersection_Complement.
    - eapply gamma_parent_reachable_included; eauto.
    - intros. apply decidable_prop_decidable. pose proof (finGraph g).
      apply (@reachable_decidable_prime _ _ _ _ _ _ (maGraph g)).
      + apply LocalFiniteGraph_FiniteGraph; auto.
      + apply (valid_parent _ x r); auto.
      + apply FiniteGraph_EnumCovered; auto.
  Qed.

  Lemma no_edge_gen_dst: forall (g: Graph) x pa p a b,
      ~ List.In (x, tt) (snd p) -> (pregraph_gen_dst g (x, tt) pa) |= p is a ~o~> b satisfying (fun _ => True) -> g |= p is a ~o~> b satisfying (fun _ => True).
  Proof.
    intros. destruct H0 as [[? ?] [? ?]]. split; split; auto; clear H0 H3.
    - clear H2. destruct p as [p l]. simpl in H. revert p H1 H. induction l; intros.
      + simpl. auto.
      + rewrite pfoot_cons in H1. remember (dst (pregraph_gen_dst g (x, tt) pa) a0).
        simpl in Heqy. unfold updateEdgeFunc in Heqy. simpl in H. destruct (equiv_dec (x, tt) a0).
        * exfalso. apply H. left. auto.
        * rewrite pfoot_cons. apply IHl.
          -- subst y. apply H1.
          -- intro. apply H. right. auto.
    - clear H1. destruct p as [p l]. simpl in H. revert p H2 H. induction l; intros.
      + simpl in *. apply H2.
      + rewrite valid_path_cons_iff in H2 |-* . destruct H2 as [? [? ?]]. split; [|split].
        * simpl in H0. apply H0.
        * clear H0 H2. hnf in H1. simpl in H1. unfold updateEdgeFunc in H1. destruct (equiv_dec (x, tt) a0).
          -- simpl in H. exfalso. apply H. left. auto.
          -- hnf. apply H1.
        * remember (dst (pregraph_gen_dst g (x, tt) pa) a0). simpl in Heqy. unfold updateEdgeFunc in Heqy. simpl in H. destruct (equiv_dec (x, tt) a0).
          -- exfalso. apply H. left. auto.
          -- subst y. apply IHl; auto.
  Qed.

  Lemma gen_dst_preserve_lst: forall (g: Graph) x pa, ~ reachable g pa x -> vvalid g x -> LstGraph (pregraph_gen_dst g (x, tt) pa) (fun y : addr => (y, tt)).
  Proof.
    intros. constructor. 1: simpl; apply only_one_edge. intro y; intros. destruct (in_dec SGBA_EE (x, tt) (snd p)).
    - destruct p as [p l]. simpl in i. apply (in_split_not_in_first SGBA_EE) in i. destruct i as [l1 [l2 [? ?]]]. rewrite H2 in H1. apply reachable_by_path_app_cons in H1.
      destruct H1. simpl src in H1. simpl dst in H4. unfold updateEdgeFunc in H4. destruct (equiv_dec (x, tt) (x, tt)). 2: compute in c; exfalso; apply c; auto. clear e.
      apply no_edge_gen_dst in H1. 2: simpl; auto. assert ((x, tt) = (x, tt)) by auto. rewrite <- (@only_one_edge _ _ _ _ g _ (liGraph g)) in H5; auto. destruct H5.
      rewrite H5 in H1. destruct (in_dec SGBA_EE (x, tt) l2).
      + apply (in_split_not_in_last SGBA_EE) in i. destruct i as [l3 [l4 [? ?]]]. rewrite H7 in H4. apply reachable_by_path_app_cons in H4. destruct H4 as [_ ?].
        simpl in H4. unfold updateEdgeFunc in H4. destruct (equiv_dec (x, tt) (x, tt)). 2: compute in c; exfalso; apply c; auto. clear e. apply no_edge_gen_dst in H4.
        2: simpl; auto. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H4 H1). apply reachable_by_path_is_reachable in H9. exfalso; auto.
      + apply no_edge_gen_dst in H4. 2: simpl; auto. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H4 H1). apply reachable_by_path_is_reachable in H7. exfalso; auto.
    - apply no_edge_gen_dst in H1; auto. apply no_loop_path in H1. auto.
  Qed.

  Definition Graph_gen_redirect_parent (g: Graph) (x: addr) (pa: addr) (H: weak_valid g pa) (Hv: vvalid g x) (Hn: ~ reachable g pa x): Graph.
  Proof.
    refine (generalgraph_gen_dst g (x, tt) pa _). constructor.
    - simpl. apply gen_dst_preserve_lst; auto.
    - apply (gen_dst_preserve_math g (x, tt) pa (maGraph g) H).
    - apply (gen_dst_preserve_finite g (x, tt) pa (finGraph g)).
  Defined.

End GRAPH_GList.
