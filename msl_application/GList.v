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
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
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
    + exact (fun G v => (vlabel G v, v)).
    + exact (fun _ _ => tt).
  Defined.

  Instance L_SGC_GList: Local_SpatialGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_Local_SpatialGraphConstructor
              _ _ _ _ _ _ _ SGBA SGC_GList
              (fun G v => evalid (pg_lg G) (v, tt) /\ src (pg_lg G) (v, tt) = v) _
              (fun _ _ => True) _).
    + intros.
      simpl.
      destruct H as [? ?], H0 as [? ?].
      f_equal; auto.
    + intros; simpl.
      auto.
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
    pregraph_add_edge (single_vertex_pregraph v) (v, tt) v v.

  Lemma single_uf_is_uf: forall v, uf_graph (single_uf_pregraph v).
  Proof.
    intros. hnf. intros. hnf. exists (v, nil). split.
    - hnf. auto.
    - intros. hnf in H1. hnf in H. subst v. destruct H1 as [[v p] [[? ?] [? ?]]]. simpl in H. subst v. destruct p.
      + simpl in *. subst y. exists (x, nil). split.
        * hnf. split; [split; split|]; simpl; auto.
          intros. destruct H as [[? ?] [? ?]]. clear H5. destruct x'. simpl in H. subst a. destruct l. auto.
          destruct H4 as [_ ?]. destruct p. simpl in H. destruct l.
          -- hnf in H. simpl in H. unfold updateEdgeFunc in H. destruct H as [_ [_ ?]].
             destruct (equiv_dec (x, tt) (a, u)); destruct (equiv_dec x x); [|hnf in c | |hnf in c]; exfalso; auto.
          -- unfold updateEdgeFunc in H. destruct H as [_ [? _]].
             assert ((if equiv_dec (x, tt) p then x else x) = x) by (destruct (equiv_dec (x, tt) p); auto). rewrite H4 in H. clear H4.
             destruct (equiv_dec (x, tt) (a, u)); destruct (equiv_dec x x); [|hnf in c| | hnf in c]; exfalso; auto.
        * apply Subpath_refl.
      + exfalso. clear H3. simpl in H0. simpl in H2. destruct H2 as [_ ?]. destruct p0.
        * hnf in H. simpl in H. unfold updateEdgeFunc in H. destruct H as [_ [_ ?]].
          destruct (equiv_dec (x, tt) p); destruct (equiv_dec x x); [|hnf in c| | hnf in c]; exfalso; auto.
        * unfold updateEdgeFunc in H. destruct H as [_ [? _]].
          assert ((if equiv_dec (x, tt) p0 then x else x) = x) by (destruct (equiv_dec (x, tt) p0); auto). rewrite H2 in H. clear H2.
          destruct (equiv_dec (x, tt) p); destruct (equiv_dec x x); [|hnf in c| | hnf in c]; exfalso; auto.
  Qed.

  Lemma reachabel_single_uf: forall x y, reachable (single_uf_pregraph x) x y <-> x = y.
  Proof.
    intros. split; intros.
    - destruct H as [[? ?] [[? ?] [? _]]]. simpl in H. subst a. induction l.
      + simpl in H0. auto.
      + destruct a as [? ?].
        assert (a = x). {
          clear H0 IHl. simpl in H1. destruct l.
          - destruct H1 as [_ ?]. hnf in H. simpl in H. unfold addValidFunc in H. destruct H as [[? | ?] _]; [exfalso | inversion H]; auto.
          - destruct H1 as [_ [? _]]. hnf in H. simpl in H. unfold addValidFunc in H. destruct H as [[? | ?] _]; [exfalso | inversion H]; auto.
        } subst a. rewrite pfoot_cons in H0. apply valid_path_cons in H1.
        assert (dst (single_uf_pregraph x) (x, u) = x) by (simpl; unfold updateEdgeFunc; destruct (equiv_dec (x, tt) (x, u)); auto). rewrite H in *.
        apply IHl; auto.
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

  Definition single_uf_LstGraph (v: addr): LstGraph (single_uf_pregraph v) (fun x => (x, tt)).
  Proof. constructor; simpl; intros. unfold updateEdgeFunc, addValidFunc. subst. destruct (equiv_dec (x, tt) e); intuition. Defined.

  Definition single_sound (v: addr) (H: v <> null) : LiMaFin (single_uf_pregraph v) :=
    Build_LiMaFin _ (single_uf_LstGraph v) (single_uf_MathGraph v H) (single_uf_FiniteGraph v).
    
  Definition single_Graph (v: addr) (H: v <> null) (default_dv: DV) (default_de: DE) (default_dg: DG): Graph :=
    Build_GeneralGraph _ _ _ _ (single_uf_LabeledGraph v default_dv default_de default_dg) (single_sound v H).

End GRAPH_GList.
