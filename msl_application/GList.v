Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
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
Require Import RamifyCoq.msl_application.UnionFindGraph.

Local Open Scope logic.

Class pPointwiseGraph_GList: Type :=
  {
    addr: Type;
    null: addr;
    SGBA: PointwiseGraphBasicAssum addr (addr * unit)
  }.

Existing Instance SGBA.

Definition is_null_SGBA {pSGG: pPointwiseGraph_GList} : DecidablePred addr := (existT (fun P => forall a, {P a} + {~ P a}) (fun x => x = null) (fun x => SGBA_VE x null)).

Class sPointwiseGraph_GList {pSGG_Bi: pPointwiseGraph_GList} (DV DE: Type): Type :=
  {
    pred: Type;
    SGP: PointwiseGraphPred addr (addr * unit) (DV * addr) unit pred;
    SGA: PointwiseGraphAssum SGP;
    SGAvs: PointwiseGraphAssum_vs SGP;
    SGAvn: PointwiseGraphAssum_vn SGP null
  }.

Existing Instances SGP SGA SGAvs.

Section GRAPH_GList.

  Context {pSGG: pPointwiseGraph_GList}.
  Context {DV DE DG: Type}.

  Instance SGC_GList: PointwiseGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_PointwiseGraphConstructor _ _ _ _ _ _ _ SGBA _ _).
    + exact (@vgamma addr (addr * unit) SGBA_VE SGBA_EE is_null_SGBA (fun x => (x, tt)) DV DE DG).
    + exact (fun _ _ => tt).
  Defined.

  Instance L_SGC_GList: Local_PointwiseGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_Local_PointwiseGraphConstructor
              _ _ _ _ _ _ _ SGBA SGC_GList
              (fun G v => evalid (pg_lg G) (v, tt) /\ src (pg_lg G) (v, tt) = v) _
              (fun _ _ => True) _).
    - intros. simpl. unfold vgamma.  simpl. destruct H as [? ?], H0 as [? ?]. f_equal; auto. pose proof (H3 _ H H5 H0 H6). rewrite <- !H7. clear H7.
      destruct (SGBA_VE (dst (pg_lg G1) (x, tt)) null); auto.
    - intros; simpl. auto.
  Defined.

  Global Existing Instances SGC_GList L_SGC_GList.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Notation Graph := (@Graph addr (addr * unit) _ _ is_null_SGBA (fun x => (x, tt)) DV DE DG).
  Notation LGraph := (@LGraph addr (addr * unit) _ _ DV DE DG).

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

  Definition make_set_pregraph (v: addr) (g: PreGraph addr (addr * unit)) := pregraph_add_edge (pregraph_add_vertex g v) (v, tt) v null.

  Lemma is_partial_make_set_pregraph: forall x (g: Graph), ~ vvalid g x -> is_partial_graph g (make_set_pregraph x g).
  Proof.
    intros. hnf. simpl. unfold addValidFunc, updateEdgeFunc. split; [|split; [|split]]; intros; [left; auto..| |].
    - destruct (equiv_dec (x, tt) e); auto. hnf in e0. subst e. pose proof (@only_one_edge _ _ _ _ g _ (liGraph g) (src g (x, tt)) (x, tt) H1). simpl in H2.
      assert (src g (x, tt) = src g (x, tt) /\ evalid g (x, tt)) by (split; auto). rewrite H2 in H3. inversion H3. exfalso. rewrite H5 in H. intuition.
    - destruct (equiv_dec (x, tt) e); auto. hnf in e0. subst e. destruct (@valid_graph _ _ _ _ g _ (maGraph g) _ H0) as [? _].
      pose proof (@only_one_edge _ _ _ _ g _ (liGraph g) (src g (x, tt)) (x, tt) H2). assert (src g (x, tt) = src g (x, tt) /\ evalid g (x, tt)) by (split; auto).
      rewrite H3 in H4. inversion H4. exfalso. rewrite H6 in H. intuition.
  Qed.

  Definition make_set_LabeledGraph (v: addr) (g: LabeledGraph addr (addr * unit) DV DE DG) (default_dv: DV) (default_de: DE) (default_dg: DG) : LGraph :=
    Build_LabeledGraph _ _ _ (make_set_pregraph v g) (fun x => if SGBA_VE x v then default_dv else vlabel g x) (fun e => default_de) default_dg.

  Definition make_set_MathGraph (v: addr) (g: PreGraph addr (addr * unit)) (H: v <> null) (Hm: MathGraph g is_null_SGBA): MathGraph (make_set_pregraph v g) is_null_SGBA.
  Proof.
    apply (Build_MathGraph _ is_null_SGBA).
    - intros. simpl. unfold updateEdgeFunc, addValidFunc. destruct (equiv_dec (v, tt) e). 1: intuition. simpl in H0. unfold addValidFunc in H0. destruct H0.
      + destruct Hm. apply valid_graph in H0. destruct H0. split. 1: left; auto. hnf in H1. simpl in H1. destruct H1; [left | right; left]; auto.
      + compute in c. exfalso; intuition.
    - intros. hnf in H0. simpl in H1. destruct H0.
      + subst x. destruct Hm. apply valid_not_null in H0; auto. simpl. auto.
      + subst v. auto.
  Defined.

  Definition make_set_FiniteGraph (v: addr) (g: PreGraph addr (addr * unit)) (Hf: FiniteGraph g): FiniteGraph (make_set_pregraph v g).
  Proof.
    destruct Hf. unfold EnumEnsembles.Enumerable in *. destruct finiteV as [vl [? ?]]. destruct finiteE as [el [? ?]]. constructor; hnf; simpl; unfold addValidFunc.
    - destruct (in_dec SGBA_VE v vl).
      + exists vl. split; auto. intros. unfold In in H0 |-* . rewrite H0. intuition. subst v. rewrite H0 in i. auto.
      + exists (v :: vl). split; [constructor; auto|]. intros. simpl. unfold In in H0 |-* . rewrite H0. intuition.
    - unfold In in H2 |-* . destruct (in_dec SGBA_EE (v, tt) el).
      + exists el. split; auto. intros. rewrite H2. intuition. inversion H4. rewrite H2 in i. auto.
      + exists ((v, tt) :: el). split; [constructor; auto|]. intros. simpl. rewrite H2. intuition.
  Defined.

  Lemma make_set_valid_path_pfoot: forall (v: addr) (g: PreGraph addr (addr * unit)) x p (Hn: v <> null) (Hi: ~ vvalid g v) (Hm: MathGraph g is_null_SGBA),
      x <> v -> pfoot (make_set_pregraph v g) p = x -> valid_path (make_set_pregraph v g) p -> pfoot g p = x /\ valid_path g p.
  Proof.
    intros. destruct p as [p l]. assert (forall e, List.In e l -> e <> (v, tt)). {
      intros. apply (valid_path_strong_evalid _ _ _ e) in H1; auto. hnf in H1. simpl in H1. unfold addValidFunc, updateEdgeFunc in H1.
      destruct H1 as [? [? ?]]. intro. destruct (equiv_dec (v, tt) e). 2: compute in c; auto. destruct H4; auto. destruct Hm. apply valid_not_null in H4; simpl; auto.
    } split.
    - clear H1. revert p H0. induction l; intros. 1: simpl in H0 |-* ; auto.
      assert (forall e : addr * unit, List.In e l -> e <> (v, tt)) by (intros; apply H2; right; auto). specialize (IHl H1). clear H1.
      rewrite pfoot_cons in H0 |-* . simpl dst in H0. unfold updateEdgeFunc in H0. destruct (equiv_dec (v, tt) a).
      + hnf in e. assert (a <> (v, tt)) by (apply H2; left; auto). exfalso; auto.
      + apply IHl; auto.
    - assert (p <> v). {
        intro. subst p. destruct l. 1: simpl in H0; auto. simpl in H1. destruct H1. assert (strong_evalid (make_set_pregraph v g) p) by (destruct l; [|destruct H3]; auto).
        clear H3. hnf in H4. simpl in H4. unfold addValidFunc, updateEdgeFunc in H1, H4. destruct H4 as [? _]. assert (p <> (v, tt)) by (apply H2; left; auto).
        destruct (equiv_dec (v, tt) p). 1: hnf in e; auto. destruct H3; auto. destruct Hm. apply valid_graph in H3. destruct H3 as [? _]. rewrite <- H1 in H3. auto.
      } clear H0. revert p H1 H3. induction l; intros.
      + simpl in H1. unfold addValidFunc in H1. simpl. destruct H1; [|exfalso]; auto.
      + assert (forall e : addr * unit, List.In e l -> e <> (v, tt)) by (intros; apply H2; right; auto). specialize (IHl H0). clear H0.
        assert (a <> (v, tt)) by (apply H2; left; auto). rewrite valid_path_cons_iff in H1 |-* . destruct H1 as [? [? ?]]. split; [|split].
        * simpl in H1. unfold updateEdgeFunc in H1. destruct (equiv_dec (v, tt) a); [exfalso|]; auto.
        * hnf in H4. simpl in H4. unfold addValidFunc, updateEdgeFunc in H4. destruct H4 as [? [? ?]].
          destruct (equiv_dec (v, tt) a); [hnf in e; exfalso|]; auto. destruct H4; [|exfalso]; auto. clear c.
          destruct H6. 2: destruct Hm; apply valid_graph in H4; destruct H4; rewrite H6 in H4; exfalso; auto.
          destruct H7. 2: destruct Hm; apply valid_graph in H4; destruct H4; hnf in H8; simpl in H8; rewrite H7 in H8; exfalso; destruct H8; auto. hnf. split; auto.
        * simpl dst in H5. unfold updateEdgeFunc in H5. destruct (equiv_dec (v, tt) a); [hnf in e; exfalso|]; auto. apply IHl; auto.
          destruct H4 as [? _]. simpl in H4. unfold addValidFunc in H4. destruct H4; [|exfalso]; auto. destruct Hm. apply valid_graph in H4. destruct H4 as [_ ?].
          hnf in H4. simpl in H4. intro. rewrite H6 in H4. destruct H4; auto.
  Qed.

  Definition make_set_LstGraph (v: addr) (g: PreGraph addr (addr * unit)) (Hn: v <> null) (Hi: ~ vvalid g v) (Hm: MathGraph g is_null_SGBA)
             (Hl: LstGraph g (fun x => (x, tt))): LstGraph (make_set_pregraph v g) (fun x => (x, tt)).
  Proof.
    constructor; simpl.
    - unfold addValidFunc, updateEdgeFunc. intros. destruct H.
      + destruct Hl. specialize (only_one_edge x e H). destruct (equiv_dec (v, tt) e).
        * hnf in e0. subst e. rewrite <- only_one_edge. split; intros.
          -- destruct H0. subst v. rewrite only_one_edge. auto.
          -- rewrite only_one_edge in H0. inversion H0. subst v. split; auto.
        * compute in c. rewrite <- only_one_edge. split; intros.
          -- destruct H0. split; auto. destruct H1; auto. exfalso; auto.
          -- destruct H0. split; auto.
      + subst v. split; intros.
        * destruct H. destruct H0; auto. destruct (equiv_dec (x, tt) e).
          -- hnf in e0; auto.
          -- destruct Hm. specialize (valid_graph _ H0). destruct valid_graph. rewrite H in H1. exfalso; auto.
        * destruct (equiv_dec (x, tt) e).
          -- hnf in e0. split; auto.
          -- compute in c. exfalso; auto.
    - intros. destruct_eq_dec x v.
      + subst x. destruct p as [p l]. destruct H as [[? ?] [? _]]. simpl in H. subst p. simpl in H1. destruct l; auto. unfold updateEdgeFunc in H1. destruct H1.
        assert (strong_evalid (make_set_pregraph v g) p) by (simpl in H1; destruct l; [|destruct H1]; auto). hnf in H2. simpl in H2. unfold addValidFunc, updateEdgeFunc in H2.
        destruct H2 as [? [? ?]]. destruct (equiv_dec (v, tt) p).
        * exfalso. destruct H4; auto. destruct Hm. apply valid_not_null in H4; simpl; auto.
        * compute in c. exfalso. destruct H2; auto. destruct Hm. apply valid_graph in H2. destruct H2. subst v. auto.
      + destruct Hl. apply no_loop_path. destruct H as [[? ?] [? ?]]. assert (pfoot g p = x /\ valid_path g p) by (apply (make_set_valid_path_pfoot v); auto).
        destruct H4. split; split; auto.
  Defined.

  Definition make_set_sound (v: addr)  (g: PreGraph addr (addr * unit)) (Hn: v <> null) (Hi: ~ vvalid g v) (Hlmf: LiMaFin g) : LiMaFin (make_set_pregraph v g) :=
    Build_LiMaFin _ (make_set_LstGraph v g Hn Hi ma li) (make_set_MathGraph v g Hn ma) (make_set_FiniteGraph v g fin).

  Definition make_set_Graph (default_dv: DV) (default_de: DE) (default_dg: DG) (v: addr) (g: Graph) (Hn: v <> null) (Hi: ~ vvalid g v) : Graph :=
    Build_GeneralGraph _ _ _ _ (make_set_LabeledGraph v g default_dv default_de default_dg) (make_set_sound v g Hn Hi (sound_gg g)).

  Lemma uf_under_bound_make_set_graph: forall (default_dv: DV) (default_de: DE) (default_dg: DG) (v: addr) (g: Graph) (Hn: v <> null) (Hi: ~ vvalid g v) (extract: DV -> nat),
      extract default_dv = O -> uf_under_bound extract g -> uf_under_bound extract (make_set_Graph default_dv default_de default_dg v g Hn Hi).
  Proof.
    intros. hnf in H0 |-* . simpl. intro x; intros. unfold addValidFunc in H1. destruct (SGBA_VE x v).
    - hnf in e. subst v. destruct H1; [exfalso; auto |]. clear H1. hnf. intros. rewrite H. destruct p as [p l]. destruct l; simpl; auto. exfalso.
      apply pfoot_in_cons in H2. destruct H2 as [e [? ?]]. simpl in H3. unfold updateEdgeFunc in H3. pose proof (valid_path_strong_evalid _ _ _ _ H1 H2). hnf in H4.
      simpl in H4. unfold addValidFunc, updateEdgeFunc in H4. destruct H4 as [? [? ?]]. destruct (equiv_dec (x, tt) e). 1: exfalso; auto. compute in c.
      destruct H4; auto. destruct (@valid_graph _ _ _ _ g _ (maGraph g) _ H4) as [_ ?]. rewrite H3 in H7. destruct H7; auto.
    - compute in c. destruct H1; [|exfalso; auto]. hnf. intros. assert (pfoot g p = x /\ valid_path g p) by (apply (make_set_valid_path_pfoot v); auto; exact (maGraph g)).
      destruct H4. unfold uf_bound in H0. apply H0; auto.
  Qed.

  Definition single_uf_pregraph (v: addr) : PreGraph addr (addr * unit) :=
    pregraph_add_edge (single_vertex_pregraph v) (v, tt) v null.

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

End GRAPH_GList.
