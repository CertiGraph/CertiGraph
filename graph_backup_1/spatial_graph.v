Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import CertiGraph.Coqlib.
Require Import CertiGraph.msl_ext.abs_addr.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.msl_ext.log_normalize.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.graph.graph.
Require Import CertiGraph.graph.graph_reachable.
Require Import Coq.Logic.Classical.
Import CertiGraph.msl_ext.seplog.OconNotation.

Definition gamma {Vertex Data} {EV: EqDec Vertex} {PG : PreGraph Vertex Data} (BG: BiGraph PG) (v: Vertex) : Data * Vertex * Vertex := let (v1, v2) := biEdge BG v in (node_label v, v1, v2).

Lemma update_bigraph_gamma {A D: Type} {EV: EqDec A} {PG : PreGraph A D}:
  forall (g: BiGraph PG) (v: A) (d: D) (l r: A), gamma (update_BiGraph g v d l r) v = (d, l, r).
Proof.
  intros. unfold gamma, biEdge. destruct (@only_two_neighbours A D EV _ (@update_BiGraph A D EV PG g v d l r) v) as [v1 [v2 ?]].
  simpl in *. unfold change_edge_func, change_node_label in *. destruct (t_eq_dec v v).
  + inversion e. subst; auto.
  + exfalso; auto.
Qed.

Class PointwiseGraphSetting: Type := {
  Data: Type;
  addr: Type;
  null: addr;
  addr_eq_dec: forall x y: addr, {x = y} + {x <> y};
  addr_eqb: addr -> addr -> bool := fun x y => if addr_eq_dec x y then true else false
}.

Instance AV_SGraph `{PointwiseGraphSetting} : AbsAddr.
  apply (mkAbsAddr addr (Data * addr * addr) (fun x y => addr_eqb x y)); simpl; intros.
  + unfold addr_eqb.
    destruct (addr_eq_dec p1 p2), (addr_eq_dec p2 p1); try congruence.
  + unfold addr_eqb in H0.
    destruct (addr_eq_dec p1 p1); congruence.
Defined.

Instance AddrDec `{PointwiseGraphSetting}: EqDec Addr. apply Build_EqDec. intros. apply (addr_eq_dec t1 t2). Defined.
Opaque AddrDec.

Definition Null {SGS: PointwiseGraphSetting} : (@Addr AV_SGraph) := null.

Class Graph {SGS: PointwiseGraphSetting} : Type := {
  pg: PreGraph Addr Data;
  bi: BiGraph pg;
  ma: MathGraph pg Null
}.
 
Coercion pg : Graph >-> PreGraph.
 
Coercion bi : Graph >-> BiGraph.
 
Coercion ma : Graph >-> MathGraph.
 
Instance single_graph_double {SGS: PointwiseGraphSetting} v d (Hn: v <> Null): Graph := {
  pg := single_PreGraph _ v d v v;
  bi := single_BiGraph _ v d v v;
  ma := single_MathGraph_double _ _ v d Hn
}.
 
Instance single_graph_left {SGS: PointwiseGraphSetting} v d (Hn: v <> Null): Graph := {
  pg := single_PreGraph _ v d v Null;
  bi := single_BiGraph _ v d v Null;
  ma := single_MathGraph_left _ _ v d Hn
}.
 
Instance single_graph_right {SGS: PointwiseGraphSetting} v d (Hn: v <> Null): Graph := {
  pg := single_PreGraph _ v d Null v;
  bi := single_BiGraph _ v d Null v;
  ma := single_MathGraph_right _ _ v d Hn
}.

Class PointwiseGraphAssum: Type := {
  SGA_Pred: Type;
  SGA_ND: NatDed SGA_Pred;
  SGA_SL : SepLog SGA_Pred;
  SGA_ClSL: ClassicalSep SGA_Pred;
  SGA_PSL : PreciseSepLog SGA_Pred;
  SGA_CoSL: CorableSepLog SGA_Pred;
  SGA_OSL: OverlapSepLog SGA_Pred;
  SGA_DSL : DisjointedSepLog SGA_Pred;
  SGA_COSL: CorableOverlapSepLog SGA_Pred;

  SG_Setting: PointwiseGraphSetting;
  trinode : Addr -> Val -> SGA_Pred;
  SGA_MSL: MapstoSepLog AV_SGraph trinode;
  SGA_sMSL: StaticMapstoSepLog AV_SGraph trinode(* ; *)
  (* SGA_nMSL: NormalMapstoSepLog AV_SGraph trinode *)
}.

Global Existing Instances SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL (* SGA_nMSL *).

Hint Resolve SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL (* SGA_nMSL *).

Local Open Scope logic.

Section PointwiseGraph.

  Context {SGA : PointwiseGraphAssum}.

  Definition graph_cell (g: Graph) (v : Addr) : SGA_Pred := trinode v (gamma g v).

  Lemma precise_graph_cell: forall g v, precise (graph_cell g v).
  Proof. intros. unfold graph_cell. destruct (gamma bi v) as [[? ?] ?]. apply mapsto_precise. Qed.

  Lemma sepcon_unique_graph_cell: forall g, sepcon_unique (graph_cell g).
  Proof.
    repeat intro. unfold graph_cell. destruct (gamma bi x) as [[? ?] ?]. apply mapsto_conflict.
    simpl. unfold addr_eqb. destruct (addr_eq_dec x x); auto.
  Qed.

  Lemma joinable_graph_cell : forall g, joinable (graph_cell g).
  Proof.
    intros. unfold joinable; intros. unfold graph_cell. apply disj_mapsto.
    simpl. unfold addr_eqb. destruct (addr_eq_dec x y); tauto.
  Qed.

  Existing Instances pg bi ma.

  Definition graph (x : Addr) (g: Graph) : SGA_Pred :=
    !!(x = Null \/ valid x) && EX l : list Addr, !!reachable_list pg x l && iter_sepcon l (graph_cell g).

  Lemma graph_unfold_Null: forall (g: Graph), graph Null g = emp.
  Proof.
    intros. apply pred_ext; unfold graph.
    + apply andp_left2, exp_left. intros. apply derives_extract_prop. intro. destruct x.
      - simpl. apply derives_refl.
      - exfalso. assert (In a (a :: x)). apply in_eq. rewrite (H a) in H0. apply reachable_head_valid in H0.
        apply valid_not_null in H0. auto.
    + apply andp_right.
      - apply prop_right. left; auto.
      - apply (exp_right nil). simpl. apply andp_right.
        * apply prop_right. intro. split; intro. inversion H. apply reachable_head_valid in H.
          apply valid_not_null in H. exfalso; auto.
        * apply derives_refl.
  Qed.

  Lemma graph_unfold_valid:
    forall x (g: Graph) d l r, valid x -> gamma g x = (d, l, r) ->
                         graph x g = trinode x (d, l, r) ⊗ graph l g ⊗ graph r g.
  Proof.
    intros. assert (TRI: trinode x (d, l, r) = iter_sepcon (x :: nil) (graph_cell g)). {
      unfold iter_sepcon. rewrite sepcon_comm, emp_sepcon. unfold graph_cell. rewrite H0. auto.
    } apply pred_ext.
    + unfold graph. apply andp_left2, exp_left. intro li.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup li (sepcon_unique_graph_cell g))). normalize_overlap.
      rename H2 into NODUPLi.
      unfold gamma in H0. unfold biEdge in H0. destruct (only_two_neighbours x) as [v1 [v2 ?]].
      inversion H0; subst. clear H0.
      assert (In l (edge_func x)). rewrite e. apply in_eq.
      destruct (compute_neighbor g x li H H1 l H0) as [leftL [? ?]].
      assert (In r (edge_func x)). rewrite e. apply in_cons, in_eq.
      destruct (compute_neighbor g x li H H1 r H4) as [rightL [? ?]].
      apply (exp_right rightL). normalize_overlap. apply (exp_right leftL). normalize_overlap. apply andp_right.
      - rewrite <- !prop_and. apply prop_right. do 2 (split; auto).
        split.
        * destruct (weak_valid_complete _ (valid_graph x H r H4)); auto.
        * destruct (weak_valid_complete _ (valid_graph x H l H0)); auto.
      - rewrite TRI, ocon_assoc.
        rewrite !(iter_sepcon_ocon t_eq_dec); auto.
        2: repeat constructor; simpl; tauto.
        2: apply remove_dup_nodup.
        2: apply precise_graph_cell.
        2: apply joinable_graph_cell.
        2: apply precise_graph_cell.
        2: apply joinable_graph_cell.
        rewrite iter_sepcon_permutation with (l2 := remove_dup t_eq_dec ((x :: nil) ++ remove_dup t_eq_dec (leftL ++ rightL))).
        * apply derives_refl.
        * apply (eq_as_set_permutation t_eq_dec); auto.
          apply remove_dup_nodup. apply eq_as_set_spec. intro y.
          rewrite <- remove_dup_in_inv. simpl.
          rewrite <- remove_dup_in_inv.
          rewrite in_app_iff. rewrite (H1 y).
          apply (reachable_list_bigraph_in l r); auto.
    + unfold graph. normalize_overlap. intro rightL. normalize_overlap. intro leftL. normalize_overlap.
      apply (exp_right (remove_dup t_eq_dec ((x :: nil) ++ remove_dup t_eq_dec (leftL ++ rightL)))). rewrite <- andp_assoc.
      rewrite <- prop_and. rewrite TRI.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup leftL (sepcon_unique_graph_cell g))).
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup rightL (sepcon_unique_graph_cell g))).
      normalize_overlap. apply andp_right.
      - apply prop_right. split. right; auto. intro.
        rewrite <- remove_dup_in_inv. simpl. rewrite <- remove_dup_in_inv.
        rewrite in_app_iff. symmetry. apply (reachable_list_bigraph_in l r); auto.
        unfold gamma in H0. unfold biEdge in H0. destruct (only_two_neighbours x) as [? [? ?]]. inversion H0. subst. auto.
      - rewrite ocon_assoc. rewrite !(iter_sepcon_ocon t_eq_dec); auto.
        * repeat constructor; simpl; tauto.
        * apply remove_dup_nodup.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
  Qed.

  Lemma graph_root_nv: forall x g, graph x g |-- !!(x = Null \/ valid x).
  Proof. intros. unfold graph. apply andp_left1, prop_left. intros. apply TT_prop_right; auto. Qed.

  Lemma graph_unfold':
    forall x g,
      graph x g = (!!(x = Null) && emp) ||
          EX d:Data, EX l:Addr, EX r:Addr, !!(gamma g x = (d, l, r) /\ valid x) &&
                                                        (trinode x (d, l, r) ⊗ graph l g ⊗ graph r g).
  Proof.
    intros. apply pred_ext.
    + destruct (t_eq_dec x Null).
      - subst. apply orp_right1. rewrite graph_unfold_Null. normalize.
      - apply orp_right2. destruct (gamma g x) as [[dd ll] rr] eqn:? .
        apply (exp_right dd), (exp_right ll), (exp_right rr).
        rewrite (add_andp _ _ (graph_root_nv x g)). apply andp_right.
        * apply andp_left2, prop_left; intros. apply TT_prop_right. destruct H. tauto. split; auto.
        * normalize. destruct H; [tauto | rewrite (graph_unfold_valid _ _ dd ll rr); auto].
    + apply orp_left.
      - normalize. rewrite graph_unfold_Null. auto.
      - normalize. intros d l r [? ?]. rewrite <- (graph_unfold_valid _ _ d l r); auto.
  Qed.

  Lemma graph_unfold:
    forall x (g: Graph) d l r, gamma g x = (d, l, r) ->
                         graph x g = !!(x = Null) && emp ||
                                        !!(valid x) && (trinode x (d, l, r) ⊗ graph l g ⊗ graph r g).
  Proof.
    intros. apply pred_ext.
    + rewrite (add_andp _ _ (graph_root_nv x g)). normalize. destruct H0.
      - subst. rewrite graph_unfold_Null. apply orp_right1. normalize.
      - apply orp_right2. rewrite (graph_unfold_valid _ _ d l r H0 H). normalize.
    + apply orp_left.
      - normalize. rewrite graph_unfold_Null. auto.
      - normalize. rewrite (graph_unfold_valid _ _ d l r H0 H). auto.
  Qed.

  Lemma precise_graph: forall x g, precise (graph x g).
  Proof.
    intros. apply precise_andp_right. apply precise_exp_iter_sepcon.
    + apply sepcon_unique_graph_cell.
    + apply classic.
    + apply precise_graph_cell.
    + apply reachable_list_permutation.
  Qed.

  Fixpoint graphs (l : list Addr) g :=
    match l with
      | nil => emp
      | v :: l' => graph v g ⊗ graphs l' g
    end.

  Lemma precise_graphs: forall S g, precise (graphs S g).
  Proof. intros; induction S; simpl. apply precise_emp. apply precise_ocon. apply precise_graph. apply IHS. Qed.

  Lemma graphs_list_well_defined: forall S g, graphs S g |-- !!well_defined_list g S.
  Proof.
    induction S; intros; unfold well_defined_list in *; simpl.
    + apply prop_right. intros; tauto.
    + unfold graph.
      rewrite (add_andp _ _ (IHS _)).
      normalize_overlap.
      apply prop_right.
      intro y; intros. destruct H1.
      - subst. auto.
      - specialize (H0 _ H1). apply H0.
  Qed.

  Lemma graphs_unfold: forall S g, graphs S g =
                                      !!(well_defined_list g S) &&
                                      EX l: list Addr, !!reachable_set_list pg S l &&
                                                       iter_sepcon l (graph_cell g).
  Proof.
    induction S; intros.
    + unfold graphs. apply pred_ext.
      - apply andp_right.
        * apply prop_right. hnf. intros. inversion H.
        * apply (exp_right nil). simpl. apply andp_right; auto. apply prop_right. hnf.
          intros. split; intros. unfold reachable_through_set in H. destruct H as [s [? _]]. inversion H. inversion H.
      - normalize. destruct l. simpl; auto. hnf in H0. specialize (H0 a).
        assert (In a (a :: l)) by apply in_eq.
        rewrite <- H0 in H1. unfold reachable_through_set in H1. destruct H1 as [? [? _]]. inversion H1.
    + unfold graphs. fold graphs. rewrite IHS. unfold graph. apply pred_ext. clear IHS.
      - normalize_overlap. rename x into la.
        normalize_overlap. rename x into lS.
        normalize_overlap.
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell g))).
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell g))).
        normalize_overlap.
        rewrite (iter_sepcon_ocon t_eq_dec); auto. apply (exp_right (remove_dup t_eq_dec (la ++ lS))).
        rewrite <- andp_assoc, <- prop_and. apply andp_right.
        * apply prop_right. split.
          1: {
            unfold well_defined_list in *. intros. simpl in H5.
            destruct H5; [subst | apply H0]; auto. }
          1: {
            unfold reachable_set_list in *.
            unfold reachable_list in *. intros.
            rewrite <- remove_dup_in_inv.
            rewrite reachable_through_set_eq.
            specialize (H1 x). specialize (H2 x).
            split; intro; [apply in_or_app | apply in_app_or in H5];
            destruct H5; [left | right | left | right]; tauto.
          }
        * auto.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
      - normalize.
        assert (In a (a :: S)) by apply in_eq.
        assert (weak_valid a). 1: {
          unfold well_defined_list in H.
          specialize (H a).
          destruct (H H1); apply weak_valid_spec; [left | right]; auto.
        }
        destruct (reachable_through_single_reachable g _ _ H0 a H1 H2) as [la [? ?]].
        normalize_overlap. apply (exp_right la).
        assert (Sublist S (a :: S)) by (intro s; intros; apply in_cons; auto).
        assert (well_defined_list g S) by (unfold well_defined_list in *; intros; apply H; apply in_cons; auto).
        destruct (reachable_through_sublist_reachable _ _ _ H0 _ H5 H6) as [lS [? ?]].
        normalize_overlap. apply (exp_right lS). normalize_overlap.
        rewrite <- !prop_and. apply andp_right.
        * apply prop_right. auto.
        * rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (sepcon_unique_graph_cell g))).
          normalize.
          rewrite (iter_sepcon_ocon t_eq_dec); auto.
          2: apply precise_graph_cell.
          2: apply joinable_graph_cell.
          rewrite iter_sepcon_permutation with (l2 := remove_dup t_eq_dec (la ++ lS)); auto.
          apply NoDup_Permutation; auto. apply remove_dup_nodup.
          intros. rewrite <- remove_dup_in_inv. clear -H7 H3 H0.
          specialize (H0 x). specialize (H7 x). specialize (H3 x). rewrite <- H0.
          rewrite reachable_through_set_eq. rewrite in_app_iff. tauto.
  Qed.

  Lemma reachable_eq_graphs_eq:
    forall S S' (g: Graph), Same_set (reachable_through_set pg S) (reachable_through_set pg S') ->
                      well_defined_list g S -> well_defined_list g S' ->  graphs S g = graphs S' g.
  Proof.
    intros; apply pred_ext; rewrite !graphs_unfold; normalize; apply (exp_right l);
    normalize; apply andp_right; auto; apply prop_right; unfold reachable_set_list in *;
    destruct H; unfold Included in * |- ; intros; rewrite <- H2; split; unfold Ensembles.In in *; auto.
  Qed.

  Lemma single_graph_growth_double:
    forall x d (H: x <> Null), trinode x (d, x, x) |-- graph x (single_graph_double x d H).
  Proof.
    intros. unfold graph. apply andp_right.
    + apply prop_right. right. hnf; auto.
    + apply (exp_right (x :: nil)). apply andp_right.
      - apply prop_right. hnf. intros. split; intros.
        * simpl in H0. destruct H0; try tauto. subst.
          apply reachable_by_reflexive. split; hnf; auto.
        * apply reachable_foot_valid in H0. hnf in H0. subst. apply in_eq.
      - unfold iter_sepcon. unfold graph_cell. rewrite sepcon_emp.
        unfold gamma. unfold biEdge. unfold only_two_neighbours. simpl. auto.
  Qed.

  Lemma single_graph_growth_left:
    forall x d (H: x <> Null), trinode x (d, x, Null) |-- graph x (single_graph_left x d H).
  Proof.
    intros. unfold graph. apply andp_right.
    + apply prop_right. right. hnf; auto.
    + apply (exp_right (x :: nil)). apply andp_right.
      - apply prop_right. hnf. intros. split; intros.
        * simpl in H0. destruct H0; try tauto. subst.
          apply reachable_by_reflexive. split; hnf; auto.
        * apply reachable_foot_valid in H0. hnf in H0. subst. apply in_eq.
      - unfold iter_sepcon. unfold graph_cell. rewrite sepcon_emp.
        unfold gamma. unfold biEdge. unfold only_two_neighbours. simpl. auto.
  Qed.

  Lemma single_graph_growth_right:
    forall x d (H: x <> Null), trinode x (d, Null, x) |-- graph x (single_graph_right x d H).
  Proof.
    intros. unfold graph. apply andp_right.
    + apply prop_right. right. hnf; auto.
    + apply (exp_right (x :: nil)). apply andp_right.
      - apply prop_right. hnf. intros. split; intros.
        * simpl in H0. destruct H0; try tauto. subst.
          apply reachable_by_reflexive. split; hnf; auto.
        * apply reachable_foot_valid in H0. hnf in H0. subst. apply in_eq.
      - unfold iter_sepcon. unfold graph_cell. rewrite sepcon_emp.
        unfold gamma. unfold biEdge. unfold only_two_neighbours. simpl. auto.
  Qed.

  Lemma trinode_iter_sepcon_not_in:
    forall x d l r li g, trinode x (d, l, r) * iter_sepcon li (graph_cell g) |-- !!(~ In x li).
  Proof.
    intros; induction li.
    + apply prop_right. auto.
    + unfold iter_sepcon. fold (iter_sepcon li (graph_cell g)).
      rewrite <- sepcon_assoc. rewrite (sepcon_comm (trinode x (d, l, r))). rewrite sepcon_assoc.
      rewrite (add_andp _ _ IHli). normalize. rewrite <- sepcon_assoc. unfold graph_cell at 1.
      destruct (t_eq_dec a x).
      - subst.
        assert (trinode x (gamma g x) * trinode x (d, l, r) |-- FF). {
          apply mapsto_conflict. simpl. unfold addr_eqb. destruct (addr_eq_dec x x); auto.
        } rewrite (add_andp _ _ H0). normalize.
      - apply prop_right. simpl. intro. destruct H0; auto.
  Qed.

  Lemma trinode_graphs_unreachable:
    forall x d l r S g, x <> Null ->
                        trinode x (d, l, r) * graphs S g |-- !!(forall s, In s S -> ~ reachable g s x /\ s <> x).
  Proof.
    intros. rewrite graphs_unfold. normalize. intro li; intros.
    rewrite (add_andp _ _ (trinode_iter_sepcon_not_in _ _ _ _ _ _)).
    normalize. apply prop_right. intros. split.
    + intro; apply H2. clear H2. specialize (H1 x). rewrite <- H1. exists s. split; auto.
    + intro. subst. unfold reachable_set_list in H1. unfold reachable_through_set in H1.
      apply H2. rewrite <- H1. exists x. split; auto.
      apply reachable_by_reflexive. specialize (H0 x). apply H0 in H3. split.
      - destruct H3. tauto. auto.
      - hnf; auto.
  Qed.

  Lemma reachable_subgraph_derives:
    forall (g1 g2: Graph) x,
      ((reachable_subgraph g1 (x :: nil)) -=- (reachable_subgraph g2 (x :: nil))) ->
      graph x g1 |-- graph x g2.
  Proof.
    Implicit Arguments valid [[Vertex] [Data] [EV]].
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV]].
    intros. destruct H as [? [? ?]]. rewrite (add_andp _ _ (graph_root_nv _ _)).
    normalize. destruct H2.
    + subst. rewrite !graph_unfold_Null; auto.
    + unfold graph. normalize. apply (exp_right l).
      rewrite <- andp_assoc, <- prop_and. apply andp_right.
      - apply prop_right. simpl in H. unfold reachable_valid in H. split.
        * right. specialize (H x).
          assert (valid g1 x /\ reachable_through_set g1 (x :: nil) x). {
            split. auto. exists x. split.
            + apply in_eq.
            + apply reachable_by_reflexive. split; auto. hnf; auto.
          } rewrite H in H4. tauto.
        * unfold reachable_list in *. intros. specialize (H3 y).
          specialize (H y). rewrite H3. split; intros.
          1: {
            apply reachable_valid_and_through_single in H4.
            rewrite H in H4. destruct H4. destruct H5 as [s [? ?]].
            simpl in H5. destruct H5. subst; auto. tauto.
          }
          1: {
            apply reachable_valid_and_through_single in H4.
            rewrite <- H in H4. destruct H4. destruct H5 as [s [? ?]].
            simpl in H5. destruct H5. subst; auto. tauto.
          }
      - assert (forall z, In z l -> valid (reachable_subgraph g1 (x :: nil)) z). {
          intros. simpl. hnf. hnf in H3. rewrite H3 in H4. split.
          + apply reachable_foot_valid in H4; auto.
          + exists x. split. apply in_eq. auto.
        } clear H3. induction l. simpl. auto.
        unfold iter_sepcon.
        fold (iter_sepcon l (graph_cell g1)).
        fold (iter_sepcon l (graph_cell g2)).
        apply derives_trans with (graph_cell g1 a * iter_sepcon l (graph_cell g2));
          apply sepcon_derives; auto.
        * apply IHl. intros. apply H4. apply in_cons; auto.
        * unfold graph_cell. unfold gamma. unfold biEdge.
          destruct (only_two_neighbours g1 g1 a) as [? [? ?]].
          destruct (only_two_neighbours g2 g2 a) as [? [? ?]].
          assert (In a (a :: l)) by apply in_eq. specialize (H4 a H3).
          specialize (H0 a H4). specialize (H1 a H4).
          simpl in *. simpl. rewrite H0. rewrite H1 in e.
          rewrite e in e0. inversion e0. subst. auto.
    Implicit Arguments valid [[Vertex] [Data] [EV] [PreGraph]].
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV] [BiGraph]].
  Qed.

  Lemma reachable_subgraph_eq:
    forall (g1 g2 : Graph) x,
      ((reachable_subgraph g1 (x :: nil)) -=- (reachable_subgraph g2 (x :: nil))) -> graph x g1 = graph x g2.
  Proof.
    intros. apply pred_ext.
    + apply reachable_subgraph_derives; auto.
    + apply reachable_subgraph_derives; apply vi_sym; auto.
  Qed.
  
Instance update_graph (g: Graph) v d l r (Hi: in_math g v l r) (Hn: v <> Null): Graph := {
  pg := update_PreGraph _ v d l r;
  bi := update_BiGraph g v d l r;
  ma := update_MathGraph g v d l r Hi Hn
}.

  Lemma graphs_growth: forall x d l r (Hn: x <> Null) (g: Graph) (Hi: in_math g x l r),
                         trinode x (d, l, r) * graphs (l :: r :: nil) g |-- graph x (update_graph g x d l r Hi Hn).
  Proof.
    intros. rewrite (graph_unfold _ _ d l r).
    2 : apply update_bigraph_gamma.
    apply orp_right2, andp_right. apply prop_right; hnf; tauto.
    rewrite (add_andp _ _ (trinode_graphs_unreachable _ _ _ _ _ _ Hn)). normalize. 
    apply derives_trans with (trinode x (d, l, r) *
                              (graph l (update_graph g x d l r Hi Hn) ⊗ graph r (update_graph g x d l r Hi Hn))).
    2: rewrite ocon_assoc; apply sepcon_ocon.
    apply sepcon_derives; auto. unfold graphs. rewrite ocon_emp.
    apply ocon_derives; apply reachable_subgraph_derives.
    + assert (In l (l :: r :: nil)) by apply in_eq. destruct (H l H0).
      apply unreachable_node_add_graph_eq with g; eauto. exact g.
    + assert (In r (l :: r :: nil)) by apply in_cons, in_eq. destruct (H r H0).
      apply unreachable_node_add_graph_eq with g; auto. exact g.
  Qed.

  Lemma update_graph_single: forall x d l r (Hn: x <> Null) (g: Graph) (Hi: in_math g x l r),
                               trinode x (d, l, r) |-- graph_cell (update_graph g x d l r Hi Hn) x.
  Proof.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV]].
    intros. unfold graph_cell. unfold gamma. unfold biEdge.
    destruct (only_two_neighbours _ (update_graph g x d l r Hi Hn) x) as [v1 [v2 ?]].
    simpl in e. unfold change_edge_func in e. simpl. unfold change_node_label.
    destruct (@t_eq_dec (@addr (@SG_Setting SGA)) (@AddrDec (@SG_Setting SGA)) x x). 2: tauto.
    inversion e. subst. auto.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV] [BiGraph]].
  Qed.

  Lemma update_graph_iter_sepcon:
    forall x d l r li (Hn: x <> Null) (g: Graph) (Hi: in_math g x l r),
      ~ In x li -> iter_sepcon li (graph_cell g) |-- iter_sepcon li (graph_cell (update_graph g x d l r Hi Hn)).
  Proof.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV]].
    intros.
    induction li. simpl. auto.
    unfold iter_sepcon.
    fold (iter_sepcon li (graph_cell g)).
    fold (iter_sepcon li (graph_cell (update_graph g x d l r Hi Hn))).
    apply sepcon_derives.
    + unfold graph_cell. unfold gamma. unfold biEdge.
      destruct (only_two_neighbours _ (update_graph g x d l r Hi Hn) a) as [v1 [v2 ?]].
      destruct (only_two_neighbours _ g a) as [v3 [v4 ?]].
      assert (x <> a) by (intro; apply H; subst; apply in_eq). simpl in e. simpl. change addr with Addr in *.
      unfold change_node_label. unfold change_edge_func in e.
      destruct (t_eq_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst. auto.
    + apply IHli. intro. apply H. apply in_cons; auto.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV] [BiGraph]].
  Qed.

  Lemma graph_growth_right: forall x d r (Hn: x <> Null)
                                   (g: Graph) (Hi: in_math g x x r),
                              trinode x (d, x, r) * graph r g |-- graph x (update_graph g x d x r Hi Hn).
  Proof.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV]].
    intros. unfold graph. normalize.
    rewrite (add_andp _ _ (trinode_iter_sepcon_not_in _ _ _ _ _ _)). normalize.
    apply (exp_right (x :: l)). rewrite <- andp_assoc, <- prop_and. apply andp_right.
    + apply prop_right. split.
      - simpl. unfold change_valid. right; right; auto.
      - apply (reachable_list_update_graph_right g x d r Hn Hi l); auto.
    + unfold iter_sepcon at 2. fold (iter_sepcon l (graph_cell (update_graph g x d x r Hi Hn))).
      apply sepcon_derives.
      - apply (update_graph_single x d x r Hn g Hi).
      - apply (update_graph_iter_sepcon x d x r l Hn g Hi H1).
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV] [BiGraph]].
  Qed.

  Lemma graph_growth_left: forall x d l (Hn: x <> Null)
                                 (g: Graph) (Hi: in_math g x l x),
                             trinode x (d, l, x) * graph l g |-- graph x (update_graph g x d l x Hi Hn).
  Proof.
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV]].
    intros. unfold graph. normalize. intro li; intros.
    rewrite (add_andp _ _ (trinode_iter_sepcon_not_in _ _ _ _ _ _)). normalize.
    apply (exp_right (x :: li)). rewrite <- andp_assoc, <- prop_and. apply andp_right.
    + apply prop_right. split.
      - simpl. unfold change_valid. right; right; auto.
      - apply (reachable_list_update_graph_left g x d l Hn Hi li); auto.
    + unfold iter_sepcon at 2. fold (iter_sepcon li (graph_cell (update_graph g x d l x Hi Hn))).
      apply sepcon_derives.
      - apply (update_graph_single x d l x Hn g Hi).
      - apply (update_graph_iter_sepcon x d l x li Hn g Hi H1).
    Implicit Arguments only_two_neighbours [[Vertex] [Data] [EV] [BiGraph]].
  Qed.

End PointwiseGraph.
