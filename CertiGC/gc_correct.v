Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.floyd.sublist.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.graph_isomorphism.
Require Import RamifyCoq.CertiGC.GCGraph.
Import ListNotations.

Local Open Scope Z_scope.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertex_valid (g: LGraph): Prop := forall v, vvalid g v <-> graph_has_v g v.

Definition edge_valid (g: LGraph): Prop := forall e, evalid g e <-> graph_has_e g e.

Definition src_edge (g: LGraph): Prop := forall e, src g e = fst e.

Lemma cvae_vvalid_eq: forall g v' l v0,
    vvalid (fold_left (copy_v_add_edge v') l g) v0 <-> vvalid g v0.
Proof.
  intros. split; intro.
  - revert g H. induction l; intros; simpl in H; [assumption|].
    apply IHl in H; replace (vvalid (copy_v_add_edge v' g a) v0) with (vvalid g v0) in H by reflexivity; assumption.
  - revert g H. induction l; intros; simpl; [assumption|].
    apply IHl; replace (vvalid (copy_v_add_edge v' g a) v0) with (vvalid g v0) by reflexivity; assumption.
Qed.

Lemma lcv_vvalid_disj: forall g v v' to,
    vvalid (lgraph_copy_v g v to) v' <-> vvalid g v' \/ v' = new_copied_v g to.
  unfold lgraph_copy_v; simpl; unfold pregraph_copy_v.
  intros ? ? ? ?. apply cvae_vvalid_eq.
Qed.

Lemma sound_fr_lcv_vv: forall g v to,
    vertex_valid g ->
    graph_has_gen g to ->
    vertex_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold vertex_valid in H.
  split; intro.
  - apply lcv_vvalid_disj in H1; destruct H1.
    + apply H in H1; apply lcv_graph_has_v_old; assumption.
    + subst v0; apply lcv_graph_has_v_new; assumption.
  - rewrite lcv_vvalid_disj.
    apply lcv_graph_has_v_inv in H1; [|assumption];
      rewrite <- H in H1; assumption.
Qed.

Lemma fr_vv_correct: forall g g' from to p,
    vertex_valid g -> graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    vertex_valid g'.
Proof.
  intros. inversion H1; subst; try assumption.
  - apply sound_fr_lcv_vv; assumption.
  - replace (vertex_valid new_g) with
        (vertex_valid (lgraph_copy_v g (dst g e) to)) by (subst new_g; reflexivity).
    apply sound_fr_lcv_vv; assumption.
Qed.

Lemma frl_vv_correct: forall g g' from to r1 r2 fi il,
    vertex_valid g ->
    graph_has_gen g to ->
    forward_roots_loop from to fi il r1 g r2 g' ->
    vertex_valid g'.
Proof.
  intros. revert r1 r2 g g' fi H H0 H1.
  induction il.
  - intros. inversion H1; subst; assumption.
  - intros. inversion H1; subst.
    pose proof (fr_vv_correct _ _ _ _ _ H H0 H4).
    rewrite (fr_graph_has_gen _ _ _ _ _ _ H0 H4 to) in H0.
    apply (IHil (upd_roots from to (inl (Z.of_nat a)) g r1 fi) r2 g2 g' fi H2 H0 H9).
Qed.

Lemma frr_vv_correct: forall g g' from to fi r1 r2,
    vertex_valid g ->
    graph_has_gen g to ->
    forward_roots_relation from to fi r1 g r2 g' ->
    vertex_valid g'.
Proof.
  intros. inversion H1; subst; try assumption.
  pose proof (fr_vv_correct _ _ _ _ _ H H0 H3).
  rewrite (fr_graph_has_gen _ _ _ _ _ _ H0 H3 to) in H0.
  apply (frl_vv_correct _ _ _ _ _ _ _ _ H5 H0 H4).
Qed.

Lemma dsr_vv_correct: forall g g' from to to_index,
    vertex_valid g ->
    graph_has_gen g to ->
    do_scan_relation from to to_index g g' ->
    vertex_valid g'.
Proof.
  intros. destruct H1 as [? [? ?]].
  split; intros.
  - apply (svwl_graph_has_v _ _ _ _ _ H0 H1).
    unfold vertex_valid in H; rewrite <- H.
    admit.
  - inversion H1; subst; try assumption.
    + unfold vertex_valid in H; rewrite H; assumption.
    + admit.
    + admit.
Abort.

Lemma dgr_vv_correct: forall g g' from to fi r1 r2,
    vertex_valid g ->
    graph_has_gen g to ->
    do_generation_relation from to fi r1 r2 g g' ->
    vertex_valid g'.
Proof.
  intros.
  destruct H1 as [? [? [? [? ?]]]].
  subst.
  pose proof (frr_vv_correct _ _ _ _ _ _ _ H H0 H1).
  rewrite (frr_graph_has_gen _ _ _ _ _ _ _ H0 H1 to) in H0.
  (* pose proof (dsr_vv_correct _ _ _ _ _ H3 H0 H2). *)
  admit.
Abort.

Lemma gcr_vv_correct: forall g g' to fi r1 r2,
    vertex_valid g ->
    graph_has_gen g to ->
    garbage_collect_relation fi r1 r2 g g' ->
    vertex_valid g'.
Proof.
  intros. destruct H1 as [? [? ?]].
  inversion H1; subst; try assumption.
  admit.
Abort.

Lemma lcv_get_edges: forall (g: LGraph) v v' to,
    graph_has_v g v' ->
    graph_has_gen g to ->
    get_edges (lgraph_copy_v g v to) v' = get_edges g v'.
Proof.
  intros. unfold get_edges, make_fields, make_fields'.
  rewrite <- lcv_raw_fields by assumption. reflexivity.
Qed.

Lemma cvae_src_new: forall new l g e,
    src g e = new ->
    src (fold_left (copy_v_add_edge new) l g) e = new.
Proof.
  intros. revert g H. induction l.
  1: simpl; intros; assumption.
  intros. simpl.
  apply IHl. simpl. unfold updateEdgeFunc.
  if_tac; [reflexivity | assumption].
Qed.

Lemma cvae_src': forall new l g e v,
    src g e = v ->
    src (fold_left (copy_v_add_edge new) l g) e = v.
Proof.
  intros. revert g H. induction l.
  1: simpl; intros; assumption.
  intros. simpl.
  apply IHl. simpl. unfold updateEdgeFunc.
  rewrite H. apply if_false.
  intro. admit. (* need some more conditions, like NoDup *)
Abort.

Lemma cvae_src_disj: forall g g' new (e: EType) (l: list (EType * VType)),
    g' = (fold_left (copy_v_add_edge new) l g) ->
    (In e (map fst l) -> src g' e = new) /\
    (~ In e (map fst l) -> src g' e = src g e).
Proof.
  intros. split.
  - revert g H. induction l; [inversion 2|].
    intros. simpl in H.
    simpl in H0. destruct H0.
    + assert (src (copy_v_add_edge new g a) e = new). {
        simpl; rewrite H0; unfold updateEdgeFunc.
        apply if_true; apply equiv_reflexive.
      }
      rewrite H. apply (cvae_src_new  _ _ _ _ H1).
    + apply (IHl (copy_v_add_edge new g a)); assumption.
  - revert g H. induction l.
    1: intros; simpl in H; rewrite H; reflexivity.
    intros. simpl in H0; unfold not in H0.
    simpl in H; apply IHl in H.
    2: intro; apply H0; right; assumption.
    rewrite H; simpl; unfold updateEdgeFunc; apply if_false.
    intro. apply H0. left. assumption.
Qed.

Lemma pcv_src_disj: forall g old new e v,
    src (pregraph_copy_v g old new) e = v ->
    v = new \/ v = src g e.
Proof.
  intros. unfold pregraph_copy_v in H.
  remember (combine (combine (repeat new (Datatypes.length (get_edges g old)))
                             (map snd (get_edges g old))) (map (dst g)
                                                               (get_edges g old))).
  remember (fold_left (copy_v_add_edge new) l (pregraph_add_vertex g new)) as g'.
  destruct (cvae_src_disj _ _ _ e _ Heqg').
  rewrite <- H.
  assert (In e (map fst l) \/ ~ In e (map fst l)) by (apply Classical_Prop.classic).
  destruct H2; [left; apply H0; assumption | right; apply H1; assumption].
Qed.

Lemma cvae_evalid: forall g new l e,
    evalid g e ->
    evalid (fold_left (copy_v_add_edge new) l g) e.
Proof.
  intros.
  - revert g H. induction l.
    + simpl; intros; assumption.
    + intros. simpl. apply IHl. simpl.
      unfold addValidFunc; left; assumption.
Qed.

(** Reset related properties *)

Lemma fold_left_remove_edge_vvalid: forall (g: PreGraph VType EType) l v,
    vvalid (fold_left pregraph_remove_edge l g) v <-> vvalid g v.
Proof.
  intros. revert g; induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. reflexivity.
Qed.

Lemma lrvae_vvalid: forall g v1 v2,
    vvalid (lgraph_remove_vertex_and_edges g v1) v2 <-> vvalid g v2 /\ v1 <> v2.
Proof.
  intros. simpl. unfold pregraph_remove_vertex_and_edges.
  rewrite fold_left_remove_edge_vvalid, remove_vertex_vvalid. intuition.
Qed.

Lemma fold_left_lrvae_vvalid: forall g l v,
    vvalid (fold_left lgraph_remove_vertex_and_edges l g) v <->
    vvalid g v /\ ~ In v l.
Proof.
  intros. revert g v. induction l; intros; simpl. 1: intuition.
  rewrite IHl, lrvae_vvalid. intuition.
Qed.

Lemma vertex_valid_reset: forall g gen,
    vertex_valid g -> vertex_valid (reset_graph gen g).
Proof.
  intros. unfold vertex_valid in *. intros. simpl. rewrite graph_has_v_reset.
  unfold remove_nth_gen_ve. rewrite fold_left_lrvae_vvalid. rewrite H. intuition.
  - apply H2. clear H2. destruct v as [vgen vidx]. simpl in *. subst vgen.
    change (gen, vidx) with ((fun idx : nat => (gen, idx)) vidx). apply in_map.
    rewrite nat_inc_list_In_iff. destruct H1. simpl in *. red in H1. assumption.
  - apply H2. clear H2. apply list_in_map_inv in H0. destruct H0 as [vidx [? _]].
    subst v. simpl. reflexivity.
Qed.

Lemma remove_ve_src_unchanged: forall g gen e,
    src (remove_nth_gen_ve g gen) e = src g e.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g e. induction l; intros; simpl. 1: reflexivity. rewrite IHl.
  clear. simpl. unfold pregraph_remove_vertex_and_edges.
  transitivity (src (pregraph_remove_vertex g a) e). 2: reflexivity.
  remember (pregraph_remove_vertex g a) as g'. remember (get_edges g a) as l.
  clear a g Heqg' Heql. rename g' into g. revert g e. induction l; intros; simpl.
  1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma src_edge_reset: forall g gen, src_edge g -> src_edge (reset_graph gen g).
Proof.
  intros. unfold src_edge in *. intros.
  simpl. rewrite remove_ve_src_unchanged. apply H.
Qed.

Lemma fold_left_remove_edge_evalid: forall (g: PreGraph VType EType) l e,
    evalid (fold_left pregraph_remove_edge l g) e <-> evalid g e /\ ~ In e l.
Proof.
  intros. revert g; induction l; intros; simpl. 1: intuition.
  rewrite IHl, remove_edge_evalid. intuition.
Qed.

Lemma lrvae_evalid: forall g v e,
    evalid (lgraph_remove_vertex_and_edges g v) e <->
    evalid g e /\ ~ In e (get_edges g v).
Proof.
  intros. simpl. unfold pregraph_remove_vertex_and_edges.
  rewrite fold_left_remove_edge_evalid. intuition.
Qed.

Lemma fold_left_lrvae_evalid: forall g l e,
    evalid (fold_left lgraph_remove_vertex_and_edges l g) e <->
    evalid g e /\ forall v, In v l -> ~ In e (get_edges g v).
Proof.
  intros. revert g e. induction l; intros; simpl. 1: intuition.
  rewrite IHl, lrvae_evalid. intuition.
  - subst. contradiction.
  - specialize (H1 _ H4). apply H1. assumption.
  - apply (H1 a); intuition.
  - apply (H1 v); intuition.
Qed.

Lemma edge_valid_reset: forall g gen, edge_valid g -> edge_valid (reset_graph gen g).
Proof.
  intros. unfold edge_valid in *. intros. rewrite graph_has_e_reset. simpl.
  unfold remove_nth_gen_ve. rewrite fold_left_lrvae_evalid, H. intuition.
  - destruct e. unfold egeneration in H0. simpl in H0. apply (H2 v).
    + destruct v as [vgen vidx]. simpl in *. subst vgen.
      change (gen, vidx) with ((fun idx : nat => (gen, idx)) vidx). apply in_map.
      rewrite nat_inc_list_In_iff. destruct H1 as [[_ ?] _]. simpl in H0. assumption.
    + destruct H1. simpl in H3. assumption.
  - apply H2. clear H2. apply get_edges_fst in H3. destruct e. simpl in *. subst v0.
    unfold egeneration. simpl. apply list_in_map_inv in H0. destruct H0 as [x [? _]].
    subst v. simpl. reflexivity.
Qed.

(** GC Graph Isomorphism *)

Definition root_map (vmap: VType -> VType) (r: root_t): root_t :=
  match r with
  | inl x => inl x
  | inr r => inr (vmap r)
  end.

Lemma bijective_root_map: forall vmap1 vmap2,
    bijective vmap1 vmap2 -> bijective (root_map vmap1) (root_map vmap2).
Proof.
  intros. destruct H. split; intros.
  - destruct x, y; simpl in H; inversion H; try reflexivity. apply injective in H1.
    subst; reflexivity.
  - destruct x; simpl; try reflexivity. rewrite surjective. reflexivity.
Qed.

Definition gc_graph_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t): Prop :=
  let vertices1 := filter_sum_right roots1 in
  let vertices2 := filter_sum_right roots2 in
  let sub_g1 := reachable_sub_labeledgraph g1 vertices1 in
  let sub_g2 := reachable_sub_labeledgraph g2 vertices2 in
  exists vmap12 vmap21 emap12 emap21,
    roots2 = map (root_map vmap12) roots1 /\
    label_preserving_graph_isomorphism_explicit
      sub_g1 sub_g2 vmap12 vmap21 emap12 emap21.

Lemma gc_graph_iso_refl: forall g roots, gc_graph_iso g roots g roots.
Proof.
  intros. red. exists id, id, id, id. split. 2: apply lp_graph_iso_exp_refl.
  clear. induction roots; simpl; auto. rewrite <- IHroots. f_equal. destruct a; auto.
Qed.

Lemma gc_graph_iso_sym: forall g1 roots1 g2 roots2,
    gc_graph_iso g1 roots1 g2 roots2 -> gc_graph_iso g2 roots2 g1 roots1.
Proof.
  intros. unfold gc_graph_iso in *.
  destruct H as [vmap12 [vmap21 [emap12 [emap21 [? ?]]]]].
  exists vmap21, vmap12, emap21, emap12. split.
  - destruct H0 as [[?H _] _]. clear -H H0.
    apply bijective_root_map, bijective_map, bijective_sym in H0. destruct H0.
    rewrite H, surjective. reflexivity.
  - apply lp_graph_iso_exp_sym. assumption.
Qed.

Lemma gc_graph_iso_trans: forall g1 roots1 g2 roots2 g3 roots3,
    gc_graph_iso g1 roots1 g2 roots2 -> gc_graph_iso g2 roots2 g3 roots3 ->
    gc_graph_iso g1 roots1 g3 roots3.
Proof.
  intros. unfold gc_graph_iso in *. destruct H as [v12 [v21 [e12 [e21 [? ?]]]]].
  destruct H0 as [v23 [v32 [e23 [e32 [? ?]]]]].
  exists (compose v23 v12), (compose v21 v32), (compose e23 e12), (compose e21 e32).
  split. 2: eapply lp_graph_iso_exp_trans; eauto.
  rewrite H0. rewrite H. rewrite map_map. clear. induction roots1; simpl; auto.
  rewrite IHroots1. f_equal. destruct a; simpl; reflexivity.
Qed.

Definition gen_single_edge_pair_list
           (g: LGraph) (p: VType * VType): list (EType * EType) :=
  let (k, v) := p in let el1 := get_edges g k in
                     let el2 := map (fun e => (v, snd e)) el1 in combine el1 el2.

Definition gen_edge_pair_list
           (g: LGraph) (l: list (VType * VType)): list (EType * EType) :=
  concat (map (gen_single_edge_pair_list g) l).

Lemma get_edges_NoDup: forall g v, NoDup (get_edges g v).
Proof.
  intros. unfold get_edges. unfold make_fields. remember (raw_fields (vlabel g v)).
  clear Heql. remember O. clear Heqn g. revert n. induction l; intros; simpl.
  1: constructor. destruct a; [destruct s|]; simpl; [apply IHl..|].
  rewrite NoDup_cons_iff. split. 2: apply IHl. intro.
  rewrite <- filter_sum_right_In_iff in H.
  apply In_nth with (d := field_t_inhabitant) in H. destruct H as [p [? ?]].
  apply make_fields'_edge_depends_on_index in H0. 1: inversion H0; omega.
  rewrite make_fields'_eq_length in H. rewrite Zlength_correct. split. 1: omega.
  apply Nat2Z.inj_lt; assumption.
Qed.

Lemma gsepl_DoubleNoDup: forall (v1 v2 : VType) (g : LGraph),
    v1 <> v2 -> DoubleNoDup (gen_single_edge_pair_list g (v1, v2)).
Proof.
  intros. simpl. pose proof (get_edges_NoDup g v1). remember (get_edges g v1).
  assert (forall e, In e l -> fst e = v1) by
      (intros; subst l; apply get_edges_fst in H1; assumption). clear Heql g.
  induction l; simpl. 1: constructor. rewrite DoubleNoDup_cons_iff.
  destruct a as [? idx]. simpl. assert (v = v1) by
      (change v with (fst (v, idx)); apply H1; left; reflexivity). subst v.
  split; [|split; [|split]].
  - apply IHl. 1: apply NoDup_cons_1 in H0; assumption. intros. apply H1.
    simpl. right; assumption.
  - intro. inversion H2. contradiction.
  - unfold InEither. rewrite combine_split by (rewrite map_length; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + apply NoDup_cons_2 in H0. contradiction.
    + rewrite in_map_iff in H2. destruct H2 as [x [? ?]]. inversion H2.
      apply H. auto.
  - unfold InEither. rewrite combine_split by (rewrite map_length; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + specialize (H1 (v2, idx)). simpl in H1. apply H.
      rewrite H1; [|right]; [reflexivity | assumption].
    + rewrite in_map_iff in H2. destruct H2 as [[? ?] [? ?]]. simpl in *.
      inversion H2. subst n. clear H2. assert (v = v1) by
          (change v with (fst (v, idx)); apply H1; right; assumption). subst.
      apply NoDup_cons_2 in H0. contradiction.
Qed.

Lemma gsepl_InEither: forall x g a,
    InEither x (gen_single_edge_pair_list g a) -> IsEither (fst x) a.
Proof.
  intros. destruct a as [v1 v2]. red. simpl.
  unfold gen_single_edge_pair_list in H. remember (get_edges g v1).
  assert (forall e, In e l -> fst e = v1) by
      (intros; subst l; apply get_edges_fst in H0; assumption). clear Heql g.
  induction l; simpl in *. 1: inversion H. rewrite InEither_cons_iff in H.
  destruct a as [v idx]. simpl in *. assert (v = v1) by
      (change v with (fst (v, idx)); apply H0; left; reflexivity). subst v. destruct H.
  - red in H. simpl in H. destruct H; subst; simpl; intuition.
  - apply IHl; auto.
Qed.

Lemma gepl_InEither: forall x g l,
    InEither x (gen_edge_pair_list g l) -> InEither (fst x) l.
Proof.
  intros. induction l; simpl in *; unfold gen_edge_pair_list in H; simpl in H.
  1: inversion H. fold (gen_edge_pair_list g l) in H. rewrite InEither_app_iff in H.
  rewrite InEither_cons_iff.
  destruct H; [left; eapply gsepl_InEither; eauto | right; apply IHl; assumption].
Qed.

Lemma gepl_DoubleNoDup:
  forall g l, DoubleNoDup l -> DoubleNoDup (gen_edge_pair_list g l).
Proof.
  intros g l. revert g. induction l; intros.
  1: unfold gen_edge_pair_list; simpl; constructor.
  unfold gen_edge_pair_list. simpl. fold (gen_edge_pair_list g l).
  destruct a as [v1 v2]. apply DoubleNoDup_cons_iff in H. destruct H as [? [? [? ?]]].
  rewrite DoubleNoDup_app_iff. split; [|split]. 2: apply IHl; assumption.
  - apply gsepl_DoubleNoDup. assumption.
  - intros. apply gsepl_InEither in H3. intro. apply gepl_InEither in H4. red in H3.
    simpl in H3. destruct H3; rewrite H3 in H4; contradiction.
Qed.

Definition gc_graph_quasi_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t) (from to: nat): Prop :=
  is_partial_lgraph g1 g2 /\
  exists (l: list (VType * VType)),
    roots2 = map (root_map (list_bi_map l)) roots1 /\
    forall v1 v2, In (v1, v2) l ->
                  vvalid g1 v1 /\ vvalid g2 v2 /\ vgeneration v1 = from /\
                  vgeneration v2 = to /\ vlabel g1 v1 = vlabel g2 v2 /\
                  reachable_through_set g1 (filter_sum_right roots1) v1 /\
                  (forall e1, In e1 (get_edges g1 v1) ->
                              let e2 := (v2, snd e1) in
                              In e2 (get_edges g2 v2) /\
                              (dst g2 e2 = list_bi_map l (dst g1 e1) \/
                               dst g2 e2 = dst g1 e1)).

Lemma fr_O_quasi_iso: forall from to p g1 g2 roots1 roots2 g3 f_info,
    forward_p_compatible p roots2 g2 from ->
    gc_graph_quasi_iso g1 roots1 g2 roots2 from to ->
    forward_relation from to O (forward_p2forward_t p roots2 g2) g2 g3 ->
    gc_graph_quasi_iso g2 roots2 g3 (upd_roots from to p g2 roots2 f_info) from to.
Proof.
Abort.

Lemma quasi_iso_foward_roots: forall g1 roots1 g2 roots2 gen f_info,
    forward_roots_relation gen (S gen) f_info roots1 g1 roots2 g2 ->
    gc_graph_quasi_iso g1 roots1 g2 roots2 gen (S gen).
Proof.
Abort.

Lemma quasi_iso_do_scan: forall g1 roots1 g2 roots2 gen to_index g3,
    gc_graph_quasi_iso g1 roots1 g2 roots2 gen (S gen) ->
    do_scan_relation gen (S gen) to_index g2 g3 ->
    gc_graph_quasi_iso g1 roots1 g3 roots2 gen (S gen).
Proof.
Abort.

Lemma quasi_iso_reset_iso: forall g1 roots1 g2 roots2 gen,
    gc_graph_quasi_iso g1 roots1 g2 roots2 gen (S gen) ->
    no_edge2gen g2 gen -> roots_have_no_gen roots2 gen ->
    gc_graph_iso g1 roots1 (reset_graph gen g2) roots2.
Proof.
  intros. red in H. red. destruct H as [? [vpl [? ?]]].
Abort.
