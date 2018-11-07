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

Definition sound_gc_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g.

Lemma reset_is_sound: forall (g: LGraph) gen,
    sound_gc_graph g -> sound_gc_graph (reset_graph gen g).
Proof.
  intros. destruct H as [? [? ?]]. split; [|split].
  - apply vertex_valid_reset; auto.
  - apply edge_valid_reset; auto.
  - apply src_edge_reset; auto.
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

Lemma get_edges_map_map: forall g v,
    get_edges g v = map (fun idx => (v, idx)) (map snd (get_edges g v)).
Proof.
  intros. rewrite map_map. unfold get_edges, make_fields.
  remember (raw_fields (vlabel g v)). remember O. clear Heql Heqn. revert n.
  induction l; intros; simpl; auto; destruct a; [destruct s|];
    simpl; rewrite <- IHl; auto.
Qed.

Lemma get_edges_inv: forall g v e,
    In e (get_edges g v) <->
    exists idx, e = (v, idx) /\ In idx (map snd (get_edges g v)).
Proof.
  intros. destruct e as [gen idx]. split; intros.
  - pose proof H. apply get_edges_fst in H0. simpl in H0. subst gen. exists idx.
    rewrite get_edges_In in H. split; auto.
  - destruct H as [? [? ?]]. inversion H. subst. rewrite get_edges_In. assumption.
Qed.

Lemma In_snd_get_edges: forall g v idx,
    In idx (map snd (get_edges g v)) -> In (v, idx) (get_edges g v).
Proof. intros. rewrite get_edges_inv. exists idx. split; auto. Qed.

Lemma vlabel_get_edges_snd: forall v1 v2 (g1 g2: LGraph),
    vlabel g1 v1 = vlabel g2 v2 ->
    map snd (get_edges g1 v1) = map snd (get_edges g2 v2).
Proof.
  intros. unfold get_edges. unfold make_fields. rewrite H.
  remember (raw_fields (vlabel g2 v2)). clear H Heql. remember O. clear Heqn.
  revert n. induction l; intros; simpl; auto.
  destruct a; [destruct s |]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma gsepl_key: forall e g v,
    In e (get_edges g (fst e)) ->
    In (e, (v, snd e)) (gen_single_edge_pair_list g (fst e, v)).
Proof.
  intros. simpl. remember (get_edges g (fst e)). clear Heql.
  induction l; simpl in *; auto. destruct H; [left; subst | right; apply IHl]; auto.
Qed.

Lemma gsepl_value: forall (e: EType) k (g1 g2: LGraph),
    In e (get_edges g2 (fst e)) -> vlabel g1 k = vlabel g2 (fst e) ->
    In (k, snd e, e) (gen_single_edge_pair_list g1 (k, fst e)).
Proof.
  intros. destruct e as [gen idx]. simpl in *. rewrite get_edges_In in H.
  rewrite get_edges_map_map. apply vlabel_get_edges_snd in H0. rewrite H0.
  remember (map snd (get_edges g2 gen)). rewrite map_map. simpl. clear -H.
  induction l; simpl. 1: inversion H. simpl in H.
  destruct H; [left; subst a; reflexivity | right; apply IHl; assumption].
Qed.

Lemma gepl_key: forall (g : LGraph) (vpl : list (VType * VType)) (e : EType) v,
    In e (get_edges g (fst e)) -> In (fst e, v) vpl ->
    In (e, (v, snd e)) (gen_edge_pair_list g vpl).
Proof.
  intros. induction vpl. 1: inversion H0. unfold gen_edge_pair_list. simpl.
  fold (gen_edge_pair_list g vpl). simpl in H0. rewrite in_app_iff.
  destruct H0; [left; subst a; apply gsepl_key | right; apply IHvpl]; auto.
Qed.

Lemma gepl_value: forall (e: EType) k (g1 g2: LGraph) vpl,
    In e (get_edges g2 (fst e)) -> In (k, fst e) vpl ->
    vlabel g1 k = vlabel g2 (fst e) -> In (k, snd e, e) (gen_edge_pair_list g1 vpl).
Proof.
  intros. induction vpl. 1: inversion H0. unfold gen_edge_pair_list. simpl.
  fold (gen_edge_pair_list g1 vpl). simpl in H0. rewrite in_app_iff. destruct H0.
  - left. subst a. eapply gsepl_value; eauto.
  - right. apply IHvpl. auto.
Qed.

Definition GenNoDup (l: list VType) (gen: nat): Prop :=
  NoDup l /\ forall v, In v l -> vgeneration v = gen.

Definition PairGenNoDup (l: list (VType * VType)) (from to: nat): Prop :=
  let (left_l, right_l) := split l in GenNoDup left_l from /\ GenNoDup right_l to.

Lemma PairGenNoDup_DoubleNoDup: forall l from to,
    from <> to -> PairGenNoDup l from to -> DoubleNoDup l.
Proof.
  intros. red in H0 |-* . destruct (split l) as [l1 l2]. destruct H0 as [[? ?] [? ?]].
  rewrite NoDup_app_eq. do 2 (split; auto). repeat intro. apply H1 in H4.
  apply H3 in H5. rewrite H4 in H5. contradiction.
Qed.

Definition from_gen_spec (g: LGraph) (roots: roots_t) (l: list VType) gen: Prop :=
  NoDup l /\ forall v,
    (reachable_through_set g (filter_sum_right roots) v /\ vgeneration v = gen) <->
    In v l.

Definition to_gen_spec (g1 g2: LGraph) (l: list VType) gen: Prop :=
  NoDup l /\ (forall v, In v l <-> vvalid g2 v /\ ~ vvalid g1 v) /\
  forall v, In v l -> vgeneration v = gen.

Definition gc_graph_quasi_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t) (from to: nat): Prop :=
  is_partial_lgraph g1 g2 /\
  exists (l: list (VType * VType)),
    roots2 = map (root_map (list_bi_map l)) roots1 /\
    (forall v1 v2,
        In (v1, v2) l ->
        vlabel g1 v1 = vlabel g2 v2 /\
        forall idx, In idx (map snd (get_edges g1 v1)) ->
                    (dst g2 (v2, idx) = dst g1 (v1, idx) \/
                     dst g2 (v2, idx) = list_bi_map l (dst g1 (v1, idx)))) /\
    let (from_l, to_l) := split l in
    from_gen_spec g1 roots1 from_l from /\ to_gen_spec g1 g2 to_l to.

Definition gen_has_index_dec (g: LGraph) (gen idx: nat):
  {gen_has_index g gen idx} + {~ gen_has_index g gen idx}.
Proof.
  unfold gen_has_index.
  destruct (lt_dec idx (number_of_vertices (nth_gen g gen))); [left | right]; auto.
Defined.

Lemma graph_has_v_dec: forall (g: LGraph) (v: VType),
    {graph_has_v g v} + {~ graph_has_v g v}.
Proof.
  intros. destruct v as [vgen vidx]. destruct (graph_has_gen_dec g vgen).
  - destruct (gen_has_index_dec g vgen vidx). 1: left; red; simpl; split; auto.
    right. intro; apply n. destruct H. simpl in H0. auto.
  - right. intro. apply n. destruct H. simpl in H. assumption.
Defined.

Lemma vvalid_lcm: forall g v, vertex_valid g -> vvalid g v \/ ~ vvalid g v.
Proof. intros. red in H. rewrite H. destruct (graph_has_v_dec g v); auto. Qed.

Lemma quasi_iso_reset_iso: forall g1 roots1 g2 roots2 gen,
    gc_graph_quasi_iso g1 roots1 g2 roots2 gen (S gen) ->
    sound_gc_graph g2 -> sound_gc_graph g1 ->
    no_edge2gen g1 gen -> no_edge2gen g2 gen -> roots_have_no_gen roots2 gen ->
    gc_graph_iso g1 roots1 (reset_graph gen g2) roots2.
Proof.
  intros. red in H. red. destruct H as [? [vpl [? [? ?]]]].
  destruct (split vpl) as [from_l to_l] eqn:? . destruct H7 as [[? ?] [? [? ?N]]].
  assert (DoubleNoDup vpl). {
    apply (PairGenNoDup_DoubleNoDup _ gen (S gen)). 1: omega. red. rewrite Heqp.
    split; split; auto; intros.
    - rewrite <- H8 in H11. destruct H11; auto. }
  assert (Hn: DoubleNoDup (gen_edge_pair_list g1 vpl)) by
      (apply gepl_DoubleNoDup; auto). pose proof (split_combine vpl).
  rewrite Heqp in H12.
  assert (forall x, vvalid g1 x -> InEither x vpl ->
                    exists k v, In (k, v) vpl /\ x = k /\ list_bi_map vpl x = v). {
    intros. apply (list_bi_map_In vpl x) in H14. destruct H14 as [k [v [? ?]]].
    exists k, v. destruct H15; auto. destruct H15. subst x. rewrite <- H12 in H14.
    apply in_combine_r in H14. apply H10 in H14. destruct H14 as [_ ?].
    contradiction. } remember (list_bi_map vpl) as vmap.
  remember (list_bi_map (gen_edge_pair_list g1 vpl)) as emap.
  assert (Hs: forall e, evalid g1 e -> vmap (src g1 e) = src g2 (emap e)). {
    intros. destruct H1 as [? [? ?]]. red in H1, H15, H16. rewrite H15 in H14.
    destruct H14. rewrite H16 in *. rewrite <- H1 in H14. subst vmap emap.
    destruct H0 as [_ [_ ?]]. red in H0. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H14 i). destruct H13 as [k [v [? [? ?]]]].
      rewrite H18, H19 in *. subst k. pose proof (gepl_key _ _ _ _ H17 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H18) as [? _]. rewrite H20.
      rewrite H0. simpl. reflexivity.
    - rewrite !list_bi_map_not_In; auto. intro; apply n; apply gepl_InEither in H18.
      auto. }
  assert (Hd: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) e ->
             vmap (dst g1 e) = dst g2 (emap e)). {
    intros. simpl in H14. destruct H14 as [? [? ?]].
    destruct H1 as [? [? ?]]. red in H1, H17, H18. pose proof H14.
    rewrite H17 in H14. destruct H14. rewrite H18 in *. rewrite <- H1 in H14.
    assert (~ In (dst g1 e) to_l). {
      intro. rewrite H10 in H21. destruct H21.
      apply reachable_through_set_foot_valid in H16. contradiction. }
    subst vmap emap. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H14 i). destruct H13 as [k [v [? [? ?]]]]. subst k.
      pose proof (gepl_key _ _ _ _ H20 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H22) as [? _]. rewrite H24.
      destruct (H6 _ _ H13) as [? ?]. rewrite get_edges_inv in H20.
      destruct H20 as [idx [? ?]]. rewrite H20 in *. simpl in *.
      specialize (H26 _ H27). destruct H26; auto. rewrite <- H20 in *.
      destruct (InEither_dec (dst g1 e) vpl).
      2: rewrite list_bi_map_not_In; auto. red in i0. rewrite Heqp in i0.
      rewrite in_app_iff in i0. destruct i0. 2: contradiction.
      rewrite <- H8 in H28. destruct H28 as [_ ?]. exfalso.
      assert (graph_has_e g2 (v, idx)). {
        split; simpl.
        - rewrite <- H12 in H13. apply in_combine_r in H13.
          rewrite H10 in H13. destruct H13. destruct H0 as [? _]. red in H0.
          rewrite <- H0. assumption.
        - apply In_snd_get_edges. apply vlabel_get_edges_snd in H25.
          rewrite <- H25. assumption. } destruct v as [vgen vidx].
      assert (vgen = S gen). {
        rewrite <- H12 in H13. apply in_combine_r in H13. apply N in H13.
        simpl in H13. assumption. } subst vgen.
      assert (S gen <> gen) by omega. specialize (H3 _ H30 vidx (snd e)).
      simpl in H3. rewrite H20 in *. simpl in *. apply H3; auto.
      change (prod nat nat) with VType. rewrite H26; auto.
    - assert (~ InEither (dst g1 e) vpl). {
        intro. unfold InEither in H22. rewrite Heqp, in_app_iff in H22.
        destruct H22; auto. rewrite <- H8 in H22. destruct H22 as [_ ?].
        assert (vgeneration (fst e) <> gen). {
          intro. apply n. unfold InEither. rewrite Heqp, in_app_iff. left.
          rewrite <- H8. split; auto. }
        assert (graph_has_e g1 e) by (split; [rewrite <- H1|]; auto).
        destruct e as [[vgen vidx] eidx] eqn:? . simpl in H23.
        specialize (H2 _ H23 vidx eidx). simpl in H2. specialize (H2 H24).
        contradiction. } rewrite !list_bi_map_not_In; auto.
      2: intro; apply n; apply gepl_InEither in H23; auto.
      destruct H as [[_ [_ [_ ?]]] _]. apply H; auto.
      apply reachable_through_set_foot_valid in H16. auto. }
  assert (He: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) e ->
             evalid (remove_nth_gen_ve g2 gen) (emap e)). {
    intros. destruct (reset_is_sound _ gen H0) as [? [? ?]]. rewrite Heqemap.
    simpl in H14. destruct H14 as [? [? ?]]. pose proof H14. red in H16. simpl in H16.
    rewrite H16. rewrite graph_has_e_reset. destruct H1 as [? [? ?]]. red in H21.
    rewrite H21 in H14. destruct H14. red in H1. rewrite <- H1 in H14.
    destruct H0 as [? [? _]]. red in H0. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H14 i) as [k [v [? [? ?]]]]. subst k.
      pose proof (gepl_key _ _ _ _ H23 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H25) as [? _]. rewrite H27.
      unfold graph_has_e, egeneration. simpl. rewrite <- H0. pose proof H13.
      rewrite <- H12 in H13. apply in_combine_r in H13. pose proof H13.
      rewrite H10 in H13. destruct H13 as [? _]. apply N in H29. rewrite H29.
      split; [split|]; [auto | | omega]. rewrite get_edges_inv in H23.
      destruct H23 as [idx [? ?]]. rewrite H23. simpl. apply H6 in H28.
      destruct H28 as [? _]. apply vlabel_get_edges_snd in H28.
      rewrite get_edges_In, <- H28. assumption.
    - red in H24. rewrite list_bi_map_not_In, <- H24.
      2: intro; apply n; apply gepl_InEither in H25; auto. split.
      1: destruct H as [[_ [? _]] _]; apply H; auto. unfold egeneration. red in H22.
      intro. rewrite H22 in H18. apply n. red. rewrite Heqp.
      rewrite in_app_iff, <- H8. left. symmetry in H25. split; assumption. }
  assert (Hv: forall x,
             vvalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) x ->
             vvalid (remove_nth_gen_ve g2 gen) (vmap x)). {
    destruct (reset_is_sound _ gen H0) as [? [? ?]].
    intros. simpl in H17. destruct H17. rewrite Heqvmap in *.
    specialize (H14 (list_bi_map vpl x)). simpl in H14. rewrite H14.
    rewrite graph_has_v_reset. destruct (InEither_dec x vpl).
    - specialize (H13 _ H17 i). destruct H13 as [v1 [v2 [? [? ?]]]].
      subst x; rewrite H20. rewrite <- H12 in H13. apply in_combine_r in H13.
      pose proof H13. apply N in H13. rewrite H10 in H19. destruct H19 as [? _].
      destruct H0 as [? _]. red in H0. rewrite <- H0. split; auto. omega.
    - rewrite list_bi_map_not_In; auto. destruct H as [[? _] _].
      destruct H0 as [? _]. red in H0. rewrite <- H0. split. 1: apply H; auto.
      intro. apply n. clear n. red. rewrite Heqp, in_app_iff. left. rewrite <- H8.
      symmetry in H19. split; assumption. }
  assert (Hp: forall v,
             vvalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) v ->
             reachable_through_set (remove_nth_gen_ve g2 gen)
                                   (filter_sum_right roots2) (vmap v)). {
    intros. destruct (reset_is_sound _ gen H0) as [? [? ?]].
    simpl in H14. destruct H14. unfold reachable_through_set in H18 |-* .
    destruct H18 as [s [? ?]].
    assert (forall x, reachable g1 s x ->
                      reachable_through_set g1 (filter_sum_right roots1) x) by
        (intros; exists s; split; assumption).
    rewrite <- filter_sum_right_In_iff in H18.
    apply (in_map (root_map vmap)) in H18. rewrite <- H5 in H18.
    simpl in H18. apply filter_sum_right_In_iff in H18. exists (vmap s).
    split; auto. unfold reachable, reachable_by in H19. destruct H19 as [p ?].
    assert (forall e, In e (snd p) -> evalid (reachable_sub_labeledgraph
                                                g1 (filter_sum_right roots1)) e). {
      intros. simpl. split.
      - destruct H19 as [? [? ?]]. destruct p. eapply valid_path_evalid; eauto.
      - destruct (reachable_path_edge_in _ _ _ _ H19 _ H21).
        apply H20 in H22. apply H20 in H23. split; assumption. }
    destruct H19 as [[? ?] [? ?]]. unfold reachable, reachable_by.
    destruct p. simpl in H19. subst v0. simpl snd in *.
    assert (forall e, In e l -> vmap (src g1 e) = src g2 (emap e) /\
                                vmap (dst g1 e) = dst g2 (emap e)). {
      intros. split; [apply Hs | apply Hd]; auto. apply H21 in H19. simpl in H19.
      destruct H19. assumption. } clear H21. exists (vmap s, map emap l).
    assert (Hvp: valid_path (remove_nth_gen_ve g2 gen) (vmap s, map emap l)). {
      clear H18 H22 H24. revert s H19 H20 H23. induction l; intros.
      - simpl in *. apply Hv. split; auto. apply H20, reachable_refl; auto.
      - simpl map. rewrite valid_path_cons_iff in *. destruct H23 as [? [? ?]].
        rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged.
        assert (In a (a :: l)) by (left; reflexivity). apply H19 in H23.
        destruct H23. rewrite H18, H23, <- H24. split; auto. split.
        + red. red in H15, H16, H17.
          rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged, <- H23, <- H24.
          destruct H21 as [? [? ?]]. subst s.
          assert (reachable g1 (src g1 a) (src g1 a)) by
              (apply reachable_refl; auto).
          assert (reachable g1 (src g1 a) (dst g1 a)). {
            apply step_reachable with (dst g1 a); auto.
            2: apply reachable_refl; auto. exists a; auto. }
          split; [|split; apply Hv]; [apply He | | ]; simpl; split; auto.
        + apply IHl; auto. 1: intros; apply H19; right; assumption.
          intros. apply H20. apply step_reachable with (dst g1 a); auto.
          2: destruct H21 as [_ [? _]]; subst s; assumption. exists a; auto.
          destruct H21; assumption. } split; split; auto.
    - destruct l. 1: simpl in H22 |-* ; rewrite H22; reflexivity.
      assert (e :: l <> nil) by (intro HS; inversion HS).
      apply exists_last in H21. destruct H21 as [l' [a ?]]. rewrite e0 in *.
      rewrite map_app. simpl map. rewrite pfoot_last in H22 |-* .
      rewrite remove_ve_dst_unchanged. assert (In a (l' +:: a)) by
          (rewrite in_app_iff; right; left; reflexivity). apply H19 in H21.
      destruct H21. rewrite <- H22, H25. reflexivity.
    - rewrite path_prop_equiv; auto. }
  assert (Nv: forall x, gen <> vgeneration x -> InEither x vpl ->
                        exists k v, In (k, v) vpl /\ x = v /\ list_bi_map vpl x = k). {
    intros. apply (list_bi_map_In vpl x) in H15. destruct H15 as [k [v [? ?]]].
    exists k, v. destruct H16; auto. destruct H16. subst x. rewrite <- H12 in H15.
    apply in_combine_l in H15. rewrite <- H8 in H15. destruct H15 as [_ ?].
    exfalso. apply H14. subst gen. reflexivity. }
  assert (Hv': forall v, vvalid (remove_nth_gen_ve g2 gen) v -> vvalid g1 (vmap v)). {
    intros. destruct (reset_is_sound _ gen H0) as [? [? ?]].
    red in H15. rewrite H15 in H14. rewrite graph_has_v_reset in H14.
    destruct H14. destruct H0 as [? [? ?]]. red in H0. rewrite <- H0 in H14.
    subst vmap. destruct (InEither_dec v vpl).
    -- specialize (Nv _ H18 i). destruct Nv as [v1 [v2 [? [? ?]]]].
       subst v. rewrite H23. rewrite <- H12 in H21. apply in_combine_l in H21.
       rewrite <- H8 in H21. destruct H21.
       apply reachable_through_set_foot_valid in H21. assumption.
    -- rewrite list_bi_map_not_In; auto.
       destruct (vvalid_lcm _ v (proj1 H1)); auto. exfalso. apply n. red.
       rewrite Heqp, in_app_iff. right. rewrite H10. split; assumption. }
  exists vmap, vmap, emap, emap. split; auto. constructor; intros.
  - constructor; intros.
    + subst. apply bijective_list_bi_map; assumption.
    + subst. apply bijective_list_bi_map; assumption.
    + simpl. split; [apply Hv | apply Hp]; assumption.
    + simpl. split. 1: apply Hv'; destruct H14; assumption. admit.
    + simpl. split. 1: apply He; assumption.
      rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged, <- Hd, <- Hs; auto.
      2: destruct H14; auto. destruct H14 as [? [? ?]].
      split; apply Hp; simpl; split; auto;
        eapply reachable_through_set_foot_valid; eauto.
    + simpl. split.
      * simpl in H14. destruct H14. destruct (reset_is_sound _ gen H0) as [? [? ?]].
        red in H17. rewrite H17 in H14. rewrite graph_has_e_reset in H14. destruct H14.
        destruct H14. rewrite Heqemap. destruct (InEither_dec (fst e') vpl).
        -- unfold egeneration in H19. specialize (Nv _ H19 i).
           destruct Nv as [k [v [? [? ?]]]]; subst v. destruct (H6 _ _ H21) as [? _].
           eapply gepl_value in H22; eauto. destruct H1 as [? [? ?]]. red in H24.
           destruct (DoubleNoDup_list_bi_map _ _ _ Hn H22) as [_ ?].
           rewrite H26, H24. split; simpl.
           ++ rewrite <- H12 in H21. apply in_combine_l in H21. rewrite <- H8 in H21.
              destruct H21. apply reachable_through_set_foot_valid in H21.
              red in H1. rewrite <- H1. assumption.
           ++ rewrite get_edges_In. rewrite get_edges_inv in H20.
              destruct H20 as [idx [? ?]]. rewrite H20 in *. simpl in *.
              destruct (H6 _ _ H21) as [? _]. apply vlabel_get_edges_snd in H28.
              rewrite H28. assumption.
        -- destruct H1 as [? [? ?]]. destruct H0 as [? _]. red in H0.
           rewrite <- H0 in H14. destruct (vvalid_lcm _ (fst e') H1).
           2: { exfalso. apply n. red. rewrite Heqp, in_app_iff. right.
                rewrite H10. split; assumption. } rewrite list_bi_map_not_In.
           ++ red in H21. rewrite H21. split; simpl.
              ** red in H1. rewrite <- H1. auto.
              ** rewrite get_edges_inv in H20 |-* . destruct H20 as [idx [? ?]].
                 exists idx. split; auto. destruct H as [_ [? _]].
                 rewrite (vlabel_get_edges_snd _ (fst e') _ g2); auto.
           ++ intro; apply n; apply gepl_InEither in H24; simpl in H24; assumption.
      * admit.
    + simpl. rewrite remove_ve_src_unchanged. destruct H14 as [? _]. apply Hs. auto.
    + simpl. rewrite remove_ve_dst_unchanged. apply Hd; auto.
  - simpl in H14. destruct H14. simpl. rewrite remove_ve_vlabel_unchanged.
    subst vmap. destruct (InEither_dec v vpl).
    + specialize (H13 _ H14 i). destruct H13 as [v1 [v2 [? [? ?]]]].
      specialize (H6 _ _ H13). subst v. rewrite H17. destruct H6; auto.
    + rewrite list_bi_map_not_In; auto. destruct H as [_ [? _]]. apply H; auto.
  - simpl. destruct (elabel g1 e).
    destruct (elabel (remove_nth_gen_ve g2 gen) (emap e)). reflexivity.
Abort.

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
