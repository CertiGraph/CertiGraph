Require Import Stdlib.ZArith.ZArith.
Require Export Stdlib.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.msl.log_normalize.
Require Import VST.zlist.sublist.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.graph_isomorphism.
Require Import CertiGraph.graph.reachable_ind.
Require Import CertiGraph.CertiGC.GCGraph.
Import ListNotations.

#[local] Open Scope Z_scope.

#[local] Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertex_valid (g: LGraph): Prop := forall v, vvalid g v <-> graph_has_v g v.

Definition edge_valid (g: LGraph): Prop := forall e, evalid g e <-> graph_has_e g e.

Definition src_edge (g: PreGraph VType EType): Prop := forall e, src g e = fst e.

Definition edge_label_same (g: LGraph): Prop := forall e, elabel g e = snd e.

Definition sound_gc_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ edge_label_same g.

(** Reset is sound *)

#[local] Lemma fold_left_remove_edge_vvalid: forall (g: PreGraph VType EType) l v,
    vvalid (fold_left pregraph_remove_edge l g) v <-> vvalid g v.
Proof. now intros; revert g; induction l; [|intros; simpl; rewrite IHl]. Qed.

#[local] Lemma lrvae_vvalid: forall g v1 v2,
    vvalid (lgraph_remove_vertex_and_edges g v1) v2 <-> vvalid g v2 /\ v1 <> v2.
Proof.
  intros. simpl. unfold pregraph_remove_vertex_and_edges.
  rewrite fold_left_remove_edge_vvalid, remove_vertex_vvalid. intuition.
Qed.

#[local] Lemma fold_left_lrvae_vvalid: forall g l v,
    vvalid (fold_left lgraph_remove_vertex_and_edges l g) v <->
    vvalid g v /\ ~ In v l.
Proof.
  intros; revert g v; induction l; intros; simpl; [|rewrite IHl, lrvae_vvalid]; intuition.
Qed.

#[local] Lemma vertex_valid_reset: forall g gen,
    vertex_valid g -> vertex_valid (reset_graph gen g).
Proof.
  intros. unfold vertex_valid in *. intros. simpl. rewrite graph_has_v_reset.
  unfold remove_nth_gen_ve. rewrite fold_left_lrvae_vvalid. rewrite H. intuition; destruct H2.
  - destruct v as [vgen vidx]. simpl in *. subst vgen.
    change (gen, vidx) with ((fun idx : nat => (gen, idx)) vidx). apply in_map.
    rewrite nat_inc_list_In_iff. destruct H1. now red in H1.   - apply list_in_map_inv in H0. destruct H0 as [? [? _]]; now subst v.
Qed.

#[local] Lemma remove_ve_src_unchanged: forall g gen e,
    src (remove_nth_gen_ve g gen) e = src g e.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g e. induction l; intros; simpl; [reflexivity|]. rewrite IHl.
  clear. simpl. unfold pregraph_remove_vertex_and_edges.
  transitivity (src (pregraph_remove_vertex g a) e). 2: reflexivity.
  remember (pregraph_remove_vertex g a) as g'. remember (get_edges g a) as l.
  clear a g Heqg' Heql. rename g' into g. revert g e.
  now induction l; intros; simpl; [|rewrite IHl].
Qed.

#[local] Lemma src_edge_reset: forall (g: LGraph) gen,
    src_edge g -> src_edge (reset_graph gen g).
Proof.
  intros. unfold src_edge in *. intros.
  simpl. rewrite remove_ve_src_unchanged. apply H.
Qed.

#[local] Lemma fold_left_remove_edge_evalid: forall (g: PreGraph VType EType) l e,
    evalid (fold_left pregraph_remove_edge l g) e <-> evalid g e /\ ~ In e l.
Proof.
  intros; revert g; induction l; intros; simpl; [|rewrite IHl, remove_edge_evalid]; intuition.
Qed.

#[local] Lemma lrvae_evalid: forall g v e,
    evalid (lgraph_remove_vertex_and_edges g v) e <->
    evalid g e /\ ~ In e (get_edges g v).
Proof.
  intros. simpl. unfold pregraph_remove_vertex_and_edges.
  rewrite fold_left_remove_edge_evalid. intuition.
Qed.

#[local] Lemma fold_left_lrvae_evalid: forall g l e,
    evalid (fold_left lgraph_remove_vertex_and_edges l g) e <->
    evalid g e /\ forall v, In v l -> ~ In e (get_edges g v).
Proof.
  intros. revert g e. induction l; intros; simpl; [|rewrite IHl, lrvae_evalid]; intuition.
  - subst. contradiction.
  - specialize (H1 _ H4). now apply H1.
  - apply (H1 a); intuition.
  - apply (H1 v); intuition.
Qed.

#[local] Lemma edge_valid_reset: forall g gen, edge_valid g -> edge_valid (reset_graph gen g).
Proof.
  intros. unfold edge_valid in *. intros. rewrite graph_has_e_reset. simpl.
  unfold remove_nth_gen_ve. rewrite fold_left_lrvae_evalid, H. intuition.
  - destruct e. unfold egeneration in H0. simpl in H0. apply (H2 v).
    2: now destruct H1.
    destruct v as [vgen vidx]. simpl in *. subst vgen.
    change (gen, vidx) with ((fun idx : nat => (gen, idx)) vidx). apply in_map.
    rewrite nat_inc_list_In_iff; now destruct H1 as [[_ ?] _].
  - destruct H2. apply get_edges_fst in H3. destruct e. simpl in *. subst v0.
    unfold egeneration. simpl. apply list_in_map_inv in H0.
    destruct H0 as [x [? _]]; now subst v.
Qed.

#[local] Lemma edge_label_same_reset: forall g gen,
    edge_label_same g -> edge_label_same (reset_graph gen g).
Proof.
  unfold edge_label_same. intros g gen He e. simpl.
  rewrite remove_ve_elabel_unchanged. apply He.
Qed.

Lemma reset_sound: forall (g: LGraph) gen,
    sound_gc_graph g -> sound_gc_graph (reset_graph gen g).
Proof.
  intros. destruct H as [? [? [? ?]]].
  now split; [|split; [|split]];
    [apply vertex_valid_reset | apply edge_valid_reset |
      apply src_edge_reset | apply edge_label_same_reset ].
Qed.

(** Quasi-Isomorphism to Full-Isomorphism *)

Definition exterior_map (vmap: VType -> VType) (r: exterior_t): exterior_t :=
  match r with
  | ExteriorUnboxed z => ExteriorUnboxed z
  | ExteriorOutlier p => ExteriorOutlier p
  | ExteriorVertex r => ExteriorVertex (vmap r)
  end.

#[local] Lemma bijective_exterior_map: forall vmap1 vmap2,
    bijective vmap1 vmap2 -> bijective (exterior_map vmap1) (exterior_map vmap2).
Proof.
  intros. destruct H. split; intros.
  - now destruct x, y; inversion H; [| |apply injective in H1; subst].
  - now destruct x; simpl; [| | rewrite surjective].
Qed.

Definition gc_graph_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t): Prop :=
  let vertices1 := filter_proj exterior_proj_vertex roots1 in
  let vertices2 := filter_proj exterior_proj_vertex roots2 in
  let sub_g1 := reachable_sub_labeledgraph g1 vertices1 in
  let sub_g2 := reachable_sub_labeledgraph g2 vertices2 in
  exists vmap12 vmap21 emap12 emap21,
    roots2 = map (exterior_map vmap12) roots1 /\
    label_preserving_graph_isomorphism_explicit
      sub_g1 sub_g2 vmap12 vmap21 emap12 emap21.

Lemma gc_graph_iso_refl: forall g roots, gc_graph_iso g roots g roots.
Proof.
  intros. red. exists id, id, id, id. split. 2: apply lp_graph_iso_exp_refl.
  clear. induction roots; simpl; auto. rewrite <- IHroots. f_equal. destruct a; auto.
Qed.

#[local] Lemma map_exterior_map_bijective:
  forall (roots1 roots2 : roots_t) (vmap12 vmap21 : VType -> VType),
    roots2 = map (exterior_map vmap12) roots1 ->
    bijective vmap12 vmap21 -> roots1 = map (exterior_map vmap21) roots2.
Proof.
  intros roots1 roots2 vmap12 vmap21 H H0.
  apply bijective_exterior_map, bijective_map, bijective_sym in H0. destruct H0.
  now rewrite H, surjective.
Qed.

Lemma gc_graph_iso_trans: forall g2 roots2 g1 roots1 g3 roots3,
    gc_graph_iso g1 roots1 g2 roots2 -> gc_graph_iso g2 roots2 g3 roots3 ->
    gc_graph_iso g1 roots1 g3 roots3.
Proof.
  intros. unfold gc_graph_iso in *. destruct H as [v12 [v21 [e12 [e21 [? ?]]]]].
  destruct H0 as [v23 [v32 [e23 [e32 [? ?]]]]].
  exists (compose v23 v12), (compose v21 v32), (compose e23 e12), (compose e21 e32).
  split; [|eapply lp_graph_iso_exp_trans; eauto].
  rewrite H0. rewrite H. rewrite map_map. clear. induction roots1; simpl; auto.
  rewrite IHroots1. f_equal. now destruct a.
Qed.

Definition gen_single_edge_pair_list
           (g: LGraph) (p: VType * VType): list (EType * EType) :=
  let (k, v) := p in let el1 := get_edges g k in
                     let el2 := map (fun e => (v, snd e)) el1 in combine el1 el2.

Definition gen_edge_pair_list
           (g: LGraph) (l: list (VType * VType)): list (EType * EType) :=
  concat (map (gen_single_edge_pair_list g) l).

#[local] Lemma get_edges_snd_NoDup: forall g v, NoDup (map snd (get_edges g v)).
Proof.
  intros. unfold get_edges. unfold make_fields.
  remember (raw_fields (vlabel g v)). remember O.
  clear Heql Heqn g. revert n. induction l; intros; simpl; [constructor|].
  destruct a; rewrite filter_proj_cons; simpl; [| apply IHl..].
  rewrite NoDup_cons_iff. split; trivial. intro.
  apply list_in_map_inv in H. destruct H as [x [? ?]].
  rewrite <- (filter_proj_In_iff field_proj_edge_spec) in H0.
  apply In_nth with (d := field_t_inhabitant) in H0. destruct H0 as [p [? ?]].
  apply make_fields'_edge_depends_on_index in H1; [subst x; simpl in H; lia|].
  rewrite make_fields'_eq_length in H0. rewrite Zlength_correct. split; [lia|].
  apply Nat2Z.inj_lt; assumption.
Qed.

#[local] Lemma get_edges_map_map: forall g v,
    get_edges g v = map (fun idx => (v, idx)) (map snd (get_edges g v)).
Proof.
  intros. rewrite map_map. unfold get_edges, make_fields.
  remember (raw_fields (vlabel g v)). remember O. clear Heql Heqn. revert n.
  induction l; intros; simpl; auto; destruct a; rewrite filter_proj_cons;
    simpl; rewrite <- IHl; auto.
Qed.

#[local] Lemma get_edges_NoDup: forall g v, NoDup (get_edges g v).
Proof.
  intros. rewrite get_edges_map_map, <- combine_repeat_eq_map;
            apply NoDup_combine_r, get_edges_snd_NoDup.
Qed.

#[local] Lemma gsepl_DoubleNoDup: forall (v1 v2 : VType) (g : LGraph),
    v1 <> v2 -> DoubleNoDup (gen_single_edge_pair_list g (v1, v2)).
Proof.
  intros. simpl. pose proof (get_edges_NoDup g v1). remember (get_edges g v1).
  assert (forall e, In e l -> fst e = v1) by
      (intros; subst l; apply get_edges_fst in H1; assumption). clear Heql g.
  induction l; simpl; [constructor|]. rewrite DoubleNoDup_cons_iff.
  destruct a as [? idx]. simpl. assert (v = v1) by
      (change v with (fst (v, idx)); apply H1; left; reflexivity). subst v.
  split; [|split; [|split]].
  - apply IHl. 1: apply NoDup_cons_1 in H0; assumption. intros. apply H1.
    simpl. now right.
  - intro. inversion H2. contradiction.
  - unfold InEither. rewrite combine_split by (rewrite length_map; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + apply NoDup_cons_2 in H0. contradiction.
    + rewrite in_map_iff in H2. destruct H2 as [x [? ?]]. inversion H2. auto.
  - unfold InEither. rewrite combine_split by (rewrite length_map; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + specialize (H1 (v2, idx)). simpl in H1. apply H; now rewrite H1; [|right].
    + rewrite in_map_iff in H2. destruct H2 as [[? ?] [? ?]]. simpl in *.
      inversion H2. subst n. clear H2. assert (v = v1) by
          (change v with (fst (v, idx)); apply H1; right; assumption). subst.
      apply NoDup_cons_2 in H0. contradiction.
Qed.

#[local] Lemma gsepl_InEither: forall x g a,
    InEither x (gen_single_edge_pair_list g a) -> IsEither (fst x) a.
Proof.
  intros. destruct a as [v1 v2]. red. simpl.
  unfold gen_single_edge_pair_list in H. remember (get_edges g v1).
  assert (forall e, In e l -> fst e = v1) by
      (intros; subst l; apply get_edges_fst in H0; assumption). clear Heql g.
  induction l; simpl in *; [inversion H|].
  rewrite InEither_cons_iff in H.
  destruct a as [v idx]. simpl in *. assert (v = v1) by
      (change v with (fst (v, idx)); apply H0; left; reflexivity). subst v. destruct H.
  - red in H. simpl in H. destruct H; subst; simpl; intuition.
  - apply IHl; auto.
Qed.

#[local] Lemma gepl_InEither: forall x g l,
    InEither x (gen_edge_pair_list g l) -> InEither (fst x) l.
Proof.
  intros. induction l; simpl in *; unfold gen_edge_pair_list in H; simpl in H.
  1: inversion H. fold (gen_edge_pair_list g l) in H. rewrite InEither_app_iff in H.
  rewrite InEither_cons_iff.
  destruct H; [left; eapply gsepl_InEither; eauto | right; apply IHl; assumption].
Qed.

#[local] Lemma gepl_DoubleNoDup:
  forall g l, DoubleNoDup l -> DoubleNoDup (gen_edge_pair_list g l).
Proof.
  intros g l. revert g. induction l; intros.
  1: unfold gen_edge_pair_list; simpl; constructor.
  unfold gen_edge_pair_list. simpl. fold (gen_edge_pair_list g l).
  destruct a as [v1 v2]. apply DoubleNoDup_cons_iff in H. destruct H as [? [? [? ?]]].
  rewrite DoubleNoDup_app_iff.
  split3; [apply gsepl_DoubleNoDup | apply IHl|]; trivial.
  intros. apply gsepl_InEither in H3. intro. apply gepl_InEither in H4. red in H3.
  simpl in H3. destruct H3; rewrite H3 in H4; contradiction.
Qed.

#[local] Lemma get_edges_inv: forall g v e,
    In e (get_edges g v) <->
    exists idx, e = (v, idx) /\ In idx (map snd (get_edges g v)).
Proof.
  intros. destruct e as [gen idx]. split; intros.
  - pose proof H. apply get_edges_fst in H0. simpl in H0. subst gen. exists idx.
    rewrite get_edges_In in H. split; auto.
  - destruct H as [? [? ?]]. inversion H. subst. rewrite get_edges_In. assumption.
Qed.

#[local] Lemma In_snd_get_edges: forall g v idx,
    In idx (map snd (get_edges g v)) -> In (v, idx) (get_edges g v).
Proof. intros. rewrite get_edges_inv. exists idx. split; auto. Qed.

#[local] Lemma vlabel_get_edges_snd: forall v1 v2 (g1 g2: LGraph),
    vlabel g1 v1 = vlabel g2 v2 ->
    map snd (get_edges g1 v1) = map snd (get_edges g2 v2).
Proof.
  intros. unfold get_edges. unfold make_fields. rewrite H.
  remember (raw_fields (vlabel g2 v2)). remember O.
  clear H Heql Heqn.
  revert n. induction l; intros; simpl; auto.
  now destruct a; rewrite filter_proj_cons; simpl; rewrite IHl.
Qed.

#[local] Lemma gsepl_key: forall e g v,
    In e (get_edges g (fst e)) ->
    In (e, (v, snd e)) (gen_single_edge_pair_list g (fst e, v)).
Proof.
  intros. simpl. remember (get_edges g (fst e)). clear Heql.
  induction l; simpl in *; auto. now destruct H; [left; subst | right; apply IHl].
Qed.

#[local] Lemma gsepl_value: forall (e: EType) k (g1 g2: LGraph),
    In e (get_edges g2 (fst e)) -> vlabel g1 k = vlabel g2 (fst e) ->
    In (k, snd e, e) (gen_single_edge_pair_list g1 (k, fst e)).
Proof.
  intros. destruct e as [gen idx]. simpl in *. rewrite get_edges_In in H.
  rewrite get_edges_map_map. apply vlabel_get_edges_snd in H0. rewrite H0.
  remember (map snd (get_edges g2 gen)). rewrite map_map. simpl. clear -H.
  induction l; simpl; [inversion H |].
  now destruct H; [left; subst a | right; apply IHl].
Qed.

#[local] Lemma gepl_key: forall (g : LGraph) (vpl : list (VType * VType)) (e : EType) v,
    In e (get_edges g (fst e)) -> In (fst e, v) vpl ->
    In (e, (v, snd e)) (gen_edge_pair_list g vpl).
Proof.
  intros. induction vpl; [inversion H0|]. unfold gen_edge_pair_list. simpl.
  fold (gen_edge_pair_list g vpl). simpl in H0. rewrite in_app_iff.
  destruct H0; [left; subst a; apply gsepl_key | right; apply IHvpl]; auto.
Qed.

#[local] Lemma gepl_value: forall (e: EType) k (g1 g2: LGraph) vpl,
    In e (get_edges g2 (fst e)) -> In (k, fst e) vpl ->
    vlabel g1 k = vlabel g2 (fst e) -> In (k, snd e, e) (gen_edge_pair_list g1 vpl).
Proof.
  intros. induction vpl; [inversion H0|]. unfold gen_edge_pair_list. simpl.
  fold (gen_edge_pair_list g1 vpl). simpl in H0. rewrite in_app_iff.
  now destruct H0; [left; subst a; eapply gsepl_value; eauto| right; apply IHvpl].
Qed.

Definition GenNoDup (l: list VType) (gen: nat): Prop :=
  NoDup l /\ forall v, In v l -> vgeneration v = gen.

Definition PairGenNoDup (l: list (VType * VType)) (from to: nat): Prop :=
  let (left_l, right_l) := split l in GenNoDup left_l from /\ GenNoDup right_l to.

#[local] Lemma PairGenNoDup_DoubleNoDup: forall l from to,
    from <> to -> PairGenNoDup l from to -> DoubleNoDup l.
Proof.
  intros. red in H0 |-* . destruct (split l) as [l1 l2]. destruct H0 as [[? ?] [? ?]].
  rewrite NoDup_app_iff. do 2 (split; auto). repeat intro. apply H1 in H4.
  apply H3 in H5. rewrite H4 in H5. contradiction.
Qed.

Definition from_gen_quasi_spec
           (g: LGraph) (roots: roots_t) (l: list VType) gen: Prop :=
  NoDup l /\ forall v,
    (reachable_through_set g (filter_proj exterior_proj_vertex roots) v /\ vgeneration v = gen) <->
    In v l.

Definition to_gen_spec (g1 g2: LGraph) (l: list VType) gen: Prop :=
  NoDup l /\ (forall v, In v l <-> vvalid g2 v /\ ~ vvalid g1 v) /\
  forall v, In v l -> vgeneration v = gen.

Definition roots_map (l: list (VType * VType)): roots_t -> roots_t :=
  map (exterior_map (list_bi_map l)).

Definition remset_ready_roots (l: list (VType * VType)): roots_t :=
  roots_map l (map ExteriorVertex (map fst l)).

Definition old_nonfrom_edges_mapped
           (g1 g2: LGraph) (l: list (VType * VType)) (from: nat): Prop :=
  forall e,
    evalid g1 e ->
    vgeneration (fst e) <> from ->
    evalid g2 e /\
    src g2 e = src g1 e /\
    dst g2 e = list_bi_map l (dst g1 e).

Definition old_vertices_valid (g1 g2: LGraph): Prop :=
  forall v, vvalid g1 v -> vvalid g2 v.

Definition unmarked_from_edges_unchanged
           (g1 g2: LGraph) (from: nat): Prop :=
  forall e,
    evalid g1 e ->
    vgeneration (fst e) = from ->
    raw_mark (vlabel g2 (fst e)) = false ->
    evalid g2 e /\
    src g2 e = src g1 e /\
    dst g2 e = dst g1 e.

Definition remset_partial_graph
           (g1 g2: LGraph) (l: list (VType * VType)) (from: nat): Prop :=
  old_vertices_valid g1 g2 /\
  old_nonfrom_edges_mapped g1 g2 l from /\
  unmarked_from_edges_unchanged g1 g2 from.

Definition remset_item_records_edge
           (item: remset_space_item) (e: EType): Prop :=
  match item with
  | RemSetInterior (InteriorVertexPos v pos) =>
      v = fst e /\ pos = Z.of_nat (snd e)
  | RemSetExterior _ => False
  end.

Definition remset_space_records_edge
           (pending: remset_space) (e: EType): Prop :=
  exists item, In item pending /\ remset_item_records_edge item e.

Definition old_nonfrom_edges_to_are_pending
           (g: LGraph) (v: VType) (from: nat)
           (pending: remset_space): Prop :=
  forall e,
    evalid g e ->
    vgeneration (fst e) <> from ->
    dst g e = v ->
    remset_space_records_edge pending e.

Definition unmarked_old_nonfrom_edges_to_are_pending
           (base current: LGraph) (from: nat)
           (pending: remset_space): Prop :=
  forall v,
    vgeneration v = from ->
    raw_mark (vlabel current v) = false ->
    old_nonfrom_edges_to_are_pending base v from pending.

Definition old_nonfrom_edges_mapped_pending
           (g1 g2: LGraph) (l: list (VType * VType))
           (from: nat) (pending: remset_space): Prop :=
  forall e,
    evalid g1 e ->
    vgeneration (fst e) <> from ->
    (remset_space_records_edge pending e /\
     evalid g2 e /\
     src g2 e = src g1 e /\
     dst g2 e = dst g1 e /\
     vgeneration (dst g1 e) = from) \/
    (evalid g2 e /\
     src g2 e = src g1 e /\
     dst g2 e = list_bi_map l (dst g1 e)).

Definition remset_partial_graph_pending
           (g1 g2: LGraph) (l: list (VType * VType))
           (from: nat) (pending: remset_space): Prop :=
  old_vertices_valid g1 g2 /\
  old_nonfrom_edges_mapped_pending g1 g2 l from pending /\
  unmarked_from_edges_unchanged g1 g2 from.

Definition gc_graph_remset_quasi_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t) (from to: nat): Prop :=
  exists (l: list (VType * VType)),
    roots2 = roots_map l roots1 /\
    (forall v1 v2,
        In (v1, v2) l ->
        vlabel g1 v1 = vlabel g2 v2 /\
        forall idx, In idx (map snd (get_edges g1 v1)) ->
                    (dst g2 (v2, idx) = dst g1 (v1, idx) \/
                     dst g2 (v2, idx) = list_bi_map l (dst g1 (v1, idx)))) /\
    let (from_l, to_l) := split l in
    from_gen_quasi_spec g1 roots1 from_l from /\ to_gen_spec g1 g2 to_l to /\
    (forall v, vvalid g1 v -> ~ In v from_l -> vlabel g1 v = vlabel g2 v) /\
    old_vertices_valid g1 g2 /\
    old_nonfrom_edges_mapped g1 g2 l from.

Definition gen_has_index_dec (g: LGraph) (gen idx: nat):
  {gen_has_index g gen idx} + {~ gen_has_index g gen idx}.
Proof.
  unfold gen_has_index.
  destruct (lt_dec idx (number_of_vertices (nth_gen g gen))); [left | right]; auto.
Defined.

#[local] Lemma graph_has_v_dec: forall (g: LGraph) (v: VType),
    {graph_has_v g v} + {~ graph_has_v g v}.
Proof.
  intros. destruct v as [vgen vidx]. destruct (graph_has_gen_dec g vgen).
  - destruct (gen_has_index_dec g vgen vidx). 1: left; red; simpl; split; auto.
    right; intro; apply n; destruct H; auto.
  - right; intro; apply n; destruct H; auto.
Defined.

#[local] Lemma vvalid_lcm: forall g v, vertex_valid g -> vvalid g v \/ ~ vvalid g v.
Proof. intros. red in H. rewrite H. destruct (graph_has_v_dec g v); auto. Qed.

Lemma reachable_map_reachable_sub_edges:
  forall (g_src: LGraph) (g_dst: PreGraph VType EType)
         roots_src (vmap: VType -> VType) (emap: EType -> EType) s v p,
    (forall x, reachable g_src s x -> reachable_through_set g_src roots_src x) ->
    g_src |= (s, p) is s ~o~> v satisfying (fun _ => True) ->
    vvalid g_dst (vmap s) ->
    (forall e, evalid (reachable_sub_labeledgraph g_src roots_src) e ->
       vmap (src g_src e) = src g_dst (emap e)) ->
    (forall e, evalid (reachable_sub_labeledgraph g_src roots_src) e ->
       vmap (dst g_src e) = dst g_dst (emap e)) ->
    (forall e, evalid (reachable_sub_labeledgraph g_src roots_src) e ->
       evalid g_dst (emap e)) ->
    (forall x, vvalid (reachable_sub_labeledgraph g_src roots_src) x ->
       vvalid g_dst (vmap x)) ->
    reachable g_dst (vmap s) (vmap v).
Proof.
  intros g_src g_dst roots_src vmap emap s v p Hthrough Hpath Hsvalid
         Hsrc_map Hdst_map He_map Hv_map.
  pose proof Hpath as Hpath_full.
  destruct Hpath as [[_ Hfoot] [Hvalid _]].
  assert (Hmap: forall e, In e p ->
        vmap (src g_src e) = src g_dst (emap e) /\
        vmap (dst g_src e) = dst g_dst (emap e) /\
        strong_evalid g_dst (emap e)). {
    intros e Hin.
    assert (Hsub: evalid (reachable_sub_labeledgraph g_src roots_src) e). {
      simpl. split.
      - eapply valid_path_evalid; eauto.
      - destruct (reachable_path_edge_in _ _ _ _ Hpath_full _ Hin).
        split; apply Hthrough; assumption.
    }
    pose proof (Hsrc_map e Hsub) as Hsrc_eq.
    pose proof (Hdst_map e Hsub) as Hdst_eq.
    split; [exact Hsrc_eq | split; [exact Hdst_eq |]].
    red. rewrite <- Hsrc_eq, <- Hdst_eq. split; [apply He_map; exact Hsub |].
    pose proof (valid_path_strong_evalid _ _ _ _ Hvalid Hin) as
        [_ [Hsrc_valid Hdst_valid]].
    simpl in Hsub. destruct Hsub as [_ [Hsrc_reach Hdst_reach]].
    split; apply Hv_map; simpl; split; assumption.
  }
  assert (Hmapped_valid: valid_path g_dst (vmap s, map emap p)). {
    clear Hfoot Hthrough Hpath_full Hsrc_map Hdst_map He_map Hv_map.
    revert s Hvalid Hsvalid Hmap.
    induction p as [| a p IHp]; intros s Hvalid Hsvalid Hmap.
    - simpl. exact Hsvalid.
    - simpl map. rewrite valid_path_cons_iff in Hvalid |-*.
      destruct Hvalid as [Hhead [Ha_strong Htail]].
      destruct (Hmap a (or_introl eq_refl)) as
          [Ha_src [Ha_dst Ha_mapped_strong]].
      split; [rewrite Hhead; exact Ha_src | split; [exact Ha_mapped_strong |]].
      rewrite <- Ha_dst. apply IHp.
      + exact Htail.
      + destruct Ha_mapped_strong as [_ [_ Ha_dst_valid]].
        rewrite Ha_dst. exact Ha_dst_valid.
      + intros e Hin. apply Hmap. right; exact Hin.
  }
  exists (vmap s, map emap p).
  split.
  - split; [simpl; auto |].
    destruct p as [| e p].
    + simpl in Hfoot |-* . rewrite Hfoot. reflexivity.
    + assert (e :: p <> nil) by (intro HS; inversion HS).
      apply exists_last in H. destruct H as [l' [a Hlast]]. rewrite Hlast in *.
      rewrite map_app. simpl map.
      change (pfoot g_dst (vmap s, map emap l' +:: emap a) = vmap v).
      rewrite pfoot_last in Hfoot |-* .
      assert (Hin_a: In a (l' +:: a)) by
          (rewrite in_app_iff; right; left; reflexivity).
      destruct (Hmap a Hin_a) as [_ [Hdst_eq _]].
      rewrite <- Hdst_eq, Hfoot. reflexivity.
  - split; [exact Hmapped_valid |].
    rewrite path_prop_equiv; auto.
Qed.

Lemma remset_quasi_iso_reset_iso: forall g1 roots1 g2 roots2 from to,
    from <> to -> gc_graph_remset_quasi_iso g1 roots1 g2 roots2 from to ->
    sound_gc_graph g2 -> sound_gc_graph g1 ->
    no_edge2gen g2 from -> no_dangling_dst g1 ->
    gc_graph_iso g1 roots1 (reset_graph from g2) roots2.
Proof.
  intros g1 roots1 g2 roots2 from to Hfr Hq Hsound2 Hsound1 Hnedge2 Hndd1.
  red in Hq. red.
  destruct Hq as [vpl [Hroots [Hcopy Hspec]]]. unfold roots_map in Hroots.
  destruct (split vpl) as [from_l to_l] eqn:Heqp.
  destruct Hspec as [[Hfrom_nd Hfrom] [[Hto_nd [Hto_valid Hto_gen]]
                       [Hlabel [Hvertex_map Hedge_map]]]].
  assert (Hdnd: DoubleNoDup vpl). {
    apply (PairGenNoDup_DoubleNoDup _ from to); [lia|]. red. rewrite Heqp.
    split.
    + split.
      * exact Hfrom_nd.
      * intros v Hv. rewrite <- Hfrom in Hv. destruct Hv as [_ Hgen]. exact Hgen.
    + split.
      * exact Hto_nd.
      * exact Hto_gen.
  }
  assert (Hednd: DoubleNoDup (gen_edge_pair_list g1 vpl)) by
      (apply gepl_DoubleNoDup; auto).
  pose proof (split_combine vpl) as Hsplit_combine.
  rewrite Heqp in Hsplit_combine.
  assert (Hleft_map: forall x, vvalid g1 x -> InEither x vpl ->
                    exists k v, In (k, v) vpl /\ x = k /\ list_bi_map vpl x = v). {
    intros x Hxvalid Hxin. apply (list_bi_map_In vpl x) in Hxin.
    destruct Hxin as [k [v [Hin Hcase]]].
    exists k, v. destruct Hcase as [Hcase | Hcase]; auto.
    destruct Hcase as [Hx Hxv]. subst x.
    erewrite <- Hsplit_combine in Hin; eauto. apply in_combine_r in Hin.
    rewrite Hto_valid in Hin. destruct Hin as [_ Hnot]. contradiction.
  }
  remember (list_bi_map vpl) as vmap.
  remember (list_bi_map (gen_edge_pair_list g1 vpl)) as emap.
  destruct (reset_sound _ from Hsound2) as [Hvv_reset [Hev_reset [Hsrc_reset Hels_reset]]].
  destruct Hsound2 as [Hvv2 [Hev2 [Hsrc2 Hels2]]].
  destruct Hsound1 as [Hvv1 [Hev1 [Hsrc1 Hels1]]].
  unfold vertex_valid, edge_valid, src_edge, edge_label_same in *.
  simpl in Hev_reset, Hsrc_reset, Hels_reset.
  assert (Hs: forall e, evalid g1 e -> vmap (src g1 e) = src g2 (emap e)). {
    intros e He.
    assert (Hge: graph_has_e g1 e) by (apply (proj1 (Hev1 e)); exact He).
    destruct Hge as [Hsrc_has Hfield].
    subst vmap emap. destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - destruct (Hleft_map (fst e)) as [k [v [Hkv [Hfst Hmap]]]].
      + apply (proj2 (Hvv1 _)); exact Hsrc_has.
      + exact Hin.
      + subst k. rewrite Hsrc1. rewrite Hmap.
        pose proof (gepl_key _ _ _ _ Hfield Hkv) as Hedge_in.
        destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hedge_in) as [Hemap _].
        rewrite Hemap. rewrite Hsrc2. reflexivity.
    - rewrite Hsrc1. rewrite !list_bi_map_not_In.
      + rewrite Hsrc2. reflexivity.
      + intro Hedge_in. apply Hnin. apply gepl_InEither in Hedge_in. exact Hedge_in.
      + exact Hnin.
  }
  assert (Hd: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) e
             -> vmap (dst g1 e) = dst g2 (emap e)). {
    intros e Hesub. simpl in Hesub. destruct Hesub as [Hevalid [Hsrc_reach Hdst_reach]].
    assert (Hge: graph_has_e g1 e) by (apply (proj1 (Hev1 e)); exact Hevalid).
    destruct Hge as [Hsrc_has Hfield].
    assert (Hsrc_valid: vvalid g1 (fst e)) by (apply (proj2 (Hvv1 _)); exact Hsrc_has).
    assert (Hdst_not_to: ~ In (dst g1 e) to_l). {
      intro Hin. rewrite Hto_valid in Hin. destruct Hin as [_ Hnot_valid].
      apply reachable_through_set_foot_valid in Hdst_reach. contradiction.
    }
    destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - subst vmap emap.
      destruct (Hleft_map (fst e) Hsrc_valid Hin) as [k [v [Hkv [Hfst Hmap]]]].
      subst k.
      pose proof (gepl_key _ _ _ _ Hfield Hkv) as Hedge_in.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hedge_in) as [Hemap _].
      rewrite Hemap.
      destruct (Hcopy _ _ Hkv) as [Hvlab Hdst_copy].
      rewrite get_edges_inv in Hfield. destruct Hfield as [idx [Heq Hidx]].
      rewrite Heq in *. simpl in *.
      specialize (Hdst_copy _ Hidx). destruct Hdst_copy as [Hdst_copy | Hdst_copy].
      + rewrite Hdst_copy. rewrite list_bi_map_not_In; auto.
        intro Hdst_in. unfold InEither in Hdst_in. rewrite Heqp, in_app_iff in Hdst_in.
        destruct Hdst_in as [Hdst_from | Hdst_to]; [| contradiction].
        rewrite <- Hfrom in Hdst_from. destruct Hdst_from as [_ Hdst_gen].
        assert (Hedge2: graph_has_e g2 (v, idx)). {
          split; simpl.
          - erewrite <- Hsplit_combine in Hkv; eauto. apply in_combine_r in Hkv.
            rewrite Hto_valid in Hkv. destruct Hkv as [Hvvalid _].
            apply (proj1 (Hvv2 _)); exact Hvvalid.
          - apply In_snd_get_edges. apply vlabel_get_edges_snd in Hvlab.
            rewrite <- Hvlab. assumption.
        }
        assert (vgeneration v = to) as Hvgen_to. {
          erewrite <- Hsplit_combine in Hkv; eauto. apply in_combine_r in Hkv.
          apply Hto_gen. exact Hkv.
        }
        destruct v as [vgen vidx]. simpl in Hvgen_to. subst vgen.
        assert (to <> from) by lia.
        specialize (Hnedge2 _ H vidx idx). simpl in Hnedge2.
        specialize (Hnedge2 Hedge2). simpl in Hnedge2.
        apply Hnedge2. replace (dst g2 (to, vidx, idx)) with (dst g1 (fst e, idx)); auto.
      + rewrite Hdst_copy. reflexivity.
    - rewrite Heqemap. rewrite list_bi_map_not_In.
      + assert (Hsrc_not_from: vgeneration (fst e) <> from). {
          intro Hsrc_from. apply Hnin. unfold InEither. rewrite Heqp, in_app_iff. left.
          rewrite <- Hfrom. split.
          - rewrite <- Hsrc1. exact Hsrc_reach.
          - exact Hsrc_from.
        }
        destruct (Hedge_map e Hevalid Hsrc_not_from) as [_ [_ Hdst_map]].
        rewrite Heqvmap. symmetry. exact Hdst_map.
      + intro Hedge_in. apply Hnin. apply gepl_InEither in Hedge_in. exact Hedge_in.
  }
  assert (He: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) e
             -> evalid (remove_nth_gen_ve g2 from) (emap e)). {
    intros e Hesub. rewrite Heqemap. simpl in Hesub.
    destruct Hesub as [Hevalid [Hsrc_reach Hdst_reach]].
    rewrite Hev_reset, graph_has_e_reset.
    assert (Hge: graph_has_e g1 e) by (apply (proj1 (Hev1 e)); exact Hevalid).
    destruct Hge as [Hsrc_has Hfield].
    assert (Hsrc_valid: vvalid g1 (fst e)) by (apply (proj2 (Hvv1 _)); exact Hsrc_has).
    destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - destruct (Hleft_map (fst e) Hsrc_valid Hin) as [k [v [Hkv [Hfst Hmap]]]].
      subst k.
      pose proof (gepl_key _ _ _ _ Hfield Hkv) as Hedge_in.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hedge_in) as [Hemap _].
      rewrite Hemap.
      unfold graph_has_e, egeneration. simpl.
      pose proof Hkv as Hkv0.
      erewrite <- Hsplit_combine in Hkv; eauto. apply in_combine_r in Hkv.
      pose proof Hkv as Hvto. apply Hto_gen in Hvto.
      rewrite Hto_valid in Hkv. destruct Hkv as [Hvvalid _].
      split; [split | lia].
      + apply (proj1 (Hvv2 _)); exact Hvvalid.
      + rewrite get_edges_inv in Hfield. destruct Hfield as [idx [Heq Hidx]].
        rewrite Heq in *. simpl in *.
        destruct (Hcopy _ _ Hkv0) as [Hvlab _].
        apply In_snd_get_edges. apply vlabel_get_edges_snd in Hvlab.
        rewrite <- Hvlab. assumption.
    - rewrite list_bi_map_not_In.
      + assert (Hsrc_not_from: vgeneration (fst e) <> from). {
          intro Hsrc_from. apply Hnin. unfold InEither. rewrite Heqp, in_app_iff. left.
          rewrite <- Hfrom. split.
          - rewrite <- Hsrc1. exact Hsrc_reach.
          - exact Hsrc_from.
        }
        destruct (Hedge_map e Hevalid Hsrc_not_from) as [He2 _].
        split.
        * apply (proj1 (Hev2 _)); exact He2.
        * unfold egeneration. lia.
      + intro Hedge_in. apply Hnin. apply gepl_InEither in Hedge_in. exact Hedge_in.
  }
  assert (Hv: forall x,
             vvalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) x
             -> vvalid (remove_nth_gen_ve g2 from) (vmap x)). {
    intros x Hx. simpl in Hx. destruct Hx as [Hxvalid Hxreach].
    rewrite Hvv_reset. rewrite graph_has_v_reset.
    destruct (InEither_dec x vpl) as [Hxin | Hxnotin].
    - destruct (Hleft_map x Hxvalid Hxin) as [k [v [Hkv [Hxk Hmap]]]].
      subst x. rewrite Hmap.
      erewrite <- Hsplit_combine in Hkv; eauto. apply in_combine_r in Hkv.
      pose proof Hkv as Hvto. apply Hto_gen in Hvto.
      rewrite Hto_valid in Hkv. destruct Hkv as [Hvvalid _].
      apply (proj1 (Hvv2 _)) in Hvvalid. split; auto. lia.
    - rewrite Heqvmap. rewrite list_bi_map_not_In; auto.
      assert (Hgen_ne: vgeneration x <> from). {
        intro Hxfrom. apply Hxnotin. unfold InEither. rewrite Heqp, in_app_iff. left.
        rewrite <- Hfrom. split; assumption.
      }
      assert (Hv2: vvalid g2 x) by (apply Hvertex_map; assumption).
      split.
      + apply (proj1 (Hvv2 _)); exact Hv2.
      + lia.
  }
  assert (Hp: forall v,
             vvalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) v
             -> reachable_through_set (remove_nth_gen_ve g2 from)
                 (filter_proj exterior_proj_vertex roots2) (vmap v)). {
    intros v Hvsub. simpl in Hvsub. destruct Hvsub as [Hvvalid Hvreach].
    unfold reachable_through_set in Hvreach |-* . destruct Hvreach as [s [Hsroot Hreach]].
    assert (Hthrough: forall x, reachable g1 s x ->
                      reachable_through_set g1 (filter_proj exterior_proj_vertex roots1) x) by
        (intros; exists s; split; assumption).
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hsroot.
    apply (in_map (exterior_map vmap)) in Hsroot. rewrite <- Hroots in Hsroot.
    simpl in Hsroot. apply (filter_proj_In_iff exterior_proj_vertex_spec) in Hsroot.
    exists (vmap s). split; auto.
    unfold reachable, reachable_by in Hreach. destruct Hreach as [p Hpvalid].
    destruct Hpvalid as [[Hphead Hptail] [Hpprop Hplast]]. unfold reachable, reachable_by.
    destruct p as [phead pedges]. simpl in Hphead. subst phead. simpl snd in *.
    apply reachable_map_reachable_sub_edges
      with (g_src := g1) (g_dst := remove_nth_gen_ve g2 from)
           (roots_src := filter_proj exterior_proj_vertex roots1)
           (vmap := vmap) (emap := emap) (p := pedges).
    - exact Hthrough.
    - split; [split | split]; simpl; auto.
    - assert (Hsvalid_g1: vvalid g1 s) by
          (eapply valid_path_valid; [exact Hpprop | left; reflexivity]).
      apply Hv. simpl. split; auto.
      apply Hthrough. apply reachable_refl. exact Hsvalid_g1.
    - intros e Hesub. rewrite remove_ve_src_unchanged.
      apply Hs. simpl in Hesub. destruct Hesub as [Hevalid _]. exact Hevalid.
    - intros e Hesub. rewrite remove_ve_dst_unchanged. apply Hd. exact Hesub.
    - intros e Hesub. apply He. exact Hesub.
    - intros x Hx. apply Hv. exact Hx.
  }
  assert (Nv: forall x, from <> vgeneration x -> InEither x vpl ->
                        exists k v, In (k, v) vpl /\ x = v /\ list_bi_map vpl x = k). {
    intros x Hxgen Hxin. apply (list_bi_map_In vpl x) in Hxin.
    destruct Hxin as [k [v [Hin Hcase]]]. exists k, v.
    destruct Hcase as [Hcase | Hcase]; auto.
    destruct Hcase as [Hx Hxv]. subst x.
    erewrite <- Hsplit_combine in Hin; eauto. apply in_combine_l in Hin.
    rewrite <- Hfrom in Hin. destruct Hin as [_ Hgen]. exfalso. apply Hxgen. auto.
  }
  assert (Hv': forall v, vvalid (remove_nth_gen_ve g2 from) v -> vvalid g1 (vmap v)). {
    intros v Hvreset. rewrite Hvv_reset in Hvreset. rewrite graph_has_v_reset in Hvreset.
    destruct Hvreset as [Hvhas2 Hvgen].
    assert (Hv2: vvalid g2 v) by (apply (proj2 (Hvv2 _)); exact Hvhas2).
    destruct (InEither_dec v vpl) as [Hin | Hnin].
    - specialize (Nv _ Hvgen Hin) as [v1 [v2 [Hpair [Hv_eq Hmap]]]]. subst v.
      rewrite Heqvmap, Hmap. erewrite <- Hsplit_combine in Hpair; eauto.
      apply in_combine_l in Hpair. rewrite <- Hfrom in Hpair.
      destruct Hpair as [Hreach _]. apply reachable_through_set_foot_valid in Hreach. exact Hreach.
    - rewrite Heqvmap, list_bi_map_not_In; auto.
      destruct (vvalid_lcm _ v Hvv1) as [Hv1 | Hnot1]; auto.
      exfalso. apply Hnin. unfold InEither. rewrite Heqp, in_app_iff. right.
      rewrite Hto_valid. split; assumption.
  }
  assert (He': forall e, evalid (remove_nth_gen_ve g2 from) e -> evalid g1 (emap e)). {
    intros e Hereset. rewrite Hev_reset, graph_has_e_reset in Hereset.
    destruct Hereset as [[Hsrc_has2 Hfield2] Hegen].
    rewrite Heqemap. destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - unfold egeneration in Hegen. specialize (Nv _ Hegen Hin) as [k [v [Hpair [Hv_eq Hmap]]]].
      subst v. pose proof Hpair as Hpair_v.
      destruct (Hcopy _ _ Hpair) as [Hvlab _].
      eapply gepl_value in Hpair; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hpair) as [_ Hemap].
      rewrite Hemap. rewrite Hev1. split; simpl.
      + erewrite <- Hsplit_combine in Hpair_v; eauto. apply in_combine_l in Hpair_v.
        rewrite <- Hfrom in Hpair_v. destruct Hpair_v as [Hreach _].
        apply reachable_through_set_foot_valid in Hreach.
        apply (proj1 (Hvv1 _)); exact Hreach.
      + rewrite get_edges_In. rewrite get_edges_inv in Hfield2.
        destruct Hfield2 as [idx [Heq Hidx]]. rewrite Heq in *. simpl in *.
        apply vlabel_get_edges_snd in Hvlab. rewrite Hvlab. assumption.
    - rewrite list_bi_map_not_In.
      + assert (Hvsrc1: vvalid g1 (fst e)). {
          destruct (vvalid_lcm _ (fst e) Hvv1) as [Hv1 | Hnot1]; auto.
          exfalso. apply Hnin. unfold InEither. rewrite Heqp, in_app_iff. right.
          rewrite Hto_valid. split.
          - apply (proj2 (Hvv2 _)); exact Hsrc_has2.
          - exact Hnot1.
        }
        assert (Hnot_from_l: ~ In (fst e) from_l). {
          intro Hin_from. apply Hnin. unfold InEither. rewrite Heqp, in_app_iff. left. exact Hin_from.
        }
        rewrite Hev1. split; simpl.
        * apply (proj1 (Hvv1 _)); exact Hvsrc1.
        * rewrite get_edges_inv in Hfield2 |-* . destruct Hfield2 as [idx [Heq Hidx]].
          exists idx. split; auto.
          rewrite (vlabel_get_edges_snd _ (fst e) _ g2);
            [exact Hidx | apply Hlabel; auto].
      + intro Hedge_in. apply Hnin. apply gepl_InEither in Hedge_in. exact Hedge_in.
  }
  assert (Hs': forall e, evalid (remove_nth_gen_ve g2 from) e ->
                         vmap (src g2 e) = src g1 (emap e)). {
    intros e Hereset. rewrite Hev_reset, graph_has_e_reset in Hereset.
    destruct Hereset as [[Hsrc_has2 Hfield2] Hegen].
    rewrite Hsrc2. subst vmap emap. unfold egeneration in Hegen.
    destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - specialize (Nv _ Hegen Hin) as [k [v [Hpair [Hv_eq Hmap]]]]. rewrite <- Hv_eq in *.
      destruct (Hcopy _ _ Hpair) as [Hvlab _]. eapply gepl_value in Hpair; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hpair) as [_ Hemap].
      rewrite Hmap, Hemap. rewrite Hsrc1. reflexivity.
    - rewrite !list_bi_map_not_In; auto. intro Hedge_in. apply gepl_InEither in Hedge_in. auto.
  }
  assert (Hvb: bijective vmap vmap) by (subst; apply bijective_list_bi_map; auto).
  assert (Hd': forall e,
             evalid (reachable_sub_labeledgraph
                       (reset_graph from g2) (filter_proj exterior_proj_vertex roots2)) e ->
             vmap (dst g2 e) = dst g1 (emap e)). {
    intros e Hesub. simpl in Hesub. destruct Hesub as [Hereset [Hsrc_reach Hdst_reach]].
    pose proof Hereset as Hereset_orig.
    rewrite Hev_reset, graph_has_e_reset in Hereset.
    destruct Hereset as [[Hsrc_has2 Hfield2] Hegen].
    apply reachable_through_set_foot_valid in Hdst_reach.
    rewrite Hvv_reset, graph_has_v_reset in Hdst_reach.
    destruct Hdst_reach as [Hdst_has2 Hdst_gen].
    assert (Hdst_not_from_l: ~ In (dst g2 e) from_l). {
      intro Hin. rewrite <- Hfrom in Hin. destruct Hin as [_ Hgen].
      rewrite remove_ve_dst_unchanged in Hdst_gen. apply Hdst_gen. symmetry. exact Hgen.
    }
    destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    - subst vmap emap. unfold egeneration in Hegen.
      specialize (Nv _ Hegen Hin) as [k [v [Hpair [Hv_eq Hmap]]]]. rewrite <- Hv_eq in *.
      destruct (Hcopy _ _ Hpair) as [Hvlab Hdst_copy].
      pose proof Hpair as Hpair_edge. eapply gepl_value in Hpair_edge; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hpair_edge) as [_ Hemap]. rewrite Hemap.
      destruct e as [esrc idx]. simpl in Hv_eq. subst esrc. simpl in *.
      rewrite get_edges_In in Hfield2. apply vlabel_get_edges_snd in Hvlab.
      rewrite <- Hvlab in Hfield2. specialize (Hdst_copy _ Hfield2).
      destruct Hdst_copy as [Hdst_copy | Hdst_copy].
      + rewrite Hdst_copy. rewrite list_bi_map_not_In; auto.
        intro Hdst_in. unfold InEither in Hdst_in. rewrite Heqp, in_app_iff in Hdst_in.
        destruct Hdst_in as [Hdst_from | Hdst_to].
        * rewrite <- Hdst_copy in Hdst_from. contradiction.
        * rewrite Hto_valid in Hdst_to. destruct Hdst_to as [_ Hnot_g1].
          assert (Hsrc_g1: graph_has_v g1 k). {
            erewrite <- Hsplit_combine in Hpair; eauto. apply in_combine_l in Hpair.
            rewrite <- Hfrom in Hpair. destruct Hpair as [Hreach _].
            apply reachable_through_set_foot_valid in Hreach.
            apply (proj1 (Hvv1 _)); exact Hreach.
          }
          rewrite <- get_edges_In in Hfield2. specialize (Hndd1 _ Hsrc_g1 _ Hfield2).
          rewrite <- Hvv1 in Hndd1. contradiction.
      + rewrite Hdst_copy. apply (surjective _ _ Hvb).
    - assert (Hedge_not: ~ InEither e (gen_edge_pair_list g1 vpl)) by
          (intro Hedge_in; apply Hnin; apply gepl_InEither in Hedge_in; exact Hedge_in).
      pose proof (He' _ Hereset_orig) as He_g1.
      rewrite Heqemap in He_g1. rewrite list_bi_map_not_In in He_g1; auto.
      rewrite Heqemap. rewrite list_bi_map_not_In; auto.
      assert (Hsrc_not_from: vgeneration (fst e) <> from). {
        intro Hsrc_from. unfold egeneration in Hegen. simpl in Hegen. lia.
      }
      destruct (Hedge_map e He_g1 Hsrc_not_from) as [_ [_ Hdst_map]].
      rewrite Hdst_map. rewrite <- Heqvmap. apply (surjective _ _ Hvb).
  }
  assert (Hp': forall v,
             vvalid (reachable_sub_labeledgraph (reset_graph from g2)
                       (filter_proj exterior_proj_vertex roots2)) v ->
             reachable_through_set g1 (filter_proj exterior_proj_vertex roots1) (vmap v)). {
    intros v Hvsub. simpl in Hvsub. destruct Hvsub as [Hvreset Hvreach].
    unfold reachable_through_set in Hvreach |-* . destruct Hvreach as [s [Hsroot Hreach]].
    assert (Hthrough: forall x, reachable (remove_nth_gen_ve g2 from) s x ->
                      reachable_through_set (remove_nth_gen_ve g2 from)
                        (filter_proj exterior_proj_vertex roots2) x) by
        (intros; exists s; split; assumption).
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hsroot. rewrite Hroots in Hsroot.
    apply (in_map (exterior_map vmap)) in Hsroot.
    rewrite (surjective _ _ (bijective_map _ _ (bijective_exterior_map _ _ Hvb))) in Hsroot.
    simpl in Hsroot. apply (filter_proj_In_iff exterior_proj_vertex_spec) in Hsroot.
    exists (vmap s). split; auto.
    unfold reachable, reachable_by in Hreach. destruct Hreach as [p Hpvalid].
    destruct Hpvalid as [[Hphead Hptail] [Hpprop Hplast]]. unfold reachable, reachable_by.
    destruct p as [phead pedges]. simpl in Hphead. subst phead. simpl snd in *.
    apply reachable_map_reachable_sub_edges
      with (g_src := reset_graph from g2) (g_dst := g1)
           (roots_src := filter_proj exterior_proj_vertex roots2)
           (vmap := vmap) (emap := emap) (p := pedges).
    - exact Hthrough.
    - split; [split | split]; simpl; auto.
    - assert (Hsvalid_reset: vvalid (remove_nth_gen_ve g2 from) s) by
          (eapply valid_path_valid; [exact Hpprop | left; reflexivity]).
      apply Hv'. exact Hsvalid_reset.
    - intros e Hesub.
      change (vmap (src (remove_nth_gen_ve g2 from) e) = src g1 (emap e)).
      rewrite remove_ve_src_unchanged.
      simpl in Hesub. destruct Hesub as [Hereset _]. apply Hs'. exact Hereset.
    - intros e Hesub.
      change (vmap (dst (remove_nth_gen_ve g2 from) e) = dst g1 (emap e)).
      rewrite remove_ve_dst_unchanged. apply Hd'. exact Hesub.
    - intros e Hesub. simpl in Hesub. destruct Hesub as [Hereset _]. apply He'. exact Hereset.
    - intros x Hx. apply Hv'. destruct Hx as [Hx _]. exact Hx.
  }
  exists vmap, vmap, emap, emap. split; auto. constructor; intros.
  - constructor; intros; auto.
    + subst. apply bijective_list_bi_map; assumption.
    + simpl. split; [apply Hv | apply Hp]; assumption.
    + simpl. split; [apply Hv' | apply Hp']; auto. destruct H; assumption.
    + simpl. split. 1: apply He; assumption.
      rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged, <- Hd, <- Hs; auto.
      2: destruct H; auto. destruct H as [? [? ?]].
      split; apply Hp; simpl; split; auto;
        eapply reachable_through_set_foot_valid; eauto.
    + simpl. split; [apply He' | rewrite <- Hs', <- Hd']; auto;
               destruct H as [? [? ?]]; auto. simpl src in H0. simpl dst in H1.
      rewrite remove_ve_src_unchanged in H0. rewrite remove_ve_dst_unchanged in H1.
      split; apply Hp'; simpl; split; auto;
        eapply reachable_through_set_foot_valid; eauto.
    + simpl. rewrite remove_ve_src_unchanged. destruct H as [? _]. apply Hs. auto.
    + simpl. rewrite remove_ve_dst_unchanged. apply Hd; auto.
  - simpl in H. destruct H as [Hvvalid _]. simpl. rewrite remove_ve_vlabel_unchanged.
    destruct (InEither_dec v vpl) as [Hin | Hnin].
    + destruct (Hleft_map _ Hvvalid Hin) as [v1 [v2 [Hpair [Hv_eq Hmap]]]].
      subst v1. rewrite Hmap.
      destruct (Hcopy _ _ Hpair) as [Hvlab _]. exact Hvlab.
    + rewrite Heqvmap, list_bi_map_not_In; auto.
      apply Hlabel; auto. intro Hin_from. apply Hnin. unfold InEither.
      rewrite Heqp, in_app_iff. left; assumption.
  - simpl in H |- * . rewrite remove_ve_elabel_unchanged. rewrite Heqemap.
    destruct (InEither_dec (fst e) vpl) as [Hin | Hnin].
    + destruct H as [Hevalid _].
      assert (Hge: graph_has_e g1 e) by (apply (proj1 (Hev1 e)); exact Hevalid).
      destruct Hge as [Hsrc_has Hfield].
      assert (Hsrc_valid: vvalid g1 (fst e)) by (apply (proj2 (Hvv1 _)); exact Hsrc_has).
      destruct (Hleft_map (fst e) Hsrc_valid Hin) as [k [v0 [Hpair [Hfst Hmap]]]]. subst k.
      pose proof (gepl_key _ _ _ _ Hfield Hpair) as Hedge_in.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hednd Hedge_in) as [Hemap _].
      rewrite Hemap. rewrite Hels1, Hels2. reflexivity.
    + rewrite list_bi_map_not_In; auto. 1: rewrite Hels2, Hels1; reflexivity.
      intro Hedge_in. apply Hnin. apply gepl_InEither in Hedge_in. assumption.
Qed.

#[local] Lemma new_gen_heap_new_gen_relation: forall g1 h1 g2 h2 gen,
    new_gen_heap_relation gen g1 h1 g2 h2 -> new_gen_relation gen g1 g2.
Proof.
  intros g1 h1 g2 h2 gen Hrel.
  unfold new_gen_heap_relation, new_gen_relation in *.
  destruct (graph_has_gen_dec g1 gen) as [Hhas | Hnot].
  - destruct Hrel as [Hg _]. symmetry. exact Hg.
  - destruct Hrel as [gi [sp [i [Hs [_ [Hnum [_ [_ [_ [Hg _]]]]]]]]]].
    exists gi. split; assumption.
Qed.

#[local] Lemma ngr_vertex_valid: forall g1 g2 gen,
    vertex_valid g1 -> new_gen_relation gen g1 g2 -> vertex_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold vertex_valid in *. intros. simpl.
    rewrite H. now split; intros; [apply ang_graph_has_v | apply ang_graph_has_v_inv in H1].
Qed.

#[local] Lemma ngr_edge_valid: forall g1 g2 gen,
    edge_valid g1 -> new_gen_relation gen g1 g2 -> edge_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold edge_valid in *. intros. simpl.
    rewrite H. now split; intros; destruct H1; split;
    [apply ang_graph_has_v | | apply ang_graph_has_v_inv in H1|].
Qed.

#[local] Lemma ngr_src_edge: forall (g1 g2: LGraph) gen,
    src_edge g1 -> new_gen_relation gen g1 g2 -> src_edge g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. now unfold src_edge in *.
Qed.

#[local] Lemma ngr_edge_label_same: forall (g1 g2: LGraph) gen,
    edge_label_same g1 -> new_gen_relation gen g1 g2 -> edge_label_same g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. now unfold edge_label_same in *.
Qed.

Lemma ngr_sound: forall g1 g2 gen,
    sound_gc_graph g1 -> new_gen_relation gen g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? [? ?]]]. split; [|split; [|split]].
  - eapply ngr_vertex_valid; eauto.
  - eapply ngr_edge_valid; eauto.
  - eapply ngr_src_edge; eauto.
  - eapply ngr_edge_label_same; eauto.
Qed.

#[local] Lemma cvae_vvalid_iff: forall g v' l v0,
    vvalid (fold_left (copy_v_add_edge v') l g) v0 <-> vvalid g v0.
Proof.
  intros. split; intro.
  - revert g H. induction l; intros; simpl in H; [assumption|].
    apply IHl in H; replace (vvalid (copy_v_add_edge v' g a) v0) with (vvalid g v0)
      in H by reflexivity; assumption.
  - revert g H. induction l; intros; simpl; [assumption|].
    apply IHl; replace (vvalid (copy_v_add_edge v' g a) v0) with (vvalid g v0) by
        reflexivity; assumption.
Qed.

#[local] Lemma pcv_vvalid_iff: forall g v v' new,
    vvalid (pregraph_copy_v g v new) v' <-> vvalid g v' \/ v' = new.
Proof.
  intros. unfold pregraph_copy_v. rewrite cvae_vvalid_iff. simpl.
  unfold addValidFunc. reflexivity.
Qed.

#[local] Lemma lcv_graph_has_v_iff: forall (g : LGraph) (v : VType) (to : nat) (x : VType),
  graph_has_gen g to ->
  graph_has_v (lgraph_copy_v g v to) x <-> graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. split; intros.
  - now apply lcv_graph_has_v_inv in H0.
  - now destruct H0; [apply lcv_graph_has_v_old | subst x; apply lcv_graph_has_v_new].
Qed.

#[local] Lemma lcv_vertex_valid: forall g v to,
    vertex_valid g -> graph_has_gen g to -> vertex_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold vertex_valid in *. intros. simpl.
  rewrite pcv_vvalid_iff, lcv_graph_has_v_iff; auto. now rewrite H.
Qed.

#[local] Lemma fr_O_vertex_valid: forall g g' from to p,
    vertex_valid g -> graph_has_gen g to -> forward_relation from to 0 p g g' ->
    vertex_valid g'.
Proof.
  intros. inversion H1; subst; try assumption; try now apply lcv_vertex_valid.
Qed.

#[local] Lemma lcv_get_edges_old: forall (g: LGraph) v v' to,
    graph_has_v g v' -> graph_has_gen g to ->
    get_edges (lgraph_copy_v g v to) v' = get_edges g v'.
Proof.
  intros. unfold get_edges, make_fields.
  now erewrite <- lcv_raw_fields by assumption.
Qed.

#[local] Lemma cvae_evalid_iff: forall g v l e,
    evalid (fold_left (copy_v_add_edge v) l g) e <-> evalid g e \/ In e (map fst l).
Proof.
  intros. revert g. induction l; intros; simpl; [intuition|].
  rewrite IHl. unfold copy_v_add_edge. simpl. unfold addValidFunc. intuition.
Qed.

#[local] Lemma pcv_evalid_iff: forall g v new e,
    evalid (pregraph_copy_v g v new) e <->
    evalid g e \/ In e (map (fun x => (new, snd x)) (get_edges g v)).
Proof.
  intros. unfold pregraph_copy_v. rewrite cvae_evalid_iff. rewrite map_fst_combine.
  - replace (length (get_edges g v)) with (length (map snd (get_edges g v))) by
        (rewrite length_map; reflexivity). rewrite combine_repeat_eq_map, map_map.
    reflexivity.
  - unfold EType at 1. rewrite length_combine, repeat_length, !length_map.
    apply Nat.min_id.
Qed.

#[local] Lemma lcv_lacv_get_edges: forall g v to new,
    get_edges (lgraph_copy_v g v to) new = get_edges (lgraph_add_copied_v g v to) new.
Proof.
  intros. unfold lgraph_copy_v, get_edges, make_fields. rewrite <- lmc_raw_fields.
  reflexivity.
Qed.

#[local] Lemma lcv_edge_valid: forall g v to,
    edge_valid g -> graph_has_gen g to -> edge_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold edge_valid in *. intros. unfold graph_has_e in *. simpl.
  rewrite pcv_evalid_iff, lcv_graph_has_v_iff, H; auto. split; intros.
  - destruct H1 as [[? ?] | ?].
    + split; [now left|]. rewrite lcv_get_edges_old; auto.
    + assert (fst e = new_copied_v g to). {
        apply list_in_map_inv in H1; destruct H1 as [x [? ?]]; subst e; simpl; auto. }
      split; [now right|]. rewrite H2.
      now rewrite get_edges_map_map, lcv_lacv_get_edges, lacv_get_edges_new, map_map.
  - destruct H1. destruct H1; [left | right].
    + split; auto. rewrite lcv_get_edges_old in H2; assumption.
    + rewrite H1 in H2.
      rewrite get_edges_map_map, lcv_lacv_get_edges, lacv_get_edges_new, map_map in H2.
      assumption.
Qed.

#[local] Lemma fr_O_edge_valid: forall g1 g2 from to p,
    edge_valid g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> edge_valid g2.
Proof.
  intros. inversion H1; subst; try assumption; try now apply lcv_edge_valid.
Qed.

#[local] Lemma flcvae_src_old: forall g new (l: list (EType * VType)) e,
    ~ In e (map fst l) -> src (fold_left (copy_v_add_edge new) l g) e = src g e.
Proof.
  intros. revert g H. induction l; intros; simpl; trivial.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption.
  simpl. unfold updateEdgeFunc. rewrite if_false; trivial.
  unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

#[local] Lemma flcvae_src_new: forall g new (l: list (EType * VType)) e,
    In e (map fst l) -> src (fold_left (copy_v_add_edge new) l g) e = new.
Proof.
  intros. revert g. induction l. 1: simpl in H; exfalso; assumption.
  intros. simpl in *. destruct H.
  - subst e. destruct (in_dec equiv_dec (fst a) (map fst l)).
    + apply IHl; auto.
    + rewrite flcvae_src_old; auto. simpl. unfold updateEdgeFunc.
      rewrite if_true; reflexivity.
  - apply IHl; assumption.
Qed.

#[local] Lemma pcv_src_old: forall (g : LGraph) (old new : VType) (e : VType * nat),
    fst e <> new -> src (pregraph_copy_v g old new) e = src g e.
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_src_old. 1: now simpl.
  intro. apply H. rewrite map_fst_combine in H0.
  - destruct e. simpl in *. apply in_combine_l, repeat_spec in H0. assumption.
  - unfold EType. now rewrite length_combine, repeat_length, !length_map, Nat.min_id.
Qed.

#[local] Lemma pcv_src_new: forall (g : LGraph) (old new : VType) (n : nat),
       In n (map snd (get_edges g old)) ->
       src (pregraph_copy_v g old new) (new, n) = new.
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_src_new; auto.
  rewrite map_fst_combine.
  - replace (length (get_edges g old)) with (length (map snd (get_edges g old))) by
        now rewrite length_map. rewrite combine_repeat_eq_map, map_map.
    apply list_in_map_inv in H. destruct H as [[v idx] [? ?]]. simpl in H. subst idx.
    change (new, n) with ((fun x : VType * nat => (new, snd x)) (v, n)).
    now apply in_map.
  - unfold EType. now rewrite length_combine, repeat_length, !length_map, Nat.min_id.
Qed.

#[local] Lemma pcv_src_edge: forall (g: LGraph) v new,
    src_edge g -> src_edge (pregraph_copy_v g v new).
Proof.
  intros. unfold src_edge in *. intros. unfold pregraph_copy_v.
  replace (length (get_edges g v)) with (length (map snd (get_edges g v))) by
      (rewrite length_map; reflexivity). remember (get_edges g v) as el.
  remember (combine (combine (repeat new (Datatypes.length (map snd el))) (map snd el))
                    (map (dst g) el)) as l. destruct (in_dec equiv_dec e (map fst l)).
  - rewrite flcvae_src_new; auto.
    rewrite combine_repeat_eq_map, map_map, combine_map_join in Heql.
    apply list_in_map_inv in i. destruct i as [x [? ?]]. subst l.
    apply list_in_map_inv in H1. destruct H1 as [x0 [? ?]]. subst x e. simpl. auto.
  - rewrite flcvae_src_old; auto. simpl. apply H.
Qed.

#[local] Lemma fr_O_src_edge: forall (g1 g2: LGraph) from to p,
    src_edge g1 -> forward_relation from to O p g1 g2 -> src_edge g2.
Proof.
  intros. inversion H0; subst; try assumption; try (apply pcv_src_edge; assumption).
Qed.

#[local] Lemma fr_O_edge_label_same: forall (g1 g2: LGraph) from to p,
    edge_label_same g1 -> forward_relation from to O p g1 g2 -> edge_label_same g2.
Proof. intros. inversion H0; subst; try assumption. Qed.

Lemma fr_O_sound: forall g1 g2 from to p,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? [? ?]]]. split; [|split; [|split]].
  - eapply fr_O_vertex_valid; eauto.
  - eapply fr_O_edge_valid; eauto.
  - eapply fr_O_src_edge; eauto.
  - eapply fr_O_edge_label_same; eauto.
Qed.

Lemma new_gen_heap_sound: forall g1 h1 g2 h2 gen,
    sound_gc_graph g1 -> new_gen_heap_relation gen g1 h1 g2 h2 -> sound_gc_graph g2.
Proof.
  intros g1 h1 g2 h2 gen Hsound Hrel.
  eapply (ngr_sound g1 g2 gen); eauto. unfold new_gen_relation, new_gen_heap_relation in *.
  destruct (graph_has_gen_dec g1 gen).
  - destruct Hrel as [Hg _]. symmetry. assumption.
  - destruct Hrel as [gi [sp [i [Hs [_ [Hnum [_ [_ [_ [Hg _]]]]]]]]]].
    exists gi. split; assumption.
Qed.

Lemma forward_remset_item_P_holds:
  forall (P: LGraph -> Prop) from to g h rh rmst item g' h' rh' rmst',
    (forall g1 g2 p,
        P g1 -> graph_has_gen g1 to -> forward_relation from to O p g1 g2 -> P g2) ->
    P g -> graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    P g'.
Proof.
  intros P from to g h rh rmst item g' h' rh' rmst' HP HPg Hto Hfri.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hnotin.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [new_g new_h] eqn:Hfgh.
    inversion Hfri; subst. eapply HP; eauto.
    pose proof (fr_forward_graph_and_heap
                  from to 0 (remset_item2forward_t item rmst g) g h) as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr. exact Hfr.
  - inversion Hfri; subst. assumption.
Qed.

Lemma forward_remset_item_fold_P_holds:
  forall (P: LGraph -> Prop) from to r g h rh rmst g' h' rh' rmst',
    (forall g1 g2 p,
        P g1 -> graph_has_gen g1 to -> forward_relation from to O p g1 g2 -> P g2) ->
    P g -> graph_has_gen g to ->
    (g', h', rh', rmst') = fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    P g'.
Proof.
  intros P from to r. induction r; intros g h rh rmst g' h' rh' rmst' HP HPg Hto Hfold.
  - inversion Hfold; subst. assumption.
  - destruct (forward_remset_item from to (g, h, rh, rmst) a)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    change (fold_left (forward_remset_item from to) (a :: r) (g, h, rh, rmst))
      with (fold_left (forward_remset_item from to) r
              (forward_remset_item from to (g, h, rh, rmst) a)) in Hfold.
    rewrite Hfri in Hfold.
    eapply (IHr g2 h2 rh2 rmst2 g' h' rh' rmst').
    + exact HP.
    + eapply forward_remset_item_P_holds; eauto.
    + apply (proj1 (forward_remset_item_ghg from to g h rh rmst a
                      g2 h2 rh2 rmst2 Hto (eq_sym Hfri) to)); exact Hto.
    + exact Hfold.
Qed.

Lemma forward_remset_gh_P_holds:
  forall (P: LGraph -> Prop) from to g h rh rmst g' h' rh' rmst',
    (forall g1 g2 p,
        P g1 -> graph_has_gen g1 to -> forward_relation from to O p g1 g2 -> P g2) ->
    P g -> graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    P g'.
Proof.
  intros P from to g h rh rmst g' h' rh' rmst' HP HPg Hto Hfrg.
  unfold forward_remset_gh in Hfrg.
  eapply forward_remset_item_fold_P_holds; eassumption.
Qed.

Lemma forward_remset_gh_sound:
  forall from to g h rh rmst g' h' rh' rmst',
    sound_gc_graph g -> graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    sound_gc_graph g'.
Proof.
  intros. eapply forward_remset_gh_P_holds; eauto.
  intros. eapply fr_O_sound; eauto.
Qed.

Lemma forward_remset_item_step_state_with_tail:
  forall from to g h rh rmst item rest g' h' rh' rmst',
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    remset_and_remset_space_compatible g from rmst rest ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    graph_has_gen g' to /\
    copy_compatible g' /\
    remset_nodup rmst' /\
    remset_graph_compatible g' rmst' /\
    remset_and_remset_space_compatible g' from rmst' rest.
Proof.
  intros from to g h rh rmst item rest g' h' rh' rmst'
         Hneq Hto Hcc Hrnd Hrgc Hric Hrest Hfri.
  split.
  - rewrite <- (forward_remset_item_ghg from to g h rh rmst item
                  g' h' rh' rmst' Hto Hfri to).
    exact Hto.
  - split.
    + exact (fri_copy_compatible from to g h rh rmst item g' h' rh' rmst'
               Hneq Hto Hcc Hfri).
    + split.
      * exact (fri_remset_nodup from to g h rh rmst item g' h' rh' rmst'
                 Hrnd Hfri).
      * split.
        -- exact (fri_remset_graph_compatible from to g h rh rmst item
                    g' h' rh' rmst' Hto Hcc Hrnd Hrgc Hric Hfri).
        -- unfold remset_and_remset_space_compatible in Hrest |- *.
           rewrite Forall_forall in Hrest |- *.
           intros tail_item Hin_tail.
           specialize (Hrest _ Hin_tail).
           eapply fri_remset_item_compatible with (rmst := rmst) (item := item);
             eassumption.
Qed.

(** Semi-Isomorphism **)

Definition from_gen_semi_spec (g1 g2: LGraph) (l: list VType) (gen: nat): Prop :=
  NoDup l /\ forall v,
    (raw_mark (vlabel g2 v) = true /\ vvalid g1 v /\ vgeneration v = gen) <->
    In v l.

Definition gc_graph_remset_semi_iso_parts
           (Partial: LGraph -> LGraph -> list (VType * VType) -> nat -> Prop)
           (g1 g2: LGraph) (from to: nat) (l: list (VType * VType)): Prop :=
  (forall v1 v2 : VType,
      In (v1, v2) l ->
      v2 = copied_vertex (vlabel g2 v1) /\
      vlabel g1 v1 = vlabel g2 v2 /\
      (forall idx : nat,
          In idx (map snd (get_edges g1 v1)) ->
          dst g2 (v2, idx) = dst g1 (v1, idx) \/
          dst g2 (v2, idx) = list_bi_map l (dst g1 (v1, idx)))) /\
    let (from_l, to_l) := split l in
    from_gen_semi_spec g1 g2 from_l from /\ to_gen_spec g1 g2 to_l to /\
    (forall v, vvalid g1 v -> ~ In v from_l -> vlabel g1 v = vlabel g2 v) /\
    Partial g1 g2 l from.

Definition gc_graph_remset_semi_iso
           (g1 g2: LGraph) (from to: nat) (l: list (VType * VType)): Prop :=
  gc_graph_remset_semi_iso_parts remset_partial_graph g1 g2 from to l.

Definition gc_graph_pending_remset_semi_iso
           (g1 g2: LGraph) (from to: nat)
           (pending: remset_space) (l: list (VType * VType)): Prop :=
  gc_graph_remset_semi_iso_parts
    (fun g1 g2 l from => remset_partial_graph_pending g1 g2 l from pending)
    g1 g2 from to l.

Lemma gc_graph_remset_semi_iso_parts_partial:
  forall Partial g1 g2 from to l,
    gc_graph_remset_semi_iso_parts Partial g1 g2 from to l ->
    Partial g1 g2 l from.
Proof.
  intros Partial g1 g2 from to l [_ Hspec].
  destruct (split l) as [from_l to_l].
  tauto.
Qed.

Lemma gc_graph_remset_semi_iso_parts_DoubleNoDup:
  forall Partial g1 g2 from to l,
    from <> to ->
    gc_graph_remset_semi_iso_parts Partial g1 g2 from to l ->
    DoubleNoDup l.
Proof.
  intros Partial g1 g2 from to l Hneq [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Heqp.
  apply (PairGenNoDup_DoubleNoDup l from to); auto.
  red. rewrite Heqp.
  destruct Hspec as [[Hfrom_nd Hfrom] [[Hto_nd [_ Hto_gen]] _]].
  split.
  - split; [exact Hfrom_nd |].
    intros v Hin. rewrite <- Hfrom in Hin.
    destruct Hin as [_ [_ Hgen]]. exact Hgen.
  - split; [exact Hto_nd | exact Hto_gen].
Qed.

Lemma remset_semi_iso_DoubleNoDup: forall g1 g2 from to l,
    from <> to -> gc_graph_remset_semi_iso g1 g2 from to l -> DoubleNoDup l.
Proof.
  intros g1 g2 from to l Hneq Hiso.
  eapply gc_graph_remset_semi_iso_parts_DoubleNoDup; eauto.
Qed.

Lemma pending_remset_semi_iso_DoubleNoDup:
  forall g1 g2 from to pending l,
    from <> to ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l ->
    DoubleNoDup l.
Proof.
  intros g1 g2 from to pending l Hneq Hsemi.
  eapply gc_graph_remset_semi_iso_parts_DoubleNoDup; eauto.
Qed.

Lemma pending_remset_semi_iso_old_nonfrom_edge_marked_or_current:
  forall base g from to pending l e v,
    from <> to ->
    gc_graph_pending_remset_semi_iso base g from to pending l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    dst base e = v ->
    vgeneration v = from ->
    raw_mark (vlabel g v) = true \/ dst g e = v.
Proof.
  intros base g from to pending l e v Hneq Hsemi Hevalid Hsrcgen Hdst Hgen.
  unfold gc_graph_pending_remset_semi_iso,
    gc_graph_remset_semi_iso_parts in Hsemi.
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [_ Hto_gen]] [_ Hpartial]]].
  unfold remset_partial_graph_pending in Hpartial.
  destruct Hpartial as [_ [Hedges _]].
  specialize (Hedges e Hevalid Hsrcgen).
  destruct Hedges as [Hpending | Hmapped].
  - destruct Hpending as [_ [_ [_ [Hdst_eq _]]]].
    right. now rewrite Hdst_eq.
  - destruct Hmapped as [_ [_ Hdst_map]].
    destruct (in_dec equiv_dec v from_l) as [Hin_from | Hnot_from].
    + left. apply (proj2 (Hfrom v)) in Hin_from. tauto.
    + destruct (in_dec equiv_dec v to_l) as [Hin_to | Hnot_to].
      * specialize (Hto_gen _ Hin_to). lia.
      * right. rewrite Hdst_map, Hdst.
        apply list_bi_map_not_In.
        unfold InEither. rewrite Hsplit, in_app_iff. tauto.
Qed.

Definition no_unmarked_old_nonfrom_dst
           (base current: LGraph) (from: nat): Prop :=
  forall e,
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst base e) = from ->
    raw_mark (vlabel current (dst base e)) = false ->
    False.

Lemma remset_item_records_edge_functional:
  forall item e1 e2,
    remset_item_records_edge item e1 ->
    remset_item_records_edge item e2 ->
    e1 = e2.
Proof.
  intros item e1 e2 H1 H2.
  destruct item as [addr | [v pos]]; simpl in *; [contradiction |].
  destruct e1 as [v1 idx1], e2 as [v2 idx2]. simpl in *.
  destruct H1 as [Hv1 Hidx1].
  destruct H2 as [Hv2 Hidx2].
  subst v1 v2.
  assert (idx1 = idx2) by lia.
  now subst idx2.
Qed.

Lemma old_nonfrom_edge_mapped_lcv:
  forall base g from to l v e,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    graph_has_gen g to ->
    old_vertices_valid base g ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    evalid g e ->
    src g e = src base e ->
    dst g e = list_bi_map l (dst base e) ->
    dst base e <> v ->
    vgeneration v = from ->
    evalid (lgraph_copy_v g v to) e /\
    src (lgraph_copy_v g v to) e = src base e /\
    dst (lgraph_copy_v g v to) e =
      list_bi_map ((v, new_copied_v g to) :: l) (dst base e).
Proof.
  intros base g from to l v e Hneq Hsound_base Hsound_g Hndd Hto
         Holdvalid Hevalid Hsrcgen He_g Hsrc_g Hdst_g Hdst_not_v Hgenv.
  destruct Hsound_base as [Hvv_base [Hev_base [_ _]]].
  destruct Hsound_g as [Hvv_g [_ [_ _]]].
  assert (Hge: graph_has_e base e) by
      (apply (proj1 (Hev_base e)); exact Hevalid).
  destruct Hge as [Hsrc_has Hfield].
  assert (Hsrc_valid_base: vvalid base (fst e)) by
      (apply (proj2 (Hvv_base _)); exact Hsrc_has).
  assert (Hdst_has: graph_has_v base (dst base e)) by
      (apply (Hndd (fst e)); assumption).
  assert (Hdst_valid_base: vvalid base (dst base e)) by
      (apply (proj2 (Hvv_base _)); exact Hdst_has).
  assert (Hnew_not_valid: ~ vvalid g (new_copied_v g to)). {
    intro Hbad. apply (proj1 (Hvv_g _)) in Hbad.
    pose proof (graph_has_v_not_eq g to _ Hbad). contradiction.
  }
  assert (Hsrc_not_new: fst e <> new_copied_v g to). {
    intro Hbad. apply Hnew_not_valid. rewrite <- Hbad.
    apply Holdvalid; assumption.
  }
  assert (Hdst_not_new: dst base e <> new_copied_v g to). {
    intro Hbad.
    destruct (Nat.eq_dec (vgeneration (dst base e)) from) as [Hdst_from | Hdst_not_from].
    - rewrite Hbad in Hdst_from. simpl in Hdst_from. lia.
    - apply Hnew_not_valid. rewrite <- Hbad.
      apply Holdvalid; assumption.
  }
  split.
  - simpl. rewrite pcv_evalid_iff. now left.
  - split.
    + simpl. rewrite pcv_src_old; auto.
    + simpl. rewrite pcv_dst_old; auto.
      rewrite Hdst_g. symmetry. rewrite list_bi_map_cons_1; auto.
      unfold IsEither. simpl. intuition.
Qed.

Lemma old_nonfrom_edges_mapped_lcv:
  forall base g from to l v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    graph_has_gen g to ->
    old_vertices_valid base g ->
    old_nonfrom_edges_mapped base g l from ->
    no_unmarked_old_nonfrom_dst base g from ->
    raw_mark (vlabel g v) = false ->
    vgeneration v = from ->
    old_nonfrom_edges_mapped base (lgraph_copy_v g v to)
      ((v, new_copied_v g to) :: l) from.
Proof.
  intros base g from to l v Hneq Hsound_base Hsound_g Hndd Hto
         Holdvalid Hedges Hclosed Hmark Hgenv.
  unfold old_nonfrom_edges_mapped in *.
  intros e Hevalid Hsrcgen.
  specialize (Hedges e Hevalid Hsrcgen).
  destruct Hedges as [He_g [Hsrc_g Hdst_g]].
  assert (Hdst_not_v: dst base e <> v). {
    intro Hbad. subst v.
    eapply Hclosed; eauto.
  }
  eapply old_nonfrom_edge_mapped_lcv; eauto.
Qed.

Lemma old_nonfrom_edges_mapped_pending_lcv:
  forall base g from to l pending v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    graph_has_gen g to ->
    old_vertices_valid base g ->
    old_nonfrom_edges_mapped_pending base g l from pending ->
    old_nonfrom_edges_to_are_pending base v from pending ->
    vgeneration v = from ->
    list_bi_map l v = v ->
    old_nonfrom_edges_mapped_pending base (lgraph_copy_v g v to)
      ((v, new_copied_v g to) :: l) from pending.
Proof.
  intros base g from to l pending v Hneq Hsound_base Hsound_g Hndd Hto
         Holdvalid Hedges Hpending Hgenv Hmap_v.
  unfold old_nonfrom_edges_mapped_pending in *.
  intros e Hevalid Hsrcgen.
  specialize (Hedges e Hevalid Hsrcgen).
  destruct Hedges as [Hpending_e | Hmapped].
  - destruct Hpending_e as [Hrec [He_g [Hsrc_g [Hdst_eq Hdst_from]]]].
    left. split; [exact Hrec |].
    pose proof Hsound_base as Hsound_base'.
    pose proof Hsound_g as Hsound_g'.
    destruct Hsound_base' as [Hvv_base [Hev_base [_ _]]].
    destruct Hsound_g' as [Hvv_g [_ [_ _]]].
    assert (Hge: graph_has_e base e) by
        (apply (proj1 (Hev_base e)); exact Hevalid).
    destruct Hge as [Hsrc_has _].
    assert (Hsrc_valid_base: vvalid base (fst e)) by
        (apply (proj2 (Hvv_base _)); exact Hsrc_has).
    assert (Hnew_not_valid: ~ vvalid g (new_copied_v g to)). {
      intro Hbad. apply (proj1 (Hvv_g _)) in Hbad.
      pose proof (graph_has_v_not_eq g to _ Hbad). contradiction.
    }
    assert (Hsrc_not_new: fst e <> new_copied_v g to). {
      intro Hbad. apply Hnew_not_valid. rewrite <- Hbad.
      apply Holdvalid; assumption.
    }
    split.
    + simpl. rewrite pcv_evalid_iff. now left.
    + split.
      * simpl. rewrite pcv_src_old; auto.
      * split.
        -- simpl. rewrite pcv_dst_old; auto.
        -- exact Hdst_from.
  - destruct Hmapped as [He_g [Hsrc_g Hdst_g]].
    destruct (V_EqDec (dst base e) v) as [Hdst_v | Hdst_not_v].
    + hnf in Hdst_v. left. split; [eapply Hpending; eauto |].
      pose proof Hsound_base as Hsound_base'.
      pose proof Hsound_g as Hsound_g'.
      destruct Hsound_base' as [Hvv_base [Hev_base [_ _]]].
      destruct Hsound_g' as [Hvv_g [_ [_ _]]].
      assert (Hge: graph_has_e base e) by
          (apply (proj1 (Hev_base e)); exact Hevalid).
      destruct Hge as [Hsrc_has _].
      assert (Hsrc_valid_base: vvalid base (fst e)) by
          (apply (proj2 (Hvv_base _)); exact Hsrc_has).
      assert (Hnew_not_valid: ~ vvalid g (new_copied_v g to)). {
        intro Hbad. apply (proj1 (Hvv_g _)) in Hbad.
        pose proof (graph_has_v_not_eq g to _ Hbad). contradiction.
      }
      assert (Hsrc_not_new: fst e <> new_copied_v g to). {
        intro Hbad. apply Hnew_not_valid. rewrite <- Hbad.
        apply Holdvalid; assumption.
      }
      split.
      * simpl. rewrite pcv_evalid_iff. now left.
      * split.
        -- simpl. rewrite pcv_src_old; auto.
        -- split.
           ++ simpl. rewrite pcv_dst_old; auto.
              rewrite Hdst_g, Hdst_v, Hmap_v. reflexivity.
           ++ rewrite Hdst_v. exact Hgenv.
    + right.
      eapply old_nonfrom_edge_mapped_lcv; eauto.
Qed.

Lemma old_vertices_valid_lcv:
  forall base g to v,
    old_vertices_valid base g ->
    old_vertices_valid base (lgraph_copy_v g v to).
Proof.
  unfold old_vertices_valid.
  intros base g to v Hvertices x Hvalid.
  simpl. rewrite pcv_vvalid_iff. left.
  apply Hvertices. exact Hvalid.
Qed.

Lemma remset_semi_iso_refl: forall g from to,
    sound_gc_graph g -> gen_unmarked g from ->
    gc_graph_remset_semi_iso g g from to nil.
Proof.
  intros g from to Hsound Hunmarked. split.
  - intros v1 v2 Hin. inversion Hin.
  - destruct (split []) eqn:Hsplit. simpl in Hsplit. inversion Hsplit. subst.
    split.
    + red. split. 1: constructor. intros v; split; intros H.
      * destruct H as [Hmark [Hvalid Hgen]].
        destruct Hsound as [Hvv _]. red in Hvv. rewrite Hvv in Hvalid.
        destruct v as [gen idx]. simpl in Hgen. subst gen. simpl in Hvalid.
        destruct Hvalid as [Hhas_gen Hhas_idx].
        red in Hunmarked.
        specialize (Hunmarked Hhas_gen idx Hhas_idx).
        rewrite Hmark in Hunmarked. discriminate.
      * inversion H.
    + split.
      * red. split. 1: constructor. split; [split |]; intros; intuition auto with *.
      * split.
        -- intros. reflexivity.
        -- unfold remset_partial_graph.
           split.
           ++ unfold old_vertices_valid. auto.
           ++ split.
              ** unfold old_nonfrom_edges_mapped. simpl.
                 intros e Hevalid _. split; [exact Hevalid | split; reflexivity].
              ** unfold unmarked_from_edges_unchanged.
                 intros e Hevalid _ _. split; [exact Hevalid | split; reflexivity].
Qed.

Lemma old_nonfrom_edges_mapped_pending_nil:
  forall g1 g2 l from,
    old_nonfrom_edges_mapped_pending g1 g2 l from nil ->
    old_nonfrom_edges_mapped g1 g2 l from.
Proof.
  unfold old_nonfrom_edges_mapped_pending, old_nonfrom_edges_mapped,
    remset_space_records_edge.
  intros g1 g2 l from Hedges e He Hsrcgen.
  specialize (Hedges e He Hsrcgen).
  destruct Hedges as [[[item [Hin _]] _] | Hmapped].
  - inversion Hin.
  - exact Hmapped.
Qed.

Lemma old_nonfrom_edges_mapped_pending_intro:
  forall g1 g2 l from pending,
    old_nonfrom_edges_mapped g1 g2 l from ->
    old_nonfrom_edges_mapped_pending g1 g2 l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending, old_nonfrom_edges_mapped.
  intros g1 g2 l from pending Hedges e He Hsrcgen.
  right. apply Hedges; assumption.
Qed.

Lemma remset_space_records_edge_cons_drop:
  forall item pending e,
    (forall e0, ~ remset_item_records_edge item e0) ->
    remset_space_records_edge (item :: pending) e ->
    remset_space_records_edge pending e.
Proof.
  intros item pending e Hnone [item0 [[Hin | Hin] Hrec]].
  - subst item0. contradiction (Hnone e Hrec).
  - exists item0. split; assumption.
Qed.

Lemma remset_exterior_records_no_edge:
  forall addr e,
    ~ remset_item_records_edge (RemSetExterior addr) e.
Proof.
  intros addr e Hrec. simpl in Hrec. exact Hrec.
Qed.

Lemma old_nonfrom_edges_mapped_pending_cons_drop:
  forall g1 g2 l from item pending,
    (forall e, ~ remset_item_records_edge item e) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from (item :: pending) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros g1 g2 l from item pending Hnone Hedges e He Hsrcgen.
  destruct (Hedges e He Hsrcgen) as [Hpending | Hmapped].
  - destruct Hpending as [Hrec Hcurrent].
    left. split; [|exact Hcurrent].
    eapply remset_space_records_edge_cons_drop; eauto.
  - right. exact Hmapped.
Qed.

Lemma old_nonfrom_edges_mapped_pending_cons_drop_old_nonfrom:
  forall g1 g2 l from item pending,
    (forall e, vgeneration (fst e) <> from -> ~ remset_item_records_edge item e) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from (item :: pending) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros g1 g2 l from item pending Hnone Hedges e He Hsrcgen.
  destruct (Hedges e He Hsrcgen) as [Hpending | Hmapped].
  - destruct Hpending as [[item0 [[Hin | Hin] Hrec]] Hcurrent].
    + subst item0. contradiction (Hnone e Hsrcgen Hrec).
    + left. split; [exists item0; split; assumption | exact Hcurrent].
  - right. exact Hmapped.
Qed.

Lemma old_nonfrom_edges_mapped_pending_consume_item_not_to:
  forall (g1 g2: LGraph) (l: list (VType * VType)) from item
         (pending: remset_space) e,
    remset_item_records_edge item e ->
    vgeneration (dst g2 e) <> from ->
    old_nonfrom_edges_mapped_pending g1 g2 l from (item :: pending) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros g1 g2 l from item pending e Hitem Hdst_not Hedges e0 He0 Hsrcgen0.
  destruct (Hedges e0 He0 Hsrcgen0) as [Hpending | Hmapped].
  - destruct Hpending as [[item0 [[Hin | Hin] Hrec]] [He_g [Hsrc_g [Hdst_eq Hdst_from]]]].
    + subst item0.
      assert (Heq: e0 = e) by
          (eapply remset_item_records_edge_functional; eauto).
      subst e0. rewrite Hdst_eq in Hdst_not. contradiction.
    + left. split.
      * exists item0. split; assumption.
      * split; [exact He_g |]. split; [exact Hsrc_g |].
        split; [exact Hdst_eq | exact Hdst_from].
  - right. exact Hmapped.
Qed.

Lemma old_nonfrom_edges_mapped_pending_consume_item_no_current_edge:
  forall (g1 g2: LGraph) (l: list (VType * VType)) from item
         (pending: remset_space),
    (forall e, remset_item_records_edge item e -> ~ evalid g2 e) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from (item :: pending) ->
    old_nonfrom_edges_mapped_pending g1 g2 l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros g1 g2 l from item pending Hno_current Hedges e0 He0 Hsrcgen0.
  destruct (Hedges e0 He0 Hsrcgen0) as [Hpending | Hmapped].
  - destruct Hpending as [[item0 [[Hin | Hin] Hrec]]
                           [He_g [Hsrc_g [Hdst_eq Hdst_from]]]].
    + subst item0. exfalso. exact (Hno_current e0 Hrec He_g).
    + left. split.
      * exists item0. split; assumption.
      * split; [exact He_g |]. split; [exact Hsrc_g |].
        split; [exact Hdst_eq | exact Hdst_from].
  - right. exact Hmapped.
Qed.

Lemma remset_partial_graph_pending_lift_edges:
  forall g1 g2 l from pending1 pending2,
    (old_nonfrom_edges_mapped_pending g1 g2 l from pending1 ->
     old_nonfrom_edges_mapped_pending g1 g2 l from pending2) ->
    remset_partial_graph_pending g1 g2 l from pending1 ->
    remset_partial_graph_pending g1 g2 l from pending2.
Proof.
  unfold remset_partial_graph_pending.
  intros g1 g2 l from pending1 pending2 Hlift
         [Hold [Hedges Hunmarked]].
  split; [exact Hold |].
  split; [|exact Hunmarked].
  now apply Hlift.
Qed.

Lemma pending_remset_semi_iso_nil:
  forall g1 g2 from to l,
    gc_graph_pending_remset_semi_iso g1 g2 from to nil l ->
    gc_graph_remset_semi_iso g1 g2 from to l.
Proof.
  intros g1 g2 from to l [Hcopy Hspec].
  split; [exact Hcopy |].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
  split; [exact Hfrom |]. split; [exact Hto |].
  split; [exact Hlabel |].
  unfold remset_partial_graph_pending in Hpartial.
  unfold remset_partial_graph.
  destruct Hpartial as [Hold [Hedges Hunmarked]].
  split; [exact Hold |]. split; [|exact Hunmarked].
  now apply old_nonfrom_edges_mapped_pending_nil.
Qed.

Lemma remset_semi_iso_pending:
  forall g1 g2 from to l pending,
    gc_graph_remset_semi_iso g1 g2 from to l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l.
Proof.
  intros g1 g2 from to l pending [Hcopy Hspec].
  split; [exact Hcopy |].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
  split; [exact Hfrom |]. split; [exact Hto |].
  split; [exact Hlabel |].
  unfold remset_partial_graph in Hpartial.
  unfold remset_partial_graph_pending.
  destruct Hpartial as [Hold [Hedges Hunmarked]].
  split; [exact Hold |]. split; [|exact Hunmarked].
  now apply old_nonfrom_edges_mapped_pending_intro.
Qed.

Lemma pending_remset_semi_iso_lift_partial:
  forall g1 g2 from to pending1 pending2 l,
    (remset_partial_graph_pending g1 g2 l from pending1 ->
     remset_partial_graph_pending g1 g2 l from pending2) ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending1 l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending2 l.
Proof.
  intros g1 g2 from to pending1 pending2 l Hlift [Hcopy Hspec].
  split; [exact Hcopy |].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
  split; [exact Hfrom |]. split; [exact Hto |].
  split; [exact Hlabel |].
  now apply Hlift.
Qed.

Lemma pending_remset_semi_iso_cons_drop:
  forall g1 g2 from to item pending l,
    (forall e, ~ remset_item_records_edge item e) ->
    gc_graph_pending_remset_semi_iso g1 g2 from to (item :: pending) l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l.
Proof.
  intros g1 g2 from to item pending l Hnone Hiso.
  eapply pending_remset_semi_iso_lift_partial; [|exact Hiso].
  intros Hpartial.
  eapply remset_partial_graph_pending_lift_edges; [|exact Hpartial].
  intros Hedges. eapply old_nonfrom_edges_mapped_pending_cons_drop; eauto.
Qed.

Lemma pending_remset_semi_iso_cons_drop_old_nonfrom:
  forall g1 g2 from to item pending l,
    (forall e, vgeneration (fst e) <> from -> ~ remset_item_records_edge item e) ->
    gc_graph_pending_remset_semi_iso g1 g2 from to (item :: pending) l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l.
Proof.
  intros g1 g2 from to item pending l Hnone Hiso.
  eapply pending_remset_semi_iso_lift_partial; [|exact Hiso].
  intros Hpartial.
  eapply remset_partial_graph_pending_lift_edges; [|exact Hpartial].
  intros Hedges.
  eapply old_nonfrom_edges_mapped_pending_cons_drop_old_nonfrom; eauto.
Qed.

Lemma pending_remset_semi_iso_consume_item_not_to:
  forall (g1 g2: LGraph) from to item (pending: remset_space)
         (l: list (VType * VType)) e,
    remset_item_records_edge item e ->
    vgeneration (dst g2 e) <> from ->
    gc_graph_pending_remset_semi_iso g1 g2 from to (item :: pending) l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l.
Proof.
  intros g1 g2 from to item pending l e Hitem Hdst_not Hiso.
  eapply pending_remset_semi_iso_lift_partial; [|exact Hiso].
  intros Hpartial.
  eapply remset_partial_graph_pending_lift_edges; [|exact Hpartial].
  intros Hedges.
  eapply old_nonfrom_edges_mapped_pending_consume_item_not_to; eauto.
Qed.

Lemma pending_remset_semi_iso_consume_item_no_current_edge:
  forall (g1 g2: LGraph) from to item (pending: remset_space)
         (l: list (VType * VType)),
    (forall e, remset_item_records_edge item e -> ~ evalid g2 e) ->
    gc_graph_pending_remset_semi_iso g1 g2 from to (item :: pending) l ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l.
Proof.
  intros g1 g2 from to item pending l Hno_current Hiso.
  eapply pending_remset_semi_iso_lift_partial; [|exact Hiso].
  intros Hpartial.
  eapply remset_partial_graph_pending_lift_edges; [|exact Hpartial].
  intros Hedges.
  eapply old_nonfrom_edges_mapped_pending_consume_item_no_current_edge; eauto.
Qed.

Lemma pending_remset_semi_iso_refl:
  forall g from to pending,
    sound_gc_graph g -> gen_unmarked g from ->
    gc_graph_pending_remset_semi_iso g g from to pending nil.
Proof.
  intros g from to pending Hsound Hunmarked.
  apply remset_semi_iso_pending.
  now apply remset_semi_iso_refl.
Qed.

Lemma pcv_is_partial_graph: forall (g: LGraph) old new,
    sound_gc_graph g -> ~ vvalid g new ->
    is_partial_graph g (pregraph_copy_v g old new).
Proof.
  intros. destruct H as [? [? [? Hels]]]. red in H, H1, H2. split; [|split; [|split]]; intros.
  - rewrite pcv_vvalid_iff. now left.
  - rewrite pcv_evalid_iff. now left.
  - rewrite pcv_src_old; auto. intro. now rewrite H2, H5 in H4.
  - rewrite pcv_dst_old; auto. rewrite H1 in H3. destruct H3. rewrite <- H in H3.
    intro. now rewrite H6 in H3.
Qed.

Lemma ucov_copied_vertex: forall g old_v new_v,
    copied_vertex (update_copied_old_vlabel g old_v new_v old_v) = new_v.
Proof.
  intros. unfold update_copied_old_vlabel, update_vlabel. now rewrite if_true.
Qed.

Lemma ucov_not_eq: forall g old_v new_v x,
    old_v <> x -> update_copied_old_vlabel g old_v new_v x = vlabel g x.
Proof.
  intros. unfold update_copied_old_vlabel, update_vlabel. now rewrite if_false.
Qed.

Lemma lcv_sound: forall g v to,
    graph_has_gen g to -> sound_gc_graph g -> sound_gc_graph (lgraph_copy_v g v to).
Proof.
  intros. unfold sound_gc_graph in *. destruct H0 as [? [? [? ?]]]. split; [|split; [|split]].
  - eapply lcv_vertex_valid; eauto.
  - eapply lcv_edge_valid; eauto.
  - eapply pcv_src_edge; eauto.
  - assumption.
Qed.

Lemma ucov_rawmark: forall g old_v new_v,
    raw_mark (update_copied_old_vlabel g old_v new_v old_v) = true.
Proof.
  intros. unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; easy.
Qed.

Lemma lcv_raw_mark_old: forall g v to,
    raw_mark (vlabel (lgraph_copy_v g v to) v) = true.
Proof. intros. simpl. apply ucov_rawmark. Qed.

Lemma lcv_raw_mark_true_pres:
  forall g old_v to v,
    graph_has_gen g to ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = true ->
    raw_mark (vlabel (lgraph_copy_v g old_v to) v) = true.
Proof.
  intros g old_v to v Hto Hv Hmark.
  destruct (V_EqDec v old_v) as [Heq | Hneq].
  - hnf in Heq. subst v. apply lcv_raw_mark_old.
  - rewrite <- lcv_raw_mark; auto.
Qed.

Lemma fr_O_raw_mark_true_pres:
  forall from to p g g' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = true ->
    forward_relation from to O p g g' ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to p g g' v Hto Hv Hmark Hfr.
  destruct p as [z | out | vtx | e]; inversion Hfr; subst; simpl; auto;
    try (rewrite <- lgd_raw_mark_eq; auto);
    try (eapply lcv_raw_mark_true_pres; eauto).
Qed.

Lemma fr_O_forward_vertex_marked:
  forall from to (g g': LGraph) v,
    vgeneration v = from ->
    forward_relation from to O (ForwardVertex v) g g' ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to g g' v Hgen Hfr.
  inversion Hfr; subst; try contradiction; auto.
  apply lcv_raw_mark_old.
Qed.

Lemma fr_O_forward_edge_dst_marked:
  forall from to (g g': LGraph) e,
    vgeneration (dst g e) = from ->
    forward_relation from to O (ForwardEdge e) g g' ->
    raw_mark (vlabel g' (dst g e)) = true.
Proof.
  intros from to g g' e Hgen Hfr.
  inversion Hfr; subst; try contradiction; auto.
  subst new_g.
  rewrite <- lgd_raw_mark_eq.
  apply lcv_raw_mark_old.
Qed.

Lemma fr_O_raw_mark_false_inv:
  forall from to p g g' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    vgeneration v = from ->
    raw_mark (vlabel g' v) = false ->
    forward_relation from to O p g g' ->
    raw_mark (vlabel g v) = false.
Proof.
  intros from to p g g' v Hto Hv Hgen Hmark Hfr.
  destruct p as [z | out | vtx | e]; inversion Hfr; subst; auto;
    try (rewrite <- lgd_raw_mark_eq in Hmark; exact Hmark).
  - destruct (V_EqDec v vtx) as [Heq | Hneq].
    + hnf in Heq. subst v. rewrite lcv_raw_mark_old in Hmark. discriminate.
    + rewrite <- (lcv_raw_mark g vtx to v) in Hmark; auto.
  - subst new_g. rewrite <- lgd_raw_mark_eq in Hmark.
    destruct (V_EqDec v (dst g e)) as [Heq | Hneq].
    + hnf in Heq. subst v. rewrite lcv_raw_mark_old in Hmark. discriminate.
    + rewrite <- (lcv_raw_mark g (dst g e) to v) in Hmark; auto.
Qed.

Lemma forward_remset_item_graph_has_v_pres:
  forall from to g h rh rmst item g' h' rh' rmst' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    graph_has_v g' v.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' v Hto Hv Hfri.
  eapply (forward_remset_item_P_holds
            (fun g0 => graph_has_v g0 v)); eauto.
  intros g1 g2 p Hv1 Hto1 Hfr.
  eapply fr_graph_has_v; eauto.
Qed.

Lemma forward_remset_item_fold_raw_mark_true_pres:
  forall from to r g h rh rmst g' h' rh' rmst' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = true ->
    (g', h', rh', rmst') = fold_left (forward_remset_item from to) r
                                     (g, h, rh, rmst) ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to r g h rh rmst g' h' rh' rmst' v Hto Hv Hmark Hfold.
  assert (Hpres: forall g1 g2 p,
             graph_has_v g1 v /\ raw_mark (vlabel g1 v) = true ->
             graph_has_gen g1 to ->
             forward_relation from to O p g1 g2 ->
             graph_has_v g2 v /\ raw_mark (vlabel g2 v) = true). {
    intros g1 g2 p [Hv1 Hmark1] Hto1 Hfr.
    split.
    - eapply fr_graph_has_v; eauto.
    - eapply fr_O_raw_mark_true_pres; eauto.
  }
  destruct (forward_remset_item_fold_P_holds
              (fun g => graph_has_v g v /\ raw_mark (vlabel g v) = true)
              from to r g h rh rmst g' h' rh' rmst'
              Hpres (conj Hv Hmark) Hto Hfold) as [_ Hmark'].
  exact Hmark'.
Qed.

Lemma no_unmarked_old_nonfrom_dst_lcv:
  forall base g from to v,
    from <> to ->
    no_unmarked_old_nonfrom_dst base g from ->
    no_unmarked_old_nonfrom_dst base (lgraph_copy_v g v to) from.
Proof.
  unfold no_unmarked_old_nonfrom_dst.
  intros base g from to v Hneq Hclosed e He Hsrc Hdst Hmark.
  destruct (V_EqDec (dst base e) v) as [Heq | Hne_v].
  - hnf in Heq. subst. rewrite lcv_raw_mark_old in Hmark. discriminate.
  - assert (Hne_new: dst base e <> new_copied_v g to). {
      intro Hbad. rewrite Hbad in Hdst. simpl in Hdst. lia.
    }
    unfold lgraph_copy_v in Hmark.
    rewrite lmc_vlabel_not_eq in Hmark by (intro Hbad; apply Hne_v; hnf; exact Hbad).
    rewrite lacv_vlabel_old in Hmark by exact Hne_new.
    eapply Hclosed; eauto.
Qed.

Lemma no_unmarked_old_nonfrom_dst_lgd:
  forall base g from e v,
    no_unmarked_old_nonfrom_dst base g from ->
    no_unmarked_old_nonfrom_dst base (labeledgraph_gen_dst g e v) from.
Proof.
  unfold no_unmarked_old_nonfrom_dst.
  intros base g from e v Hclosed edge Hevalid Hsrc Hdst Hmark.
  eapply Hclosed; eauto.
Qed.

Lemma unmarked_from_edges_unchanged_lcv:
  forall base g from to v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    old_vertices_valid base g ->
    unmarked_from_edges_unchanged base g from ->
    unmarked_from_edges_unchanged base (lgraph_copy_v g v to) from.
Proof.
  unfold unmarked_from_edges_unchanged.
  intros base g from to v Hneq Hsound_base Hsound_g Hvertices Hunmarked.
  intros [[egen eidx] fidx] Hevalid Hsrcgen Hmark.
  simpl in Hsrcgen.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  destruct Hsound_g as [Hvv_g _].
  assert (Hge: graph_has_e base ((egen, eidx), fidx)) by
      (apply (proj1 (Hev_base _)); exact Hevalid).
  destruct Hge as [Hsrc_has _].
  assert (Hsrc_valid_base: vvalid base (egen, eidx)) by
      (apply (proj2 (Hvv_base _)); exact Hsrc_has).
  assert (Hsrc_has_g: graph_has_v g (egen, eidx)) by
      (apply (proj1 (Hvv_g _)); apply Hvertices; exact Hsrc_valid_base).
  assert (Hsrc_not_new: (egen, eidx) <> new_copied_v g to). {
    unfold new_copied_v. intro Hbad. inversion Hbad. lia.
  }
  assert (Hmark_old: raw_mark (vlabel g (egen, eidx)) = false). {
    destruct (V_EqDec (egen, eidx) v) as [Heq | Hne].
    - hnf in Heq. subst v.
      rewrite lcv_raw_mark_old in Hmark. discriminate.
    - unfold lgraph_copy_v in Hmark.
      rewrite lmc_vlabel_not_eq in Hmark by (intro Hbad; apply Hne; hnf; exact Hbad).
      rewrite lacv_vlabel_old in Hmark by exact Hsrc_not_new.
      exact Hmark.
  }
  specialize (Hunmarked ((egen, eidx), fidx) Hevalid Hsrcgen Hmark_old).
  destruct Hunmarked as [He_g [Hsrc_g Hdst_g]].
  split.
  - simpl. rewrite pcv_evalid_iff. now left.
  - split.
    + simpl. rewrite pcv_src_old; auto.
    + simpl. rewrite pcv_dst_old; auto.
Qed.

Lemma remset_partial_graph_lcv:
  forall base g from to l v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    graph_has_gen g to ->
    remset_partial_graph base g l from ->
    no_unmarked_old_nonfrom_dst base g from ->
    raw_mark (vlabel g v) = false ->
    vgeneration v = from ->
    remset_partial_graph base (lgraph_copy_v g v to)
      ((v, new_copied_v g to) :: l) from.
Proof.
  intros base g from to l v Hneq Hsound_base Hsound_g Hndd Hto
         Hpartial Hclosed Hmark Hgen.
  unfold remset_partial_graph in *.
  destruct Hpartial as [Holdvalid [Hedges Hunmarked]].
  split.
  - now apply old_vertices_valid_lcv.
  - split.
    + eapply old_nonfrom_edges_mapped_lcv; eauto.
    + eapply unmarked_from_edges_unchanged_lcv; eauto.
Qed.

Lemma old_vertices_valid_lgd:
  forall base g e v,
    old_vertices_valid base g ->
    old_vertices_valid base (labeledgraph_gen_dst g e v).
Proof.
  unfold old_vertices_valid.
  intros base g e v Hold x Hx.
  apply Hold. exact Hx.
Qed.

Lemma old_nonfrom_edges_mapped_lgd:
  forall base g l from e v,
    sound_gc_graph base ->
    ~ vvalid base (fst e) ->
    old_nonfrom_edges_mapped base g l from ->
    old_nonfrom_edges_mapped base (labeledgraph_gen_dst g e v) l from.
Proof.
  unfold old_nonfrom_edges_mapped.
  intros base g l from e v Hsound Hnot_base Hedges e0 He0 Hsrcgen.
  specialize (Hedges e0 He0 Hsrcgen).
  destruct Hedges as [He_g [Hsrc_g Hdst_g]].
  destruct Hsound as [Hvv_base [Hev_base _]].
  split; [exact He_g |]. split; [exact Hsrc_g |].
  rewrite lgd_dst_old; [exact Hdst_g |].
  intro Heq. subst e0.
  assert (Hge: graph_has_e base e) by (apply (proj1 (Hev_base _)); exact He0).
  destruct Hge as [Hsrc_has _].
  apply Hnot_base. apply (proj2 (Hvv_base _)). exact Hsrc_has.
Qed.

Lemma old_nonfrom_edges_mapped_pending_lgd_mapped:
  forall (base g: LGraph) (l: list (VType * VType)) from item
         (pending: remset_space) (e: EType) (v: VType),
    evalid base e ->
    evalid g e ->
    src g e = src base e ->
    vgeneration (fst e) <> from ->
    remset_item_records_edge item e ->
    v = list_bi_map l (dst base e) ->
    old_nonfrom_edges_mapped_pending base g l from (item :: pending) ->
    old_nonfrom_edges_mapped_pending base (labeledgraph_gen_dst g e v) l from pending.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros base g l from item pending e v Hevalid_base Hevalid_g Hsrc_g Hsrcgen
         Hitem Hv Hedges e0 He0 Hsrcgen0.
  specialize (Hedges e0 He0 Hsrcgen0).
  destruct Hedges as [Hpending | Hmapped].
  - destruct Hpending as [Hrec_pending [He_g0 [Hsrc_g0 [Hdst_eq0 Hdst_from0]]]].
    destruct Hrec_pending as [item0 [[Hin | Hin] Hrec]].
    + subst item0.
      assert (Heq: e0 = e) by
          (eapply remset_item_records_edge_functional; eauto).
      subst e0. right.
      split; [exact Hevalid_g |]. split; [exact Hsrc_g |].
      rewrite lgd_dst_new. exact Hv.
    + destruct_eq_dec e0 e.
      * subst e0. right.
        split; [exact Hevalid_g |]. split; [exact Hsrc_g |].
        rewrite lgd_dst_new. exact Hv.
      * left. split.
        -- exists item0. split; [exact Hin | exact Hrec].
        -- split; [exact He_g0 |]. split; [exact Hsrc_g0 |].
           split.
           ++ rewrite lgd_dst_old; auto.
           ++ exact Hdst_from0.
  - destruct Hmapped as [He_g [Hsrc_old Hdst_old]].
    right. split; [exact He_g |]. split; [exact Hsrc_old |].
    destruct_eq_dec e0 e.
    + subst e0. rewrite lgd_dst_new. exact Hv.
    + rewrite lgd_dst_old; auto.
Qed.

Lemma unmarked_from_edges_unchanged_lgd:
  forall base g from e v,
    sound_gc_graph base ->
    ~ vvalid base (fst e) ->
    unmarked_from_edges_unchanged base g from ->
    unmarked_from_edges_unchanged base (labeledgraph_gen_dst g e v) from.
Proof.
  unfold unmarked_from_edges_unchanged.
  intros base g from e v Hsound Hnot_base Hunmarked e0 He0 Hsrcgen Hmark.
  rewrite <- lgd_raw_mark_eq in Hmark.
  specialize (Hunmarked e0 He0 Hsrcgen Hmark).
  destruct Hunmarked as [He_g [Hsrc_g Hdst_g]].
  destruct Hsound as [Hvv_base [Hev_base _]].
  split; [exact He_g |]. split; [exact Hsrc_g |].
  rewrite lgd_dst_old; [exact Hdst_g |].
  intro Heq. subst e0.
  assert (Hge: graph_has_e base e) by (apply (proj1 (Hev_base _)); exact He0).
  destruct Hge as [Hsrc_has _].
  apply Hnot_base. apply (proj2 (Hvv_base _)). exact Hsrc_has.
Qed.

Lemma unmarked_from_edges_unchanged_lgd_nonfrom:
  forall (base g: LGraph) from (e: EType) (v: VType),
    evalid base e ->
    vgeneration (fst e) <> from ->
    unmarked_from_edges_unchanged base g from ->
    unmarked_from_edges_unchanged base (labeledgraph_gen_dst g e v) from.
Proof.
  unfold unmarked_from_edges_unchanged.
  intros base g from e v Hevalid Hsrcgen Hunmarked e0 He0 Hsrcgen0 Hmark.
  rewrite <- lgd_raw_mark_eq in Hmark.
  specialize (Hunmarked e0 He0 Hsrcgen0 Hmark).
  destruct Hunmarked as [He_g [Hsrc_g Hdst_g]].
  split; [exact He_g |]. split; [exact Hsrc_g |].
  destruct_eq_dec e0 e.
  - subst e0. contradiction.
  - rewrite lgd_dst_old; auto.
Qed.

Lemma remset_partial_graph_lgd:
  forall base g l from e v,
    sound_gc_graph base ->
    ~ vvalid base (fst e) ->
    remset_partial_graph base g l from ->
    remset_partial_graph base (labeledgraph_gen_dst g e v) l from.
Proof.
  intros base g l from e v Hsound Hnot_base Hpartial.
  unfold remset_partial_graph in *.
  destruct Hpartial as [Holdvalid [Hedges Hunmarked]].
  split.
  - now apply old_vertices_valid_lgd.
  - split.
    + eapply old_nonfrom_edges_mapped_lgd; eauto.
    + eapply unmarked_from_edges_unchanged_lgd; eauto.
Qed.

Lemma remset_partial_graph_pending_lgd_mapped:
  forall (base g: LGraph) (l: list (VType * VType)) from item
         (pending: remset_space) (e: EType) (v: VType),
    evalid base e ->
    evalid g e ->
    src g e = src base e ->
    vgeneration (fst e) <> from ->
    remset_item_records_edge item e ->
    v = list_bi_map l (dst base e) ->
    remset_partial_graph_pending base g l from (item :: pending) ->
    remset_partial_graph_pending base (labeledgraph_gen_dst g e v) l from pending.
Proof.
  intros base g l from item pending e v Hevalid_base Hevalid_g Hsrc_g Hsrcgen
         Hitem Hv Hpartial.
  unfold remset_partial_graph_pending in *.
  destruct Hpartial as [Holdvalid [Hedges Hunmarked]].
  split.
  - now apply old_vertices_valid_lgd.
  - split.
    + eapply old_nonfrom_edges_mapped_pending_lgd_mapped; eauto.
    + eapply unmarked_from_edges_unchanged_lgd_nonfrom; eauto.
Qed.

Lemma lcv_remset_semi_iso_parts:
  forall (Partial: LGraph -> LGraph -> list (VType * VType) -> nat -> Prop)
         (from to: nat) (base g: LGraph) l v,
    from <> to -> sound_gc_graph base -> sound_gc_graph g ->
    graph_has_gen g to -> vvalid g v -> vgeneration v = from ->
    raw_mark (vlabel g v) = false ->
    no_dangling_dst base ->
    (forall base0 g0 l0,
        Partial base0 g0 l0 from -> old_vertices_valid base0 g0) ->
    (forall base0 g0 l0,
        Partial base0 g0 l0 from ->
        unmarked_from_edges_unchanged base0 g0 from) ->
    DoubleNoDup l ->
    gc_graph_remset_semi_iso_parts Partial base g from to l ->
    Partial base (lgraph_copy_v g v to)
      ((v, new_copied_v g to) :: l) from ->
    gc_graph_remset_semi_iso_parts Partial base (lgraph_copy_v g v to) from to
      ((v, new_copied_v g to) :: l).
Proof.
  intros Partial from to base g l v Hneq Hsound_base Hsound_g Hto_gen_has
         Hv_valid Hgen Hmark Hndd Hpartial_vertices Hpartial_unmarked
         Hdd_l Hiso Hpartial_new.
  pose proof Hsound_base as Hsound_base0.
  pose proof Hsound_g as Hsound_g0.
  assert (Hsound_lcv: sound_gc_graph (lgraph_copy_v g v to)) by
      (apply lcv_sound; auto).
  destruct Hiso as [Hcopy Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
  destruct Hfrom as [Hfrom_nd Hfrom].
  destruct Hto as [Hto_nd [Hto_valid Hto_gen]].
  pose proof (Hpartial_vertices base g l Hpartial) as Holdvalid.
  pose proof (Hpartial_unmarked base g l Hpartial) as Hunmarked.
  destruct Hsound_base as [Hvv_base [Hev_base [Hsrc_base _]]].
  destruct Hsound_g as [Hvv_g [Hev_g [Hsrc_g _]]].
  assert (Hv_base: vvalid base v). {
    destruct (vvalid_lcm base v Hvv_base) as [Hv_base | Hv_not_base];
      [exact Hv_base |].
    assert (Hin_to: In v to_l) by (rewrite Hto_valid; split; auto).
    specialize (Hto_gen _ Hin_to). lia.
  }
  assert (Hv_has_base: graph_has_v base v) by
      (apply (proj1 (Hvv_base _)); exact Hv_base).
  assert (Hnew_not_valid: ~ vvalid g (new_copied_v g to)). {
    intro Hbad. apply (proj1 (Hvv_g _)) in Hbad.
    pose proof (graph_has_v_not_eq g to _ Hbad). contradiction.
  }
  assert (Hv_not_from_l: ~ In v from_l). {
    intro Hin. rewrite <- Hfrom in Hin.
    destruct Hin as [Htrue _]. rewrite Hmark in Htrue. discriminate.
  }
  assert (Hlabel_v: vlabel base v = vlabel g v) by
      (apply Hlabel; auto).
  assert (Hnew_not_to_l: ~ In (new_copied_v g to) to_l). {
    intro Hin. apply Hto_valid in Hin. destruct Hin as [Hbad _].
    contradiction.
  }
  assert (Hdd_cons: DoubleNoDup ((v, new_copied_v g to) :: l)). {
    rewrite DoubleNoDup_cons_iff. split; [exact Hdd_l |].
    split.
    - intro Hbad. apply (f_equal vgeneration) in Hbad.
      rewrite Hgen in Hbad. unfold new_copied_v in Hbad. simpl in Hbad.
      lia.
    - split.
      + intro Hin. unfold InEither in Hin. rewrite Hsplit, in_app_iff in Hin.
        destruct Hin as [Hin | Hin]; [contradiction |].
        specialize (Hto_gen _ Hin). lia.
      + intro Hin. unfold InEither in Hin. rewrite Hsplit, in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        * rewrite <- Hfrom in Hin. destruct Hin as [_ [_ Hnew_gen]].
          unfold new_copied_v in Hnew_gen. simpl in Hnew_gen. lia.
        * contradiction.
  }
  split.
  - intros v1 v2 Hin.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst v1 v2. split.
      * simpl. now rewrite ucov_copied_vertex.
      * split.
        -- rewrite lcv_vlabel_new; [exact Hlabel_v | now rewrite Hgen].
        -- intros idx Hidx.
           assert (Hevalid_base: evalid base (v, idx)). {
             apply (proj2 (Hev_base _)).
             split; [exact Hv_has_base | now rewrite get_edges_In].
           }
           specialize (Hunmarked (v, idx) Hevalid_base Hgen Hmark).
           destruct Hunmarked as [_ [_ Hdst_same]].
           left. simpl. rewrite pcv_dst_new.
           ++ exact Hdst_same.
           ++ erewrite <- vlabel_get_edges_snd; eauto.
    + assert (Hin_from_l: In v1 from_l) by
          (apply In_map_fst in Hin; now rewrite map_fst_split, Hsplit in Hin).
      assert (Hin_to_l: In v2 to_l) by
          (apply In_map_snd in Hin; now rewrite map_snd_split, Hsplit in Hin).
      assert (Hv1_not_v: v1 <> v) by
          (intro Hbad; subst v1; contradiction).
      assert (Hv2_not_v: v2 <> v). {
        intro Hbad. subst v2. specialize (Hto_gen _ Hin_to_l). lia.
      }
      assert (Hv1_not_new: v1 <> new_copied_v g to). {
        intro Hbad. subst v1. rewrite <- Hfrom in Hin_from_l.
        destruct Hin_from_l as [_ [_ Hnew_gen]].
        unfold new_copied_v in Hnew_gen. simpl in Hnew_gen. lia.
      }
      assert (Hv2_not_new: v2 <> new_copied_v g to) by
          (intro Hbad; subst v2; contradiction).
      specialize (Hcopy _ _ Hin) as [Hcopied [Hlabel_pair Hfields]].
      split.
      * simpl. rewrite ucov_not_eq by
            (intro Hbad; apply Hv1_not_v; symmetry; exact Hbad).
        rewrite lacv_vlabel_old by exact Hv1_not_new.
        exact Hcopied.
      * split.
        -- simpl. rewrite ucov_not_eq by
             (intro Hbad; apply Hv2_not_v; symmetry; exact Hbad).
           rewrite lacv_vlabel_old by exact Hv2_not_new.
           exact Hlabel_pair.
        -- intros idx Hidx. simpl. rewrite pcv_dst_old by exact Hv2_not_new.
           specialize (Hfields _ Hidx). destruct Hfields as [Hfields | Hfields].
           ++ now left.
           ++ destruct (InEither_dec (dst base (v1, idx)) l) as [Hin_either | Hnot_either].
              ** right. rewrite list_bi_map_cons_1; auto.
                 eapply DoubleNoDup_cons_InEither; eauto.
              ** rewrite list_bi_map_not_In in Hfields by exact Hnot_either.
                 now left.
  - simpl. rewrite Hsplit.
    red in Hdd_cons. simpl in Hdd_cons. rewrite Hsplit in Hdd_cons.
    pose proof (NoDup_app_l _ _ _ Hdd_cons) as Hfrom_nd_cons.
    pose proof (NoDup_app_r _ _ _ Hdd_cons) as Hto_nd_cons.
    split.
    + split; [exact Hfrom_nd_cons |].
      intros v0. split; intros Hx.
      * destruct Hx as [Hraw [Hvalid_base Hgen0]].
        destruct (V_EqDec v0 v) as [Heq | Hne_v].
        -- hnf in Heq. subst v0. now left.
        -- right. rewrite <- Hfrom. split; [|split; auto].
           assert (Hhas_g: graph_has_v g v0) by
               (apply (proj1 (Hvv_g _)); apply Holdvalid; exact Hvalid_base).
           rewrite <- (lcv_raw_mark g v to v0) in Hraw; auto.
      * simpl in Hx. destruct Hx as [Hx | Hx].
        -- subst v0. split; [apply lcv_raw_mark_old | split; auto].
        -- rewrite <- Hfrom in Hx. destruct Hx as [Hraw [Hvalid_base Hgen0]].
           split; [|split; auto].
           assert (Hhas_g: graph_has_v g v0) by
               (apply (proj1 (Hvv_g _)); apply Holdvalid; exact Hvalid_base).
           rewrite <- (lcv_raw_mark g v to v0); auto.
           intro Hbad. subst v0. rewrite Hmark in Hraw. discriminate.
    + split.
      * split; [exact Hto_nd_cons |]. split.
        -- intros v0. split; intros Hx.
           ++ simpl in Hx. destruct Hx as [Hx | Hx].
              ** subst v0. split.
                 --- simpl. rewrite pcv_vvalid_iff. now right.
                 --- intro Hbad. apply Hnew_not_valid. apply Holdvalid. exact Hbad.
              ** rewrite Hto_valid in Hx. destruct Hx as [Hvalid_g Hnot_base].
                 split; [|exact Hnot_base].
                 simpl. rewrite pcv_vvalid_iff. now left.
           ++ destruct Hx as [Hvalid_lcv Hnot_base].
              simpl in Hvalid_lcv. rewrite pcv_vvalid_iff in Hvalid_lcv.
              destruct Hvalid_lcv as [Hvalid_g | Hnew].
              ** right. rewrite Hto_valid. split; assumption.
              ** left. symmetry. exact Hnew.
        -- intros v0 Hx. simpl in Hx. destruct Hx as [Hx | Hx].
           ++ subst v0. unfold new_copied_v. reflexivity.
           ++ now apply Hto_gen.
      * split.
        -- intros v0 Hvalid_base Hnot_in.
           simpl in Hnot_in. apply Decidable.not_or in Hnot_in.
           destruct Hnot_in as [Hv0_not_v Hv0_not_from_l].
           simpl. rewrite ucov_not_eq by exact Hv0_not_v.
           rewrite lacv_vlabel_old.
           ++ apply Hlabel; assumption.
           ++ intro Hbad. subst v0. apply Hnew_not_valid.
              apply Holdvalid. exact Hvalid_base.
        -- exact Hpartial_new.
Qed.

Lemma lcv_remset_semi_iso:
  forall (from to: nat) (base g: LGraph) l v,
    from <> to -> sound_gc_graph base -> sound_gc_graph g ->
    graph_has_gen g to -> vvalid g v -> vgeneration v = from ->
    raw_mark (vlabel g v) = false ->
    no_dangling_dst base -> gc_graph_remset_semi_iso base g from to l ->
    no_unmarked_old_nonfrom_dst base g from ->
    gc_graph_remset_semi_iso base (lgraph_copy_v g v to) from to
      ((v, new_copied_v g to) :: l).
Proof.
  intros from to base g l v Hneq Hsound_base Hsound_g Hto_gen_has
         Hv_valid Hgen Hmark Hndd Hiso Hclosed.
  assert (Hdd: DoubleNoDup l) by
      (eapply remset_semi_iso_DoubleNoDup; eauto).
  assert (Hpartial_new:
            remset_partial_graph base (lgraph_copy_v g v to)
              ((v, new_copied_v g to) :: l) from). {
    eapply remset_partial_graph_lcv; eauto.
    eapply gc_graph_remset_semi_iso_parts_partial; exact Hiso.
  }
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 => remset_partial_graph base0 g0 l0 from0)
            base g from to l) in Hiso.
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 => remset_partial_graph base0 g0 l0 from0)
            base (lgraph_copy_v g v to) from to
            ((v, new_copied_v g to) :: l)).
  eapply lcv_remset_semi_iso_parts; eauto.
  - intros base0 g0 l0 Hpartial. exact (proj1 Hpartial).
  - intros base0 g0 l0 Hpartial. exact (proj2 (proj2 Hpartial)).
Qed.

Lemma remset_partial_graph_pending_lcv:
  forall base g from to l pending v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    graph_has_gen g to ->
    remset_partial_graph_pending base g l from pending ->
    old_nonfrom_edges_to_are_pending base v from pending ->
    vgeneration v = from ->
    list_bi_map l v = v ->
    remset_partial_graph_pending base (lgraph_copy_v g v to)
      ((v, new_copied_v g to) :: l) from pending.
Proof.
  intros base g from to l pending v Hneq Hsound_base Hsound_g Hndd Hto
         Hpartial Hpending Hgen Hmap_v.
  unfold remset_partial_graph_pending in *.
  destruct Hpartial as [Holdvalid [Hedges Hunmarked]].
  split.
  - now apply old_vertices_valid_lcv.
  - split.
    + eapply old_nonfrom_edges_mapped_pending_lcv; eauto.
    + eapply unmarked_from_edges_unchanged_lcv; eauto.
Qed.

Lemma lcv_pending_remset_semi_iso:
  forall (from to: nat) (base g: LGraph) pending l v,
    from <> to -> sound_gc_graph base -> sound_gc_graph g ->
    graph_has_gen g to -> vvalid g v -> vgeneration v = from ->
    raw_mark (vlabel g v) = false ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso base g from to pending l ->
    old_nonfrom_edges_to_are_pending base v from pending ->
    gc_graph_pending_remset_semi_iso base (lgraph_copy_v g v to) from to pending
      ((v, new_copied_v g to) :: l).
Proof.
  intros from to base g pending l v Hneq Hsound_base Hsound_g Hto_gen_has
         Hv_valid Hgen Hmark Hndd Hiso Hpending.
  assert (Hdd: DoubleNoDup l) by
      (eapply (pending_remset_semi_iso_DoubleNoDup base g from to pending l);
       eauto).
  assert (Hpartial_new:
            remset_partial_graph_pending base (lgraph_copy_v g v to)
              ((v, new_copied_v g to) :: l) from pending). {
    eapply remset_partial_graph_pending_lcv.
    - exact Hneq.
    - exact Hsound_base.
    - exact Hsound_g.
    - exact Hndd.
    - exact Hto_gen_has.
    - eapply gc_graph_remset_semi_iso_parts_partial; exact Hiso.
    - exact Hpending.
    - exact Hgen.
    - assert (Hnot_either: ~ InEither v l). {
      unfold gc_graph_pending_remset_semi_iso,
        gc_graph_remset_semi_iso_parts in Hiso.
      destruct Hiso as [_ Hspec].
      destruct (split l) as [from_l to_l] eqn:Hsplit.
      destruct Hspec as [[_ Hfrom] [[_ [_ Hto_gen]] _]].
      unfold InEither. rewrite Hsplit, in_app_iff.
      intros [Hin_from | Hin_to].
      - apply (proj2 (Hfrom v)) in Hin_from.
        destruct Hin_from as [Hmark_true _].
        rewrite Hmark_true in Hmark. discriminate.
      - specialize (Hto_gen _ Hin_to). lia.
      }
      now rewrite list_bi_map_not_In.
  }
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 =>
               remset_partial_graph_pending base0 g0 l0 from0 pending)
            base g from to l) in Hiso.
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 =>
               remset_partial_graph_pending base0 g0 l0 from0 pending)
            base (lgraph_copy_v g v to) from to
            ((v, new_copied_v g to) :: l)).
  eapply lcv_remset_semi_iso_parts; eauto.
  - intros base0 g0 l0 Hpartial. exact (proj1 Hpartial).
  - intros base0 g0 l0 Hpartial. exact (proj2 (proj2 Hpartial)).
Qed.

Lemma lgd_remset_semi_iso:
  forall (from to: nat) (base g: LGraph) l v n e,
    from <> to -> sound_gc_graph base -> sound_gc_graph g ->
    graph_has_gen g to -> interior_compatible g from (InteriorVertexPos v n) ->
    vgeneration (dst g e) = from -> Znth n (make_fields g v) = FieldEdge e ->
    raw_mark (vlabel g (dst g e)) = true -> ~ vvalid base v ->
    no_dangling_dst base -> gc_graph_remset_semi_iso base g from to l ->
    gc_graph_remset_semi_iso
      base (labeledgraph_gen_dst g e (copied_vertex (vlabel g (dst g e)))) from to l.
Proof.
  intros from to base g l v n e Hneq Hsound_base Hsound_g Hto Hic Hdst_from
         Hfield Hdst_mark Hnot_base Hndd Hiso.
  pose proof Hsound_base as Hsound_base0.
  simpl in Hic. destruct Hic as [Hv_g [Hlen [Hv_mark Hv_tag]]].
  assert (Hd: DoubleNoDup l) by (now apply (remset_semi_iso_DoubleNoDup base g from to)).
  destruct Hiso as [Hcopy Hspec].
  pose proof Hcopy as Hcopy_all.
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto_spec [Hlabel Hpartial]]].
  destruct Hfrom as [Hfrom_nd Hfrom].
  destruct Hto_spec as [Hto_nd [Hto_valid Hto_gen]].
  unfold remset_partial_graph in Hpartial.
  destruct Hpartial as [Holdvalid [Hnonfrom_edges Hunmarked]].
  destruct Hsound_base as [Hvv_base [Hev_base [Hsrc_base _]]].
  destruct Hsound_g as [Hvv_g [Hev_g [Hsrc_g _]]].
  assert (Hf: from_l = map fst l) by
      (rewrite map_fst_split, Hsplit; reflexivity).
  assert (Ht: to_l = map snd l) by
      (rewrite map_snd_split, Hsplit; reflexivity).
  split.
  - intros v1 v2 Hin.
    specialize (Hcopy _ _ Hin).
    destruct Hcopy as [Hcopied [Hlabel_pair Hfields]].
    split; [exact Hcopied |]. split; [exact Hlabel_pair |].
    intros idx Hidx.
    specialize (Hfields _ Hidx).
    simpl. unfold updateEdgeFunc. if_tac; [|exact Hfields].
    red in H. subst e.
    apply make_fields_Znth_edge in Hfield; auto.
    inversion Hfield. subst v.
    rewrite <- H1 in *.
    assert (Hv1_base: vvalid base v1). {
      apply In_map_fst in Hin. rewrite map_fst_split, Hsplit, <- Hfrom in Hin.
      now destruct Hin as [_ [? _]].
    }
    assert (Hold_dst_in_from:
              dst g (v2, idx) = dst base (v1, idx) ->
              In (dst base (v1, idx)) from_l). {
      intros Hdst_eq. rewrite <- Hfrom. split.
      - rewrite <- Hdst_eq. exact Hdst_mark.
      - split.
        + apply (proj2 (Hvv_base _)).
          red in Hndd. apply (Hndd v1); auto.
          * apply (proj1 (Hvv_base _)). exact Hv1_base.
          * now rewrite get_edges_In.
        + rewrite <- Hdst_eq. exact Hdst_from.
    }
    destruct (V_EqDec (dst g (v2, idx)) (dst base (v1, idx)))
      as [Hdst_eq | Hdst_neq].
    + hnf in Hdst_eq. rewrite Hdst_eq.
      assert (Hin_from: In (dst base (v1, idx)) from_l) by
          (apply Hold_dst_in_from; exact Hdst_eq).
      rewrite Hf, In_map_fst_iff in Hin_from.
      destruct Hin_from as [b Hin_b].
      destruct (DoubleNoDup_list_bi_map _ _ _ Hd Hin_b) as [Hmap _].
      rewrite Hmap.
      apply Hcopy_all in Hin_b. destruct Hin_b as [? _]. subst b. now right.
    + destruct Hfields as [Hfields | Hfields].
      * exfalso. apply Hdst_neq. hnf. exact Hfields.
      * exfalso.
        destruct (InEither_dec (dst base (v1, idx)) l) as [Hin_either | Hnot_either].
        2: now rewrite list_bi_map_not_In in Hfields.
        red in Hin_either. rewrite Hsplit, in_app_iff in Hin_either.
        destruct Hin_either as [Hin_from | Hin_to].
        -- rewrite Hf, In_map_fst_iff in Hin_from.
           destruct Hin_from as [b Hin_b].
           destruct (DoubleNoDup_list_bi_map _ _ _ Hd Hin_b) as [Hmap _].
           rewrite Hmap in Hfields.
           rewrite <- Hfields in Hin_b.
           apply In_map_snd in Hin_b. rewrite <- Ht in Hin_b.
           apply Hto_gen in Hin_b. now rewrite Hdst_from in Hin_b.
        -- rewrite Hto_valid in Hin_to. destruct Hin_to as [_ Hnot_valid].
           apply Hnot_valid. apply (proj2 (Hvv_base _)).
           red in Hndd. apply (Hndd v1); auto.
           ++ apply (proj1 (Hvv_base _)). exact Hv1_base.
           ++ now rewrite get_edges_In.
  - rewrite Hsplit. split.
    + split; [exact Hfrom_nd |].
      intros v0. rewrite <- Hfrom.
      rewrite <- lgd_raw_mark_eq. reflexivity.
    + split.
      * split; [exact Hto_nd |]. split.
        -- intros v0. rewrite Hto_valid. reflexivity.
        -- exact Hto_gen.
      * split.
        -- intros v0 Hv0 Hnot_in.
           apply Hlabel; assumption.
        -- eapply remset_partial_graph_lgd; eauto.
           apply make_fields_Znth_edge in Hfield; auto.
           subst e. exact Hnot_base.
           unfold remset_partial_graph. split; [exact Holdvalid |].
           split; [exact Hnonfrom_edges | exact Hunmarked].
Qed.

Lemma lgd_remset_semi_iso_parts_mapped:
  forall (Partial1 Partial2:
            LGraph -> LGraph -> list (VType * VType) -> nat -> Prop)
         (from to: nat) (base g: LGraph) l e v,
    sound_gc_graph base ->
    evalid base e ->
    v = list_bi_map l (dst base e) ->
    gc_graph_remset_semi_iso_parts Partial1 base g from to l ->
    Partial2 base (labeledgraph_gen_dst g e v) l from ->
    gc_graph_remset_semi_iso_parts Partial2 base (labeledgraph_gen_dst g e v)
                                  from to l.
Proof.
  intros Partial1 Partial2 from to base g l e v Hsound_base Hevalid Hv Hiso
         Hpartial_new.
  destruct Hiso as [Hcopy Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
  destruct Hfrom as [Hfrom_nd Hfrom].
  destruct Hto as [Hto_nd [Hto_valid Hto_gen]].
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  split.
  - intros v1 v2 Hin.
    specialize (Hcopy _ _ Hin).
    destruct Hcopy as [Hcopied [Hlabel_pair Hfields]].
    split; [exact Hcopied |]. split; [exact Hlabel_pair |].
    intros idx Hidx.
    rewrite lgd_dst_old.
    + exact (Hfields idx Hidx).
    + intro Heq. subst e.
      assert (Hin_to: In v2 to_l) by
          (apply In_map_snd in Hin; now rewrite map_snd_split, Hsplit in Hin).
      rewrite Hto_valid in Hin_to.
      destruct Hin_to as [_ Hnot_valid].
      apply Hnot_valid.
      assert (Hge: graph_has_e base (v2, idx)) by
          (apply (proj1 (Hev_base _)); exact Hevalid).
      destruct Hge as [Hsrc_has _].
      apply (proj2 (Hvv_base _)). exact Hsrc_has.
  - rewrite Hsplit. split.
    + split; [exact Hfrom_nd |].
      intros v0. rewrite <- Hfrom.
      rewrite <- lgd_raw_mark_eq. reflexivity.
    + split.
      * split; [exact Hto_nd |]. split.
        -- intros v0. rewrite Hto_valid. reflexivity.
        -- exact Hto_gen.
      * split.
        -- intros v0 Hvalid Hnot_in.
           apply Hlabel; assumption.
        -- exact Hpartial_new.
Qed.

Lemma lgd_pending_remset_semi_iso_mapped:
  forall (from to: nat) (base g: LGraph) pending l item e v,
    sound_gc_graph base ->
    evalid base e ->
    evalid g e ->
    src g e = src base e ->
    vgeneration (fst e) <> from ->
    remset_item_records_edge item e ->
    v = list_bi_map l (dst base e) ->
    gc_graph_pending_remset_semi_iso base g from to (item :: pending) l ->
    gc_graph_pending_remset_semi_iso
      base (labeledgraph_gen_dst g e v) from to pending l.
Proof.
  intros from to base g pending l item e v Hsound_base Hevalid_base Hevalid_g
         Hsrc_g Hsrcgen Hitem Hv Hiso.
  assert (Hpartial_new:
            remset_partial_graph_pending
              base (labeledgraph_gen_dst g e v) l from pending). {
    eapply remset_partial_graph_pending_lgd_mapped; eauto.
    eapply gc_graph_remset_semi_iso_parts_partial; exact Hiso.
  }
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 =>
               remset_partial_graph_pending base0 g0 l0 from0 (item :: pending))
            base g from to l) in Hiso.
  change (gc_graph_remset_semi_iso_parts
            (fun base0 g0 l0 from0 =>
               remset_partial_graph_pending base0 g0 l0 from0 pending)
            base (labeledgraph_gen_dst g e v) from to l).
  eapply lgd_remset_semi_iso_parts_mapped; eauto.
Qed.

Definition special_edge_cond (g: LGraph) (p: forward_p_type): Prop :=
  match p with
  | FwdPntExtr _ => True
  | FwdPntIntr (InteriorVertexPos v _) => ~ vvalid g v
  end.

Lemma exterior_map_id: exterior_map id = id.
Proof. extensionality x. unfold exterior_map. now destruct x. Qed.

Lemma roots_map_map_cons: forall a l (roots: roots_t),
    DoubleNoDup (a :: l) ->
    roots_map (a :: l) roots = roots_map [a] (roots_map l roots).
Proof.
  intros. induction roots; simpl; auto. rewrite IHroots. f_equal. destruct a0; simpl; trivial.
  f_equal. clear IHroots. destruct (InEither_dec v (a :: l)).
  - destruct a as [a b]. rewrite DoubleNoDup_cons_iff in H.
    destruct H as [? [? [? ?]]]. rewrite InEither_cons_iff in i. destruct i.
    + red in H3. simpl in H3. destruct H3.
      * subst v. rewrite (list_bi_map_not_In l a); auto.
        unfold list_bi_map. simpl. now rewrite if_true; [rewrite if_true|].
      * subst v. rewrite (list_bi_map_not_In l b); auto.
        unfold list_bi_map. simpl. rewrite if_false; [rewrite if_true|]; [rewrite if_false| | ]; try easy.
        rewrite if_true; easy.
    + unfold list_bi_map at 1. simpl. rewrite if_false.
      2: unfold equiv; intro; now subst. rewrite if_false.
      2: unfold equiv; intro; now subst. fold (list_bi_map l v).
      remember (list_bi_map l v) as v'. assert (InEither v' l). {
        subst v'. apply list_bi_map_In in H3. destruct H3 as [k0 [v0 [? ?]]].
        apply In_InEither in H3. destruct H3.
        destruct H4 as [[? ?] | [? ?]]; now rewrite H6. }
      unfold list_bi_map. simpl. rewrite if_false.
      2: unfold equiv; intro; now subst. rewrite if_false.
      2: unfold equiv; intro; now subst. easy.
  - rewrite list_bi_map_not_In; auto. assert (~ InEither v l). {
      intro. apply n. rewrite InEither_cons_iff. now right. }
    rewrite (list_bi_map_not_In _ _ H0). assert (~ InEither v [a]). {
      intro. apply n. rewrite InEither_cons_iff. left. unfold InEither in H1.
      unfold IsEither. destruct a as [a b]. simpl in *. intuition. }
    rewrite (list_bi_map_not_In _ _ H1). easy.
Qed.

Lemma roots_map_nil: forall (roots: roots_t), roots_map [] roots = roots.
Proof. intros. unfold roots_map. now rewrite list_bi_map_nil, exterior_map_id, map_id_eq. Qed.

Lemma roots_map_app: forall l roots1 roots2,
    roots_map l (roots1 ++ roots2) = roots_map l roots1 ++ roots_map l roots2.
Proof.
  intros. unfold roots_map. apply map_app.
Qed.

Lemma roots_map_map_app: forall l1 l2 (roots: roots_t),
    DoubleNoDup (l1 ++ l2) ->
    roots_map (l1 ++ l2) roots = roots_map l1 (roots_map l2 roots).
Proof.
  induction l1; intros; simpl.
  - rewrite roots_map_nil. reflexivity.
  - pose proof H. rewrite DoubleNoDup_app_iff in H0. destruct H0 as [H0 _]. simpl in H.
    rewrite (roots_map_map_cons a l1), (roots_map_map_cons a (l1 ++ l2)); auto. f_equal.
    apply IHl1. eapply DoubleNoDup_cons_tl; eassumption.
Qed.

Lemma roots_map_the_same: forall l (roots: roots_t),
    (forall r, In (ExteriorVertex r) roots -> ~ InEither r l) -> roots_map l roots = roots.
Proof.
  do 2 intro. induction roots; intros; simpl; auto. rewrite IHroots.
  - f_equal. destruct a; simpl; auto. assert (~ InEither v l). {
      apply H. now left. } now rewrite list_bi_map_not_In.
  - intros. apply H. now right.
Qed.

Definition rf_list_relation (l: list (VType * VType)) (p: forward_p_type) (n: nat): Prop :=
  forall v, p = FwdPntExtr (ExteriorVertex v) -> vgeneration v = n -> In v (map fst l).

Definition semi_map (l: list (VType * VType)) (p: forward_p_type): forward_p_type :=
  match p with
  | FwdPntExtr extr => FwdPntExtr (exterior_map (list_map l) extr)
  | FwdPntIntr _ => p
  end.

Lemma roots_map_bijective: forall l,
    DoubleNoDup l -> bijective (roots_map l) (roots_map l).
Proof. intros. now apply bijective_map, bijective_exterior_map, bijective_list_bi_map. Qed.

Lemma roots_map_new_copied_eq:
  forall (to : nat) (v : VType) (g : LGraph) (roots : roots_t),
    roots_graph_compatible roots g ->
    roots_have_no_gen roots (vgeneration v) ->
    roots = roots_map [(v, new_copied_v g to)] roots.
Proof.
  intros to v g roots Hg Hr. rewrite roots_map_the_same; auto. intros. red in Hr.
  specialize (Hr _ H). intro. hnf in H0. simpl in H0. destruct H0 as [? | [? | ?]]; auto.
  -- now rewrite H0 in Hr.
  -- red in Hg. rewrite Forall_forall in Hg.
     rewrite (filter_proj_In_iff exterior_proj_vertex_spec) in H. apply Hg in H.
     rewrite <- H0 in H. unfold new_copied_v in H. destruct H.
     simpl in H1. red in H1. lia.
Qed.

Lemma remset_semi_iso_In_map_fst: forall g1 g2 from to l,
    gc_graph_remset_semi_iso g1 g2 from to l ->
    forall v, In v (map fst l) -> vgeneration v = from.
Proof.
  intros. destruct H as [_ Hspec]. destruct (split l) eqn:Heqp.
  destruct Hspec as [[_ Hfrom] _].
  rewrite map_fst_split, Heqp in H0. simpl in H0. rewrite <- Hfrom in H0.
  now destruct H0 as [_ [_ ?]].
Qed.

Lemma remset_semi_iso_marked_in_map_fst: forall g1 g2 from to l v,
    from <> to ->
    vertex_valid g1 ->
    gc_graph_remset_semi_iso g1 g2 from to l ->
    raw_mark (vlabel g2 v) = true ->
    vvalid g2 v ->
    vgeneration v = from ->
    In v (map fst l).
Proof.
  intros g1 g2 from to l v Hneq Hvv Hiso Hmark Hvalid Hgen.
  destruct Hiso as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [Hto_valid Hto_gen]] _]].
  rewrite map_fst_split, Hsplit.
  destruct (vvalid_lcm g1 v Hvv) as [Hvalid_base | Hnot_base].
  - rewrite <- Hfrom. split; [exact Hmark | split; assumption].
  - exfalso.
    assert (Hin_to: In v to_l) by (rewrite Hto_valid; split; assumption).
    specialize (Hto_gen _ Hin_to). lia.
Qed.

Lemma pending_remset_semi_iso_marked_in_map_fst:
  forall g1 g2 from to pending l v,
    from <> to ->
    vertex_valid g1 ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l ->
    raw_mark (vlabel g2 v) = true ->
    vvalid g2 v ->
    vgeneration v = from ->
    In v (map fst l).
Proof.
  intros g1 g2 from to pending l v Hneq Hvv Hiso Hmark Hvalid Hgen.
  destruct Hiso as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [Hto_valid Hto_gen]] _]].
  rewrite map_fst_split, Hsplit.
  destruct (vvalid_lcm g1 v Hvv) as [Hvalid_base | Hnot_base].
  - rewrite <- Hfrom. split; [exact Hmark | split; assumption].
  - exfalso.
    assert (Hin_to: In v to_l) by (rewrite Hto_valid; split; assumption).
    specialize (Hto_gen _ Hin_to). lia.
Qed.

Lemma pending_remset_semi_iso_marked_list_bi_map:
  forall g1 g2 from to pending l v,
    from <> to ->
    vertex_valid g1 ->
    gc_graph_pending_remset_semi_iso g1 g2 from to pending l ->
    raw_mark (vlabel g2 v) = true ->
    vvalid g2 v ->
    vgeneration v = from ->
    list_bi_map l v = copied_vertex (vlabel g2 v).
Proof.
  intros g1 g2 from to pending l v Hneq Hvv Hiso Hmark Hvalid Hgen.
  assert (Hin_fst: In v (map fst l)) by
      (eapply pending_remset_semi_iso_marked_in_map_fst; eauto).
  rewrite In_map_fst_iff in Hin_fst.
  destruct Hin_fst as [v2 Hin_pair].
  assert (Hdd: DoubleNoDup l) by
      (eapply (pending_remset_semi_iso_DoubleNoDup g1 g2 from to pending l);
       eauto).
  destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hin_pair) as [Hmap _].
  rewrite Hmap.
  destruct Hiso as [Hcopy _].
  specialize (Hcopy _ _ Hin_pair) as [Hcopied _].
  now subst v2.
Qed.

Lemma old_nonfrom_edges_mapped_pending_current_edge:
  forall g1 g2 l from pending e,
    old_nonfrom_edges_mapped_pending g1 g2 l from pending ->
    evalid g1 e ->
    vgeneration (fst e) <> from ->
    evalid g2 e /\ src g2 e = src g1 e.
Proof.
  unfold old_nonfrom_edges_mapped_pending.
  intros g1 g2 l from pending e Hedges Hevalid Hsrcgen.
  destruct (Hedges e Hevalid Hsrcgen) as [Hpending | Hmapped].
  - destruct Hpending as [_ [He_g [Hsrc_g _]]].
    split; assumption.
  - destruct Hmapped as [He_g [Hsrc_g _]].
    split; assumption.
Qed.

Lemma pending_remset_semi_iso_old_nonfrom_field_evalid_base:
  forall base g from to pending l v i e,
    sound_gc_graph base ->
    gc_graph_pending_remset_semi_iso base g from to pending l ->
    vvalid base v ->
    vgeneration v <> from ->
    0 <= i < Zlength (raw_fields (vlabel g v)) ->
    Znth i (make_fields g v) = FieldEdge e ->
    evalid base e.
Proof.
  intros base g from to pending l v i e Hsound_base Hsemi Hvbase Hgen Hlen Hfield.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [_ [Hlabel _]]].
  assert (Hnot_in: ~ In v from_l). {
    intro Hin. rewrite <- Hfrom in Hin.
    destruct Hin as [_ [_ Hfrom_gen]]. contradiction.
  }
  assert (Hlabel_v: vlabel base v = vlabel g v) by
      (apply Hlabel; assumption).
  assert (Hfield_base: Znth i (make_fields base v) = FieldEdge e) by
      (unfold make_fields; rewrite Hlabel_v; exact Hfield).
  apply make_fields_Znth_edge in Hfield; auto.
  subst e.
  apply (proj2 (Hev_base _)).
  split.
  - apply (proj1 (Hvv_base _)); exact Hvbase.
  - rewrite get_edges_In_iff.
    rewrite <- Hfield_base.
    apply Znth_In.
    rewrite make_fields_eq_length.
    simpl. now rewrite Hlabel_v.
Qed.

Lemma pending_remset_semi_iso_old_nonfrom_edge_dst_base:
  forall base g from to pending l e,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso base g from to pending l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    dst g e = dst base e /\
    vvalid base (dst base e) /\
    vgeneration (dst base e) = from.
Proof.
  intros base g from to pending l e Hneq Hsound_base Hndd_base Hsemi
         Hevalid Hsrcgen Hdstgen.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  assert (Hdd: DoubleNoDup l) by
      (eapply (pending_remset_semi_iso_DoubleNoDup base g from to pending l);
       eauto).
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [Hto_valid Hto_gen]] [_ Hpartial]]].
  unfold remset_partial_graph_pending in Hpartial.
  destruct Hpartial as [_ [Hedges _]].
  specialize (Hedges e Hevalid Hsrcgen).
  assert (Hge: graph_has_e base e) by
      (apply (proj1 (Hev_base _)); exact Hevalid).
  assert (Hdst_base_has: graph_has_v base (dst base e)) by
      (destruct Hge as [Hsrc_has Hfield];
       apply (Hndd_base (fst e)); assumption).
  assert (Hdst_base_valid: vvalid base (dst base e)) by
      (apply (proj2 (Hvv_base _)); exact Hdst_base_has).
  destruct Hedges as [Hpending | Hmapped].
  - destruct Hpending as [_ [_ [_ [Hdst_eq Hdst_from]]]].
    split; [exact Hdst_eq |].
    split; [exact Hdst_base_valid | exact Hdst_from].
  - destruct Hmapped as [_ [_ Hdst_map]].
    destruct (in_dec equiv_dec (dst base e) from_l) as [Hin_from | Hnot_from].
    + assert (Hfrom_l: from_l = map fst l) by
          (rewrite map_fst_split, Hsplit; reflexivity).
      rewrite Hfrom_l in Hin_from.
      rewrite In_map_fst_iff in Hin_from.
      destruct Hin_from as [dst_copy Hpair].
      destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hpair) as [Hmap _].
      rewrite Hmap in Hdst_map.
      assert (Hin_to: In dst_copy to_l) by
          (apply In_map_snd in Hpair;
           rewrite map_snd_split, Hsplit in Hpair; exact Hpair).
      specialize (Hto_gen _ Hin_to).
      rewrite Hdst_map in Hdstgen. lia.
    + assert (~ In (dst base e) to_l) as Hnot_to. {
        intro Hin_to. rewrite Hto_valid in Hin_to.
        destruct Hin_to as [_ Hnot_valid]. contradiction.
      }
      assert (~ InEither (dst base e) l) as Hnot_either. {
        unfold InEither. rewrite Hsplit, in_app_iff. tauto.
      }
      rewrite list_bi_map_not_In in Hdst_map by exact Hnot_either.
      split; [exact Hdst_map |].
      split; [exact Hdst_base_valid |].
      now rewrite Hdst_map in Hdstgen.
Qed.

Lemma pending_remset_semi_iso_marked_edge_map:
  forall base g from to pending l e,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso base g from to pending l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    raw_mark (vlabel g (dst g e)) = true ->
    list_bi_map l (dst base e) = copied_vertex (vlabel g (dst g e)).
Proof.
  intros base g from to pending l e Hneq Hsound_base Hndd_base Hsemi
         Hevalid Hsrcgen Hdstgen Hmark.
  pose proof Hsound_base as Hsound_base0.
  destruct Hsound_base0 as [Hvv_base _].
  destruct (pending_remset_semi_iso_old_nonfrom_edge_dst_base
              base g from to pending l e Hneq Hsound_base Hndd_base Hsemi
              Hevalid Hsrcgen Hdstgen)
    as [Hdst_eq [Hdst_valid_base Hdst_base_gen]].
  assert (Holdvalid: old_vertices_valid base g). {
    pose proof Hsemi as Hsemi0.
    destruct Hsemi0 as [_ Hspec].
    destruct (split l) as [from_l to_l].
    destruct Hspec as [_ [_ [_ Hpartial]]].
    exact (proj1 Hpartial).
  }
  assert (Hdst_valid_g: vvalid g (dst base e)) by
      (apply Holdvalid; exact Hdst_valid_base).
  rewrite Hdst_eq in Hmark.
  rewrite Hdst_eq.
  eapply (pending_remset_semi_iso_marked_list_bi_map
            base g from to pending l (dst base e)); eauto.
Qed.

Lemma remset_interior_nonedge_records_no_current_edge:
  forall g v pos f e,
    sound_gc_graph g ->
    0 <= pos < Zlength (raw_fields (vlabel g v)) ->
    Znth pos (make_fields g v) = f ->
    (forall e0, f <> FieldEdge e0) ->
    remset_item_records_edge (RemSetInterior (InteriorVertexPos v pos)) e ->
    ~ evalid g e.
Proof.
  intros g v pos f e Hsound Hpos Hfield Hnonedge Hrec Hevalid.
  destruct Hsound as [_ [Hev _]].
  assert (Hge: graph_has_e g e) by
      (apply (proj1 (Hev _)); exact Hevalid).
  destruct Hrec as [Hv Hidx].
  destruct e as [ev idx]. simpl in *. subst ev.
  destruct Hge as [_ Hin_edge].
  rewrite get_edges_In_iff in Hin_edge.
  apply In_Znth in Hin_edge.
  destruct Hin_edge as [j [Hj HZnth]].
  assert (Hj_raw: 0 <= j < Zlength (raw_fields (vlabel g v))) by
      (rewrite <- make_fields_eq_length; exact Hj).
  pose proof (make_fields_Znth_edge g v j (v, idx) Hj_raw HZnth) as Heq.
  inversion Heq. subst idx.
  assert (pos = j) by
      (rewrite Hidx, Z2Nat.id by lia; reflexivity).
  subst pos.
  rewrite Z2Nat.id in Hfield by lia.
  simpl in HZnth.
  rewrite Hfield in HZnth.
  exact (Hnonedge _ HZnth).
Qed.

Lemma remset_interior_records_current_edge_field:
  forall g v pos e,
    sound_gc_graph g ->
    0 <= pos < Zlength (raw_fields (vlabel g v)) ->
    remset_item_records_edge (RemSetInterior (InteriorVertexPos v pos)) e ->
    evalid g e ->
    Znth pos (make_fields g v) = FieldEdge e.
Proof.
  intros g v pos e Hsound Hpos Hrec Hevalid.
  destruct Hsound as [_ [Hev _]].
  assert (Hge: graph_has_e g e) by
      (apply (proj1 (Hev _)); exact Hevalid).
  destruct Hrec as [Hv Hidx].
  destruct e as [ev idx]. simpl in *. subst ev.
  destruct Hge as [_ Hin_edge].
  rewrite get_edges_In_iff in Hin_edge.
  apply In_Znth in Hin_edge.
  destruct Hin_edge as [j [Hj HZnth]].
  assert (Hj_raw: 0 <= j < Zlength (raw_fields (vlabel g v))) by
      (rewrite <- make_fields_eq_length; exact Hj).
  pose proof (make_fields_Znth_edge g v j (v, idx) Hj_raw HZnth) as Heq.
  inversion Heq. subst idx.
  assert (pos = j) by
      (rewrite Hidx, Z2Nat.id by lia; reflexivity).
  subst pos.
  rewrite Z2Nat.id by lia.
  simpl in HZnth.
  exact HZnth.
Qed.

Lemma remset_semi_iso_old_nonfrom_edge_dst_base:
  forall base g from to l e,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base g from to l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    dst g e = dst base e /\
    vvalid base (dst base e) /\
    vgeneration (dst base e) = from /\
    raw_mark (vlabel g (dst base e)) <> true.
Proof.
  intros base g from to l e Hneq Hsound_base Hndd_base Hsemi
         Hevalid Hsrcgen Hdstgen.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  pose proof Hsemi as Hsemi0.
  assert (Hdd: DoubleNoDup l) by
      (eapply remset_semi_iso_DoubleNoDup; [exact Hneq | exact Hsemi0]).
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [Hto_valid Hto_gen]] [_ Hpartial]]].
  unfold remset_partial_graph in Hpartial.
  destruct Hpartial as [_ [Hedges _]].
  specialize (Hedges e Hevalid Hsrcgen).
  destruct Hedges as [_ [_ Hdst_map]].
  assert (Hge: graph_has_e base e) by
      (apply (proj1 (Hev_base _)); exact Hevalid).
  assert (Hdst_base_has: graph_has_v base (dst base e)) by
      (destruct Hge as [Hsrc_has Hfield];
       apply (Hndd_base (fst e)); assumption).
  assert (Hdst_base_valid: vvalid base (dst base e)) by
      (apply (proj2 (Hvv_base _)); exact Hdst_base_has).
  destruct (in_dec equiv_dec (dst base e) from_l) as [Hin_from | Hnot_from].
  - assert (Hfrom_l: from_l = map fst l) by
        (rewrite map_fst_split, Hsplit; reflexivity).
    rewrite Hfrom_l in Hin_from.
    rewrite In_map_fst_iff in Hin_from.
    destruct Hin_from as [dst_copy Hpair].
    destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hpair) as [Hmap _].
    rewrite Hmap in Hdst_map.
    assert (Hin_to: In dst_copy to_l) by
        (apply In_map_snd in Hpair; rewrite map_snd_split, Hsplit in Hpair; exact Hpair).
    specialize (Hto_gen _ Hin_to).
    rewrite Hdst_map in Hdstgen. lia.
  - assert (~ In (dst base e) to_l) as Hnot_to. {
      intro Hin_to. rewrite Hto_valid in Hin_to.
      destruct Hin_to as [_ Hnot_valid]. contradiction.
    }
    assert (~ InEither (dst base e) l) as Hnot_either. {
      unfold InEither. rewrite Hsplit, in_app_iff. tauto.
    }
    rewrite list_bi_map_not_In in Hdst_map by exact Hnot_either.
    split; [exact Hdst_map |].
    split; [exact Hdst_base_valid |].
    rewrite Hdst_map in Hdstgen.
    split; [exact Hdstgen |].
    intro Hmark.
    apply Hnot_from. rewrite <- Hfrom.
    split; [exact Hmark | split; assumption].
Qed.

Lemma remset_semi_iso_no_marked_old_nonfrom_edge:
  forall base g from to l e,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base g from to l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    raw_mark (vlabel g (dst g e)) = true ->
    False.
Proof.
  intros base g from to l e Hneq Hsound_base Hndd_base Hsemi
         Hevalid Hsrcgen Hdstgen Hmark.
  destruct (remset_semi_iso_old_nonfrom_edge_dst_base
              base g from to l e Hneq Hsound_base Hndd_base Hsemi
              Hevalid Hsrcgen Hdstgen) as [Hdst_eq [_ [_ Hnot_mark]]].
  rewrite Hdst_eq in Hmark.
  exact (Hnot_mark Hmark).
Qed.

Lemma remset_semi_iso_no_unmarked_old_nonfrom_edge:
  forall base g from to l e,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base g from to l ->
    no_unmarked_old_nonfrom_dst base g from ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    raw_mark (vlabel g (dst g e)) = false ->
    False.
Proof.
  intros base g from to l e Hneq Hsound_base Hndd_base Hsemi Hclosed
         Hevalid Hsrcgen Hdstgen Hmark.
  destruct (remset_semi_iso_old_nonfrom_edge_dst_base
              base g from to l e Hneq Hsound_base Hndd_base Hsemi
              Hevalid Hsrcgen Hdstgen) as [Hdst_eq [_ [Hdst_base_gen _]]].
  eapply Hclosed; eauto.
  rewrite <- Hdst_eq. exact Hmark.
Qed.

Lemma fr_O_remset_semi_iso:
  forall (from to : nat) (p : forward_p_type) (base g1 g2 : LGraph) l1,
    from <> to -> sound_gc_graph base -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    gc_graph_remset_semi_iso base g1 from to l1 -> forward_p_compatible' p g1 from ->
    no_dangling_dst base -> no_dangling_dst g1 -> special_edge_cond base p ->
    no_unmarked_old_nonfrom_dst base g1 from ->
    forward_relation from to O (forward_p2forward_t p g1) g1 g2 ->
    exists l2, gc_graph_remset_semi_iso base g2 from to (l2 ++ l1) /\
            upd_fwd from to g1 p = semi_map (l2 ++ l1) p /\
            rf_list_relation (l2 ++ l1) p from /\
            (forall roots, roots_graph_compatible roots g1 ->
                      roots_have_no_gen roots from ->
                      roots = roots_map l2 roots).
Proof.
  intros from to p base g1 g2 l1 Hneq Hsound_base Hsound_g1 Hto Hsemi
         Hcompat Hndd_base Hndd_g1 Hspecial Hclosed Hfr.
  pose proof Hsound_base as Hsound_base0.
  pose proof Hsound_g1 as Hsound_g1_0.
  assert (Hdd: DoubleNoDup l1) by (eapply remset_semi_iso_DoubleNoDup; eauto).
  assert (Hbij: bijective (roots_map l1) (roots_map l1)) by
      (now apply roots_map_bijective).
  assert (Hvv_base: vertex_valid base) by (destruct Hsound_base as [Hvv _]; exact Hvv).
  assert (Hvv_g1: vertex_valid g1) by (destruct Hsound_g1 as [Hvv _]; exact Hvv).
  destruct p; simpl in Hcompat, Hfr.
  - destruct extr as [z | gp | v]; simpl in *; inversion Hfr; subst;
      [exists []; simpl..|].
    + split; [|split; [|split]]; auto. 2: now intros; rewrite roots_map_nil.
      hnf. intros. inversion H.
    + split; [|split; [|split]]; auto. 2: now intros; rewrite roots_map_nil.
      hnf. intros. inversion H.
    + split; [|split; [|split]]; auto. 3: now intros; rewrite roots_map_nil.
      * unfold update_vertex. destruct (Nat.eq_dec (vgeneration v) from) as [Hvfrom | _].
        1: contradiction. do 2 f_equal. rewrite list_map_not_In; auto.
        intro Hin. eapply remset_semi_iso_In_map_fst in Hin; eauto.
      * hnf. intros. inversion H. subst. contradiction.
    + split; auto.
      unfold update_vertex.
      destruct (Nat.eq_dec (vgeneration v) (vgeneration v)) as [_ | Hneq'].
      2: contradiction. rewrite H2. destruct (split l1) as [ll lr] eqn:Hsplit.
      assert (Hvvalid_g1: vvalid g2 v). {
        red in Hvv_g1. rewrite Hvv_g1. exact Hcompat.
      }
      assert (Hin_fst: In v (map fst l1)). {
        eapply remset_semi_iso_marked_in_map_fst with
          (g1 := base) (g2 := g2) (from := vgeneration v) (to := to); eauto.
      }
      split; [|split].
      * do 2 f_equal. symmetry. apply list_map_In.
        -- rewrite map_fst_split, Hsplit. simpl in Hdd.
           red in Hdd. rewrite Hsplit in Hdd. apply NoDup_app_l in Hdd. exact Hdd.
        -- rewrite In_map_fst_iff in Hin_fst.
           destruct Hin_fst as [b Hin_b].
           destruct (Hsemi) as [Hcopy _].
           destruct (Hcopy _ _ Hin_b) as [Hcopied _]. now subst b.
      * hnf. intros. inversion H. subst. assumption.
      * intros. now rewrite roots_map_nil.
    + exists [(v, (new_copied_v g1 to))]. simpl. split; [|split; [|split]].
      * apply lcv_remset_semi_iso; auto.
        red in Hvv_g1. rewrite Hvv_g1. exact Hcompat.
      * unfold update_vertex.
        destruct (Nat.eq_dec (vgeneration v) (vgeneration v)) as [_ | Hneq'].
        2: contradiction. rewrite H1. do 2 f_equal. symmetry. apply list_map_In.
        2: simpl; now left. simpl. constructor.
        -- intro Hin. rewrite map_fst_split in Hin.
           destruct (split l1) as [ll lr] eqn:Hsplit. simpl in Hin.
           destruct Hsemi as [_ Hspec]. rewrite Hsplit in Hspec.
           destruct Hspec as [[_ Hfrom] _]. rewrite <- Hfrom in Hin.
           destruct Hin as [Hmark _]. rewrite H1 in Hmark. discriminate.
        -- apply DoubleNoDup_fst. exact Hdd.
      * hnf. intros. inversion H. subst. simpl. left. reflexivity.
      * apply roots_map_new_copied_eq.
  - destruct intr as [v i]. simpl in *.
    destruct Hcompat as [Hv_g1 [Hlen [Hv_mark Hv_tag]]].
    destruct (Znth i (make_fields g1 v)) eqn:Heqf; simpl in Hfr; inversion Hfr; subst;
      try (exists []; split; [|split; [|split]]; [easy ..| now intros; rewrite roots_map_nil]).
    + exists []. split; [|split; [|split]]; [auto ..| now intros; rewrite roots_map_nil].
      * eapply lgd_remset_semi_iso; eauto. simpl. easy.
      * simpl; intros v0 Hv Heq; inversion Hv.
    + exists [(dst g1 e, new_copied_v g1 to)]. simpl.
      split; [|split; [|split]];
        [|reflexivity | intros v0 Hv Heq; inversion Hv | apply roots_map_new_copied_eq].
      cut (gc_graph_remset_semi_iso base (lgraph_copy_v g1 (dst g1 e) to)
             (vgeneration (dst g1 e)) to ((dst g1 e, new_copied_v g1 to) :: l1)).
      * intros Hm. assert (Hfn: fst e <> new_copied_v g1 to). {
          apply make_fields_Znth_edge in Heqf; auto. subst e. simpl.
          destruct v as [gen idx]. red in Hv_g1. simpl in Hv_g1. destruct Hv_g1. red in H0.
          intro Hbad. unfold new_copied_v in Hbad. inversion Hbad. subst gen idx.
          lia.
        }
        eapply (lgd_remset_semi_iso _ _ _ _ _ v i e) in Hm; eauto.
        -- subst new_g. simpl dst in Hm. rewrite pcv_dst_old in Hm; auto.
           simpl in Hm. rewrite ucov_copied_vertex in Hm. assumption.
        -- now apply lcv_sound.
        -- now rewrite <- lcv_graph_has_gen.
        -- Opaque lgraph_copy_v. simpl. Transparent lgraph_copy_v.
           split; [|split; [|split; [|split]]]; auto.
           ++ rewrite lcv_graph_has_v_iff; auto.
           ++ rewrite <- lcv_raw_fields; auto.
           ++ rewrite <- lcv_raw_mark by
                  (auto; intro Hbad; subst v; destruct Hv_tag as [_ Hgen_neq];
                   contradiction).
              exact Hv_mark.
           ++ rewrite <- lcv_raw_tag by
                  (auto; intro Hbad; subst v; destruct Hv_tag as [_ Hgen_neq];
                   contradiction).
              destruct Hv_tag as [Htag _]. exact Htag.
           ++ destruct Hv_tag as [_ Hgen_neq]. exact Hgen_neq.
        -- simpl. rewrite pcv_dst_old; auto.
        -- unfold lgraph_copy_v. rewrite lmc_make_fields, lacv_make_fields_not_eq.
           1: easy. apply make_fields_Znth_edge in Heqf; auto. now subst e.
        -- simpl dst. rewrite pcv_dst_old; auto. apply lcv_raw_mark_old.
      * apply lcv_remset_semi_iso; auto.
        red in Hvv_g1. rewrite Hvv_g1. red in Hndd_g1. apply (Hndd_g1 v); auto.
        rewrite get_edges_In_iff. rewrite <- Heqf. apply Znth_In.
        now rewrite make_fields_eq_length.
Qed.

Lemma fr_O_no_unmarked_old_nonfrom_dst_t:
  forall base from to p g g',
    from <> to ->
    forward_relation from to O p g g' ->
    no_unmarked_old_nonfrom_dst base g from ->
    no_unmarked_old_nonfrom_dst base g' from.
Proof.
  intros base from to p g g' Hneq Hfr Hclosed.
  destruct p; inversion Hfr; subst; auto;
    try solve [eapply no_unmarked_old_nonfrom_dst_lcv; eauto];
    try solve [eapply no_unmarked_old_nonfrom_dst_lgd; eauto];
    eapply no_unmarked_old_nonfrom_dst_lgd;
    eapply no_unmarked_old_nonfrom_dst_lcv; eauto.
Qed.

Definition quasi_roots_map
           (roots: roots_t) (l: list (VType * VType)): roots_t :=
  map (exterior_map (list_map l)) roots.

Lemma remset_semi_iso_In_map_snd: forall (g1 g2 : LGraph) (from to : nat) l,
  gc_graph_remset_semi_iso g1 g2 from to l ->
  forall v : VType, In v (map snd l) -> ~ vvalid g1 v.
Proof.
  intros. destruct H as [_ Hspec]. destruct (split l) eqn:Heqp.
  destruct Hspec as [_ [[_ [Hto _]] _]].
  rewrite map_snd_split, Heqp in H0. simpl in H0.
  rewrite Hto in H0. now destruct H0.
Qed.

Lemma roots_graph_compatible_app: forall roots1 roots2 g,
   roots_graph_compatible (roots1 ++ roots2) g <->
   roots_graph_compatible roots1 g /\ roots_graph_compatible roots2 g.
Proof.
 intros.
 unfold roots_graph_compatible.
 rewrite filter_proj_app.
 apply Forall_app_iff.
Qed.

Lemma frl_remset_semi_iso:
  forall (from to : nat) base l1 (roots1 roots2: roots_t) (g1 g2 : LGraph),
    from <> to -> sound_gc_graph base -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_graph_compatible roots1 g1 ->
    no_dangling_dst base -> no_dangling_dst g1 -> copy_compatible g1 ->
    gc_graph_remset_semi_iso base g1 from to l1 ->
    no_unmarked_old_nonfrom_dst base g1 from ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    exists l2, gc_graph_remset_semi_iso base g2 from to (l2 ++ l1)
              /\ roots2 = quasi_roots_map roots1 (l2 ++ l1).
Proof.
  intros from to base l1 roots1 roots2 g1 g2 Hneq Hsound_base Hsound_g1 Hto
         Hroots Hndd_base Hndd_g1 Hcopy Hsemi Hclosed Hfrr.
  revert base l1 Hsound_base Hsound_g1 Hto Hroots Hndd_base Hndd_g1
         Hcopy Hsemi Hclosed.
  induction Hfrr; intros.
  - exists nil. simpl. auto.
  - assert (Hfp: forward_p_compatible' (FwdPntExtr r) g1 from). {
      simpl. destruct r; simpl; auto. apply rgc_cons_vertex in Hroots. assumption.
    }
    destruct (fr_O_remset_semi_iso from to (FwdPntExtr r) base g1 g2 l1)
      as [l2 [Hsemi2 [Hupd [Hrf Hroots_id]]]]; simpl; auto.
    destruct (IHHfrr base (l2 ++ l1)) as [l3 [Hsemi3 Hroots3]]; auto.
    + eapply fr_O_sound; eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_roots_graph_compatible; eauto.
      now apply roots_graph_compatible_inv in Hroots.
    + eapply fr_O_no_dangling_dst' with (p := FwdPntExtr r); eauto.
    + eapply fr_copy_compatible; eauto.
    + eapply fr_O_no_unmarked_old_nonfrom_dst_t; eauto.
    + exists (l3 ++ l2). rewrite <- app_assoc. split; auto. subst roots2. f_equal.
      inversion Hupd as [Hupd_exterior]. clear Hupd. rewrite Hupd_exterior.
      unfold exterior_map. destruct r; auto.
      f_equal. assert (DoubleNoDup (l3 ++ l2 ++ l1))
        by (eapply remset_semi_iso_DoubleNoDup; eauto).
      apply list_map_DoubleNoDup_incl_eq; auto.
      intros. apply Hrf; auto. eapply remset_semi_iso_In_map_fst; eauto.
Qed.

Lemma svfl_remset_semi_iso:
  forall from to v l l1 base g2 g3 roots,
    from <> to -> sound_gc_graph base -> sound_gc_graph g2 -> graph_has_gen g2 to ->
    roots_graph_compatible roots g2 ->
    no_dangling_dst base -> no_dangling_dst g2 -> roots_have_no_gen roots from ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g2 v)))%nat) ->
    ~ vvalid base v -> vvalid g2 v -> raw_mark (vlabel g2 v) = false ->
    raw_tag (vlabel g2 v) < NO_SCAN_TAG ->
    vgeneration v <> from -> copy_compatible g2 ->
    gc_graph_remset_semi_iso base g2 from to l1 ->
    no_unmarked_old_nonfrom_dst base g2 from ->
    scan_vertex_for_loop from to v l g2 g3 ->
    exists l2, gc_graph_remset_semi_iso base g3 from to (l2 ++ l1) /\
               roots = roots_map l2 roots.
Proof.
  pose (H3:=True).
  do 3 intro. induction l; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? NOSCAN; intros;
    inversion H16; subst; clear H16.
  - exists []. simpl. split; auto. now rewrite roots_map_nil.
  - pose proof H19.
    assert (He: forward_p2forward_t (FwdPntIntr (InteriorVertexPos v (Z.of_nat a))) g2 =
                interior2forward (InteriorVertexPos v (Z.of_nat a)) g2) by easy.
    rewrite <- He in H19.
    assert (interior_compatible g2 from (InteriorVertexPos v (Z.of_nat a))). {
      simpl. destruct H1. red in H1. rewrite <- H1. intuition auto with *.
      rewrite Zlength_correct. apply inj_lt, H8. now left. }
    eapply (fr_O_remset_semi_iso _ _ _ base) in H19; eauto.
    destruct H19 as [l3 [? [_ [_ ?]]]]. simpl in H19.
    assert (Hsound_g0: sound_gc_graph g0) by (eapply fr_O_sound; eauto).
    assert (graph_has_v g2 v) by (destruct H1; red in H1; now rewrite <- H1).
    eapply (IHl (l3 ++ l1) base) in H22; eauto.
    + destruct H22 as [l2 [? ?]]. exists (l2 ++ l3). rewrite <- app_assoc. split; auto.
      rewrite H22 at 1. rewrite roots_map_map_app.
      * f_equal. apply H19; auto.
      * eapply (remset_semi_iso_DoubleNoDup _ _ from) in H21; eauto.
        rewrite app_assoc in H21. rewrite DoubleNoDup_app_iff in H21. now destruct H21.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_roots_graph_compatible; eauto.
    + eapply fr_O_no_dangling_dst' with
        (p := FwdPntIntr (InteriorVertexPos v (Z.of_nat a))); eauto.
    + intros.
      rewrite <- (fr_raw_fields 0 from to
                    (interior2forward (InteriorVertexPos v (Z.of_nat a)) g2)
                    g2 g0 H2 H16 v H20).
      apply H8; now right.
    + destruct Hsound_g0 as [Hvv_g0 _]. red in Hvv_g0. rewrite Hvv_g0.
      eapply fr_graph_has_v; eauto.
    + rewrite <- (fr_raw_mark 0 from to
                    (interior2forward (InteriorVertexPos v (Z.of_nat a)) g2)
                    g2 g0 H2 H16 v H20 NOSCAN).
      exact H11.
    + rewrite <- (fr_raw_tag 0 from to
                    (interior2forward (InteriorVertexPos v (Z.of_nat a)) g2)
                    g2 g0 H2 H16 v H20 NOSCAN).
      exact H12.
    + eapply (fr_copy_compatible O from); eauto.
    + eapply fr_O_no_unmarked_old_nonfrom_dst_t; eauto.
Qed.

Lemma svfl_no_unmarked_old_nonfrom_dst:
  forall base from to v l g1 g2,
    from <> to ->
    graph_has_gen g1 to ->
    no_unmarked_old_nonfrom_dst base g1 from ->
    scan_vertex_for_loop from to v l g1 g2 ->
    no_unmarked_old_nonfrom_dst base g2 from.
Proof.
  intros base from to v l g1 g2 Hneq Hto Hclosed Hsvfl.
  induction Hsvfl; auto.
  apply IHHsvfl.
  - erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_O_no_unmarked_old_nonfrom_dst_t; eauto.
Qed.

Lemma svwl_no_unmarked_old_nonfrom_dst:
  forall base from to l g1 g2,
    from <> to ->
    graph_has_gen g1 to ->
    no_unmarked_old_nonfrom_dst base g1 from ->
    scan_vertex_while_loop from to l g1 g2 ->
    no_unmarked_old_nonfrom_dst base g2 from.
Proof.
  intros base from to l g1 g2 Hneq Hto Hclosed Hsvwl.
  induction Hsvwl; eauto.
  eapply IHHsvwl.
  - apply (proj1 (svfl_graph_has_gen from to (to, i)
                    (nat_inc_list (Datatypes.length (raw_fields (vlabel g1 (to, i)))))
                    g1 g2 Hto H1 to)).
    exact Hto.
  - eapply svfl_no_unmarked_old_nonfrom_dst; eauto.
Qed.

Lemma svwl_remset_semi_iso:
  forall from to l l1 roots base g2 g3,
    from <> to -> sound_gc_graph base -> sound_gc_graph g2 -> graph_has_gen g2 to ->
    roots_graph_compatible roots g2 ->
    no_dangling_dst base -> no_dangling_dst g2 -> roots_have_no_gen roots from ->
    (forall i, In i l -> ~ gen_has_index base to i) -> copy_compatible g2 ->
    gen_unmarked g2 to -> gc_graph_remset_semi_iso base g2 from to l1 ->
    no_unmarked_old_nonfrom_dst base g2 from ->
    scan_vertex_while_loop from to l g2 g3 ->
    exists l2, gc_graph_remset_semi_iso base g3 from to (l2 ++ l1) /\
               roots = roots_map l2 roots.
Proof.
  pose (H3:=True).
  do 3 intro. induction l; intros; inversion H13; subst.
  - exists []; simpl. split; auto. now rewrite roots_map_nil.
  - eapply IHl; eauto. intros. apply H8. now right.
  - pose proof H18. eapply (svfl_remset_semi_iso _ _ _ _ _ base) in H18; eauto.
    + destruct H18 as [l3 [? ?]]. eapply (IHl (l3 ++ l1) _ base) in H21; eauto.
      * destruct H21 as [l2 [? ?]]. exists (l2 ++ l3). rewrite <- app_assoc.
        split; auto. rewrite roots_map_map_app.
        -- rewrite <- H18. assumption.
        -- eapply (remset_semi_iso_DoubleNoDup _ _ from) in H19; eauto.
           rewrite app_assoc in H19. rewrite DoubleNoDup_app_iff in H19. now destruct H19.
      * eapply svfl_P_holds; eauto. apply fr_O_sound.
      * erewrite <- svfl_graph_has_gen; eauto.
      * red. rewrite Forall_forall. intros. eapply svfl_graph_has_v; eauto.
        red in H4. rewrite Forall_forall in H4. now apply H4.
      * eapply (svfl_no_dangling_dst from to); eauto. 1: split; now simpl.
        unfold no_scan in H17; lia. intros. now rewrite nat_inc_list_In_iff in H19.
      * intros. apply H8. now right.
      * eapply svfl_copy_compatible; eauto.
      * eapply svfl_gen_unmarked; eauto.
      * eapply svfl_no_unmarked_old_nonfrom_dst; eauto.
    + intros. now rewrite nat_inc_list_In_iff in H15.
    + destruct H0. red in H0. rewrite H0. intro. destruct H19. simpl in H20.
      apply (H8 a); [left |]; auto.
    + destruct H1. red in H1. rewrite H1. split; now simpl.
    + unfold no_scan in H17; lia.
Qed.

Lemma frr_rgc_aux: forall from to roots1 g1 roots2 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 ->
    roots_graph_compatible roots1 g1 ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall ready, roots_graph_compatible ready g1 ->
    roots_graph_compatible ready g2 /\ roots_graph_compatible roots2 g2.
Proof.
   induction 5; intros; auto.
   pose proof fr_upd_roots_graph_compatible 0 from to 0 g1 g2 (r :: ready ++ roots1) H0 H1
     ltac:(simpl; list_solve) H3 H. unfold upd_roots in H6.
   rewrite upd_Znth0, Znth_0_cons in H6.
   spec H6. change (?A :: ?B) with ([A]++B) in H2 |- *.
   rewrite !roots_graph_compatible_app in *.
   destruct H2; split; auto.
   assert (graph_has_gen g2 to) by (erewrite <- fr_graph_has_gen; eauto).
   assert (copy_compatible g2) by (eapply fr_copy_compatible; try apply H3; eauto).
   change (?A :: ?B) with ([A]++B) in H6|-*.
   rewrite !roots_graph_compatible_app in *.
   destruct H6 as [? [? ?]].
   specialize (IHforward_roots_relation H7 H8 H10 (ready+:: upd_exterior from to g1 r)).
   rewrite !roots_graph_compatible_app in *.
   destruct IHforward_roots_relation; auto.
   destruct H11.
   split; auto.
Qed.

Lemma frr_roots_graph_compatible: forall from to roots1 g1 roots2 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 ->
    roots_graph_compatible roots1 g1 ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    roots_graph_compatible roots2 g2.
Proof.
   intros.
   eapply frr_rgc_aux in H3; eauto.
   destruct H3; auto.
Qed.

Definition marked_in_gen (g1 g2: LGraph) (gen: nat) (v: VType): Prop :=
  raw_mark (vlabel g2 v) = true /\ vvalid g1 v /\ vgeneration v = gen.

Definition roots_reachable_in_gen (g: LGraph) (roots: roots_t)
           (gen: nat) (v: VType): Prop :=
  reachable_through_set g (filter_proj exterior_proj_vertex roots) v /\ vgeneration v = gen.

Definition reachable_iff_marked (g1 g2: LGraph) (roots: roots_t) (gen: nat): Prop :=
  forall v, roots_reachable_in_gen g1 roots gen v <-> marked_in_gen g1 g2 gen v.

Lemma remset_semi_quasi_iso: forall from to g1 g2 l roots1 roots2,
    reachable_iff_marked g1 g2 roots1 from ->
    gc_graph_remset_semi_iso g1 g2 from to l ->
    roots2 = roots_map l roots1 ->
    gc_graph_remset_quasi_iso g1 roots1 g2 roots2 from to.
Proof.
  intros from to g1 g2 l roots1 roots2 Hr H Hroots.
  destruct H as [Hcopy Hspec].
  exists l. split; [exact Hroots |]. split.
  - intros v1 v2 Hin. specialize (Hcopy _ _ Hin).
    destruct Hcopy as [_ Hcopy]. exact Hcopy.
  - destruct (split l) as [from_l to_l].
    destruct Hspec as [Hfrom [Hto [Hlabel Hpartial]]].
    unfold remset_partial_graph in Hpartial.
    destruct Hpartial as [Holdvalid [Hedges _]].
    split.
    + destruct Hfrom as [Hnodup Hfrom].
      split; [exact Hnodup |].
      intros v. red in Hr.
      unfold roots_reachable_in_gen, marked_in_gen in Hr.
      now rewrite Hr, Hfrom.
    + split; [exact Hto |]. split; [exact Hlabel |].
      split; [exact Holdvalid | exact Hedges].
Qed.

Lemma reachable_from_roots: forall (g: LGraph) (roots: roots_t) v,
    reachable_through_set g (filter_proj exterior_proj_vertex roots) v <->
    exists i r, 0 <= i < Zlength roots /\ Znth i roots = ExteriorVertex r /\
             reachable g r v.
Proof.
  intros. unfold reachable_through_set. split; intros.
  - destruct H as [s [? ?]]. rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in H.
    apply In_Znth in H. destruct H as [i [? ?]]. exists i, s. split3; auto.
  - destruct H as [i [r [? [? ?]]]]. exists r. split; auto.
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- H0. now apply Znth_In.
Qed.

Lemma lcv_copied_vertex: forall (g : LGraph) (v : VType) (to : nat) (x : VType),
  x <> v -> graph_has_gen g to -> graph_has_v g x ->
  copied_vertex (vlabel (lgraph_copy_v g v to) x) = copied_vertex (vlabel g x).
Proof.
  intros. unfold lgraph_copy_v. rewrite lmc_vlabel_not_eq by assumption.
  rewrite lacv_vlabel_old; [| apply graph_has_v_not_eq]; easy.
Qed.

Lemma step_vvalid: forall g s t,
    sound_gc_graph g -> no_dangling_dst g -> step g s t -> vvalid g t.
Proof.
  intros. destruct H as [? [? [? Hels]]]. red in H, H0, H2, H3. rewrite step_spec in H1.
  destruct H1 as [e [? [? ?]]]. rewrite <- H5, H. rewrite H2 in H1. destruct H1.
  now apply (H0 (fst e)).
Qed.

Lemma pcv_edge: forall (g: LGraph) old_v new_v z,
    sound_gc_graph g -> no_dangling_dst g -> vvalid g old_v -> ~ vvalid g new_v ->
    g |= old_v ~> z <-> (pregraph_copy_v g old_v new_v) |= new_v ~> z.
Proof.
  intros g old_v new_v z H0 Hd H H1.
  unfold edge. destruct H0 as [? [? [? Hels]]]. red in H0, H2, H3.
  split; intros; destruct H4 as [? [? ?]].
  - split3; auto.
    + apply pcv_vvalid_iff. now right.
    + rewrite pcv_vvalid_iff. now left.
    + rewrite step_spec in *. destruct H6 as [e [? [? ?]]]. rewrite H2 in H6.
      destruct H6. rewrite get_edges_inv in H9. destruct H9 as [idx [? ?]].
      destruct e as [gen i]. simpl in *. rewrite H3 in H7. simpl in *. subst gen.
      inversion H9. subst i. clear H9. exists (new_v, idx). split3.
      * rewrite pcv_evalid_iff. right. rewrite get_edges_map_map.
        rewrite (map_map _ (fun x : VType * nat => (new_v, snd x))). simpl.
        change (new_v, idx) with ((fun x : nat => (new_v, x)) idx). now apply in_map.
      * now apply pcv_src_new.
      * now rewrite pcv_dst_new.
  - assert (step g old_v z). {
      rewrite step_spec in *. destruct H6 as [e [? [? ?]]].
      rewrite pcv_evalid_iff in H6. destruct H6.
      - exfalso. rewrite H2 in H6. destruct H6. destruct e as [gen idx]. simpl in *.
        rewrite <- H0 in H6. destruct_eq_dec gen new_v. 1: now subst.
        rewrite pcv_src_old in H7. 2: now simpl. rewrite H3 in H7. now simpl in H7.
      - rewrite get_edges_map_map,
        (map_map _ (fun x : VType * nat => (new_v, snd x))) in H6. simpl in H6.
        rewrite in_map_iff in H6. destruct H6 as [idx [? ?]]. destruct e. inversion H6.
        subst v n. clear H6. rewrite pcv_dst_new in H8; auto. exists (old_v, idx).
        rewrite H3. simpl. split; auto. rewrite H2. split; simpl. 1: now rewrite <- H0.
        now apply In_snd_get_edges. } split3; auto.
    eapply step_vvalid; eauto. split3; easy.
Qed.

Lemma pcv_reachable_old: forall g old_v new_v s t,
    sound_gc_graph g -> no_dangling_dst g -> ~ vvalid g new_v -> vvalid g s ->
    reachable (pregraph_copy_v g old_v new_v) s t <-> reachable g s t.
Proof.
  intros g old_v new_v s t Hg Hn H H0. split; intros.
  - unfold reachable, reachable_by in *. destruct H1 as [p [[? ?] [? ?]]].
    destruct p as [? p]. simpl in H1. subst v. exists (s, p).
    assert (valid_path g (s, p)). {
      clear H4 H2. revert s H0 H3. induction p; intros. 1: simpl; easy.
      rewrite valid_path_cons_iff in *. destruct H3 as [? [? ?]].
      destruct Hg as [? [? [? Hels]]]. pose proof (pcv_src_edge g old_v new_v H6). red in H7.
      destruct H2 as [? [? ?]]. rewrite H7 in *. rewrite pcv_evalid_iff in H2.
      rewrite H6. split; auto. destruct H2.
      - clear H8. assert (fst a <> new_v) by (intro; rewrite H8 in H1; now subst s).
        rewrite pcv_dst_old in H9, H3; auto. unfold strong_evalid. rewrite H6, <- H1.
        rewrite pcv_vvalid_iff in H9. destruct H9. 1: intuition. exfalso.
        red in H5. rewrite H5 in H2. destruct H2. red in Hn. apply Hn in H10; auto.
        red in H4. now rewrite <- H4, H9 in H10.
      - rewrite in_map_iff in H2. destruct H2 as [x [? _]]. destruct a. inversion H2.
        subst v. simpl in H1. now subst s. } split; split; auto.
    destruct p. 1: now simpl in *. assert (e :: p <> nil) by (intro HS; inversion HS).
    apply exists_last in H5. destruct H5 as [l' [a ?]]. rewrite e0 in *.
    rewrite pfoot_last in *. rewrite pcv_dst_old in H2; auto. assert (evalid g a) by
        (eapply valid_path_evalid; eauto; rewrite in_app_iff; now right; left).
    destruct Hg as [? [? ?]]. red in H6, H7. rewrite H7 in H5. destruct H5.
    rewrite <- H6 in H5. intro. now rewrite H10 in H5.
  - apply is_partial_graph_reachable with (g1 := g); auto.
    apply pcv_is_partial_graph; auto.
Qed.

Lemma pcv_reachable_new: forall g old_v new_v v,
    sound_gc_graph g -> no_dangling_dst g -> vvalid g old_v -> ~ vvalid g new_v ->
    reachable g old_v v <->
    v = old_v \/ reachable (pregraph_copy_v g old_v new_v) new_v v /\ new_v <> v.
Proof.
  intros. rewrite reachable_same_or_edge'; auto.
  rewrite (reachable_same_or_edge' (pregraph_copy_v g old_v new_v)).
  2: rewrite pcv_vvalid_iff; now right.
  split; intros; destruct H3; [left | right | left | ]; auto.
  - destruct H3 as [z [? ?]]. split; [right; exists z|].
    2: intro; apply reachable_foot_valid in H4; now subst.
    rewrite pcv_edge in H3; eauto. split; auto.
    eapply is_partial_graph_reachable; eauto. apply pcv_is_partial_graph; auto.
  - destruct H3. destruct H3; [easy|]. destruct H3 as [z [? ?]]. right. exists z.
    assert (g |= old_v ~> z) by (rewrite pcv_edge; eauto). split; auto.
    apply pcv_reachable_old in H5; auto. now destruct H6 as [_ [? _]].
Qed.

Definition copied_vertex_prop (g: LGraph) (from to: nat): Prop :=
  forall v,
    let cv := copied_vertex (vlabel g v) in
    graph_has_v g v -> raw_mark (vlabel g v) = true ->
    graph_has_v g cv /\ vgeneration cv = to /\ vgeneration v = from /\
    map snd (get_edges g v) = map snd (get_edges g cv) /\
    forall idx, In idx (map snd (get_edges g v)) ->
                dst g (cv, idx) = dst g (v, idx) \/
                raw_mark (vlabel g (dst g (v, idx))) = true /\
                dst g (cv, idx) = copied_vertex (vlabel g (dst g (v, idx))).

Lemma graph_unmarked_copied_vertex_prop: forall g from to,
    graph_unmarked g -> copied_vertex_prop g from to.
Proof. intros. red in H |-* . intros.  apply H in H0. rewrite H1 in H0. easy. Qed.

Lemma lcv_copied_vertex_prop: forall (to : nat) (g : LGraph) (v : VType),
    vgeneration v <> to -> sound_gc_graph g -> graph_has_gen g to ->
    raw_mark (vlabel g v) = false -> no_dangling_dst g ->
    copied_vertex_prop g (vgeneration v) to ->
    copied_vertex_prop (lgraph_copy_v g v to) (vgeneration v) to.
Proof.
  intros. unfold copied_vertex_prop in *. intro s; intros.
  apply lcv_graph_has_v_inv in H5; auto. destruct H5.
  2: subst s; rewrite lcv_vlabel_new in H6; auto; now rewrite H2 in H6.
  pose proof H0. destruct H0 as [? [? [? Hels]]]. red in H0, H8, H9.
  assert (vvalid g s) by (now rewrite <- H0 in H5).
  assert (~ vvalid g (new_copied_v g to)) by
      (intro; rewrite H0 in H11; now apply (graph_has_v_not_eq g to) in H11).
  destruct_eq_dec s v.
  - subst s. simpl. rewrite ucov_copied_vertex. simpl.
    split; [|split; [|split; [|split]]]; auto.
    + apply lcv_graph_has_v_new; auto.
    + rewrite lcv_get_edges_old, lcv_lacv_get_edges; auto.
      symmetry. apply lacv_get_edges_new.
    + intros. rewrite lcv_get_edges_old in H12; auto. rewrite pcv_dst_new; auto.
      rewrite !pcv_dst_old. 2: simpl; intro; now subst. now left.
  - rewrite <- lcv_raw_mark in H6; auto. rewrite lcv_copied_vertex; auto.
    destruct (H4 _ H5 H6) as [? [? [? [? ?]]]].
    split; [|split; [|split; [|split]]];
      [apply lcv_graph_has_v_old | | | rewrite !lcv_get_edges_old |]; auto. intros.
    rewrite <- H0 in H13. rewrite lcv_get_edges_old in H18; auto. simpl dst.
    rewrite !pcv_dst_old; [|simpl; intro; now rewrite H19 in *..].
    specialize (H17 _ H18). destruct H17 as [? | [? ?]]; [left|]; auto.
    assert (graph_has_v g (dst g (s, idx))). {
      red in H3. apply H3 with s; auto. rewrite get_edges_In; auto. }
    destruct_eq_dec (dst g (s, idx)) v. 1: now rewrite H21, H2 in H17. right.
    rewrite <- lcv_raw_mark; auto. rewrite lcv_copied_vertex; auto.
Qed.

Lemma lgd_copied_vertex_prop: forall to g e,
    no_dangling_dst g -> graph_has_gen g to ->
    vgeneration (dst g e) <> to -> vgeneration (fst e) <> vgeneration (dst g e) ->
    raw_mark (vlabel g (dst g e)) = true -> evalid g e ->
    copied_vertex_prop g (vgeneration (dst g e)) to ->
    copied_vertex_prop
      (labeledgraph_gen_dst g e (copied_vertex (vlabel g (dst g e))))
      (vgeneration (dst g e)) to.
Proof.
  intros. unfold copied_vertex_prop in *. intro s; intros. simpl in *.
  rewrite <- lgd_graph_has_v in *. destruct (H5 _ H6 H7) as [? [? [? [? ?]]]].
  split; [|split; [|split; [|split]]]; auto. intros. unfold get_edges in H13.
  rewrite lgd_make_fields_eq in H13. fold (get_edges g s) in H13.
  specialize (H12 _ H13). destruct_eq_dec e (s, idx).
  1: subst e; simpl in H2; now rewrite H10 in H2.
  rewrite (updateEdgeFunc_neq _ _ _ (s, idx)); auto.
  destruct_eq_dec e (copied_vertex (vlabel g s), idx).
  2: rewrite updateEdgeFunc_neq; auto. remember (copied_vertex (vlabel g s)) as cs.
  subst e. rewrite updateEdgeFunc_eq. destruct H12 as [? | [? ?]].
  - right. rewrite H12 in *. auto.
  - simpl in H2. rewrite H9 in *. assert (graph_has_v g (dst g (s, idx))). {
      red in H. apply H with s; auto. rewrite get_edges_In. auto. }
    specialize (H5 _ H16 H12). rewrite H15 in H2. destruct H5 as [_ [? _]].
    now rewrite H5 in H2.
Qed.

Lemma fr_O_copied_vertex_prop: forall from to p g1 g2,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    forward_p_compatible' p g1 from ->
    forward_relation from to O (forward_p2forward_t p g1) g1 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  intros. destruct p; simpl in H3, H4.
  - destruct extr eqn:? ; inversion H4; subst; try easy. apply lcv_copied_vertex_prop; auto.
  - destruct intr. destruct H3 as [? [? [? [H7' ?]]]]. simpl in H4.
    destruct (Znth field_pos (make_fields g1 vertex)) eqn:? ; simpl in H4;
      inversion H4; subst; try easy.
    + subst new_g.
      assert (fst e = vertex) by (apply make_fields_Znth_edge in Heqf; auto; now subst e).
      assert (evalid g1 e). {
        destruct H1 as [? [? [? _]]]. red in H1, H10, H11. rewrite H10. split; rewrite H9.
        1: easy. unfold get_edges.
        rewrite <- (filter_proj_In_iff field_proj_edge_spec), <- Heqf.
        apply Znth_In. now rewrite make_fields_eq_length. }
      apply lgd_copied_vertex_prop; auto. rewrite H9; auto.
    + subst new_g. eapply lcv_copied_vertex_prop in H5; eauto.
      remember (lgraph_copy_v g1 (dst g1 e) to) as g3.
      assert (fst e = vertex) by (apply make_fields_Znth_edge in Heqf; auto; now subst e).
      assert (dst g1 e = dst g3 e). {
        subst g3. simpl. rewrite pcv_dst_old; auto. rewrite H9.
        now apply graph_has_v_not_eq with (to := to) in H3. }
      assert (new_copied_v g1 to = copied_vertex (vlabel g3 (dst g3 e))). {
        rewrite <- H10. subst g3. simpl. rewrite ucov_copied_vertex. easy. }
      assert (graph_has_e g1 e). {
        split; rewrite H9. 1: easy. unfold get_edges.
        rewrite <- (filter_proj_In_iff field_proj_edge_spec), <- Heqf.
        apply Znth_In. now rewrite make_fields_eq_length. }
      assert (evalid g1 e). {
        destruct H1 as [? [? [? _]]]. red in H1, H14, H15. now rewrite H14. }
      rewrite H12, H10. apply lgd_copied_vertex_prop; try (now rewrite <- H10).
      * subst g3. apply lcv_no_dangling_dst; auto. red in H2. apply H2 with vertex; auto.
        destruct H13. now rewrite H9 in H15.
      * subst g3. rewrite <- lcv_graph_has_gen; auto.
      * now rewrite H9, <- H10.
      * rewrite <- H10. subst g3. apply lcv_raw_mark_old.
      * subst g3. destruct H1 as [? [? [? _]]]. pose proof H0.
        apply (lcv_edge_valid _ (dst g1 e)) in H0; auto. red in H0. rewrite H0.
        split; rewrite H9. 1: apply lcv_graph_has_v_old; auto.
        unfold get_edges, make_fields. rewrite <- lcv_raw_fields; auto.
        fold (make_fields g1 vertex). fold (get_edges g1 vertex). destruct H13.
        now rewrite <- H9.
Qed.

Lemma copied_vertex_reachable_by_path: forall (g : LGraph) r v (from to : nat) p,
    sound_gc_graph g -> copied_vertex_prop g from to -> raw_mark (vlabel g r) = true ->
    g |= (r, p) is r ~o~> v satisfying (fun _ => True) ->
    raw_mark (vlabel g v) = true \/
    exists p', g |= (copied_vertex (vlabel g r), p') is
                 (copied_vertex (vlabel g r)) ~o~> v satisfying (fun _ => True) /\
               length p = length p'.
Proof.
  intros. remember (length p) as n. assert (length p <= n)%nat by lia. rewrite Heqn.
  clear Heqn. revert r p H1 H2 H3. induction n; intros.
  - destruct p. 2: simpl in H3; exfalso; lia. destruct H2 as [[_ ?] _]. simpl in H2.
    subst v. left; auto.
  - destruct p. 1: destruct H2 as [[_ ?] _]; simpl in H2; subst v; left; auto.
    assert (g |= (dst g e, p) is dst g e ~o~> v satisfying (fun _ => True)). {
      change (e :: p) with ([] ++ e :: p) in H2.
      apply reachable_by_path_app_cons in H2. now destruct H2. }
    destruct H2 as [_ [? _]]. rewrite valid_path_cons_iff in H2. red in H0.
    destruct H2 as [? [[? [? ?]] ?]]. destruct H as [? [? [? _]]]. red in H, H9, H10.
    assert (graph_has_v g r) by (rewrite <- H; now rewrite <- H2 in H6).
    specialize (H0 _ H11 H1). destruct H0 as [? [? [_ [? ?]]]]. rewrite H10 in H2.
    destruct e as [r' idx]. simpl in H2. subst r'. rewrite H9 in H5. destruct H5.
    simpl in H5. rewrite get_edges_In in H5. specialize (H14 _ H5).
    remember (copied_vertex (vlabel g r)) as cr.
    assert (vvalid g (dst g (cr, idx)) ->
            g |= (cr, (cr, idx) :: nil) is cr ~o~> (dst g (cr, idx))
              satisfying (fun _ => True)). {
      intros. split; split; simpl; auto. 2: red; rewrite Forall_forall; intros; auto.
      rewrite H10. split; auto.
      split3; [| rewrite H10; simpl; now rewrite <- H in H0|]; auto.
      rewrite H9. split. 1: simpl; auto. now rewrite get_edges_In, <- H13. }
    destruct H14.
    + right. exists ((cr, idx) :: p). split. 2: simpl; auto.
      assert ((cr, (cr, idx) :: p) = path_glue (cr, [(cr, idx)]) (dst g (cr, idx), p))
        by (now unfold path_glue). unfold EType. rewrite H16.
      apply reachable_by_path_merge with (dst g (cr, idx)). 2: rewrite H14; auto.
      apply H15. now rewrite H14.
    + destruct H14. assert (length p <= n)%nat by (simpl in H3; lia).
      specialize (IHn _ _ H14 H4 H17). destruct IHn. 1: now left. right.
      destruct H18 as [p' [? ?]]. rewrite <- H16 in H18. exists ((cr, idx) :: p').
      split. 2: simpl; auto. assert ((cr, (cr, idx) :: p') =
                                     path_glue (cr, [(cr, idx)]) (dst g (cr, idx), p'))
        by (now unfold path_glue). unfold EType. rewrite H20.
      apply reachable_by_path_merge with (dst g (cr, idx)). 2: apply H18; auto.
      apply H15. assert (reachable g (dst g (cr, idx)) v) by
          (now exists (dst g (cr, idx), p')). now apply reachable_head_valid in H21.
Qed.

Lemma copied_vertex_reachable: forall (g: LGraph) (r v: VType) to,
    sound_gc_graph g -> copied_vertex_prop g (vgeneration r) to ->
    raw_mark (vlabel g r) = true -> reachable g r v ->
    reachable g (copied_vertex (vlabel g r)) v \/ raw_mark (vlabel g v) = true.
Proof.
  intros. unfold reachable, reachable_by in H2. destruct H2 as [[s p] ?].
  assert (phead (s, p) = r) by (eapply reachable_by_path_head; eauto). simpl in H3.
  subst s. remember (vgeneration r) as from. clear Heqfrom.
  eapply copied_vertex_reachable_by_path in H2; eauto. destruct H2. 1: now right.
  destruct H2 as [p' [? ?]]. left. now exists (copied_vertex (vlabel g r), p').
Qed.

Lemma copied_vertex_reachable_by_path_inv: forall (g: LGraph) (r v: VType) from to p,
    sound_gc_graph g -> copied_vertex_prop g from to ->
    raw_mark (vlabel g r) = true -> vgeneration v = from ->
    from <> to -> no_dangling_dst g -> graph_has_v g r ->
    g |= (copied_vertex (vlabel g r), p) is
      (copied_vertex (vlabel g r)) ~o~> v satisfying (fun _ => True) ->
    exists p', g |= (r, p') is r ~o~> v satisfying (fun _ => True) /\
               length p = length p'.
Proof.
  intros g r v from to p H H0 H1 H2 H3 Hd H4 H5.
  remember (length p) as n. assert (length p <= n)%nat by lia. rewrite Heqn.
  clear Heqn. revert r p H6 H1 H4 H5. induction n; intros.
  - destruct p. 2: simpl in H6; lia. destruct H5 as [[_ ?] _]. simpl in H5.
    red in H0. specialize (H0 _ H4 H1). destruct H0 as [_ [? _]]. rewrite H5, H2 in H0.
    now rewrite H0 in H3.
  - red in H0. specialize (H0 _ H4 H1). destruct H0 as [? [? [? [? ?]]]].
    remember (copied_vertex (vlabel g r)) as cr. destruct p.
    + destruct H5 as [[_ ?] _]. simpl in H5. rewrite H5, H2 in H7.
      now rewrite H7 in H3.
    + assert (g |= (dst g e, p) is dst g e ~o~> v satisfying (fun _ => True)). {
      change (e :: p) with ([] ++ e :: p) in H5.
      apply reachable_by_path_app_cons in H5. now destruct H5. }
      destruct H5 as [_ [? _]]. rewrite valid_path_cons_iff in H5.
      destruct H5 as [? [[? [? ?]] ?]]. destruct H as [? [? [? _]]]. red in H, H16, H17.
      rewrite H17 in H5. destruct e as [cr' idx]. simpl in H5. subst cr'.
      rewrite H16 in H12. destruct H12. simpl fst in *. rewrite get_edges_In in H12.
      rewrite <- H9 in H12. specialize (H10 _ H12).
      assert (vvalid g (dst g (r, idx)) ->
              g |= (r, [(r, idx)]) is r ~o~> (dst g (r, idx))
                satisfying (fun _ => True)). {
        split; split; simpl; auto.
        2: red; rewrite Forall_forall; intros; auto. rewrite H17. split; auto.
        split3; [| rewrite H17; simpl; rewrite H |]; auto.
        rewrite H16. split; simpl; auto. now rewrite get_edges_In. } destruct H10.
      * rewrite H10 in H11. exists ((r, idx) :: p). split. 2: simpl; auto.
        assert ((r, (r, idx) :: p) = path_glue (r, [(r, idx)]) (dst g (r, idx), p))
          by (now unfold path_glue). unfold EType. rewrite H19.
        apply reachable_by_path_merge with (dst g (r, idx)); auto. apply H18.
        now rewrite <- H10.
      * destruct H10. assert (length p <= n)%nat by (simpl in H6; lia).
        assert (graph_has_v g (dst g (r, idx))). {
          red in Hd. apply Hd with r; auto. now rewrite get_edges_In. }
        rewrite H19 in H11. specialize (IHn _ _ H20 H10 H21 H11).
        destruct IHn as [p' [? ?]]. exists ((r, idx) :: p'). split. 2: simpl; auto.
        assert ((r, (r, idx) :: p') =
                path_glue (r, [(r, idx)]) (dst g (r, idx), p'))
          by (now unfold path_glue). unfold EType. rewrite H24.
        apply reachable_by_path_merge with (dst g (r, idx)). 2: apply H22; auto.
        apply H18. now rewrite H.
Qed.

Lemma copied_vertex_reachable_inv: forall (g: LGraph) (r v: VType) to,
    sound_gc_graph g -> copied_vertex_prop g (vgeneration r) to ->
    raw_mark (vlabel g r) = true -> vgeneration v = vgeneration r ->
    vgeneration r <> to -> no_dangling_dst g -> graph_has_v g r ->
    reachable g (copied_vertex (vlabel g r)) v -> reachable g r v.
Proof.
  intros. remember (vgeneration r) as from. clear Heqfrom.
  unfold reachable, reachable_by in H6. destruct H6 as [[cr' p] ?]. pose proof H6.
  apply reachable_by_path_head in H7. simpl in H7. subst cr'.
  eapply copied_vertex_reachable_by_path_inv in H6; eauto. destruct H6 as [p' [? ?]].
  now exists (r, p').
Qed.

Lemma copied_vertex_pgd_reachable: forall g e to r v,
    sound_gc_graph g -> copied_vertex_prop g (vgeneration (dst g e)) to ->
    evalid g e -> raw_mark (vlabel g (dst g e)) = true -> reachable g r v ->
    reachable (pregraph_gen_dst g e (copied_vertex (vlabel g (dst g e)))) r v \/
    raw_mark (vlabel g v) = true.
Proof.
  intros. unfold reachable, reachable_by in H3. destruct H3 as [[s p] ?].
  assert (phead (s, p) = r) by (eapply reachable_by_path_head; eauto). simpl in H4.
  subst s. remember (length p) as n. assert (length p <= n)%nat by lia. clear Heqn.
  revert r p H4 H3. induction n; intros.
  - destruct p. 2: simpl in H4; lia. destruct H3 as [[_ ?] [? _]]. simpl in *.
    subst v. left. apply reachable_refl. now simpl.
  - destruct (in_dec equiv_dec e p).
    2: left; exists (r, p); rewrite no_edge_gen_dst_equiv; auto.
    change p with (snd (r, p)) in i. eapply reachable_path_unique_edge in i; eauto.
    destruct i as [p1 [p2 [? [? [? ?]]]]]. apply reachable_by_path_app_cons in H5.
    destruct H5. rewrite length_app in H8. simpl in H8.
    eapply copied_vertex_reachable_by_path in H9; eauto. destruct H9.
    1: right; auto. destruct H9 as [p' [? ?]]. assert (length p' <= n)%nat by lia.
    specialize (IHn _ _ H11 H9). destruct IHn. 2: now right. left.
    remember (copied_vertex (vlabel g (dst g e))) as cde.
    apply reachable_trans with cde; auto.
    assert (reachable (pregraph_gen_dst g e cde) r (src g e)) by
        (exists (r, p1); now rewrite no_edge_gen_dst_equiv).
    apply reachable_trans with (src g e); auto. exists (src g e, [e]).
    split; split; simpl; auto.
    + apply updateEdgeFunc_eq.
    + split; auto. red. simpl. split; auto. rewrite updateEdgeFunc_eq.
      apply reachable_head_valid in H12. simpl in H12. split; auto.
      apply reachable_foot_valid in H13. simpl in H13. auto.
    + red. rewrite Forall_forall. now intros.
Qed.

Lemma copied_vertex_pgd_reachable_inv: forall g e to r v,
    sound_gc_graph g -> copied_vertex_prop g (vgeneration (dst g e)) to ->
    no_dangling_dst g -> evalid g e -> raw_mark (vlabel g (dst g e)) = true ->
    vgeneration v = vgeneration (dst g e) -> vgeneration (dst g e) <> to ->
    reachable (pregraph_gen_dst g e (copied_vertex (vlabel g (dst g e)))) r v ->
    reachable g r v.
Proof.
  intros. unfold reachable, reachable_by in H6. destruct H6 as [[s p] ?].
  pose proof H6. apply reachable_by_path_head in H7. simpl in H7. subst s.
  destruct (in_dec equiv_dec e p).
  - change p with (snd (r, p)) in i. eapply reachable_path_unique_edge in i; eauto.
    destruct i as [p1 [p2 [? [? [? _]]]]]. apply reachable_by_path_app_cons in H7.
    simpl in *. destruct H7. rewrite updateEdgeFunc_eq in H10.
    rewrite no_edge_gen_dst_equiv in H7, H10; simpl; auto.
    assert (graph_has_v g (dst g e)). {
      red in H1. destruct H as [? [? ?]]. red in H11. rewrite H11 in H2.
      destruct H2. apply H1 with (fst e); auto. }
    eapply copied_vertex_reachable_by_path_inv in H10; eauto.
    destruct H10 as [p' [? _]].
    assert (reachable g r (src g e)) by (now exists (r, p1)).
    assert (reachable g (dst g e) v) by (now exists (dst g e, p')).
    apply reachable_trans with (src g e); auto.
    apply reachable_trans with (dst g e); auto. exists (src g e, [e]).
    split; split; simpl; auto.
    + split; auto. red. apply reachable_foot_valid in H12.
      apply reachable_head_valid in H13. auto.
    + red. rewrite Forall_forall. intros; auto.
  - exists (r, p). rewrite no_edge_gen_dst_equiv in H6; auto.
Qed.

Definition backward_edge_prop (g: LGraph) (roots: roots_t) (from to: nat): Prop :=
  forall e: EType, evalid g e -> vgeneration (fst e) = to ->
              vgeneration (dst g e) = from ->
              reachable_through_set g (filter_proj exterior_proj_vertex roots) (fst e).

Definition edge_from_gen_cond (intr : interior_t) (gen: nat) :=
  match intr with
  | InteriorVertexPos v _ => vgeneration v = gen
  end.

Lemma fr_O_backward_edge_prop_roots: forall from to i g1 g2 roots,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    0 <= i < Zlength roots ->
    forward_relation from to O (exterior2forward (Znth i roots)) g1 g2 ->
    copied_vertex_prop g1 from to -> gen_unmarked g1 to ->
    backward_edge_prop g1 roots from to ->
    backward_edge_prop g2 (upd_roots from to i g1 roots) from to.
Proof.
  intros. assert (He: forall e, evalid g1 e -> fst e <> new_copied_v g1 to). {
    intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1 in H8.
    destruct H8. eapply graph_has_v_not_eq in H8; eauto. }
  pose proof (proj1 H1) as Hv. red in Hv. unfold upd_roots, upd_exterior.
  destruct (Znth i roots) eqn:Heqr; simpl in *; rewrite ?Heqr; inversion H4; subst; clear H4;
    try (rewrite <- Heqr, upd_Znth_unchanged'); auto.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v) from) as [Hvfrom | _].
    1: contradiction. rewrite <- Heqr, upd_Znth_unchanged'; auto.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v) (vgeneration v)) as [_ | Hneq].
    2: contradiction. rewrite H11. red in H7 |- * ; intros. specialize (H7 _ H4 H8 H9).
    rewrite reachable_from_roots in *. destruct H7 as [idx [r [? [? ?]]]].
    rewrite upd_Znth_Zlength; auto. destruct (Z.eq_dec idx i).
    + subst idx. exists i, (copied_vertex (vlabel g2 v)). rewrite upd_Znth_same; auto.
      do 2 (split; auto). rewrite Heqr in H10. inversion H10. subst v. pose proof H12.
      apply reachable_foot_valid in H13. eapply copied_vertex_reachable in H12; eauto.
      destruct H12; auto. rewrite Hv in H13. specialize (H5 _ H13 H12).
      destruct H5 as [_ [_ [? _]]]. rewrite H5 in H8. now rewrite H8 in H.
    + exists idx, r. split3; auto. clear - n H10. list_solve.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v) (vgeneration v)) as [_ | Hneq].
    2: contradiction. rewrite H10. red in H7 |- * ; intros. simpl in H4.
    rewrite pcv_evalid_iff in H4. simpl in H9.
    assert (Hi: ~ vvalid g1 (new_copied_v g1 to)). {
      rewrite Hv. intro. now apply (graph_has_v_not_eq _ to) in H11. } destruct H4.
    + rewrite pcv_dst_old in H9. 2: apply He; auto. specialize (H7 _ H4 H8 H9).
      rewrite reachable_from_roots in *. destruct H7 as [idx [r [? [? ?]]]]. pose proof H12.
      rewrite upd_Znth_Zlength; auto. apply reachable_head_valid in H13.
      destruct (Z.eq_dec idx i).
      * subst idx. exists i, (new_copied_v g1 to). rewrite upd_Znth_same; auto.
        do 2 (split; auto). rewrite Heqr in H11. inversion H11. subst v. simpl.
        pose proof H12. apply reachable_head_valid in H14.
        rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)) in H12; auto.
        destruct H12 as [? | [? ?]]; auto. now rewrite <- H12, H8 in H.
      * exists idx, r. rewrite upd_Znth_diff; auto. do 2 (split; auto). simpl.
        rewrite pcv_reachable_old; auto.
    + rewrite reachable_from_roots, upd_Znth_Zlength; auto. exists i, (new_copied_v g1 to).
      rewrite upd_Znth_same; auto. do 2 (split; auto). simpl. rewrite in_map_iff in H4.
      destruct H4 as [ve [? ?]]. subst e. simpl. apply reachable_refl.
      rewrite pcv_vvalid_iff. now right.
Qed.

Lemma fr_O_backward_edge_prop_intr: forall from to intr g1 g2 roots,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    interior_compatible g1 from intr ->
    forward_relation from to O (interior2forward intr g1) g1 g2 ->
    copied_vertex_prop g1 from to -> gen_unmarked g1 to ->
    edge_from_gen_cond intr to -> backward_edge_prop g1 roots from to ->
    backward_edge_prop g2 roots from to.
Proof.
  intros. assert (He: forall e, evalid g1 e -> fst e <> new_copied_v g1 to). {
    intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1 in H9.
    destruct H9. eapply graph_has_v_not_eq in H9; eauto. }
  pose proof (proj1 H1) as Hv. red in Hv. destruct intr. simpl in H3, H4.
  destruct H3 as [? [? [? [? ?]]]].
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> fst e = vertex)
      by (intros e Heeq; apply make_fields_Znth_edge in Heeq; auto; now subst e).
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> graph_has_e g1 e). {
    destruct H1 as [? [? [? _]]]. red in H1, H14, H15. intros. split; rewrite H13; auto.
    rewrite get_edges_In_iff, <- H16. apply Znth_In. now rewrite make_fields_eq_length. }
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> evalid g1 e). {
    intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1. now apply H14. }
  assert (Ht: forall e, evalid g1 e -> vgeneration (fst e) = to ->
                   raw_mark (vlabel g1 (fst e)) = false). {
    intros. red in H6. destruct e as [v ?]. simpl in *. destruct H1 as [_ [? _]]. red in H1.
    rewrite H1 in H16. destruct H16. simpl in H16. destruct v as [gen idx]. simpl in *.
    subst gen. destruct H16. simpl in *. now specialize (H6 H16 _ H17). }
  destruct (Znth field_pos (make_fields g1 vertex)) eqn:?;
    simpl in H4; inversion H4; subst; clear H4; try easy.
  - red in H8 |- * ; intros. subst new_g. destruct_eq_dec e0 e.
    + exfalso. subst e0. simpl in H17. rewrite updateEdgeFunc_eq in H17.
      assert (graph_has_e g1 e) by (now apply H14). red in H2. destruct H18.
      specialize (H2 _ H18 _ H20). specialize (H5 _ H2 H19).
      destruct H5 as [_ [? _]]. now rewrite <- H17, H5 in H.
    + rewrite reachable_from_roots. simpl in *.
      rewrite updateEdgeFunc_neq in H17; auto. specialize (H8 _ H4 H16 H17).
      rewrite reachable_from_roots in H8. destruct H8 as [i [r [? [? ?]]]].
      eapply copied_vertex_pgd_reachable in H21; eauto. exists i, r.
        do 2 (split; auto). destruct H21; auto. rewrite Ht in H21; auto. easy.
  - red in H8 |- * ; intros. subst new_g. simpl in H4, H17. destruct_eq_dec e0 e.
    + exfalso. subst e0. rewrite updateEdgeFunc_eq in H17.
      unfold new_copied_v in H17. simpl in H17. now rewrite <- H17 in H.
    + rewrite updateEdgeFunc_neq in H17; auto. rewrite reachable_from_roots.
      simpl. rewrite pcv_evalid_iff in H4.
      assert (Hi: ~ vvalid g1 (new_copied_v g1 to)). {
        rewrite Hv. intro Hc. now apply (graph_has_v_not_eq _ to) in Hc. }
      assert (He': fst e <> new_copied_v g1 to) by (apply He, H15; auto). destruct H4.
      * rewrite pcv_dst_old in H17. 2: apply He; auto. specialize (H8 _ H4 H16 H17).
        rewrite reachable_from_roots in H8. destruct H8 as [i [r [? [? ?]]]].
        exists i, r. do 2 (split; auto). pose proof H21. apply reachable_head_valid in H22.
        rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to)) in H21; auto.
        assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r (fst e0)) by easy.
        apply (copied_vertex_pgd_reachable _ e to) in H23; simpl in *.
        -- rewrite pcv_dst_old in H23; auto. rewrite ucov_copied_vertex in H23.
           destruct H23; auto. rewrite ucov_not_eq in H23.
           2: intro; now rewrite H24, H16 in H. rewrite lacv_vlabel_old in H23.
           2: apply He; auto. rewrite Ht in H23; auto. easy.
        -- apply lcv_sound; auto.
        -- rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
        -- rewrite pcv_evalid_iff. left. apply H15; auto.
        -- rewrite pcv_dst_old; auto. apply ucov_rawmark.
      * rewrite in_map_iff in H4. destruct H4 as [ve [? ?]]. subst e0. simpl in *.
        assert (evalid g1 e) by (apply H15; auto).
        assert (vgeneration (fst e) = to). {
          apply make_fields_Znth_edge in Heqf; auto. subst e. now simpl. }
        specialize (H8 _ H4 H21 (eq_refl (vgeneration (dst g1 e)))).
        rewrite reachable_from_roots in H8. destruct H8 as [i [r [? [? ?]]]].
        exists i, r. do 2 (split; auto). pose proof (reachable_head_valid _ _ _ H23).
        rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to)) in H23; auto.
        assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r (fst e)) by easy.
        apply (copied_vertex_pgd_reachable _ e to) in H25; simpl in *.
        -- rewrite pcv_dst_old in H25; auto. rewrite ucov_copied_vertex, ucov_not_eq in H25.
           2: intro; now rewrite H26, H21 in H. rewrite lacv_vlabel_old in H25; auto.
           rewrite Ht in H25; auto. destruct H25; [|easy].
           apply reachable_trans with (fst e); auto. exists (fst e, [e]).
           split; split; simpl; auto. 3: red; rewrite Forall_forall; intros; auto.
           1: rewrite updateEdgeFunc_eq; auto. destruct H1 as [? [? [? _]]]. red in H27.
           split. 1: rewrite pcv_src_old; auto. red. simpl. red in H1, H26.
           rewrite updateEdgeFunc_eq. rewrite pcv_src_old; auto. split3.
           ** rewrite pcv_evalid_iff. now left.
           ** rewrite pcv_vvalid_iff, H27. left. rewrite H1. rewrite H26 in H4.
              now destruct H4.
           ** rewrite pcv_vvalid_iff. now right.
        -- apply lcv_sound; auto.
        -- rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
        -- rewrite pcv_evalid_iff. now left.
        -- rewrite pcv_dst_old; auto. apply ucov_rawmark.
Qed.

Definition reachable_or_marked (from: nat) (g: LGraph)
           (roots: roots_t) (v: VType): Prop :=
  vgeneration v = from /\
    (reachable_through_set g (filter_proj exterior_proj_vertex roots) v \/
       vvalid g v /\ raw_mark (vlabel g v) = true).

Definition reachable_or_marked_special_cond (g: LGraph) (roots: roots_t)
           (from to: nat) (intr: interior_t): Prop :=
  match intr with
  | InteriorVertexPos v _ => vgeneration v = to /\ backward_edge_prop g roots from to
  end.

Lemma fr_O_reachable_or_marked_intr: forall
    (from to : nat) (intr : interior_t) (g1 g2 : LGraph) (roots : roots_t),
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    roots_graph_compatible roots g1 ->
    copied_vertex_prop g1 from to -> interior_compatible g1 from intr ->
    reachable_or_marked_special_cond g1 roots from to intr ->
    forward_relation from to O (interior2forward intr g1) g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <-> reachable_or_marked from g2 roots v.
Proof.
  intros. assert (Hr: forall i r, 0 <= i < Zlength roots -> Znth i roots = ExteriorVertex r ->
                             graph_has_v g1 r). {
    intros. red in H3. rewrite Forall_forall in H3. apply H3.
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- H9. now apply Znth_In. }
  pose proof (proj1 H1) as Hv. red in Hv. destruct intr. simpl in H5, H6, H7.
  destruct H5 as [? [? [? [? ?]]]].
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> fst e = vertex)
    by (intros e Hs; apply make_fields_Znth_edge in Hs; auto; now subst e).
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> graph_has_e g1 e). {
    destruct H1 as [? [? [? _]]]. red in H1, H13, H14. intros. split; rewrite H12; auto.
    unfold get_edges. rewrite <- (filter_proj_In_iff field_proj_edge_spec), <- H15.
    apply Znth_In. now rewrite make_fields_eq_length. }
  assert (forall e, Znth field_pos (make_fields g1 vertex) = FieldEdge e -> evalid g1 e). {
    intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1. now apply H13. }
  destruct (Znth field_pos (make_fields g1 vertex)) eqn:? ; simpl in H7;
    inversion H7; subst; try easy.
  - split; intros; red in H15 |- * ; destruct H15; split; auto; destruct H16.
    + rewrite reachable_from_roots in *. destruct H16 as [i [r [? [? ?]]]].
      subst new_g. simpl. assert (evalid g1 e) by (now apply H14).
      assert (vvalid g1 v) by (now apply reachable_foot_valid in H19).
      eapply copied_vertex_pgd_reachable in H19; eauto. destruct H19. 2: now right.
      left. exists i, r. auto.
    + subst new_g. simpl. now right.
    + rewrite reachable_from_roots in *. destruct H16 as [i [r [? [? ?]]]].
      subst new_g. simpl in *. left. exists i, r. do 2 (split; auto).
      eapply copied_vertex_pgd_reachable_inv in H19; eauto.
    + subst new_g. simpl in H16. now right.
  - assert (Hs: sound_gc_graph (lgraph_copy_v g1 (dst g1 e) to)) by
      (now apply lcv_sound). assert (~ vvalid g1 (new_copied_v g1 to)). {
      rewrite Hv. intro. now apply graph_has_v_not_eq with (to := to) in H15. }
    split; intros; red in H16 |-* ; destruct H16; split; auto; destruct H18.
    + rewrite reachable_from_roots in *. destruct H18 as [i [r [? [? ?]]]].
      subst new_g. simpl. assert (vvalid g1 r) by (now apply reachable_head_valid in H20).
      rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to)) in H20; auto.
      assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r v) by (now simpl).
      assert (fst e <> new_copied_v g1 to) by
        (rewrite H12; auto; intro; subst vertex; now rewrite <- Hv in H5).
      apply (copied_vertex_pgd_reachable _ e to) in H22; auto; simpl in *.
      * rewrite pcv_dst_old, ucov_copied_vertex in H22; auto. destruct H22.
         ++ left. exists i, r. auto.
         ++ right; split; auto. apply reachable_foot_valid in H20. auto.
      * rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
      * rewrite pcv_evalid_iff. left. now apply H14.
      * rewrite pcv_dst_old; auto. apply ucov_rawmark.
    + destruct H18. right. subst new_g. simpl. split.
      * rewrite pcv_vvalid_iff. now left.
      * rewrite ucov_not_eq. 2: intro; subst v; now rewrite H17 in H19.
         rewrite lacv_vlabel_old; auto. intro. now subst v.
    + rewrite reachable_from_roots in *. destruct H18 as [i [r [? [? ?]]]].
      subst new_g. remember (lgraph_copy_v g1 (dst g1 e) to) as g3.
      assert (fst e <> new_copied_v g1 to) by
        (rewrite H12; auto; intro; subst vertex; now rewrite <- Hv in H5).
      assert (dst g1 e = dst g3 e) by (subst g3; simpl; rewrite pcv_dst_old; auto).
      assert (new_copied_v g1 to = copied_vertex (vlabel g3 (dst g3 e))). {
        rewrite <- H22. subst g3. simpl. rewrite ucov_copied_vertex. easy. }
      rewrite H23 in H20. apply copied_vertex_pgd_reachable_inv with (to := to)
        in H20; try (now rewrite <- H22); try (now subst g3).
      * rewrite Heqg3 in H20. simpl in H20. assert (vvalid g1 r) by
          (rewrite Hv; apply Hr with i; auto). left. exists i, r.
        rewrite pcv_reachable_old in H20; auto.
      * rewrite <- H22. subst g3. apply lcv_copied_vertex_prop; auto.
      * subst g3. apply lcv_no_dangling_dst; auto. red in H2. assert (graph_has_e g1 e)
          by (now apply H13). destruct H24. apply H2 with (fst e); auto.
      * subst g3. simpl. rewrite pcv_evalid_iff. left. now apply H14.
      * rewrite <- H22. subst g3. apply lcv_raw_mark_old.
    + destruct H18. subst new_g. simpl in *. rewrite pcv_vvalid_iff in H18.
      assert (v <> new_copied_v g1 to). {
        intro. subst. unfold new_copied_v in *. simpl in *.
        now rewrite <- H16 in H. } destruct H18. 2: easy.
      destruct_eq_dec (dst g1 e) v.
      * subst v. rewrite ucov_rawmark in H19. left. destruct H6 as [He Hb].
        red in Hb. assert (evalid g1 e) by (apply H14; auto).
        assert (vgeneration (fst e) = to). {
          apply make_fields_Znth_edge in Heqf; auto. subst e. now simpl. }
        specialize (Hb _ H6 H21 H16). rewrite reachable_from_roots in *.
        destruct Hb as [i [r [? [? ?]]]]. exists i, r. do 2 (split; auto).
        apply reachable_trans with (fst e); auto. destruct H1 as [? [? [? _]]].
        red in H1, H25, H26. exists (fst e, [e]). split; split; simpl; auto.
        2: red; rewrite Forall_forall; intros; auto. rewrite H26. split; auto.
        red. do 2 (split; auto). rewrite H26. rewrite H25 in H6. destruct H6.
        rewrite <- H1 in H6. easy.
      * rewrite ucov_not_eq in H19; auto. rewrite lacv_vlabel_old in H19; auto.
Qed.

Lemma fr_O_reachable_or_marked_roots: forall
    (from to : nat) (i : Z) (g1 g2 : LGraph) (roots : roots_t),
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    roots_graph_compatible roots g1 ->
    copied_vertex_prop g1 from to -> 0 <= i < Zlength roots ->
    forward_relation from to O (exterior2forward (Znth i roots)) g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
           reachable_or_marked from g2 (upd_roots from to i g1 roots) v.
Proof.
  intros. assert (Hr: forall i r, 0 <= i < Zlength roots -> Znth i roots = ExteriorVertex r ->
                             graph_has_v g1 r). {
    intros. red in H3. rewrite Forall_forall in H3. apply H3.
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- H8. now apply Znth_In. }
  pose proof (proj1 H1) as Hv. red in Hv. unfold upd_roots, upd_exterior.
  destruct (Znth i roots) eqn:Heqr;
    simpl in *; rewrite ?Heqr; inversion H6; subst; clear H6; try easy;
    try (rewrite <- Heqr, upd_Znth_unchanged'); auto; try easy.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v0) from) as [Hvfrom | _].
    1: contradiction. rewrite <- Heqr, upd_Znth_unchanged'; easy.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v0) (vgeneration v0)) as [_ | Hneq].
    2: contradiction. rewrite H10.
    split; intros; red in H6 |- * ; destruct H6; split; auto.
    + destruct H7; [| right]; auto. rewrite reachable_from_roots in H7.
      destruct H7 as [idx [r [? [? ?]]]]. destruct (Z.eq_dec idx i).
      * subst idx. rewrite Heqr in H8. inversion H8.
        assert (vvalid g2 v) by (apply reachable_foot_valid in H9; auto).
        subst v0. clear H8. eapply copied_vertex_reachable in H9; eauto.
        destruct H9. 2: right; auto. left. rewrite reachable_from_roots.
        exists i, (copied_vertex (vlabel g2 r)). rewrite upd_Znth_Zlength, upd_Znth_same; auto.
      * left. rewrite reachable_from_roots. exists idx, r.
        rewrite upd_Znth_Zlength, upd_Znth_diff; auto.
    + destruct H7; [| right]; auto. rewrite reachable_from_roots in H7.
      rewrite upd_Znth_Zlength in H7; auto. destruct H7 as [idx [r [? [? ?]]]].
      destruct (Z.eq_dec idx i).
      * subst idx. rewrite upd_Znth_same in H8; auto. inversion H8. subst r. clear H8.
        rename v0 into r. left. rewrite reachable_from_roots. exists i, r. do 2 (split; auto).
        eapply copied_vertex_reachable_inv; eauto.
      * left. rewrite reachable_from_roots. exists idx, r. rewrite upd_Znth_diff in H8; auto.
  - unfold update_vertex. destruct (Nat.eq_dec (vgeneration v0) (vgeneration v0)) as [_ | Hneq].
    2: contradiction. rewrite H9.
    assert (Hs: sound_gc_graph (lgraph_copy_v g1 v0 to)) by (now apply lcv_sound).
    assert (~ vvalid g1 (new_copied_v g1 to)). {
      rewrite Hv. intro. now apply graph_has_v_not_eq with (to := to) in H6. }
    split; intros; red in H7 |- * ; destruct H7; split; auto; destruct H8.
    + rewrite reachable_from_roots in H8. destruct H8 as [idx [r [? [? ?]]]].
      assert (vvalid g1 r) by (now apply reachable_head_valid in H11).
      destruct (Z.eq_dec idx i).
      * rewrite e, Heqr in H10. inversion H10. subst v0.
        rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)) in H11; auto. clear H10.
        destruct H11; [right | left].
        -- subst v. rewrite lcv_raw_mark_old. destruct Hs. red in H10. rewrite H10.
           split; auto. apply lcv_graph_has_v_old; auto. now rewrite <- Hv.
        -- rewrite reachable_from_roots. exists idx, (new_copied_v g1 to).
           subst idx; rewrite upd_Znth_Zlength, upd_Znth_same; auto. do 2 (split; auto).
           simpl. now destruct H8.
      * left. rewrite reachable_from_roots. exists idx, r.
        rewrite upd_Znth_Zlength, upd_Znth_diff; auto. do 2 (split; auto).
        simpl. rewrite pcv_reachable_old; auto.
    + destruct H8. right. destruct Hs. red in H11. rewrite H11.
      assert (graph_has_v g1 v) by (destruct H1; red in H1; now rewrite <- H1).
      split. 1: apply lcv_graph_has_v_old; auto. rewrite <- lcv_raw_mark; auto.
      intro. subst v0. now rewrite H9 in H10.
    + rewrite reachable_from_roots in *. destruct H8 as [idx [r [? [? ?]]]].
      rewrite upd_Znth_Zlength in H8; auto. destruct (Z.eq_dec idx i).
      * subst idx. rewrite upd_Znth_same in H10; auto. inversion H10. subst r. clear H10.
        simpl in H11. left. exists i, v0.
        rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)); auto.
        2: destruct H1; red in H1; rewrite H1; apply (Hr i); auto.
        do 2 (split; auto). right. split; auto. intro. subst v. rewrite <- H7 in H.
        unfold new_copied_v in H. now simpl in H.
      * left. rewrite upd_Znth_diff in H10; auto. simpl in H11.
        rewrite pcv_reachable_old in H11; auto. 1: exists idx, r; auto.
        rewrite Hv. eapply Hr; eauto.
    + destruct H8. destruct_eq_dec v v0.
      * subst v0. left. rewrite reachable_from_roots. exists i, v.
        do 2 (split; auto). apply reachable_refl. rewrite Hv. eapply Hr; eauto.
      * right. destruct Hs. red in H12. rewrite H12, lcv_graph_has_v_iff in H8; auto.
        destruct H8.
        2: subst v; rewrite <- H7 in H; unfold new_copied_v in H; now simpl in H.
        split. 1: now rewrite <- Hv in H8. rewrite <- lcv_raw_mark in H10; auto.
Qed.

Lemma frr_rom_aux: forall from to (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall ready v,
       roots_graph_compatible ready g1 ->
       (reachable_or_marked from g1 (ready ++ roots1) v <->
        reachable_or_marked from g2 (ready ++ roots2) v).
Proof.
  intros * ? ? ? ? ? ? ? ?.
  induction H6; [ tauto | ]; intros.
  rename IHforward_roots_relation into IH.
  assert (H0' := fr_O_sound _ _ _ _ _ H0 H1 H6).
  assert (H1' := proj1 (fr_graph_has_gen _ _ _ _ _ _ H1 H6 to) H1).
  assert (H5' := fr_copy_compatible _ _ _ _ _ _ H H1 H6 H5).
  assert (Hv: forward_p_compatible' (FwdPntExtr r) g1 from). {
    simpl. destruct r; simpl; auto. now apply rgc_cons_vertex in H2. }
  assert (H3' := fr_O_no_dangling_dst' from to (FwdPntExtr r) g1 g2 Hv H1 H5 H6 H3).
  assert (H2' := fr_upd_roots_graph_compatible 0 from to (Zlength ready)
                   g1 g2 (ready ++ r :: roots1) H1 H5 ltac:(simpl; list_solve)).
  unfold upd_roots in H2'. autorewrite with sublist in H2'. rewrite upd_Znth0 in H2'.
  rewrite roots_graph_compatible_app in H2'. specialize (H2' H6 H (conj H8 H2)).
  change (?A::?B) with ([A]++B) in H2'.
  rewrite !roots_graph_compatible_app in H2'; destruct H2' as [H11 [H2'' H2']].
  assert (H4' := fr_O_copied_vertex_prop from to (FwdPntExtr r) g1 g2 H H1 H0 H3 Hv H6 H4).
  specialize (IH H0' H1' H2' H3' H4' H5' (ready +:: upd_exterior from to g1 r) v).
  rewrite <- !app_assoc in IH. rewrite <- IH; clear IH.
  2: rewrite roots_graph_compatible_app; split; auto.
  rewrite (fr_O_reachable_or_marked_roots from to (Zlength ready) g1 g2
             (ready ++ r :: roots1)); auto.
  - unfold upd_roots. simpl. autorewrite with sublist. rewrite upd_Znth0. tauto.
  - change (r :: roots1) with ([r] ++ roots1).
    rewrite roots_graph_compatible_app; split; auto.
  - simpl; list_solve.
  - autorewrite with sublist. assumption.
Qed.

Lemma svfl_reachable_or_marked: forall from to (roots: roots_t) r l g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> graph_has_v g1 r ->
    raw_mark (vlabel g1 r) = false ->
    raw_tag (vlabel g1 r) < NO_SCAN_TAG ->
    vgeneration r = to -> gen_unmarked g1 to ->
    roots_graph_compatible roots g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 r)))%nat) ->
    backward_edge_prop g1 roots from to -> scan_vertex_for_loop from to r l g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
              reachable_or_marked from g2 roots v.
Proof.
  pose (H6:=True).
  intros until l. induction l; intros ? ? ? ? ? ? ? NOSCAN; intros; inversion H13;
    subst; clear H13; try easy. pose proof H16.
  assert (Hp: forward_p2forward_t (FwdPntIntr (InteriorVertexPos r (Z.of_nat a))) g1 =
                interior2forward (InteriorVertexPos r (Z.of_nat a)) g1) by easy.
  assert (interior_compatible g1 from (InteriorVertexPos r (Z.of_nat a))). {
    simpl. split3; [ | | split3]; auto. split; auto. lia. rewrite Zlength_correct.
    apply inj_lt, H11. now left. }
  eapply fr_O_reachable_or_marked_intr with (g2 := g3) (v := v) in H4; eauto.
  2: simpl; split; auto. remember (vgeneration r) as to. rewrite H4. apply IHl; auto.
  - eapply fr_O_sound; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto. subst to; auto.
  - erewrite <- fr_raw_tag; eauto. subst to; auto.
  - eapply fr_gen_unmarked; eauto.
  - eapply fr_roots_graph_compatible; eauto.
  - rewrite <- Hp in H16. eapply fr_O_no_dangling_dst'; eauto. apply H13.
  - rewrite <- Hp in H16. eapply fr_O_copied_vertex_prop; eauto. apply H13.
  - eapply fr_copy_compatible; eauto.
  - erewrite <- fr_raw_fields; eauto. intros. apply H11. now right.
  - eapply fr_O_backward_edge_prop_intr in H16; eauto. now simpl.
Qed.

Lemma svfl_copied_vertex_prop: forall from to v l g1 g2,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    raw_tag (vlabel g1 v) < NO_SCAN_TAG ->
    vgeneration v <> from ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 v)))%nat) ->
    copy_compatible g1 -> scan_vertex_for_loop from to v l g1 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  intros until l. induction l; intros ? ? ? ? ? ? ? ? NOSCAN; intros; inversion H8;
    subst; clear H8; try easy. pose proof H12.
  assert (forward_p_compatible' (FwdPntIntr (InteriorVertexPos v (Z.of_nat a))) g1 from). {
    simpl. do 3 (split; auto). 1: lia. rewrite Zlength_correct. apply inj_lt, H6.
    now left. } eapply (fr_O_copied_vertex_prop _ _ _ g1 g3) in H9; eauto.
  apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_O_sound; eauto.
  - eapply fr_O_no_dangling_dst'; eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto.
  - erewrite <- fr_raw_tag; eauto.
  - intros. erewrite <- fr_raw_fields; eauto. apply H6. now right.
  - eapply (fr_copy_compatible O from to); eauto.
Qed.

Lemma svfl_backward_edge_prop: forall from to roots v l g1 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 -> sound_gc_graph g1 ->
    no_dangling_dst g1 -> gen_unmarked g1 to ->
    copied_vertex_prop g1 from to ->  roots_graph_compatible roots g1 ->
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    raw_tag (vlabel g1 v) < NO_SCAN_TAG ->
    vgeneration v = to ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 v)))%nat) ->
    backward_edge_prop g1 roots from to -> scan_vertex_for_loop from to v l g1 g2 ->
    backward_edge_prop g2 roots from to.
Proof.
  pose (H4:=True).
  intros until l. induction l; intros ? ? ? ? ? ? ? ? ? ? ? ? NOSCAN; intros;
    inversion H13; subst; clear H13; try easy. pose proof H16.
  assert (Hp: forward_p2forward_t (FwdPntIntr (InteriorVertexPos v (Z.of_nat a))) g1 =
                interior2forward (InteriorVertexPos v (Z.of_nat a)) g1) by easy.
  assert (interior_compatible g1 from (InteriorVertexPos v (Z.of_nat a))). {
    simpl. do 3 (split; auto). 1: lia. rewrite Zlength_correct. apply inj_lt, H11.
    now left. }
  eapply fr_O_backward_edge_prop_intr in H10; eauto. 2: now simpl.
  remember (vgeneration v) as to. apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
  - eapply fr_O_sound; eauto.
  - rewrite <- Hp in H16. eapply fr_O_no_dangling_dst'; eauto. apply H13.
  - eapply fr_gen_unmarked; eauto.
  - rewrite <- Hp in H16. eapply fr_O_copied_vertex_prop; eauto. apply H13.
  - eapply fr_roots_graph_compatible in H16; eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto. subst to. auto.
  - erewrite <- fr_raw_tag; eauto. subst to. auto.
  - intros. erewrite <- fr_raw_fields; eauto. apply H11. now right.
Qed.

Lemma svwl_reachable_or_marked: forall from to (roots: roots_t) l g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> gen_unmarked g1 to ->
    roots_graph_compatible roots g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    backward_edge_prop g1 roots from to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
              reachable_or_marked from g2 roots v.
Proof.
  pose (H3:=True).
  do 4 intro. induction l; intros; inversion H9; subst; clear H9; try easy.
  1: apply IHl; auto. pose proof H14.
  eapply svfl_reachable_or_marked with (v := v) in H9; eauto.
  2: split; simpl; auto.
  2: unfold no_scan in H13; lia.
  2: intros; now rewrite nat_inc_list_In_iff in H10.
  rewrite H9. assert (graph_has_v g1 (to, a)) by (now split).
  assert (forall i : nat,
             In i (nat_inc_list (length (raw_fields (vlabel g1 (to, a))))) ->
             (i < length (raw_fields (vlabel g1 (to, a))))%nat). {
    intros. rewrite nat_inc_list_In_iff in H11; auto. } apply IHl; auto.
  - eapply svfl_P_holds; eauto. apply fr_O_sound.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_gen_unmarked; eauto.
  - eapply svfl_roots_graph_compatible; eauto.
  - eapply (svfl_no_dangling_dst from to); eauto. unfold no_scan in H13; lia.
  - eapply svfl_copied_vertex_prop; eauto. unfold no_scan in H13; lia.
  - eapply svfl_copy_compatible; eauto.
  - eapply svfl_backward_edge_prop; eauto. unfold no_scan in H13; lia.
Qed.

Lemma frr_copied_vertex_prop: forall from to (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> no_dangling_dst g1 ->
    copy_compatible g1 -> roots_graph_compatible roots1 g1 ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  induction 7; intros; auto.
  assert (H0' := fr_O_sound _ _ _ _ _ H0 H1 H5).
  assert (H1' := proj1 (fr_graph_has_gen _ _ _ _ _ _ H1 H5 to) H1).
  assert (H5' := fr_copy_compatible _ _ _ _ _ _ H H1 H5 H3).
  assert (Hv: forward_p_compatible' (FwdPntExtr r) g1 from). {
    simpl. destruct r; simpl; auto. now apply rgc_cons_vertex in H4. }
  assert (H3' := fr_O_no_dangling_dst' from to (FwdPntExtr r) g1 g2 Hv H1 H3 H5 H2).
  assert (H4' := fr_upd_roots_graph_compatible 0 from to 0 g1 g2 (r :: roots1)
                   H1 H3 ltac:(list_solve) H5 H H4). unfold upd_roots in H4'.
  rewrite Znth_0_cons, upd_Znth0 in H4'. change (?A::?B) with ([A]++B) in H4'.
  rewrite roots_graph_compatible_app in H4'; destruct H4'.
  apply IHforward_roots_relation; auto.
  eapply fr_O_copied_vertex_prop with (p := FwdPntExtr r); try apply H5; auto.
Qed.

Lemma backward_edge_prop_incl: forall r1 r2 g from to,
    (forall x, In x r1 -> In x r2) ->
    backward_edge_prop g r1 from to ->
    backward_edge_prop g r2 from to.
Proof.
  unfold backward_edge_prop; intros.
  specialize (H0 e H1 H2 H3); clear - H H0.
  destruct H0 as [s [? ?]]; exists s; split; auto.
  clear H1.
  apply (filter_proj_In_iff exterior_proj_vertex_spec) in H0.
  apply (filter_proj_In_iff exterior_proj_vertex_spec).
  auto.
Qed.

Lemma remset_semi_iso_backward_edge_prop_mapped_roots:
  forall base g from to l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base g from to l ->
    no_unmarked_old_nonfrom_dst base g from ->
    backward_edge_prop
      g (remset_ready_roots l) from to.
Proof.
  unfold backward_edge_prop.
  intros base g from to l Hneq Hsound_base Hsound_g Hndd_base Hsemi Hclosed.
  intros e He_g Hsrc_to Hdst_from.
  pose proof Hsemi as Hsemi0.
  pose proof Hsound_base as Hsound_base_full.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  destruct Hsound_g as [Hvv_g [Hev_g _]].
  assert (Hge_g: graph_has_e g e) by (apply (proj1 (Hev_g _)); exact He_g).
  destruct Hge_g as [Hsrc_has_g Hfield_g].
  assert (Hsrc_valid_g: vvalid g (fst e)) by
      (apply (proj2 (Hvv_g _)); exact Hsrc_has_g).
  destruct (vvalid_lcm base (fst e) Hvv_base) as [Hsrc_valid_base | Hsrc_not_base].
  - assert (Hsrc_not_from: vgeneration (fst e) <> from) by congruence.
    destruct Hsemi as [_ Hspec].
    destruct (split l) as [from_l to_l] eqn:Hsplit.
    destruct Hspec as [[_ Hfrom] [_ [Hlabel _]]].
    assert (Hsrc_not_in: ~ In (fst e) from_l). {
      intro Hin.
      rewrite <- Hfrom in Hin.
      destruct Hin as [_ [_ Hsrc_from]].
      contradiction.
    }
    assert (Hlabel_src: vlabel base (fst e) = vlabel g (fst e)) by
        (apply Hlabel; assumption).
    assert (Hge_base: graph_has_e base e). {
      split.
      - apply (proj1 (Hvv_base _)); exact Hsrc_valid_base.
      - unfold get_edges, make_fields in Hfield_g |- *.
        rewrite Hlabel_src. exact Hfield_g.
    }
    assert (He_base: evalid base e) by
        (apply (proj2 (Hev_base _)); exact Hge_base).
    destruct (raw_mark (vlabel g (dst g e))) eqn:Hmark.
    + exfalso.
      exact (remset_semi_iso_no_marked_old_nonfrom_edge
               base g from to l e Hneq Hsound_base_full Hndd_base
               Hsemi0 He_base Hsrc_not_from Hdst_from Hmark).
    + exfalso.
      exact (remset_semi_iso_no_unmarked_old_nonfrom_edge
               base g from to l e Hneq Hsound_base_full Hndd_base
               Hsemi0 Hclosed He_base Hsrc_not_from Hdst_from Hmark).
  - destruct Hsemi0 as [_ Hspec].
    destruct (split l) as [from_l to_l] eqn:Hsplit.
    destruct Hspec as [_ [[_ [Hto_valid _]] _]].
    assert (Hin_to: In (fst e) to_l). {
      rewrite Hto_valid.
      split; assumption.
    }
    assert (Hin_snd: In (fst e) (map snd l)). {
      rewrite map_snd_split, Hsplit.
      exact Hin_to.
    }
    rewrite in_map_iff in Hin_snd.
    destruct Hin_snd as [[v_old v_new] [Hsnd Hin_pair]].
    simpl in Hsnd. subst v_new.
    assert (Hdd: DoubleNoDup l) by
        (eapply remset_semi_iso_DoubleNoDup; eauto).
    destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hin_pair) as [Hmap _].
    exists (fst e).
    split.
    + rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
      unfold remset_ready_roots, roots_map.
      rewrite in_map_iff.
      exists (ExteriorVertex v_old).
      split.
      * simpl. exact (f_equal ExteriorVertex Hmap).
      * assert (Hin_fst: In v_old (map fst l)). {
          apply in_map with (f := fst) in Hin_pair.
          exact Hin_pair.
        }
        apply in_map. exact Hin_fst.
    + apply reachable_refl. exact Hsrc_valid_g.
Qed.

Lemma remset_semi_iso_mapped_roots_have_no_gen:
  forall base g from to l,
    from <> to ->
    gc_graph_remset_semi_iso base g from to l ->
    roots_have_no_gen (remset_ready_roots l) from.
Proof.
  unfold roots_have_no_gen, remset_ready_roots, roots_map.
  intros base g from to l Hneq Hsemi root Hin Hgen.
  rewrite in_map_iff in Hin.
  destruct Hin as [root0 [Hroot Hin0]].
  rewrite in_map_iff in Hin0.
  destruct Hin0 as [v [Hroot0 Hin_fst]].
  subst root0.
  simpl in Hroot. inversion Hroot; subst root.
  rewrite In_map_fst_iff in Hin_fst.
  destruct Hin_fst as [v2 Hpair].
  assert (Hdd: DoubleNoDup l) by
      (eapply remset_semi_iso_DoubleNoDup; eauto).
  destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hpair) as [Hmap _].
  rewrite Hmap in Hgen.
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [_ [[_ [_ Hto_gen]] _]].
  assert (Hin_to: In v2 to_l). {
    apply In_map_snd in Hpair.
    now rewrite map_snd_split, Hsplit in Hpair.
  }
  specialize (Hto_gen _ Hin_to).
  lia.
Qed.

Lemma remset_semi_iso_mapped_roots_graph_compatible:
  forall base g from to l,
    from <> to ->
    sound_gc_graph g ->
    gc_graph_remset_semi_iso base g from to l ->
    roots_graph_compatible
      (remset_ready_roots l) g.
Proof.
  unfold roots_graph_compatible, remset_ready_roots, roots_map.
  intros base g from to l Hneq Hsound Hsemi.
  rewrite Forall_forall.
  intros v Hin.
  rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [root0 [Hroot Hin0]].
  rewrite in_map_iff in Hin0.
  destruct Hin0 as [v0 [Hroot0 Hin_fst]].
  subst root0.
  simpl in Hroot. inversion Hroot; subst v.
  rewrite In_map_fst_iff in Hin_fst.
  destruct Hin_fst as [v2 Hpair].
  assert (Hdd: DoubleNoDup l) by
      (eapply remset_semi_iso_DoubleNoDup; eauto).
  destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hpair) as [Hmap _].
  rewrite Hmap.
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [_ [[_ [Hto_valid _]] _]].
  assert (Hin_to: In v2 to_l). {
    apply In_map_snd in Hpair.
    now rewrite map_snd_split, Hsplit in Hpair.
  }
  rewrite Hto_valid in Hin_to.
  destruct Hin_to as [Hvalid _].
  destruct Hsound as [Hvv _].
  apply (proj1 (Hvv _)). exact Hvalid.
Qed.

Lemma frr_bep_aux: forall from to (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> no_dangling_dst g1 ->
    copy_compatible g1 -> roots_graph_compatible roots1 g1 ->
    copied_vertex_prop g1 from to ->
    gen_unmarked g1 to ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall ready,
      backward_edge_prop g1 (ready ++ roots1) from to ->
      backward_edge_prop g2 (ready ++ roots2) from to.
Proof.
 induction 9; intros; auto.
 assert (H0' := fr_O_sound _ _ _ _ _ H0 H1 H7).
 assert (H1' := proj1 (fr_graph_has_gen _ _ _ _ _ _ H1 H7 to) H1).
 assert (H3' := fr_copy_compatible _ _ _ _ _ _ H H1 H7 H3).
 assert (Hv: forward_p_compatible' (FwdPntExtr r) g1 from). {
   simpl. destruct r; simpl; auto. apply rgc_cons_vertex in H4. assumption. }
 assert (H2' := fr_O_no_dangling_dst' from to (FwdPntExtr r) g1 g2 Hv H1 H3 H7 H2).
 assert (H4' := fr_upd_roots_graph_compatible 0 from to 0 g1 g2
                  (r :: roots1) H1 H3 ltac:(list_solve) H7 H H4).
 unfold upd_roots in H4'. rewrite Znth_0_cons, upd_Znth0 in H4'.
 change (?A::?B) with ([A]++B) in H4'.
 rewrite roots_graph_compatible_app in H4'; destruct H4'.
 assert (H5' := fr_O_copied_vertex_prop from to (FwdPntExtr r) g1 g2 H H1 H0 H2 Hv H7 H5).
 change (?A::?B) with ([A]++B) in H9 |- * . rewrite app_assoc in H9 |- * .
 apply IHforward_roots_relation; auto. eapply fr_gen_unmarked; try apply H7; auto.
 pose proof fr_O_backward_edge_prop_roots from to (Zlength ready) g1 g2
   (ready ++ r :: roots1) H H1 H0 H2 ltac:(list_solve). unfold upd_roots in H12.
 autorewrite with sublist in H12. rewrite upd_Znth0 in H12. rewrite <- !app_assoc in H9 |- * .
 simpl in H9 |- * . apply H12; assumption.
Qed.

Lemma reachable_or_marked_iff_marked: forall g roots from v,
    sound_gc_graph g -> no_edge2gen g from -> roots_have_no_gen roots from ->
    reachable_or_marked from g roots v <->
    raw_mark (vlabel g v) = true /\ vvalid g v /\ vgeneration v = from.
Proof.
  intros. unfold reachable_or_marked. split; intros; destruct H2.
  2: destruct H3; split; auto. destruct H3 as [? | [? ?]]; auto. exfalso.
  rewrite reachable_from_roots in H3. destruct H3 as [i [r [? [? ?]]]]. red in H1.
  assert (vgeneration r <> from) by (apply H1; rewrite <- H4; now apply Znth_In).
  clear i H1 H3 H4. unfold reachable, reachable_by in H5. destruct H5 as [[? p] ?].
  pose proof H1. apply reachable_by_path_head in H3. simpl in H3. subst v0.
  remember (length p) as n. assert (length p <= n)%nat by lia. clear Heqn.
  revert r p H3 H1 H6. induction n; intros.
  - destruct p. 2: simpl in H3; lia. destruct H1 as [[_ ?] _]. simpl in H1.
    subst v. now rewrite H2 in H6.
  - destruct p.
    + destruct H1 as [[_ ?] _]. simpl in H1. subst v. now rewrite H2 in H6.
    + pose proof H1. change (e :: p) with (nil ++ e :: p) in H1.
      apply reachable_by_path_app_cons in H1. destruct H1 as [_ ?].
      assert (length p <= n)%nat by (simpl in H3; lia). specialize (IHn _ _ H5 H1).
      apply IHn. red in H0. unfold gen2gen_no_edge in H0.
      destruct H4 as [_ [? _]]. rewrite valid_path_cons_iff in H4.
      destruct H4 as [? [[? _] _]]. destruct H as [? [? [? _]]]. red in H, H8, H9.
      rewrite H9 in *. destruct e as [[gen vidx] eidx]. simpl in *. subst r.
      simpl in *. rewrite H8 in H7. apply H0; auto.
Qed.

Lemma frr_sound: forall (g1 g2 : LGraph) from to roots1 roots2,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    forward_roots_relation from to roots1 g1 roots2 g2 -> sound_gc_graph g2.
Proof. intros. eapply frr_P_holds; eauto. apply fr_O_sound. Qed.

Lemma dsr_sound: forall (g1 g2 : LGraph) from to to_index,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    do_scan_relation from to to_index g1 g2 -> sound_gc_graph g2.
Proof. intros. eapply dsr_P_holds; eauto. apply fr_O_sound. Qed.

Definition remset_ext_effective_root (rext: remset_ext): option VType :=
  match rext with
  | RemSetVertex v _ => Some v
  | RemSetOutlier _ _ => None
  end.

Definition remset_item_effective_root
           (g: LGraph) (rmst: remset) (item: remset_space_item): option VType :=
  match item with
  | RemSetInterior (InteriorVertexPos v pos) =>
      match Znth pos (make_fields g v) with
      | FieldEdge e => Some (dst g e)
      | _ => None
      end
  | RemSetExterior addr =>
      match find_remset_ext addr rmst with
      | Some rext => remset_ext_effective_root rext
      | None => None
      end
  end.

Definition remset_ext2forward_p (rext: remset_ext): forward_p_type :=
  FwdPntExtr (remset_ext2exterior_t rext).

Definition remset_item2forward_p (item: remset_space_item) (rmst: remset)
  : forward_p_type :=
  match item with
  | RemSetInterior intr => FwdPntIntr intr
  | RemSetExterior addr =>
      match find_remset_ext addr rmst with
      | Some rext => remset_ext2forward_p rext
      | None => FwdPntExtr (ExteriorUnboxed 0)
      end
  end.

Lemma remset_item2forward_p_eq:
  forall g rmst item,
    forward_p2forward_t (remset_item2forward_p item rmst) g =
    remset_item2forward_t item rmst g.
Proof.
  intros g rmst item.
  destruct item as [addr | intr]; simpl; auto.
  destruct (find_remset_ext addr rmst); reflexivity.
Qed.

Lemma find_remset_ext_nodup:
  forall rmst rext,
    remset_nodup rmst ->
    In rext rmst ->
    find_remset_ext (extract_address rext) rmst = Some rext.
Proof.
  induction rmst as [|head rest IH]; intros rext Hrnd Hin.
  - contradiction.
  - simpl in Hin.
    rewrite remset_nodup_cons_iff in Hrnd.
    destruct Hrnd as [Haddr_nd Hrnd_rest].
    destruct Hin as [Hin | Hin].
    + subst head. simpl.
      destruct (Val.eq (extract_address rext) (extract_address rext));
        [reflexivity | contradiction].
    + simpl.
      destruct (Val.eq (extract_address head) (extract_address rext)) as [Heq | Hneq].
      * exfalso. apply Haddr_nd.
        rewrite Heq. apply in_map. exact Hin.
      * apply IH; assumption.
Qed.

Lemma find_remset_ext_nodup_vertex:
  forall rmst v addr,
    remset_nodup rmst ->
    In (RemSetVertex v addr) rmst ->
    find_remset_ext addr rmst = Some (RemSetVertex v addr).
Proof.
  intros rmst v addr Hrnd Hin.
  exact (find_remset_ext_nodup rmst (RemSetVertex v addr) Hrnd Hin).
Qed.

Lemma upd_remset_addr_other_vertex_In:
  forall from to g upd_addr rmst v addr,
    upd_addr <> addr ->
    In (RemSetVertex v addr) rmst ->
    In (RemSetVertex v addr) (upd_remset_addr from to g upd_addr rmst).
Proof.
  induction rmst as [|head rest IH]; intros v addr Hneq Hin.
  - contradiction.
  - simpl in Hin |- *.
    destruct Hin as [Hin | Hin].
    + subst head.
      simpl.
      destruct (Val.eq upd_addr addr) as [Heq | _].
      * contradiction.
      * left. reflexivity.
    + destruct (Val.eq upd_addr (extract_address head)).
      * right. exact Hin.
      * right. apply IH; assumption.
Qed.

Lemma remset_item2forward_p_compatible':
  forall g rmst item from,
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    remset_item_in_gen item rmst g from = false ->
    forward_p_compatible' (remset_item2forward_p item rmst) g from.
Proof.
  intros g rmst item from Hrgc Hric Hnotin.
  destruct item as [addr | [v pos]]; simpl in Hric, Hnotin |- *.
  - destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind.
    + destruct rext as [vtx addr' | p addr']; simpl; auto.
      apply find_remset_ext_some in Hfind.
      destruct Hfind as [Hin _].
      unfold remset_graph_compatible in Hrgc.
      rewrite Forall_forall in Hrgc.
      specialize (Hrgc _ Hin). simpl in Hrgc. assumption.
    + exfalso.
      apply in_addr_find_ext_not_none in Hric.
      contradiction.
  - destruct Hric as [Hv [Hpos Hfield]].
    apply Nat.eqb_neq in Hnotin.
    specialize (Hfield Hnotin).
    destruct Hfield as [Hmark Htag].
    split; [|split; [|split; [|split]]]; auto.
Qed.

Lemma forward_remset_item_forward_p_relation:
  forall from to g h rh rmst item g' h' rh' rmst',
    remset_item_in_gen item rmst g from = false ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    forward_relation from to O
      (forward_p2forward_t (remset_item2forward_p item rmst) g) g g'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hnotin Hfri.
  unfold forward_remset_item in Hfri.
  rewrite Hnotin in Hfri. cbn [negb] in Hfri.
  destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
    as [new_g new_h] eqn:Hfgh.
  inversion Hfri; subst; clear Hfri.
  rewrite remset_item2forward_p_eq.
  pose proof fr_forward_graph_and_heap
       from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
  rewrite Hfgh in Hfr. simpl in Hfr. exact Hfr.
Qed.

Lemma forward_remset_item_effective_root_marked:
  forall from to g h rh rmst item g' h' rh' rmst' v,
    remset_item_in_gen item rmst g from = false ->
    remset_item_effective_root g rmst item = Some v ->
    vgeneration v = from ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' v
         Hnotin Heff Hgen Hfri.
  pose proof (forward_remset_item_forward_p_relation
                from to g h rh rmst item g' h' rh' rmst'
                Hnotin Hfri) as Hfr.
  destruct item as [addr | [src pos]]; simpl in Heff, Hfr.
  - destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind;
      simpl in Heff, Hfr; try discriminate.
    destruct rext as [out addr' | root addr']; simpl in Heff, Hfr;
      try discriminate.
    inversion Heff; subst root.
    eapply fr_O_forward_vertex_marked; eauto.
  - destruct (Znth pos (make_fields g src)) as [z | p | e] eqn:Hfield;
      simpl in Heff, Hfr; try discriminate.
    inversion Heff; subst v.
    eapply fr_O_forward_edge_dst_marked; eauto.
Qed.

Lemma forward_remset_item_preserves_other_remset_vertex:
  forall from to g h rh rmst item g' h' rh' rmst' v addr,
    (match item with
     | RemSetExterior item_addr => item_addr <> addr
     | RemSetInterior _ => True
     end) ->
    In (RemSetVertex v addr) rmst ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    In (RemSetVertex v addr) rmst'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' v addr Hother Hin Hfri.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hitem.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    inversion Hfri; subst; clear Hfri.
    destruct item as [item_addr | intr]; simpl in Hother.
    + apply upd_remset_addr_other_vertex_In; assumption.
    + exact Hin.
  - inversion Hfri; subst. exact Hin.
Qed.

Lemma forward_remset_item_fold_head_effective_root_marked:
  forall from to item r g h rh rmst g' h' rh' rmst' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    remset_item_in_gen item rmst g from = false ->
    remset_item_effective_root g rmst item = Some v ->
    vgeneration v = from ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) (item :: r) (g, h, rh, rmst) ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to item r g h rh rmst g' h' rh' rmst' v
         Hto Hv Hnotin Heff Hgen Hfold.
  change (fold_left (forward_remset_item from to) (item :: r) (g, h, rh, rmst))
    with (fold_left (forward_remset_item from to) r
            (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
  destruct (forward_remset_item from to (g, h, rh, rmst) item)
    as [[[g2 h2] rh2] rmst2] eqn:Hfri.
  symmetry in Hfri.
  assert (Hmark2: raw_mark (vlabel g2 v) = true) by
      (eapply forward_remset_item_effective_root_marked; eauto).
  assert (Hto2: graph_has_gen g2 to) by
      (rewrite <- (forward_remset_item_ghg from to g h rh rmst item
                     g2 h2 rh2 rmst2 Hto Hfri to);
       exact Hto).
  assert (Hv2: graph_has_v g2 v) by
      exact (forward_remset_item_graph_has_v_pres
               from to g h rh rmst item g2 h2 rh2 rmst2 v Hto Hv Hfri).
  eapply forward_remset_item_fold_raw_mark_true_pres; eauto.
Qed.

Lemma forward_remset_item_fold_exterior_root_marked:
  forall from to r g h rh rmst g' h' rh' rmst' v addr,
    from <> to ->
    graph_has_gen g to ->
    graph_has_v g v ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    In (RemSetVertex v addr) rmst ->
    vgeneration v = from ->
    In (RemSetExterior addr) r ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to r.
  induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' v addr Hneq Hto Hv Hcc Hrnd Hrgc
           Hrrsc Hvertex Hgen Hin_space Hfold.
  - contradiction.
  - change (fold_left (forward_remset_item from to) (item :: rest) (g, h, rh, rmst))
      with (fold_left (forward_remset_item from to) rest
              (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hric_item Hrrsc_tail].
    destruct item as [item_addr | intr].
    + destruct (Val.eq item_addr addr) as [Heq_addr | Hneq_addr].
      * subst item_addr.
        eapply forward_remset_item_fold_head_effective_root_marked; eauto.
        -- reflexivity.
        -- simpl. rewrite (find_remset_ext_nodup_vertex rmst v addr Hrnd Hvertex).
           reflexivity.
      * destruct Hin_space as [Hin_head | Hin_tail].
        -- inversion Hin_head. contradiction.
        -- destruct (forward_remset_item from to (g, h, rh, rmst) (RemSetExterior item_addr))
             as [[[g2 h2] rh2] rmst2] eqn:Hfri.
           symmetry in Hfri.
           destruct (forward_remset_item_step_state_with_tail
                       from to g h rh rmst (RemSetExterior item_addr) rest
                       g2 h2 rh2 rmst2 Hneq Hto Hcc Hrnd Hrgc Hric_item
                       Hrrsc_tail Hfri)
             as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
           assert (Hv2: graph_has_v g2 v) by
               (exact (forward_remset_item_graph_has_v_pres
                         from to g h rh rmst (RemSetExterior item_addr)
                         g2 h2 rh2 rmst2 v Hto Hv Hfri)).
           assert (Hvertex2: In (RemSetVertex v addr) rmst2) by
               (eapply (forward_remset_item_preserves_other_remset_vertex
                           from to g h rh rmst (RemSetExterior item_addr)
                           g2 h2 rh2 rmst2 v addr);
                [simpl; exact Hneq_addr | exact Hvertex | exact Hfri]).
           eapply IH; eauto.
    + destruct Hin_space as [Hin_head | Hin_tail].
      * inversion Hin_head.
      * destruct (forward_remset_item from to (g, h, rh, rmst) (RemSetInterior intr))
          as [[[g2 h2] rh2] rmst2] eqn:Hfri.
        symmetry in Hfri.
        destruct (forward_remset_item_step_state_with_tail
                    from to g h rh rmst (RemSetInterior intr) rest
                    g2 h2 rh2 rmst2 Hneq Hto Hcc Hrnd Hrgc Hric_item
                    Hrrsc_tail Hfri)
          as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
        assert (Hv2: graph_has_v g2 v) by
            (exact (forward_remset_item_graph_has_v_pres
                      from to g h rh rmst (RemSetInterior intr)
                      g2 h2 rh2 rmst2 v Hto Hv Hfri)).
        assert (Hvertex2: In (RemSetVertex v addr) rmst2) by
            (eapply (forward_remset_item_preserves_other_remset_vertex
                        from to g h rh rmst (RemSetInterior intr)
                        g2 h2 rh2 rmst2 v addr);
             [simpl; exact I | exact Hvertex | exact Hfri]).
        eapply IH; eauto.
Qed.

Lemma forward_remset_gh_exterior_root_marked:
  forall from to g h rh rmst g' h' rh' rmst' v addr,
    from <> to ->
    graph_has_gen g to ->
    graph_has_v g v ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    remset_ext_space_compatible rmst rh ->
    In (RemSetVertex v addr) rmst ->
    vgeneration v = from ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' v addr
         Hneq Hto Hv Hcc Hrnd Hrgc Hrrhc Hext Hvertex Hgen Hfrg.
  unfold forward_remset_gh in Hfrg.
  eapply (forward_remset_item_fold_exterior_root_marked
            from to (Znth (Z.of_nat from) rh)
            g h rh rmst g' h' rh' rmst' v addr); eauto.
  - eapply rrhc_forall_rrsc; exact Hrrhc.
  - rewrite <- Hgen.
    rewrite <- nth_remset_space_Znth.
    eapply Hext; exact Hvertex.
Qed.

Lemma current_remset_edges_pending:
  forall g rh from v,
    sound_gc_graph g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    vgeneration v = from ->
    old_nonfrom_edges_to_are_pending g v from (nth_remset_space rh from).
Proof.
  unfold old_nonfrom_edges_to_are_pending.
  intros g rh from v Hsound Hfirst Hunrec Hgenv e Hevalid Hsrcgen Hdst.
  destruct Hsound as [Hvv [Hev _]].
  assert (Hge: graph_has_e g e) by (apply (proj1 (Hev e)); exact Hevalid).
  assert (Hin:
            In (RemSetInterior (InteriorVertexPos (fst e) (Z.of_nat (snd e))))
               (nth_remset_space rh from)) by
      (eapply no_unrecorded_backward_edge_current_remset;
       [exact Hfirst | exact Hunrec | exact Hge |
        unfold egeneration in *; exact Hsrcgen | now rewrite Hdst]).
  exists (RemSetInterior (InteriorVertexPos (fst e) (Z.of_nat (snd e)))).
  split; [exact Hin |].
  simpl. split; reflexivity.
Qed.

Lemma unmarked_current_remset_edges_pending:
  forall g rh from,
    sound_gc_graph g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    unmarked_old_nonfrom_edges_to_are_pending
      g g from (nth_remset_space rh from).
Proof.
  unfold unmarked_old_nonfrom_edges_to_are_pending.
  intros g rh from Hsound Hfirst Hunrec v Hgen _.
  eapply current_remset_edges_pending; eauto.
Qed.

Lemma forward_remset_item_recorded_old_edge_target_marked:
  forall from to base g h rh rmst item g' h' rh' rmst' pending l e v,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    remset_item_compatible g from rmst item ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso base g from to (item :: pending) l ->
    evalid base e ->
    vgeneration (fst e) <> from ->
    dst base e = v ->
    vgeneration v = from ->
    remset_item_records_edge item e ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to base g h rh rmst item g' h' rh' rmst' pending l e v
         Hneq Hsound_base Hsound_g Hto Hric Hndd_base Hsemi
         Hevalid_base Hsrcgen Hdst_base Hgenv Hrec Hfri.
  assert (Hpartial:
            remset_partial_graph_pending base g l from (item :: pending)) by
      (eapply gc_graph_remset_semi_iso_parts_partial; exact Hsemi).
  assert (Hcurrent: evalid g e /\ src g e = src base e). {
    eapply old_nonfrom_edges_mapped_pending_current_edge; eauto.
    exact (proj1 (proj2 Hpartial)).
  }
  destruct Hcurrent as [Hevalid_g Hsrc_g].
  assert (Hmarked_or_current:
            raw_mark (vlabel g v) = true \/ dst g e = v). {
    exact (pending_remset_semi_iso_old_nonfrom_edge_marked_or_current
             base g from to (item :: pending) l e v
             Hneq Hsemi Hevalid_base Hsrcgen Hdst_base Hgenv).
  }
  assert (Hgv: graph_has_v g v). {
    pose proof Hsound_base as Hsound_base0.
    pose proof Hsound_g as Hsound_g0.
    destruct Hsound_base0 as [Hvv_base [Hev_base _]].
    destruct Hsound_g0 as [Hvv_g _].
    assert (Hge_base: graph_has_e base e) by
        (apply (proj1 (Hev_base _)); exact Hevalid_base).
    assert (Hdst_has_base: graph_has_v base (dst base e)) by
        (destruct Hge_base as [Hsrc_has Hfield];
         apply (Hndd_base (fst e)); assumption).
    assert (Hvvalid_base: vvalid base v) by
        (rewrite <- Hdst_base; apply (proj2 (Hvv_base _)); exact Hdst_has_base).
    assert (Hvvalid_g: vvalid g v) by (apply (proj1 Hpartial); exact Hvvalid_base).
    apply (proj1 (Hvv_g _)); exact Hvvalid_g.
  }
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hnotin.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [new_g new_h] eqn:Hfgh.
    pose proof fr_forward_graph_and_heap
         from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    inversion Hfri; subst; clear Hfri.
    destruct Hmarked_or_current as [Hmark_g | Hdst_current].
    + eapply fr_O_raw_mark_true_pres; eauto.
    + destruct item as [addr | [src pos]]; simpl in Hrec; [contradiction |].
      destruct Hrec as [Hsrc_eq Hpos_eq]. subst src.
      destruct Hric as [_ [Hpos _]].
      assert (Hfield: Znth pos (make_fields g (fst e)) = FieldEdge e) by
          (eapply remset_interior_records_current_edge_field; eauto;
           simpl; split; [reflexivity | exact Hpos_eq]).
      simpl in Hfr. rewrite Hfield in Hfr. simpl in Hfr.
      inversion Hfr; subst; clear Hfr.
      * rewrite Hdst_current in *. contradiction.
      * subst new_g0. rewrite <- lgd_raw_mark_eq.
        rewrite <- Hdst_current. assumption.
      * subst new_g0. rewrite <- lgd_raw_mark_eq.
        rewrite <- Hdst_current. apply lcv_raw_mark_old.
  - inversion Hfri; subst; clear Hfri.
    destruct Hmarked_or_current as [Hmark_g | Hdst_current]; [exact Hmark_g |].
    destruct item as [addr | [src pos]]; simpl in Hrec; [contradiction |].
    destruct Hrec as [Hsrc_eq _]. subst src.
    simpl in Hnotin. apply negb_false_iff in Hnotin.
    apply Nat.eqb_eq in Hnotin. contradiction.
Qed.

Lemma forward_remset_item_unmarked_old_nonfrom_edges_pending:
  forall from to base g h rh rmst item g' h' rh' rmst' pending l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    remset_item_compatible g from rmst item ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso base g from to (item :: pending) l ->
    unmarked_old_nonfrom_edges_to_are_pending base g from (item :: pending) ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    unmarked_old_nonfrom_edges_to_are_pending base g' from pending.
Proof.
  unfold unmarked_old_nonfrom_edges_to_are_pending.
  intros from to base g h rh rmst item g' h' rh' rmst' pending l
         Hneq Hsound_base Hsound_g Hto Hric Hndd_base Hsemi Hpending Hfri
         v Hgenv Hmark_new.
  unfold old_nonfrom_edges_to_are_pending.
  intros e Hevalid_base Hsrcgen Hdst_base.
  assert (Hpartial:
            remset_partial_graph_pending base g l from (item :: pending)) by
      (eapply gc_graph_remset_semi_iso_parts_partial; exact Hsemi).
  assert (Hgv: graph_has_v g v). {
    pose proof Hsound_base as Hsound_base0.
    pose proof Hsound_g as Hsound_g0.
    destruct Hsound_base0 as [Hvv_base [Hev_base _]].
    destruct Hsound_g0 as [Hvv_g _].
    assert (Hge_base: graph_has_e base e) by
        (apply (proj1 (Hev_base _)); exact Hevalid_base).
    assert (Hdst_has_base: graph_has_v base (dst base e)) by
        (destruct Hge_base as [Hsrc_has Hfield];
         apply (Hndd_base (fst e)); assumption).
    assert (Hvvalid_base: vvalid base v) by
        (rewrite <- Hdst_base; apply (proj2 (Hvv_base _)); exact Hdst_has_base).
    assert (Hvvalid_g: vvalid g v) by (apply (proj1 Hpartial); exact Hvvalid_base).
    apply (proj1 (Hvv_g _)); exact Hvvalid_g.
  }
  assert (Hmark_old: raw_mark (vlabel g v) = false). {
    unfold forward_remset_item in Hfri.
    destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hnotin.
    - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
        as [new_g new_h] eqn:Hfgh.
      pose proof fr_forward_graph_and_heap
           from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
      rewrite Hfgh in Hfr. simpl in Hfr.
      inversion Hfri; subst; clear Hfri.
      eapply fr_O_raw_mark_false_inv; eauto.
    - inversion Hfri; subst; clear Hfri. exact Hmark_new.
  }
  pose proof (Hpending v Hgenv Hmark_old e Hevalid_base Hsrcgen Hdst_base)
    as Hpending_edge.
  destruct Hpending_edge as [item0 [[Hin | Hin] Hrec0]].
  - subst item0.
    pose proof (forward_remset_item_recorded_old_edge_target_marked
                  from to base g h rh rmst item g' h' rh' rmst'
                  pending l e v Hneq Hsound_base Hsound_g Hto Hric
                  Hndd_base Hsemi Hevalid_base Hsrcgen Hdst_base Hgenv Hrec0 Hfri)
      as Hmarked.
    rewrite Hmark_new in Hmarked. discriminate.
  - exists item0. split; assumption.
Qed.

Lemma forward_remset_exterior_item_pending_remset_semi_iso:
  forall from to base g h rh rmst addr g' h' rh' rmst' pending l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst (RemSetExterior addr) ->
    no_dangling_dst base ->
    gc_graph_pending_remset_semi_iso
      base g from to (RemSetExterior addr :: pending) l ->
    unmarked_old_nonfrom_edges_to_are_pending
      base g from (RemSetExterior addr :: pending) ->
    (g', h', rh', rmst') =
      forward_remset_item from to (g, h, rh, rmst) (RemSetExterior addr) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst addr g' h' rh' rmst' pending l
         Hneq Hsound_base Hsound_g Hto Hrgc Hitem Hndd_base Hsemi
         Hpending Hfri.
  assert (Hfr:
            forward_relation from to O
              (forward_p2forward_t
                 (remset_item2forward_p (RemSetExterior addr) rmst) g) g g') by
      (eapply forward_remset_item_forward_p_relation; [reflexivity | exact Hfri]).
  simpl in Hfr.
  destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind.
  - destruct rext as [out addr' | v addr']; simpl in Hfr.
    + inversion Hfr; subst; exists nil; simpl;
        eapply pending_remset_semi_iso_cons_drop; eauto;
        apply remset_exterior_records_no_edge.
    + assert (Hv_has: graph_has_v g v). {
        apply find_remset_ext_some in Hfind.
        destruct Hfind as [Hin _].
        unfold remset_graph_compatible in Hrgc.
        rewrite Forall_forall in Hrgc.
        specialize (Hrgc _ Hin). simpl in Hrgc. exact Hrgc.
      }
      assert (Hv_valid: vvalid g v). {
        destruct Hsound_g as [Hvv _].
        red in Hvv. rewrite Hvv. exact Hv_has.
      }
      inversion Hfr; subst; clear Hfr.
      * exists nil. simpl.
        eapply pending_remset_semi_iso_cons_drop; eauto.
        apply remset_exterior_records_no_edge.
      * exists nil. simpl.
        eapply pending_remset_semi_iso_cons_drop; eauto.
        apply remset_exterior_records_no_edge.
      * exists [(v, new_copied_v g to)]. simpl.
        eapply pending_remset_semi_iso_cons_drop.
        -- apply remset_exterior_records_no_edge.
        -- eapply lcv_pending_remset_semi_iso; eauto.
  - inversion Hfr; subst; exists nil; simpl;
      eapply pending_remset_semi_iso_cons_drop; eauto;
      apply remset_exterior_records_no_edge.
Qed.

Lemma forward_remset_interior_from_item_pending_remset_semi_iso:
  forall from to base g h rh rmst v pos g' h' rh' rmst' pending l,
    vgeneration v = from ->
    gc_graph_pending_remset_semi_iso
      base g from to (RemSetInterior (InteriorVertexPos v pos) :: pending) l ->
    (g', h', rh', rmst') =
      forward_remset_item from to (g, h, rh, rmst)
        (RemSetInterior (InteriorVertexPos v pos)) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst v pos g' h' rh' rmst' pending l
         Hgen Hsemi Hfri.
  unfold forward_remset_item in Hfri. simpl in Hfri.
  rewrite Hgen, Nat.eqb_refl in Hfri. simpl in Hfri.
  inversion Hfri; subst; clear Hfri.
  exists nil. simpl.
  eapply pending_remset_semi_iso_cons_drop_old_nonfrom; eauto.
  intros e Hsrcgen Hrec.
  simpl in Hrec. destruct Hrec as [Hv _].
  subst v. contradiction.
Qed.

Lemma forward_remset_interior_nonedge_item_pending_remset_semi_iso:
  forall from to base g h rh rmst v pos f g' h' rh' rmst' pending l,
    sound_gc_graph g ->
    vgeneration v <> from ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst (RemSetInterior (InteriorVertexPos v pos)) ->
    Znth pos (make_fields g v) = f ->
    (forall e, f <> FieldEdge e) ->
    gc_graph_pending_remset_semi_iso
      base g from to (RemSetInterior (InteriorVertexPos v pos) :: pending) l ->
    (g', h', rh', rmst') =
      forward_remset_item from to (g, h, rh, rmst)
        (RemSetInterior (InteriorVertexPos v pos)) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst v pos f g' h' rh' rmst' pending l
         Hsound_g Hsrc_not Hrgc Hric Hfield Hnonedge Hsemi Hfri.
  assert (Hnotin:
            remset_item_in_gen
              (RemSetInterior (InteriorVertexPos v pos)) rmst g from = false). {
    simpl. apply Nat.eqb_neq. exact Hsrc_not.
  }
  assert (Hfr:
            forward_relation from to O
              (forward_p2forward_t
                 (remset_item2forward_p
                    (RemSetInterior (InteriorVertexPos v pos)) rmst) g) g g') by
      (eapply forward_remset_item_forward_p_relation; eauto).
  simpl in Hfr. rewrite Hfield in Hfr. simpl in Hfr.
  destruct Hric as [_ [Hpos _]].
  destruct f as [z | p | e].
  - inversion Hfr; subst; clear Hfr.
    exists nil. simpl.
    eapply pending_remset_semi_iso_consume_item_no_current_edge; eauto.
    intros e Hrec.
    eapply remset_interior_nonedge_records_no_current_edge; eauto.
  - inversion Hfr; subst; clear Hfr.
    exists nil. simpl.
    eapply pending_remset_semi_iso_consume_item_no_current_edge; eauto.
    intros e Hrec.
    eapply remset_interior_nonedge_records_no_current_edge; eauto.
  - exfalso. exact (Hnonedge e eq_refl).
Qed.

Lemma forward_remset_interior_not_to_item_pending_remset_semi_iso:
  forall from to base g h rh rmst v pos e g' h' rh' rmst' pending l,
    vgeneration v <> from ->
    remset_item_compatible g from rmst (RemSetInterior (InteriorVertexPos v pos)) ->
    Znth pos (make_fields g v) = FieldEdge e ->
    vgeneration (dst g e) <> from ->
    gc_graph_pending_remset_semi_iso
      base g from to (RemSetInterior (InteriorVertexPos v pos) :: pending) l ->
    (g', h', rh', rmst') =
      forward_remset_item from to (g, h, rh, rmst)
        (RemSetInterior (InteriorVertexPos v pos)) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst v pos e g' h' rh' rmst' pending l
         Hsrc_not Hric Hfield Hdst_not Hsemi Hfri.
  assert (Hnotin:
            remset_item_in_gen
              (RemSetInterior (InteriorVertexPos v pos)) rmst g from = false). {
    simpl. apply Nat.eqb_neq. exact Hsrc_not.
  }
  assert (Hfr:
            forward_relation from to O
              (forward_p2forward_t
                 (remset_item2forward_p
                    (RemSetInterior (InteriorVertexPos v pos)) rmst) g) g g') by
      (eapply forward_remset_item_forward_p_relation; eauto).
  simpl in Hfr. rewrite Hfield in Hfr. simpl in Hfr.
  assert (Hitem:
            remset_item_records_edge
              (RemSetInterior (InteriorVertexPos v pos)) e). {
    destruct Hric as [_ [Hpos _]].
    assert (Heq: e = (v, Z.to_nat pos)) by
        (eapply make_fields_Znth_edge; eauto).
    subst e. simpl. split; [reflexivity |].
    rewrite Z2Nat.id by lia. reflexivity.
  }
  inversion Hfr; subst; clear Hfr; try contradiction.
  exists nil. simpl.
  eapply pending_remset_semi_iso_consume_item_not_to; eauto.
Qed.

Lemma forward_remset_interior_to_item_pending_remset_semi_iso:
  forall from to base g h rh rmst v pos e g' h' rh' rmst' pending l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst
      (RemSetInterior (InteriorVertexPos v pos)) ->
    no_dangling_dst base ->
    vvalid base v ->
    vgeneration v <> from ->
    Znth pos (make_fields g v) = FieldEdge e ->
    vgeneration (dst g e) = from ->
    gc_graph_pending_remset_semi_iso
      base g from to (RemSetInterior (InteriorVertexPos v pos) :: pending) l ->
    unmarked_old_nonfrom_edges_to_are_pending
      base g from (RemSetInterior (InteriorVertexPos v pos) :: pending) ->
    (g', h', rh', rmst') =
      forward_remset_item from to (g, h, rh, rmst)
        (RemSetInterior (InteriorVertexPos v pos)) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst v pos e g' h' rh' rmst' pending l
         Hneq Hsound_base Hsound_g Hto Hrgc Hric Hndd_base Hvbase
         Hsrc_not Hfield Hdst_from Hsemi Hpending Hfri.
  assert (Hnotin:
            remset_item_in_gen
              (RemSetInterior (InteriorVertexPos v pos)) rmst g from = false). {
    simpl. apply Nat.eqb_neq. exact Hsrc_not.
  }
  assert (Hfr:
            forward_relation from to O
              (forward_p2forward_t
                 (remset_item2forward_p
                    (RemSetInterior (InteriorVertexPos v pos)) rmst) g) g g') by
      (eapply forward_remset_item_forward_p_relation; eauto).
  simpl in Hfr. rewrite Hfield in Hfr. simpl in Hfr.
  destruct Hric as [Hv_g_has [Hpos Hric_field]].
  assert (Hitem:
            remset_item_records_edge
              (RemSetInterior (InteriorVertexPos v pos)) e). {
    assert (Heq: e = (v, Z.to_nat pos)) by
        (eapply make_fields_Znth_edge; eauto).
    subst e. simpl. split; [reflexivity |].
    rewrite Z2Nat.id by lia. reflexivity.
  }
  assert (Hevalid_base: evalid base e) by
      (eapply (pending_remset_semi_iso_old_nonfrom_field_evalid_base
                 base g from to
                 (RemSetInterior (InteriorVertexPos v pos) :: pending)
                 l v pos e); eauto).
  assert (Hsrcgen: vgeneration (fst e) <> from). {
    apply make_fields_Znth_edge in Hfield; auto.
    subst e. simpl. exact Hsrc_not.
  }
  assert (Hpartial:
            remset_partial_graph_pending
              base g l from
              (RemSetInterior (InteriorVertexPos v pos) :: pending)) by
      (eapply gc_graph_remset_semi_iso_parts_partial; exact Hsemi).
  assert (Hcurrent: evalid g e /\ src g e = src base e). {
    eapply old_nonfrom_edges_mapped_pending_current_edge; eauto.
    exact (proj1 (proj2 Hpartial)).
  }
  destruct Hcurrent as [Hevalid_g Hsrc_g].
  inversion Hfr; subst; clear Hfr; try contradiction.
  - exists nil. simpl.
    assert (Hmap:
              copied_vertex (vlabel g (dst g e)) =
              list_bi_map l (dst base e)) by
        (symmetry;
         eapply (pending_remset_semi_iso_marked_edge_map
                   base g (vgeneration (dst g e)) to
                   (RemSetInterior (InteriorVertexPos v pos) :: pending)
                   l e); eauto).
    eapply lgd_pending_remset_semi_iso_mapped; eauto.
  - destruct (pending_remset_semi_iso_old_nonfrom_edge_dst_base
                base g (vgeneration (dst g e)) to
                (RemSetInterior (InteriorVertexPos v pos) :: pending)
                l e Hneq Hsound_base Hndd_base Hsemi
                Hevalid_base Hsrcgen eq_refl)
      as [Hdst_eq [Hdst_valid_base Hdst_base_gen]].
    assert (Holdvalid: old_vertices_valid base g) by
        (exact (proj1 Hpartial)).
    assert (Hdst_valid_g: vvalid g (dst g e)). {
      rewrite Hdst_eq. apply Holdvalid. exact Hdst_valid_base.
    }
    assert (Hsemi_lcv:
              gc_graph_pending_remset_semi_iso
                base (lgraph_copy_v g (dst g e) to)
                (vgeneration (dst g e)) to
                (RemSetInterior (InteriorVertexPos v pos) :: pending)
                ((dst g e, new_copied_v g to) :: l)). {
      eapply lcv_pending_remset_semi_iso; eauto.
    }
    assert (Hsrc_not_new: fst e <> new_copied_v g to). {
      pose proof Hsound_g as Hsound_g0.
      destruct Hsound_g0 as [_ [Hev_g _]].
      assert (Hge_g: graph_has_e g e) by
          (apply (proj1 (Hev_g _)); exact Hevalid_g).
      destruct Hge_g as [Hsrc_has _].
      apply graph_has_v_not_eq with (to := to). exact Hsrc_has.
    }
    assert (Hevalid_lcv: evalid (lgraph_copy_v g (dst g e) to) e). {
      simpl. rewrite pcv_evalid_iff. now left.
    }
    assert (Hsrc_lcv:
              src (lgraph_copy_v g (dst g e) to) e = src base e). {
      simpl. rewrite pcv_src_old; auto.
    }
    exists [(dst g e, new_copied_v g to)]. simpl.
    eapply lgd_pending_remset_semi_iso_mapped; eauto.
    rewrite Hdst_eq.
    unfold list_bi_map. simpl.
    destruct (equiv_dec (dst base e) (dst base e)) as [_ | Hneq_self].
    + reflexivity.
    + exfalso. apply Hneq_self. reflexivity.
Qed.

Lemma forward_remset_item_pending_remset_semi_iso:
  forall from to base g h rh rmst item g' h' rh' rmst' pending l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    no_dangling_dst base ->
    (match item with
     | RemSetExterior _ => True
     | RemSetInterior (InteriorVertexPos v _) =>
         vgeneration v <> from -> vvalid base v
    end) ->
    gc_graph_pending_remset_semi_iso base g from to (item :: pending) l ->
    unmarked_old_nonfrom_edges_to_are_pending base g from (item :: pending) ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to pending (l2 ++ l).
Proof.
  intros from to base g h rh rmst item g' h' rh' rmst' pending l
         Hneq Hsound_base Hsound_g Hto Hrgc Hric Hndd_base Hbase_src
         Hsemi Hpending Hfri.
  destruct item as [addr | [v pos]].
  - eapply forward_remset_exterior_item_pending_remset_semi_iso; eauto.
  - destruct (Nat.eq_dec (vgeneration v) from) as [Hsrc_eq | Hsrc_not].
    + eapply forward_remset_interior_from_item_pending_remset_semi_iso; eauto.
    + destruct (Znth pos (make_fields g v)) as [z | p | e] eqn:Hfield.
      * eapply (forward_remset_interior_nonedge_item_pending_remset_semi_iso
                  from to base g h rh rmst v pos (FieldUnboxed z)); eauto.
        intros e Hbad. inversion Hbad.
      * eapply (forward_remset_interior_nonedge_item_pending_remset_semi_iso
                  from to base g h rh rmst v pos (FieldOutlier p)); eauto.
        intros e Hbad. inversion Hbad.
      * destruct (Nat.eq_dec (vgeneration (dst g e)) from)
          as [Hdst_eq | Hdst_not].
        -- eapply (forward_remset_interior_to_item_pending_remset_semi_iso
                    from to base g h rh rmst v pos e g' h' rh' rmst'
                    pending l); eauto.
        -- eapply (forward_remset_interior_not_to_item_pending_remset_semi_iso
                    from to base g h rh rmst v pos e g' h' rh' rmst'
                    pending l); eauto.
Qed.

Lemma forward_remset_item_fold_pending_remset_semi_iso:
  forall from to base r g h rh rmst g' h' rh' rmst' l,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    no_dangling_dst base ->
    Forall
      (fun item =>
         match item with
         | RemSetExterior _ => True
         | RemSetInterior (InteriorVertexPos v _) =>
             vgeneration v <> from -> vvalid base v
         end) r ->
    gc_graph_pending_remset_semi_iso base g from to r l ->
    unmarked_old_nonfrom_edges_to_are_pending base g from r ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    exists l2,
      gc_graph_pending_remset_semi_iso base g' from to nil (l2 ++ l) /\
      unmarked_old_nonfrom_edges_to_are_pending base g' from nil.
Proof.
  intros from to base r.
  induction r as [|item r IHr];
    intros g h rh rmst g' h' rh' rmst' l Hneq Hsound_base Hsound_g Hto
           Hcc Hrnd Hrgc Hrrsc Hndd_base Hbase_src Hsemi Hpending Hfold.
  - simpl in Hfold. inversion Hfold; subst.
    exists nil. simpl. split; assumption.
  - change (fold_left (forward_remset_item from to) (item :: r) (g, h, rh, rmst))
      with (fold_left (forward_remset_item from to) r
              (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hric_item Hrrsc_tail].
    rewrite Forall_cons_iff in Hbase_src.
    destruct Hbase_src as [Hbase_src_item Hbase_src_tail].
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    destruct (forward_remset_item_pending_remset_semi_iso
                from to base g h rh rmst item g2 h2 rh2 rmst2 r l
                Hneq Hsound_base Hsound_g Hto Hrgc Hric_item Hndd_base
                Hbase_src_item Hsemi Hpending Hfri)
      as [l2 Hsemi2].
    assert (Hsound2: sound_gc_graph g2) by
        (eapply forward_remset_item_P_holds; eauto;
         intros; eapply fr_O_sound; eauto).
    destruct (forward_remset_item_step_state_with_tail
                from to g h rh rmst item r g2 h2 rh2 rmst2
                Hneq Hto Hcc Hrnd Hrgc Hric_item Hrrsc_tail Hfri)
      as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
    assert (Hpending2:
              unmarked_old_nonfrom_edges_to_are_pending base g2 from r) by
        (exact (forward_remset_item_unmarked_old_nonfrom_edges_pending
                  from to base g h rh rmst item g2 h2 rh2 rmst2 r l
                  Hneq Hsound_base Hsound_g Hto Hric_item Hndd_base
                  Hsemi Hpending Hfri)).
    destruct (IHr g2 h2 rh2 rmst2 g' h' rh' rmst' (l2 ++ l)
                  Hneq Hsound_base Hsound2 Hto2 Hcc2 Hrnd2 Hrgc2 Hrrsc2
                  Hndd_base Hbase_src_tail Hsemi2 Hpending2 Hfold)
      as [l3 [Hsemi3 Hpending3]].
    exists (l3 ++ l2).
    split; [|exact Hpending3].
    rewrite <- app_assoc. exact Hsemi3.
Qed.

Lemma remset_space_base_sources_valid:
  forall g from rmst r,
    sound_gc_graph g ->
    remset_and_remset_space_compatible g from rmst r ->
    Forall
      (fun item =>
         match item with
         | RemSetExterior _ => True
         | RemSetInterior (InteriorVertexPos v _) =>
             vgeneration v <> from -> vvalid g v
         end) r.
Proof.
  intros g from rmst r Hsound Hrrsc.
  unfold remset_and_remset_space_compatible in Hrrsc.
  rewrite Forall_forall in Hrrsc.
  apply Forall_forall.
  intros item Hin.
  specialize (Hrrsc _ Hin).
  destruct item as [addr | [v pos]]; simpl in *; auto.
  intros _.
  destruct Hrrsc as [Hv _].
  destruct Hsound as [Hvv _].
  apply (proj2 (Hvv _)); exact Hv.
Qed.

Definition remset_forward_compatible
           (g: LGraph) (from: nat) (rmst: remset) (rh: remset_heap): Prop :=
  remset_nodup rmst /\
  remset_graph_compatible g rmst /\
  remset_and_remset_heap_compatible g from rmst rh.

Definition remset_graph_state
           (g: LGraph) (from: nat) (rmst: remset) (rh: remset_heap): Prop :=
  remset_forward_compatible g from rmst rh /\
  remset_generation_compatible from rmst rh.

Definition graph_generation_bound (g: LGraph): Prop :=
  forall gen, graph_has_gen g gen -> 0 <= Z.of_nat gen < MAX_SPACES.

Definition remset_heap_covers_graph (g: LGraph) (rh: remset_heap): Prop :=
  Zlength rh = MAX_SPACES /\ graph_generation_bound g.

Lemma remset_heap_covers_graph_range:
  forall g rh gen,
    remset_heap_covers_graph g rh ->
    graph_has_gen g gen ->
    0 <= Z.of_nat gen < Zlength rh.
Proof.
  intros g rh gen [Hlen Hbound] Hgen.
  rewrite Hlen. apply Hbound. exact Hgen.
Qed.

Lemma unmarked_old_nonfrom_edges_pending_nil_no_unmarked:
  forall base g from,
    unmarked_old_nonfrom_edges_to_are_pending base g from nil ->
    no_unmarked_old_nonfrom_dst base g from.
Proof.
  unfold unmarked_old_nonfrom_edges_to_are_pending,
    old_nonfrom_edges_to_are_pending, no_unmarked_old_nonfrom_dst.
  intros base g from Hpending e He Hsrcgen Hdstgen Hmark.
  specialize (Hpending (dst base e) Hdstgen Hmark e He Hsrcgen eq_refl).
  destruct Hpending as [item [Hin _]].
  contradiction.
Qed.

Lemma forward_remset_gh_remset_semi_iso_closed:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    no_dangling_dst g ->
    gen_unmarked g from ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    exists l,
      gc_graph_remset_semi_iso g g' from to l /\
      no_unmarked_old_nonfrom_dst g g' from.
Proof.
  intros from to g h rh rmst g' h' rh' rmst'
         Hneq Hsound Hto Hcc Hrnd Hrgc Hrrhc Hndd Hunmarked Hfirst Hunrec Hfrg.
  assert (Hrrsc:
            remset_and_remset_space_compatible
              g from rmst (nth_remset_space rh from)). {
    rewrite nth_remset_space_Znth.
    eapply rrhc_forall_rrsc; exact Hrrhc.
  }
  assert (Hbase_src:
            Forall
              (fun item =>
                 match item with
                 | RemSetExterior _ => True
                 | RemSetInterior (InteriorVertexPos v _) =>
                     vgeneration v <> from -> vvalid g v
                 end) (nth_remset_space rh from)) by
      (eapply remset_space_base_sources_valid; eauto).
  assert (Hsemi:
            gc_graph_pending_remset_semi_iso
              g g from to (nth_remset_space rh from) nil) by
      (eapply pending_remset_semi_iso_refl; eauto).
  assert (Hpending:
            unmarked_old_nonfrom_edges_to_are_pending
              g g from (nth_remset_space rh from)) by
      (eapply unmarked_current_remset_edges_pending;
       eauto).
  unfold forward_remset_gh in Hfrg.
  rewrite <- nth_remset_space_Znth in Hfrg.
  destruct (forward_remset_item_fold_pending_remset_semi_iso
              from to g (nth_remset_space rh from) g h rh rmst
              g' h' rh' rmst' nil Hneq Hsound Hsound Hto Hcc Hrnd Hrgc
              Hrrsc Hndd Hbase_src Hsemi Hpending Hfrg)
    as [l [Hpending_nil Hpending_empty]].
  exists l. split.
  - simpl in Hpending_nil.
    rewrite app_nil_r in Hpending_nil.
    now apply pending_remset_semi_iso_nil.
  - eapply unmarked_old_nonfrom_edges_pending_nil_no_unmarked.
    exact Hpending_empty.
Qed.

Lemma forward_remset_gh_interior_root_marked:
  forall from to g h rh rmst g' h' rh' rmst' src pos e,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    In (RemSetInterior (InteriorVertexPos src pos)) (Znth (Z.of_nat from) rh) ->
    remset_item_in_gen
      (RemSetInterior (InteriorVertexPos src pos)) rmst g from = false ->
    Znth pos (make_fields g src) = FieldEdge e ->
    vgeneration (dst g e) = from ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    raw_mark (vlabel g' (dst g e)) = true.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' src pos e
         Hneq Hsound Hto Hun Hndd Hfirst Hunrec Hrnd Hrgc Hrrhc Hin_item
         Hnotin Hfield Hdst Hfrg.
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hun_from: gen_unmarked g from) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  destruct (forward_remset_gh_remset_semi_iso_closed
              from to g h rh rmst g' h' rh' rmst'
              Hneq Hsound Hto Hcc Hrnd Hrgc Hrrhc Hndd Hun_from
              Hfirst Hunrec Hfrg)
    as [_ [_ Hclosed]].
  assert (Hrrsc:
            remset_and_remset_space_compatible
              g from rmst (Znth (Z.of_nat from) rh)) by
      (eapply rrhc_forall_rrsc; exact Hrrhc).
  unfold remset_and_remset_space_compatible in Hrrsc.
  rewrite Forall_forall in Hrrsc.
  specialize (Hrrsc _ Hin_item).
  simpl in Hrrsc.
  destruct Hrrsc as [Hsrc_has [Hpos _]].
  assert (Heq: e = (src, Z.to_nat pos)) by
      (eapply make_fields_Znth_edge; eauto).
  subst e.
  assert (Hge: graph_has_e g (src, Z.to_nat pos)). {
    split; [exact Hsrc_has |].
    rewrite get_edges_In_iff.
    rewrite <- Hfield.
    apply Znth_In.
    now rewrite make_fields_eq_length.
  }
  assert (Hevalid: evalid g (src, Z.to_nat pos)). {
    destruct Hsound as [_ [Hev _]].
    apply (proj2 (Hev _)); exact Hge.
  }
  apply Nat.eqb_neq in Hnotin.
  destruct (raw_mark (vlabel g' (dst g (src, Z.to_nat pos)))) eqn:Hmark; auto.
  exfalso.
  eapply Hclosed; eauto.
Qed.

Lemma frr_no_unmarked_old_nonfrom_dst:
  forall base from to roots roots' g g',
    from <> to ->
    graph_has_gen g to ->
    no_unmarked_old_nonfrom_dst base g from ->
    forward_roots_relation from to roots g roots' g' ->
    no_unmarked_old_nonfrom_dst base g' from.
Proof.
  intros base from to roots roots' g g' Hneq Hto Hclosed Hfrr.
  induction Hfrr; auto.
  apply IHHfrr.
  - rewrite <- (fr_graph_has_gen 0 from to (exterior2forward r) g1 g2 Hto H to).
    exact Hto.
  - eapply fr_O_no_unmarked_old_nonfrom_dst_t; eauto.
Qed.

Lemma forward_remset_gh_frr_remset_semi_iso:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    exists l,
      gc_graph_remset_semi_iso g g1 from to l /\
      roots' = roots_map l roots /\
      no_unmarked_old_nonfrom_dst g g1 from.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr.
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hun_from: gen_unmarked g from) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  destruct (forward_remset_gh_remset_semi_iso_closed
              from to g h rh rmst g_rem h_rem rh' rmst'
              Hneq Hsound Hto Hcc Hrnd Hrgc Hrrhc Hndd Hun_from Hfirst Hunrec Hfrg)
    as [l_rem [Hsemi_rem Hclosed_rem]].
  assert (Hsound_rem: sound_gc_graph g_rem) by
      (eapply forward_remset_gh_sound; eauto).
  assert (Hto_rem: graph_has_gen g_rem to) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to);
       exact Hto).
  assert (Hroots_rem: roots_graph_compatible roots g_rem) by
      (unfold forward_remset_gh in Hfrg;
       eapply (forward_remset_item_fold_roots_graph_compatible_pres
                 from to g h rh rmst (Znth (Z.of_nat from) rh)
                 g_rem h_rem rh' rmst' roots);
       eauto).
  assert (Hndd_rem: no_dangling_dst g_rem) by
      (unfold forward_remset_gh in Hfrg;
       eapply (fri_no_dangling_dst_fold
                 from to g h rh rmst (Znth (Z.of_nat from) rh)
                 g_rem h_rem rh' rmst');
       eauto; eapply rrhc_forall_rrsc; exact Hrrhc).
  assert (Hcc_rem: copy_compatible g_rem) by
      (exact (forward_remset_gh_copy_compatible
                from to g h rh rmst g_rem h_rem rh' rmst'
                Hneq Hto Hcc Hfrg)).
  destruct (frl_remset_semi_iso
              from to g l_rem roots roots' g_rem g1
              Hneq Hsound Hsound_rem Hto_rem Hroots_rem Hndd Hndd_rem
              Hcc_rem Hsemi_rem Hclosed_rem Hfrr)
    as [l_frr [Hsemi Hroots_quasi]].
  exists (l_frr ++ l_rem).
  split; [exact Hsemi |].
  split.
  - subst roots'. unfold quasi_roots_map, roots_map.
    apply Znth_eq_ext. list_solve.
    intros i Hi.
    rewrite Zlength_map in Hi.
    rewrite !Znth_map by auto.
    destruct (Znth i roots) eqn:Heqr; simpl; auto.
    f_equal. apply list_map_bi_map.
    intro Hin_snd.
    eapply remset_semi_iso_In_map_snd in Hin_snd; eauto.
    apply Hin_snd.
    red in Hroots.
    rewrite Forall_forall in Hroots.
    destruct Hsound as [Hvv _].
    red in Hvv. rewrite Hvv.
    apply Hroots.
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- Heqr.
    apply Znth_In. auto.
  - eapply frr_no_unmarked_old_nonfrom_dst; eauto.
Qed.

Lemma forward_remset_gh_frr_dsr_remset_semi_iso:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1 g2,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g2 ->
    exists l,
      gc_graph_remset_semi_iso g g2 from to l /\
      roots' = roots_map l roots /\
      no_unmarked_old_nonfrom_dst g g2 from.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1 g2
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr Hscan.
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hun_to: gen_unmarked g to) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  destruct (forward_remset_gh_frr_remset_semi_iso
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1
              Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr)
    as [l1 [Hsemi1 [Hroots1 Hclosed1]]].
  assert (Hsound_rem: sound_gc_graph g_rem) by
      (eapply forward_remset_gh_sound; eauto).
  assert (Hto_rem: graph_has_gen g_rem to) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to);
       exact Hto).
  assert (Hroots_rem: roots_graph_compatible roots g_rem) by
      (unfold forward_remset_gh in Hfrg;
       eapply (forward_remset_item_fold_roots_graph_compatible_pres
                 from to g h rh rmst (Znth (Z.of_nat from) rh)
                 g_rem h_rem rh' rmst' roots);
       eauto).
  assert (Hndd_rem: no_dangling_dst g_rem) by
      (unfold forward_remset_gh in Hfrg;
       eapply (fri_no_dangling_dst_fold
                 from to g h rh rmst (Znth (Z.of_nat from) rh)
                 g_rem h_rem rh' rmst');
       eauto; eapply rrhc_forall_rrsc; exact Hrrhc).
  assert (Hcc_rem: copy_compatible g_rem) by
      (exact (forward_remset_gh_copy_compatible
                from to g h rh rmst g_rem h_rem rh' rmst'
                Hneq Hto Hcc Hfrg)).
  assert (Hun_rem_to: gen_unmarked g_rem to) by
      (exact (forward_remset_gh_gen_unmarked
                from to g h rh rmst g_rem h_rem rh' rmst' to
                Hto Hneq Hfrg Hun_to)).
  assert (Hsound1: sound_gc_graph g1) by
      (eapply frr_sound; eauto).
  assert (Hto1: graph_has_gen g1 to) by
      (rewrite <- (frr_graph_has_gen from to roots g_rem roots' g1
                     Hto_rem Hfrr to);
       exact Hto_rem).
  assert (Hroots1_compat: roots_graph_compatible roots' g1) by
      (exact (frr_roots_graph_compatible
                from to roots g_rem roots' g1
                Hneq Hto_rem Hcc_rem Hroots_rem Hfrr)).
  assert (Hndd1: no_dangling_dst g1) by
      (exact (frr_no_dangling_dst
                from to roots g_rem roots' g1
                Hto_rem Hcc_rem Hneq Hroots_rem Hfrr Hndd_rem)).
  assert (Hroots_no_from: roots_have_no_gen roots' from) by
      (exact (frr_not_pointing
                from to roots g_rem roots' g1
                Hcc_rem Hroots_rem Hneq Hto_rem Hfrr)).
  assert (Hcc1: copy_compatible g1) by
      (exact (frr_copy_compatible
                from to roots g_rem roots' g1
                Hneq Hto_rem Hfrr Hcc_rem)).
  assert (Hun1_to: gen_unmarked g1 to) by
      (exact (frr_gen_unmarked
                from to roots g_rem roots' g1
                Hto_rem Hfrr to (not_eq_sym Hneq) Hun_rem_to)).
  destruct Hscan as [n [Hsvwl Hbound]].
  destruct (svwl_remset_semi_iso
              from to (seq (number_of_vertices (nth_gen g to)) n)
              l1 roots' g g1 g2 Hneq Hsound Hsound1 Hto1 Hroots1_compat
              Hndd Hndd1 Hroots_no_from
              ltac:(intros i Hin Hidx; rewrite in_seq in Hin;
                    unfold gen_has_index in Hidx; lia)
              Hcc1 Hun1_to Hsemi1 Hclosed1 Hsvwl)
    as [l2 [Hsemi2 Hroots_scan]].
  exists (l2 ++ l1).
  split; [exact Hsemi2 |].
  split.
  - rewrite Hroots1.
    rewrite (roots_map_map_app l2 l1 roots).
    + now rewrite <- Hroots1, <- Hroots_scan.
    + eapply remset_semi_iso_DoubleNoDup; eauto.
  - eapply svwl_no_unmarked_old_nonfrom_dst; eauto.
Qed.

(* Only remset items that forward_remset will process, and whose target is
   actually in from-space, act as semantic roots for this collection. *)
Fixpoint effective_remset_roots_from_space
         (g: LGraph) (rmst: remset) (from: nat)
         (r: remset_space): roots_t :=
  match r with
  | [] => []
  | item :: rest =>
      let rest_roots := effective_remset_roots_from_space g rmst from rest in
      if remset_item_in_gen item rmst g from then rest_roots
      else
        match remset_item_effective_root g rmst item with
        | Some v =>
            if Nat.eqb (vgeneration v) from
            then ExteriorVertex v :: rest_roots
            else rest_roots
        | None => rest_roots
        end
  end.

Definition effective_remset_roots
           (g: LGraph) (rmst: remset) (rh: remset_heap) (from: nat): roots_t :=
  effective_remset_roots_from_space g rmst from (nth_remset_space rh from).

Definition remset_augmented_roots
           (g: LGraph) (rmst: remset) (rh: remset_heap)
           (from: nat) (roots: roots_t): roots_t :=
  effective_remset_roots g rmst rh from ++ roots.

Lemma forward_remset_gh_frr_dsr_augmented_iso:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g_scan ->
    reachable_iff_marked
      g g_scan (remset_augmented_roots g rmst rh from roots) from ->
    no_edge2gen g_scan from ->
    exists l,
      gc_graph_iso
        g (remset_augmented_roots g rmst rh from roots)
        (reset_graph from g_scan)
        (roots_map l (remset_augmented_roots g rmst rh from roots)) /\
      roots' = roots_map l roots.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst
         Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr Hscan Hreach Hnoedge.
  destruct (forward_remset_gh_frr_dsr_remset_semi_iso
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
              g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst
              Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr Hscan)
    as [l [Hsemi [Hroots_map _]]].
  assert (Hsound_rem: sound_gc_graph g_rem) by
      (eapply forward_remset_gh_sound; eauto).
  assert (Hto_rem: graph_has_gen g_rem to) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to);
       exact Hto).
  assert (Hsound1: sound_gc_graph g1) by
      (eapply frr_sound; eauto).
  assert (Hto1: graph_has_gen g1 to) by
      (rewrite <- (frr_graph_has_gen from to roots g_rem roots' g1
                     Hto_rem Hfrr to);
       exact Hto_rem).
  assert (Hsound_scan: sound_gc_graph g_scan) by
      (eapply dsr_sound; eauto).
  exists l.
  split; [|exact Hroots_map].
  eapply remset_quasi_iso_reset_iso; eauto.
  eapply remset_semi_quasi_iso; eauto.
Qed.

Lemma effective_remset_roots_from_space_In:
  forall g rmst from r v,
    In (ExteriorVertex v) (effective_remset_roots_from_space g rmst from r) <->
    exists item,
      In item r /\
      remset_item_in_gen item rmst g from = false /\
      vgeneration v = from /\
      remset_item_effective_root g rmst item = Some v.
Proof.
  intros g rmst from r. induction r as [|item rest IH]; intros v; simpl.
  - split; intros H.
    + contradiction.
    + destruct H as [item [? _]]. contradiction.
  - destruct (remset_item_in_gen item rmst g from) eqn:Hin_gen.
    + rewrite IH. split; intros H.
      * destruct H as [item' [Hin [Hnotin Heq]]].
        exists item'. split; [right; exact Hin | split; assumption].
      * destruct H as [item' [[Hin | Hin] [Hnotin Heq]]].
        -- subst item'. rewrite Hin_gen in Hnotin. discriminate.
        -- exists item'. split; [exact Hin | split; assumption].
    + destruct (remset_item_effective_root g rmst item) as [root |] eqn:Hroot.
      * destruct (Nat.eqb (vgeneration root) from) eqn:Hroot_gen.
        -- simpl. rewrite IH. split; intros H.
           ++ destruct H as [H | [item' [Hin [Hnotin [Hgen Heq]]]]].
              ** inversion H. subst root.
                 exists item.
                 split; [left; reflexivity | split; [exact Hin_gen | split; [|exact Hroot]]].
                 apply Nat.eqb_eq. exact Hroot_gen.
              ** exists item'. split; [right; exact Hin | split; [|split]; assumption].
           ++ destruct H as [item' [[Hin | Hin] [Hnotin [Hgen Heq]]]].
              ** subst item'. rewrite Hroot in Heq. inversion Heq.
                 left. reflexivity.
              ** right. exists item'. split; [exact Hin | split; [|split]; assumption].
        -- rewrite IH. split; intros H.
           ++ destruct H as [item' [Hin [Hnotin [Hgen Heq]]]].
              exists item'. split; [right; exact Hin | split; [|split]; assumption].
           ++ destruct H as [item' [[Hin | Hin] [Hnotin [Hgen Heq]]]].
              ** subst item'. rewrite Hroot in Heq. inversion Heq; subst v.
                 rewrite Hgen, Nat.eqb_refl in Hroot_gen. discriminate.
              ** exists item'. split; [exact Hin | split; [|split]; assumption].
      * rewrite IH. split; intros H.
        -- destruct H as [item' [Hin [Hnotin [Hgen Heq]]]].
           exists item'. split; [right; exact Hin | split; [|split]; assumption].
        -- destruct H as [item' [[Hin | Hin] [Hnotin [Hgen Heq]]]].
           ++ subst item'. rewrite Hroot in Heq. discriminate.
           ++ exists item'. split; [exact Hin | split; [|split]; assumption].
Qed.

Lemma effective_remset_roots_In:
  forall g rmst rh from v,
    In (ExteriorVertex v) (effective_remset_roots g rmst rh from) <->
    exists item,
      In item (nth_remset_space rh from) /\
      remset_item_in_gen item rmst g from = false /\
      vgeneration v = from /\
      remset_item_effective_root g rmst item = Some v.
Proof.
  intros. unfold effective_remset_roots.
  apply effective_remset_roots_from_space_In.
Qed.

Lemma effective_remset_roots_in_gen:
  forall g rmst rh from v,
    In (ExteriorVertex v) (effective_remset_roots g rmst rh from) ->
    vgeneration v = from.
Proof.
  intros g rmst rh from v Hin.
  rewrite effective_remset_roots_In in Hin.
  destruct Hin as [_ [_ [_ [Hgen _]]]].
  exact Hgen.
Qed.

Lemma remset_item_effective_root_in_effective_roots_from_space_cons:
  forall g rmst from item r v,
    remset_item_in_gen item rmst g from = false ->
    remset_item_effective_root g rmst item = Some v ->
    vgeneration v = from ->
    In (ExteriorVertex v)
       (effective_remset_roots_from_space g rmst from (item :: r)).
Proof.
  intros g rmst from item r v Hnotin Heff Hgen.
  simpl.
  rewrite Hnotin, Heff, Hgen, Nat.eqb_refl.
  simpl. left. reflexivity.
Qed.

Lemma forward_remset_gh_effective_roots_marked:
  forall from to g h rh rmst g' h' rh' rmst' v,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    In (ExteriorVertex v) (effective_remset_roots g rmst rh from) ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    raw_mark (vlabel g' v) = true.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' v
         Hneq Hsound Hto Hun Hndd Hfirst Hunrec Hstate Hin Hfrg.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] [Hext _]].
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  rewrite effective_remset_roots_In in Hin.
  destruct Hin as [item [Hin_item [Hnotin [Hgen Heff]]]].
  destruct item as [addr | [src pos]]; simpl in Hnotin, Heff.
  - destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind;
      [|discriminate].
    destruct rext as [out addr' | root addr']; simpl in Heff;
      try discriminate.
    inversion Heff; subst root; clear Heff.
    apply find_remset_ext_some in Hfind.
    destruct Hfind as [Hvertex Haddr].
    simpl in Haddr. subst addr'.
    assert (Hv: graph_has_v g v). {
      unfold remset_graph_compatible in Hrgc.
      rewrite Forall_forall in Hrgc.
      specialize (Hrgc _ Hvertex).
      exact Hrgc.
    }
    eapply forward_remset_gh_exterior_root_marked; eauto.
  - destruct (Znth pos (make_fields g src)) as [z | p | e] eqn:Hfield;
      try discriminate.
    inversion Heff; subst v; clear Heff.
    rewrite nth_remset_space_Znth in Hin_item.
    eapply forward_remset_gh_interior_root_marked; eauto.
Qed.

Lemma remset_ext_effective_root_graph_has_v:
  forall g rmst rext v,
    remset_graph_compatible g rmst ->
    In rext rmst ->
    remset_ext_effective_root rext = Some v ->
    graph_has_v g v.
Proof.
  intros g rmst rext v Hrgc Hin Heff.
  unfold remset_graph_compatible in Hrgc.
  rewrite Forall_forall in Hrgc.
  specialize (Hrgc _ Hin).
  destruct rext; simpl in Heff, Hrgc; inversion Heff; subst; assumption.
Qed.

Lemma remset_item_effective_root_graph_has_v:
  forall g rmst item v from,
    sound_gc_graph g ->
    no_dangling_dst g ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    remset_item_effective_root g rmst item = Some v ->
    graph_has_v g v.
Proof.
  intros g rmst item v from Hsound Hndd Hrgc Hric Heff.
  destruct item as [addr | [src pos]]; simpl in Hric, Heff.
  - destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind; [|discriminate].
    apply find_remset_ext_some in Hfind.
    destruct Hfind as [Hin _].
    eapply remset_ext_effective_root_graph_has_v; eauto.
  - destruct Hric as [Hsrc [Hpos _]].
    destruct (Znth pos (make_fields g src)) eqn:Hfield; try discriminate.
    inversion Heff; subst v; clear Heff.
    assert (Heq: e = (src, Z.to_nat pos)) by
        (eapply make_fields_Znth_edge; eauto).
    subst e.
    eapply Hndd; eauto.
    rewrite get_edges_In_iff.
    rewrite <- Hfield.
    apply Znth_In.
    now rewrite make_fields_eq_length.
Qed.

Lemma effective_remset_roots_from_space_graph_compatible:
  forall g rmst r from,
    sound_gc_graph g ->
    no_dangling_dst g ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    roots_graph_compatible (effective_remset_roots_from_space g rmst from r) g.
Proof.
  intros g rmst r from Hsound Hndd Hrgc Hrrsc.
  unfold roots_graph_compatible.
  rewrite Forall_forall.
  intros v Hin.
  rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hin.
  rewrite effective_remset_roots_from_space_In in Hin.
  destruct Hin as [item [Hitem [_ [_ Heff]]]].
  unfold remset_and_remset_space_compatible in Hrrsc.
  rewrite Forall_forall in Hrrsc.
  eapply remset_item_effective_root_graph_has_v; eauto.
Qed.

Lemma effective_remset_roots_graph_compatible_simple:
  forall g rh rmst from,
    sound_gc_graph g ->
    no_dangling_dst g ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    roots_graph_compatible (effective_remset_roots g rmst rh from) g.
Proof.
  intros g rh rmst from Hsound Hndd Hrgc Hrrhc.
  unfold effective_remset_roots.
  rewrite nth_remset_space_Znth.
  eapply effective_remset_roots_from_space_graph_compatible; eauto.
  eapply rrhc_forall_rrsc; exact Hrrhc.
Qed.

Lemma graph_has_e_make_fields_Znth_edge:
  forall g e,
    graph_has_e g e ->
    Znth (Z.of_nat (snd e)) (make_fields g (fst e)) = FieldEdge e.
Proof.
  intros g e Hge.
  destruct Hge as [_ Hin_edge].
  rewrite get_edges_In_iff in Hin_edge.
  apply In_Znth in Hin_edge.
  destruct Hin_edge as [j [Hj HZnth]].
  assert (Hj_raw: 0 <= j < Zlength (raw_fields (vlabel g (fst e)))) by
      (rewrite <- make_fields_eq_length; exact Hj).
  pose proof (make_fields_Znth_edge g (fst e) j e Hj_raw HZnth) as Heq.
  destruct e as [src idx].
  simpl in *.
  inversion Heq.
  subst idx.
  rewrite Z2Nat.id by lia.
  exact HZnth.
Qed.

Lemma old_nonfrom_edge_dst_in_effective_remset_roots:
  forall g rh rmst from e,
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    graph_has_e g e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    In (ExteriorVertex (dst g e)) (effective_remset_roots g rmst rh from).
Proof.
  intros g rh rmst from e Hfirst Hunrec Hge Hsrc_ne Hdst_gen.
  assert (Hsrc_gt: (from < vgeneration (fst e))%nat). {
    destruct (lt_eq_lt_dec (vgeneration (fst e)) from) as [[Hlt | Heq] | Hgt].
    - destruct Hge as [Hsrc_has _].
      unfold firstn_gen_clear, graph_gen_clear in Hfirst.
      specialize (Hfirst (vgeneration (fst e)) Hlt).
      destruct (fst e) as [src_gen src_idx].
      simpl in *.
      destruct Hsrc_has as [_ Hidx].
      unfold gen_has_index in Hidx.
      simpl in Hidx.
      rewrite Hfirst in Hidx.
      lia.
    - contradiction.
    - exact Hgt.
  }
  assert (Hback: (egeneration e > vgeneration (dst g e))%nat). {
    unfold egeneration.
    rewrite Hdst_gen.
    exact Hsrc_gt.
  }
  assert (Hin:
            In (RemSetInterior (InteriorVertexPos (fst e) (Z.of_nat (snd e))))
               (nth_remset_space rh from)) by
      (eapply no_unrecorded_backward_edge_current_remset_direct;
       [exact Hunrec | exact Hge | unfold egeneration; exact Hsrc_gt | exact Hdst_gen]).
  rewrite effective_remset_roots_In.
  exists (RemSetInterior (InteriorVertexPos (fst e) (Z.of_nat (snd e)))).
  split; [exact Hin | split].
  - simpl. apply Nat.eqb_neq. exact Hsrc_ne.
  - simpl. now rewrite graph_has_e_make_fields_Znth_edge.
Qed.

Lemma old_nonfrom_edge_dst_in_remset_augmented_roots:
  forall g rh rmst from roots e,
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    graph_has_e g e ->
    vgeneration (fst e) <> from ->
    vgeneration (dst g e) = from ->
    In (ExteriorVertex (dst g e))
       (remset_augmented_roots g rmst rh from roots).
Proof.
  intros g rh rmst from roots e Hfirst Hunrec Hge Hsrc_ne Hdst_gen.
  unfold remset_augmented_roots.
  apply in_or_app.
  left.
  eapply old_nonfrom_edge_dst_in_effective_remset_roots; eauto.
Qed.

Lemma remset_semi_iso_current_non_to_valid_base:
  forall base current from to l v,
    sound_gc_graph base ->
    gc_graph_remset_semi_iso base current from to l ->
    vvalid current v ->
    vgeneration v <> to ->
    vvalid base v.
Proof.
  intros base current from to l v Hsound Hsemi Hvalid_current Hnot_to.
  destruct Hsound as [Hvv_base _].
  destruct (vvalid_lcm base v Hvv_base) as [Hvalid_base | Hnot_valid_base].
  - exact Hvalid_base.
  - exfalso.
    destruct Hsemi as [_ Hspec].
    destruct (split l) as [from_l to_l] eqn:Hsplit.
    destruct Hspec as [_ [[_ [Hto_valid Hto_gen]] _]].
    assert (Hin_to: In v to_l) by
        (rewrite Hto_valid; split; assumption).
    specialize (Hto_gen _ Hin_to).
    contradiction.
Qed.

Lemma remset_semi_iso_current_old_nonfrom_edge_dst_not_from:
  forall base current from to l e,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph current ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base current from to l ->
    no_unmarked_old_nonfrom_dst base current from ->
    graph_has_e current e ->
    vvalid base (fst e) ->
    vgeneration (fst e) <> from ->
    vgeneration (dst current e) <> from.
Proof.
  intros base current from to l e Hneq Hsound_base Hsound_current Hndd_base
         Hsemi Hclosed Hge_current Hsrc_valid_base Hsrc_not_from Hdst_from.
  pose proof Hsemi as Hsemi0.
  pose proof Hsound_base as Hsound_base_full.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  destruct Hge_current as [_ Hfield_current].
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [_ [Hlabel _]]].
  assert (Hsrc_not_in: ~ In (fst e) from_l). {
    intro Hin.
    rewrite <- Hfrom in Hin.
    destruct Hin as [_ [_ Hsrc_from]].
    contradiction.
  }
  assert (Hlabel_src: vlabel base (fst e) = vlabel current (fst e)) by
      (apply Hlabel; assumption).
  assert (Hge_base: graph_has_e base e). {
    split.
    - apply (proj1 (Hvv_base _)); exact Hsrc_valid_base.
    - unfold get_edges, make_fields in Hfield_current |- *.
      rewrite Hlabel_src. exact Hfield_current.
  }
  assert (He_base: evalid base e) by
      (apply (proj2 (Hev_base _)); exact Hge_base).
  destruct (raw_mark (vlabel current (dst current e))) eqn:Hmark.
  - exact (remset_semi_iso_no_marked_old_nonfrom_edge
             base current from to l e Hneq Hsound_base_full Hndd_base Hsemi0
             He_base Hsrc_not_from Hdst_from Hmark).
  - exact (remset_semi_iso_no_unmarked_old_nonfrom_edge
             base current from to l e Hneq Hsound_base_full Hndd_base Hsemi0
             Hclosed He_base Hsrc_not_from Hdst_from Hmark).
Qed.

Lemma remset_semi_iso_current_non_to_edge_dst_not_from:
  forall base current from to l e,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph current ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base current from to l ->
    no_unmarked_old_nonfrom_dst base current from ->
    graph_has_e current e ->
    vgeneration (fst e) <> from ->
    vgeneration (fst e) <> to ->
    vgeneration (dst current e) <> from.
Proof.
  intros base current from to l e Hneq Hsound_base Hsound_current Hndd_base
         Hsemi Hclosed Hge_current Hsrc_not_from Hsrc_not_to.
  assert (Hsrc_valid_current: vvalid current (fst e)). {
    destruct Hsound_current as [Hvv_current _].
    apply (proj2 (Hvv_current _)).
    destruct Hge_current as [Hsrc _].
    exact Hsrc.
  }
  assert (Hsrc_valid_base: vvalid base (fst e)) by
      (eapply remset_semi_iso_current_non_to_valid_base; eauto).
  exact (remset_semi_iso_current_old_nonfrom_edge_dst_not_from
           base current from to l e Hneq Hsound_base Hsound_current Hndd_base
           Hsemi Hclosed Hge_current Hsrc_valid_base Hsrc_not_from).
Qed.

Lemma remset_semi_iso_copied_edge_dst_base:
  forall base current from to l x y idx,
    from <> to ->
    sound_gc_graph base ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base current from to l ->
    In (x, y) l ->
    graph_has_e current (y, idx) ->
    vgeneration (dst current (y, idx)) = from ->
    graph_has_e base (x, idx) /\
    dst current (y, idx) = dst base (x, idx) /\
    vgeneration (dst base (x, idx)) = from.
Proof.
  intros base current from to l x y idx Hneq Hsound_base Hndd_base
         Hsemi Hpair Hedge_current Hdst_current_gen.
  pose proof Hsemi as Hsemi0.
  destruct Hsound_base as [Hvv_base [Hev_base _]].
  assert (Hdd: DoubleNoDup l) by
      (eapply remset_semi_iso_DoubleNoDup; eauto).
  destruct Hsemi as [Hcopy Hspec].
  specialize (Hcopy _ _ Hpair) as [_ [Hlabel Hdst_copy]].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] [[_ [Hto_valid Hto_gen]] _]].
  assert (Hx_valid: vvalid base x). {
    assert (Hfrom_l: from_l = map fst l) by
        (rewrite map_fst_split, Hsplit; reflexivity).
    assert (Hin_from: In x from_l). {
      rewrite Hfrom_l.
      eapply In_map_fst; exact Hpair.
    }
    rewrite <- Hfrom in Hin_from.
    tauto.
  }
  assert (Hidx: In idx (map snd (get_edges base x))). {
    destruct Hedge_current as [_ Hfield_current].
    rewrite get_edges_In in Hfield_current.
    rewrite (vlabel_get_edges_snd x y base current Hlabel).
    exact Hfield_current.
  }
  assert (Hedge_base: graph_has_e base (x, idx)). {
    split.
    - apply (proj1 (Hvv_base _)); exact Hx_valid.
    - rewrite get_edges_In. exact Hidx.
  }
  assert (Hevalid_base: evalid base (x, idx)) by
      (apply (proj2 (Hev_base _)); exact Hedge_base).
  assert (Hdst_valid_base: vvalid base (dst base (x, idx))). {
    apply (proj2 (Hvv_base _)).
    destruct Hedge_base as [Hsrc_has Hfield].
    eapply Hndd_base; eauto.
  }
  specialize (Hdst_copy idx Hidx).
  destruct Hdst_copy as [Hdst_eq | Hdst_map].
  - split; [exact Hedge_base |].
    split; [exact Hdst_eq |].
    now rewrite <- Hdst_eq.
  - destruct (in_dec equiv_dec (dst base (x, idx)) from_l)
      as [Hin_from | Hnot_from].
    + assert (Hin_fst: In (dst base (x, idx)) (map fst l)) by
          (rewrite map_fst_split, Hsplit; exact Hin_from).
      rewrite In_map_fst_iff in Hin_fst.
      destruct Hin_fst as [dst_to Hdst_pair].
      destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hdst_pair) as [Hmap _].
      rewrite Hmap in Hdst_map.
      assert (Hin_to: In dst_to to_l). {
        apply In_map_snd in Hdst_pair.
        now rewrite map_snd_split, Hsplit in Hdst_pair.
      }
      specialize (Hto_gen _ Hin_to).
      rewrite Hdst_map in Hdst_current_gen.
      lia.
    + assert (Hnot_to: ~ In (dst base (x, idx)) to_l). {
        intro Hin_to.
        rewrite Hto_valid in Hin_to.
        destruct Hin_to as [_ Hnot_valid].
        contradiction.
      }
      assert (Hnot_either: ~ InEither (dst base (x, idx)) l). {
        unfold InEither.
        rewrite Hsplit, in_app_iff.
        tauto.
      }
      rewrite list_bi_map_not_In in Hdst_map by exact Hnot_either.
      split; [exact Hedge_base |].
      split; [exact Hdst_map |].
      now rewrite Hdst_map in Hdst_current_gen.
Qed.

Lemma remset_semi_iso_old_valid:
  forall base current from to l v,
    gc_graph_remset_semi_iso base current from to l ->
    vvalid base v ->
    vvalid current v.
Proof.
  intros base current from to l v Hsemi Hvalid.
  destruct Hsemi as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [_ [_ [_ Hpartial]]].
  unfold remset_partial_graph in Hpartial.
  destruct Hpartial as [Holdvalid _].
  exact (Holdvalid _ Hvalid).
Qed.

Lemma remset_semi_iso_from_valid_iff:
  forall base current from to l v,
    from <> to ->
    sound_gc_graph base ->
    gc_graph_remset_semi_iso base current from to l ->
    vgeneration v = from ->
    (vvalid current v <-> vvalid base v).
Proof.
  intros base current from to l v Hneq Hsound Hsemi Hgen.
  split.
  - intros Hvalid.
    eapply remset_semi_iso_current_non_to_valid_base; eauto.
    rewrite Hgen. exact Hneq.
  - intros Hvalid.
    eapply remset_semi_iso_old_valid; eauto.
Qed.

Lemma forward_remset_gh_effective_root_reachable_or_marked:
  forall from to roots g h rh rmst g' h' rh' rmst' l v,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    gc_graph_remset_semi_iso g g' from to l ->
    In (ExteriorVertex v) (effective_remset_roots g rmst rh from) ->
    let ready := remset_ready_roots l in
    reachable_or_marked from g' (ready ++ roots) v.
Proof.
  intros from to roots g h rh rmst g' h' rh' rmst' l v Hneq Hsound Hto
         Hun Hndd Hfirst Hunrec Hstate Hfrg Hsemi Hin.
  cbn zeta.
  split.
  - eapply effective_remset_roots_in_gen; exact Hin.
  - right.
    split.
    + assert (Hroots:
                roots_graph_compatible (effective_remset_roots g rmst rh from) g) by
          (destruct Hstate as [[_ [Hrgc Hrrhc]] _];
           eapply effective_remset_roots_graph_compatible_simple; eauto).
      assert (Hgv: graph_has_v g v). {
        unfold roots_graph_compatible in Hroots.
        rewrite Forall_forall in Hroots.
        apply Hroots.
        rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
        exact Hin.
      }
      assert (Hvalid_g: vvalid g v) by
          (destruct Hsound as [Hvv _]; apply (proj2 (Hvv _)); exact Hgv).
      eapply remset_semi_iso_old_valid; eauto.
    + eapply forward_remset_gh_effective_roots_marked; eauto.
Qed.

Lemma forward_remset_gh_root_reachable_or_marked:
  forall from to roots ready g g' l v,
    sound_gc_graph g ->
    roots_graph_compatible roots g ->
    gc_graph_remset_semi_iso g g' from to l ->
    In (ExteriorVertex v) roots ->
    vgeneration v = from ->
    reachable_or_marked from g' (ready ++ roots) v.
Proof.
  intros from to roots ready g g' l v Hsound Hroots Hsemi Hin Hgen.
  split; [exact Hgen |].
  left.
  rewrite filter_proj_app.
  apply reachable_through_set_app_right.
  rewrite reachable_from_roots.
  apply In_Znth in Hin.
  destruct Hin as [i [Hi HZnth]].
  exists i, v.
  split.
  - exact Hi.
  - split.
    + exact HZnth.
    + apply reachable_refl.
      assert (Hgv: graph_has_v g v). {
        unfold roots_graph_compatible in Hroots.
        rewrite Forall_forall in Hroots.
        apply Hroots.
        rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
        rewrite <- HZnth.
        apply Znth_In. exact Hi.
      }
      assert (Hvalid_g: vvalid g v) by
          (destruct Hsound as [Hvv _]; apply (proj2 (Hvv _)); exact Hgv).
      eapply remset_semi_iso_old_valid; eauto.
Qed.

Lemma forward_remset_gh_augmented_root_reachable_or_marked:
  forall from to roots g h rh rmst g' h' rh' rmst' l v,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    gc_graph_remset_semi_iso g g' from to l ->
    In (ExteriorVertex v) (remset_augmented_roots g rmst rh from roots) ->
    vgeneration v = from ->
    let ready := remset_ready_roots l in
    reachable_or_marked from g' (ready ++ roots) v.
Proof.
  intros from to roots g h rh rmst g' h' rh' rmst' l v Hneq Hsound Hto
         Hun Hroots Hndd Hfirst Hunrec Hstate Hfrg Hsemi Hin Hgen.
  unfold remset_augmented_roots in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin_eff | Hin_root].
  - eapply forward_remset_gh_effective_root_reachable_or_marked; eauto.
  - eapply forward_remset_gh_root_reachable_or_marked; eauto.
Qed.

Lemma forward_remset_item_marked_from_unmarked_effective_root:
  forall from to g h rh rmst item g' h' rh' rmst' v,
    graph_has_gen g to ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = false ->
    vgeneration v = from ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    raw_mark (vlabel g' v) = true ->
    remset_item_in_gen item rmst g from = false /\
    remset_item_effective_root g rmst item = Some v.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' v Hto Hgv Hmark0
         Hgen Hfri Hmark1.
  destruct (remset_item_in_gen item rmst g from) eqn:Hnotin.
  - unfold forward_remset_item in Hfri.
    rewrite Hnotin in Hfri. simpl in Hfri.
    inversion Hfri; subst.
    rewrite Hmark0 in Hmark1. discriminate.
  - split; [reflexivity |].
    pose proof (forward_remset_item_forward_p_relation
                  from to g h rh rmst item g' h' rh' rmst'
                  Hnotin Hfri) as Hfr.
    destruct item as [addr | [src pos]]; simpl in Hfr |- *.
    + destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind; simpl in Hfr.
      * destruct rext as [out addr' | root addr']; simpl in Hfr |- *.
        -- inversion Hfr; subst; rewrite Hmark0 in Hmark1; discriminate.
        -- inversion Hfr; subst; try (rewrite Hmark0 in Hmark1; discriminate).
           destruct (V_EqDec v root) as [Heq | Hneq].
           ++ hnf in Heq. subst v. reflexivity.
           ++ rewrite <- (lcv_raw_mark g root to v) in Hmark1; auto.
              rewrite Hmark0 in Hmark1. discriminate.
      * inversion Hfr; subst; rewrite Hmark0 in Hmark1; discriminate.
    + destruct (Znth pos (make_fields g src)) as [z | p | e] eqn:Hfield;
        simpl in Hfr |- *.
      * inversion Hfr; subst; rewrite Hmark0 in Hmark1; discriminate.
      * inversion Hfr; subst; rewrite Hmark0 in Hmark1; discriminate.
      * inversion Hfr; subst; try (rewrite Hmark0 in Hmark1; discriminate).
        -- subst new_g. rewrite <- lgd_raw_mark_eq in Hmark1.
           rewrite Hmark0 in Hmark1. discriminate.
        -- subst new_g. rewrite <- lgd_raw_mark_eq in Hmark1.
           destruct (V_EqDec v (dst g e)) as [Heq | Hneq].
           ++ hnf in Heq. subst v. reflexivity.
           ++ rewrite <- (lcv_raw_mark g (dst g e) to v) in Hmark1; auto.
              rewrite Hmark0 in Hmark1. discriminate.
Qed.

Lemma upd_remset_addr_from_vertex_inv:
  forall from to g upd_addr rmst v addr,
    from <> to ->
    remset_graph_compatible g rmst ->
    copied_to_compatible from to g ->
    In (RemSetVertex v addr) (upd_remset_addr from to g upd_addr rmst) ->
    vgeneration v = from ->
    In (RemSetVertex v addr) rmst.
Proof.
  intros from to g upd_addr rmst.
  induction rmst as [|rext rest IH]; intros v addr Hneq Hrgc Hct Hin Hgen.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    rewrite remset_graph_compatible_cons_iff in Hrgc.
    destruct Hrgc as [Hrext Hrgc_rest].
    destruct (Val.eq upd_addr (extract_address rext)) as [Heq_addr | Hneq_addr].
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * destruct rext as [out old_addr | old_v old_addr]; simpl in Hin, Hrext.
        -- inversion Hin.
        -- inversion Hin; subst v addr.
           destruct (Nat.eq_dec (vgeneration old_v) from) as [Hold | Hnot].
           ++ assert (Hto_gen: vgeneration (update_vertex from to g old_v) = to) by
                (eapply update_vertex_copied_to_generation; eauto).
              rewrite Hto_gen in Hgen. exfalso. apply Hneq. symmetry. exact Hgen.
           ++ unfold update_vertex in Hgen.
              destruct (Nat.eq_dec (vgeneration old_v) from) as [Hbad | _];
                [contradiction |].
              contradiction.
      * right. exact Hin.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. eapply IH; eauto.
Qed.

Lemma forward_remset_item_exterior_effective_root_inv:
  forall from to g h rh rmst item g2 h2 rh2 rmst2 addr v,
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    copied_to_compatible from to g ->
    (g2, h2, rh2, rmst2) = forward_remset_item from to (g, h, rh, rmst) item ->
    (match find_remset_ext addr rmst2 with
     | Some rext => remset_ext_effective_root rext
     | None => None
     end) = Some v ->
    vgeneration v = from ->
    (match find_remset_ext addr rmst with
     | Some rext => remset_ext_effective_root rext
     | None => None
     end) = Some v.
Proof.
  intros from to g h rh rmst item g2 h2 rh2 rmst2 addr v
         Hneq Hto Hcc Hrnd Hrgc Hric Hct Hfri Heff Hgen.
  destruct (find_remset_ext addr rmst2) as [rext2 |] eqn:Hfind2; [|discriminate].
  destruct rext2 as [out addr2 | root addr2]; simpl in Heff; [discriminate |].
  inversion Heff; subst root; clear Heff.
  apply find_remset_ext_some in Hfind2.
  destruct Hfind2 as [Hin2 Haddr2]. simpl in Haddr2. subst addr2.
  assert (Hin: In (RemSetVertex v addr) rmst).
  {
    unfold forward_remset_item in Hfri.
    destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hitem.
    - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
        as [newg newh] eqn:Hfgh.
      inversion Hfri; subst; clear Hfri.
      destruct item as [upd_addr | intr]; simpl.
      + eapply upd_remset_addr_from_vertex_inv; eauto.
      + exact Hin2.
    - inversion Hfri; subst. exact Hin2.
  }
  rewrite (find_remset_ext_nodup_vertex rmst v addr Hrnd Hin).
  reflexivity.
Qed.

Lemma lcv_interior_effective_root_old:
  forall g root to src pos v,
    graph_has_gen g to ->
    graph_has_v g src ->
    0 <= pos < Zlength (raw_fields (vlabel g src)) ->
    (match Znth pos (make_fields (lgraph_copy_v g root to) src) with
     | FieldEdge e => Some (dst (lgraph_copy_v g root to) e)
     | _ => None
     end) = Some v ->
    (match Znth pos (make_fields g src) with
     | FieldEdge e => Some (dst g e)
     | _ => None
     end) = Some v.
Proof.
  intros g root to src pos v Hto Hsrc Hpos Heff.
  assert (Hmf: make_fields (lgraph_copy_v g root to) src = make_fields g src). {
    unfold make_fields. rewrite <- (lcv_raw_fields g root to src Hto Hsrc).
    reflexivity.
  }
  rewrite Hmf in Heff.
  destruct (Znth pos (make_fields g src)) as [z | p | e] eqn:Hfield;
    try discriminate.
  inversion Heff; subst v; clear Heff.
  rewrite pcv_dst_old.
  - reflexivity.
  - intro Hbad.
    assert (Heq: e = (src, Z.to_nat pos)) by
        (eapply make_fields_Znth_edge; eauto).
    subst e. simpl in Hbad.
    apply graph_has_v_not_eq with (to := to) in Hsrc.
    contradiction.
Qed.

Lemma lgd_lcv_interior_effective_root_old:
  forall g root to update_e src pos v,
    graph_has_gen g to ->
    graph_has_v g src ->
    0 <= pos < Zlength (raw_fields (vlabel g src)) ->
    vgeneration v <> to ->
    (match Znth pos (make_fields (lgraph_copy_v g root to) src) with
     | FieldEdge e =>
         Some (dst (labeledgraph_gen_dst (lgraph_copy_v g root to)
                     update_e (new_copied_v g to)) e)
     | _ => None
     end) = Some v ->
    (match Znth pos (make_fields g src) with
     | FieldEdge e => Some (dst g e)
     | _ => None
     end) = Some v.
Proof.
  intros g root to update_e src pos v Hto Hsrc Hpos Hnot_to Heff.
  assert (Heff_lcv:
            (match Znth pos (make_fields (lgraph_copy_v g root to) src) with
             | FieldEdge e => Some (dst (lgraph_copy_v g root to) e)
             | _ => None
             end) = Some v).
  {
    destruct (Znth pos (make_fields (lgraph_copy_v g root to) src))
      as [z | p | e] eqn:Hfield; try discriminate.
    destruct (E_EqDec update_e e) as [Heq | Hne].
    - hnf in Heq. subst e.
      rewrite lgd_dst_new in Heff.
      inversion Heff; subst v; clear Heff.
      unfold new_copied_v in Hnot_to. simpl in Hnot_to.
      contradiction.
    - rewrite lgd_dst_old in Heff by exact Hne.
      exact Heff.
  }
  eapply lcv_interior_effective_root_old; eauto.
Qed.

Lemma forward_remset_item_interior_effective_root_inv:
  forall from to g h rh rmst item g2 h2 rh2 rmst2 src pos v,
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    remset_item_compatible g from rmst
      (RemSetInterior (InteriorVertexPos src pos)) ->
    (g2, h2, rh2, rmst2) = forward_remset_item from to (g, h, rh, rmst) item ->
    remset_item_in_gen (RemSetInterior (InteriorVertexPos src pos)) rmst2 g2 from = false ->
    (match Znth pos (make_fields g2 src) with
     | FieldEdge e => Some (dst g2 e)
     | _ => None
     end) = Some v ->
    vgeneration v = from ->
    (match Znth pos (make_fields g src) with
     | FieldEdge e => Some (dst g e)
     | _ => None
     end) = Some v.
Proof.
  intros from to g h rh rmst item g2 h2 rh2 rmst2 src pos v
         Hneq Hto Hcc Hndd Hrgc Hric_item Hric_tail Hfri Hnotin Heff Hgenv.
  simpl in Hnotin.
  apply Nat.eqb_neq in Hnotin.
  destruct Hric_tail as [Hsrc_g [Hpos _]].
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hitem.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h
      as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    inversion Hfri; subst g2 h2 rh2 rmst2; clear Hfri.
    destruct item as [addr | [isrc ipos]]; simpl in Hfr.
    + destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind; simpl in Hfr.
      * destruct rext as [out addr' | root addr']; simpl in Hfr.
        -- inversion Hfr; subst; exact Heff.
        -- inversion Hfr; subst; try exact Heff.
           eapply lcv_interior_effective_root_old; eauto.
      * inversion Hfr; subst; exact Heff.
    + destruct (Znth ipos (make_fields g isrc)) as [z | p | e0] eqn:Hfield0;
        simpl in Hfr.
      * inversion Hfr; subst; exact Heff.
      * inversion Hfr; subst; exact Heff.
      * inversion Hfr; subst; try exact Heff.
        -- subst new_g. rewrite lgd_make_fields_eq in Heff.
           destruct (Znth pos (make_fields g src)) as [z | p | e] eqn:Hfield;
             try discriminate.
           inversion Heff; subst v; clear Heff.
           destruct (E_EqDec e0 e) as [Heq | Hne].
           ++ hnf in Heq. subst e.
              assert (Hge0: graph_has_e g e0). {
                destruct Hric_item as [Hisrc [Hipos _]].
                assert (Heq0: e0 = (isrc, Z.to_nat ipos)) by
                    (eapply make_fields_Znth_edge; eauto).
                subst e0. split; [exact Hisrc |].
                rewrite get_edges_In_iff.
                rewrite <- Hfield0. apply Znth_In.
                rewrite make_fields_eq_length. exact Hipos.
              }
              assert (Hdst_has: graph_has_v g (dst g e0)) by
                  (apply (Hndd (fst e0)); destruct Hge0; assumption).
              destruct (Hcc (dst g e0) Hdst_has H2) as [_ Hdiff].
              exfalso.
              simpl in H0.
              unfold updateEdgeFunc in H0.
              rewrite if_true in H0 by reflexivity.
              rewrite <- H0 in Hdiff.
              contradiction.
           ++ simpl. unfold updateEdgeFunc.
              rewrite if_false by exact Hne. reflexivity.
        -- subst new_g. rewrite lgd_make_fields_eq in Heff.
           eapply lgd_lcv_interior_effective_root_old; eauto.
  - inversion Hfri; subst. exact Heff.
Qed.

Lemma forward_remset_item_effective_roots_tail_in_cons:
  forall from to g h rh rmst item r g2 h2 rh2 rmst2 v,
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    remset_and_remset_space_compatible g from rmst r ->
    copied_to_compatible from to g ->
    (g2, h2, rh2, rmst2) = forward_remset_item from to (g, h, rh, rmst) item ->
    In (ExteriorVertex v) (effective_remset_roots_from_space g2 rmst2 from r) ->
    In (ExteriorVertex v) (effective_remset_roots_from_space g rmst from (item :: r)).
Proof.
  intros from to g h rh rmst item r g2 h2 rh2 rmst2 v
         Hneq Hto Hcc Hndd Hrnd Hrgc Hric_item Hrrsc Hct Hfri Hin.
  rewrite effective_remset_roots_from_space_In in Hin.
  destruct Hin as [tail_item [Hin_tail [Hnotin_tail [Hgenv Heff_tail]]]].
  rewrite effective_remset_roots_from_space_In.
  exists tail_item.
  split; [right; exact Hin_tail |].
  split.
  - destruct tail_item as [addr | [src pos]]; simpl in Hnotin_tail |- *.
    + reflexivity.
    + exact Hnotin_tail.
  - split; [exact Hgenv |].
    assert (Hric_tail: remset_item_compatible g from rmst tail_item). {
      unfold remset_and_remset_space_compatible in Hrrsc.
      rewrite Forall_forall in Hrrsc.
      exact (Hrrsc _ Hin_tail).
    }
    destruct tail_item as [addr | [src pos]]; simpl in Heff_tail |- *.
    + eapply (forward_remset_item_exterior_effective_root_inv
                from to g h rh rmst item g2 h2 rh2 rmst2 addr v); eauto.
    + eapply (forward_remset_item_interior_effective_root_inv
                from to g h rh rmst item g2 h2 rh2 rmst2 src pos v); eauto.
Qed.

Lemma forward_remset_item_fold_marked_from_unmarked_effective_root:
  forall from to r g h rh rmst g' h' rh' rmst' v,
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    copied_to_compatible from to g ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = false ->
    vgeneration v = from ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    raw_mark (vlabel g' v) = true ->
    In (ExteriorVertex v) (effective_remset_roots_from_space g rmst from r).
Proof.
  intros from to r.
  induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' v Hneq Hto Hcc Hndd Hrnd Hrgc Hrrsc Hct
           Hgv Hmark0 Hgen Hfold Hmark_final.
  - simpl in Hfold. inversion Hfold; subst.
    rewrite Hmark0 in Hmark_final. discriminate.
  - change (fold_left (forward_remset_item from to) (item :: rest) (g, h, rh, rmst))
      with (fold_left (forward_remset_item from to) rest
              (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hric_item Hrrsc_tail].
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    assert (Hgv2: graph_has_v g2 v) by
        (exact (forward_remset_item_graph_has_v_pres
                  from to g h rh rmst item g2 h2 rh2 rmst2 v Hto Hgv Hfri)).
    destruct (raw_mark (vlabel g2 v)) eqn:Hmark2.
    + destruct (forward_remset_item_marked_from_unmarked_effective_root
                  from to g h rh rmst item g2 h2 rh2 rmst2 v
                  Hto Hgv Hmark0 Hgen Hfri Hmark2)
        as [Hnotin Heff].
      eapply remset_item_effective_root_in_effective_roots_from_space_cons;
        eauto.
    + destruct (forward_remset_item_step_state_with_tail
                  from to g h rh rmst item rest g2 h2 rh2 rmst2
                  Hneq Hto Hcc Hrnd Hrgc Hric_item Hrrsc_tail Hfri)
        as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
      assert (Hndd2: no_dangling_dst g2) by
          (exact (fri_no_dangling_dst from to g h rh rmst item
                    g2 h2 rh2 rmst2 Hto Hcc Hrgc Hric_item Hndd Hfri)).
      assert (Hct2: copied_to_compatible from to g2) by
          (exact (forward_remset_item_copied_to_compatible
                    from to g h rh rmst item g2 h2 rh2 rmst2
                    Hneq Hto Hct Hfri)).
      assert (Hin_tail:
                In (ExteriorVertex v)
                   (effective_remset_roots_from_space g2 rmst2 from rest)) by
          (eapply (IH g2 h2 rh2 rmst2 g' h' rh' rmst' v); eauto).
      eapply forward_remset_item_effective_roots_tail_in_cons; eauto.
Qed.

Lemma forward_remset_gh_remset_semi_iso_closed_effective_roots:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    copied_to_compatible from to g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    no_dangling_dst g ->
    gen_unmarked g from ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    exists l,
      gc_graph_remset_semi_iso g g' from to l /\
      no_unmarked_old_nonfrom_dst g g' from /\
      forall v,
        In v (map fst l) ->
        In (ExteriorVertex v) (effective_remset_roots g rmst rh from).
Proof.
  intros from to g h rh rmst g' h' rh' rmst'
         Hneq Hsound Hto Hcc Hct Hrnd Hrgc Hrrhc Hndd Hunmarked Hfirst Hunrec Hfrg.
  destruct (forward_remset_gh_remset_semi_iso_closed
              from to g h rh rmst g' h' rh' rmst'
              Hneq Hsound Hto Hcc Hrnd Hrgc Hrrhc Hndd Hunmarked
              Hfirst Hunrec Hfrg)
    as [l [Hsemi Hclosed]].
  exists l. split; [exact Hsemi |].
  split; [exact Hclosed |].
  assert (Hrrsc:
            remset_and_remset_space_compatible
              g from rmst (nth_remset_space rh from)). {
    rewrite nth_remset_space_Znth.
    eapply rrhc_forall_rrsc; exact Hrrhc.
  }
  unfold forward_remset_gh in Hfrg.
  rewrite <- nth_remset_space_Znth in Hfrg.
  intros v Hin_fst.
  pose proof Hsemi as Hsemi_copy.
  destruct Hsemi_copy as [_ Hspec].
  destruct (split l) as [from_l to_l] eqn:Hsplit.
  destruct Hspec as [[_ Hfrom] _].
  rewrite map_fst_split, Hsplit in Hin_fst.
  simpl in Hin_fst.
  apply (proj2 (Hfrom v)) in Hin_fst.
  destruct Hin_fst as [Hmark [Hvvalid Hgen]].
  assert (Hgv: graph_has_v g v) by
      (destruct Hsound as [Hvv _]; apply (proj1 (Hvv _)); exact Hvvalid).
  assert (Hmark0: raw_mark (vlabel g v) = false). {
    destruct v as [vgen vidx]. simpl in Hgen. subst vgen.
    destruct Hgv as [Hgen_has Hidx].
    exact (Hunmarked Hgen_has vidx Hidx).
  }
  unfold effective_remset_roots.
  eapply forward_remset_item_fold_marked_from_unmarked_effective_root;
    eauto.
Qed.

Lemma forward_remset_gh_backward_edge_prop_mapped_roots_effective:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    copied_to_compatible from to g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    no_dangling_dst g ->
    gen_unmarked g from ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    exists l,
      gc_graph_remset_semi_iso g g' from to l /\
      no_unmarked_old_nonfrom_dst g g' from /\
      (forall v,
          In v (map fst l) ->
          In (ExteriorVertex v) (effective_remset_roots g rmst rh from)) /\
      roots_graph_compatible
        (remset_ready_roots l) g' /\
      roots_have_no_gen
        (remset_ready_roots l) from /\
      backward_edge_prop
        g' (remset_ready_roots l) from to.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' Hneq Hsound Hto Hcc Hct Hrnd
         Hrgc Hrrhc Hndd Hun_from Hfirst Hunrec Hfrg.
  destruct (forward_remset_gh_remset_semi_iso_closed_effective_roots
              from to g h rh rmst g' h' rh' rmst'
              Hneq Hsound Hto Hcc Hct Hrnd Hrgc Hrrhc Hndd Hun_from
              Hfirst Hunrec Hfrg) as [l [Hsemi [Hclosed Hprov]]].
  assert (Hsound': sound_gc_graph g') by
      (eapply forward_remset_gh_sound; eauto).
  exists l.
  split; [exact Hsemi |].
  split; [exact Hclosed |].
  split; [exact Hprov |].
  split.
  - eapply (remset_semi_iso_mapped_roots_graph_compatible g g' from to l); eauto.
  - split.
    + eapply (remset_semi_iso_mapped_roots_have_no_gen g g' from to l); eauto.
    + eapply (remset_semi_iso_backward_edge_prop_mapped_roots g g' from to l); eauto.
Qed.

Lemma remset_semi_iso_marked_reachable_from_augmented:
  forall from to roots g rh rmst g_rem l v,
    from <> to ->
    sound_gc_graph g ->
    gc_graph_remset_semi_iso g g_rem from to l ->
    (forall x,
        In x (map fst l) ->
        In (ExteriorVertex x) (effective_remset_roots g rmst rh from)) ->
    raw_mark (vlabel g_rem v) = true ->
    vvalid g_rem v ->
    vgeneration v = from ->
    roots_reachable_in_gen
      g (remset_augmented_roots g rmst rh from roots) from v.
Proof.
  intros from to roots g rh rmst g_rem l v Hneq Hsound Hsemi Hprov
         Hmark Hvalid Hgen.
  assert (Hin_fst: In v (map fst l)). {
    eapply remset_semi_iso_marked_in_map_fst; eauto.
    destruct Hsound as [Hvv _]. exact Hvv.
  }
  assert (Hin_eff: In (ExteriorVertex v) (effective_remset_roots g rmst rh from))
    by (apply Hprov; exact Hin_fst).
  split; [|exact Hgen].
  exists v.
  split.
  - rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
    unfold remset_augmented_roots.
    apply in_or_app. left. exact Hin_eff.
  - apply reachable_refl.
    apply (proj1 (remset_semi_iso_from_valid_iff
                    g g_rem from to l v Hneq Hsound Hsemi Hgen)).
    exact Hvalid.
Qed.

Lemma graph_has_e_step:
  forall g e,
    sound_gc_graph g ->
    graph_has_e g e ->
    step g (fst e) (dst g e).
Proof.
  intros g e Hsound Hge.
  rewrite step_spec.
  exists e.
  split.
  - destruct Hsound as [_ [Hevalid _]].
    apply (proj2 (Hevalid _)); exact Hge.
  - split; [|reflexivity].
    destruct Hsound as [_ [_ [Hsrc _]]].
    now rewrite Hsrc.
Qed.

Lemma roots_reachable_in_gen_edge:
  forall g roots gen e,
    sound_gc_graph g ->
    no_dangling_dst g ->
    roots_reachable_in_gen g roots gen (fst e) ->
    graph_has_e g e ->
    vgeneration (dst g e) = gen ->
    roots_reachable_in_gen g roots gen (dst g e).
Proof.
  intros g roots gen e Hsound Hndd Hreach Hge Hdst_gen.
  destruct Hreach as [Hreach Hsrc_gen].
  destruct Hge as [Hsrc_has Hfield].
  assert (Hge: graph_has_e g e) by (split; assumption).
  split; [|exact Hdst_gen].
  eapply reachable_through_set_edge; [exact Hreach |].
  unfold edge.
  split.
  - destruct Hsound as [Hvv _].
    apply (proj2 (Hvv _)).
    exact Hsrc_has.
  - split.
    + destruct Hsound as [Hvv _].
      apply (proj2 (Hvv _)).
      eapply Hndd; eauto.
    + eapply graph_has_e_step; eauto.
Qed.

Lemma graph_has_e_from_same_fields:
  forall g1 g2 v1 v2 idx,
    graph_has_v g2 v2 ->
    vlabel g1 v1 = vlabel g2 v2 ->
    In idx (map snd (get_edges g1 v1)) ->
    graph_has_e g2 (v2, idx).
Proof.
  intros g1 g2 v1 v2 idx Hgv Hlabel Hin.
  split; [exact Hgv |].
  rewrite get_edges_In.
  rewrite <- (vlabel_get_edges_snd v1 v2 g1 g2 Hlabel).
  exact Hin.
Qed.

Lemma fr_O_from_edge_inv:
  forall from to p g g' e,
    graph_has_gen g to ->
    from <> to ->
    (forall e0, p = ForwardEdge e0 -> vgeneration (fst e0) <> from) ->
    forward_relation from to O p g g' ->
    graph_has_e g' e ->
    vgeneration (fst e) = from ->
    graph_has_e g e /\ dst g' e = dst g e.
Proof.
  intros from to p g g' e Hto Hneq Hedge_src Hfr He Hsrc_gen.
  destruct p as [z | out | v | e0]; inversion Hfr; subst; simpl in *;
    try solve [split; [assumption | reflexivity]].
  - split.
    + destruct He as [Hsrc_new Hfield_new].
      assert (Hsrc_old: graph_has_v g (fst e)). {
        apply lcv_graph_has_v_inv in Hsrc_new; [|exact Hto].
        destruct Hsrc_new as [Hsrc_old | Hsrc_new].
        - exact Hsrc_old.
        - exfalso.
          unfold new_copied_v in Hsrc_new.
          destruct e as [[eg ei] idx]. simpl in *.
          inversion Hsrc_new; subst eg.
          contradiction.
      }
      split; [exact Hsrc_old |].
      unfold get_edges, make_fields in Hfield_new |- *.
      change (In e
                (filter_proj field_proj_edge
                   (make_fields (lgraph_copy_v g v to) (fst e)))) in Hfield_new.
      rewrite (lcv_raw_fields g v to (fst e) Hto Hsrc_old).
      exact Hfield_new.
    + rewrite pcv_dst_old.
      * reflexivity.
      * intro Hbad.
        unfold new_copied_v in Hbad.
        destruct e as [[eg ei] idx]. simpl in *.
        inversion Hbad; subst eg.
        contradiction.
  - destruct (E_EqDec e0 e) as [Heq | Hne].
    + hnf in Heq. subst e.
      exfalso. apply (Hedge_src e0 eq_refl). reflexivity.
    + split.
      * destruct He as [Hsrc_new Hfield_new].
        split.
        -- exact Hsrc_new.
        -- unfold get_edges, make_fields in Hfield_new |- *.
           exact Hfield_new.
      * simpl. unfold updateEdgeFunc.
        rewrite if_false by (intro Hbad; apply Hne; hnf; exact Hbad).
        reflexivity.
  - destruct (E_EqDec e0 e) as [Heq | Hne].
    + hnf in Heq. subst e.
      exfalso. apply (Hedge_src e0 eq_refl). reflexivity.
    + split.
      * subst new_g.
        destruct He as [Hsrc_new Hfield_new].
        rewrite <- lgd_graph_has_v in Hsrc_new.
        assert (Hsrc_old: graph_has_v g (fst e)). {
          apply lcv_graph_has_v_inv in Hsrc_new; [|exact Hto].
          destruct Hsrc_new as [Hsrc_old | Hsrc_new].
          - exact Hsrc_old.
          - exfalso.
            unfold new_copied_v in Hsrc_new.
            destruct e as [[eg ei] idx]. simpl in *.
            inversion Hsrc_new; subst eg.
            contradiction.
        }
        split; [exact Hsrc_old |].
        unfold get_edges, make_fields in Hfield_new |- *.
        change (In e
                  (filter_proj field_proj_edge
                     (make_fields (lgraph_copy_v g (dst g e0) to)
                        (fst e)))) in Hfield_new.
        rewrite (lcv_raw_fields g (dst g e0) to (fst e) Hto Hsrc_old).
        exact Hfield_new.
      * simpl. unfold updateEdgeFunc.
        rewrite if_false by (intro Hbad; apply Hne; hnf; exact Hbad).
        rewrite pcv_dst_old.
        -- reflexivity.
        -- intro Hbad.
           unfold new_copied_v in Hbad.
           destruct e as [[eg ei] idx]. simpl in *.
           inversion Hbad; subst eg.
           contradiction.
Qed.

Lemma remset_item2forward_t_edge_source_not_from:
  forall from rmst g item e,
    remset_item_compatible g from rmst item ->
    remset_item_in_gen item rmst g from = false ->
    remset_item2forward_t item rmst g = ForwardEdge e ->
    vgeneration (fst e) <> from.
Proof.
  intros from rmst g item e Hric Hnotin Hforward.
  destruct item as [addr | [src pos]]; simpl in Hnotin, Hforward.
  - destruct (find_remset_ext addr rmst) as [rext |] eqn:Hfind;
      [destruct rext |]; simpl in Hforward; discriminate.
  - apply Nat.eqb_neq in Hnotin.
    destruct Hric as [Hsrc [Hpos _]].
    destruct (Znth pos (make_fields g src)) as [z | p | e0] eqn:Hfield;
      simpl in Hforward; try discriminate.
    inversion Hforward; subst e0.
    assert (Heq: e = (src, Z.to_nat pos)) by
        (eapply make_fields_Znth_edge; eauto).
    rewrite Heq. simpl. exact Hnotin.
Qed.

Lemma forward_remset_item_from_edge_inv:
  forall from to g h rh rmst item g' h' rh' rmst' e,
    graph_has_gen g to ->
    from <> to ->
    remset_item_compatible g from rmst item ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    graph_has_e g' e ->
    vgeneration (fst e) = from ->
    graph_has_e g e /\ dst g' e = dst g e.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' e
         Hto Hneq Hric Hfri He Hsrc_gen.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hprocess.
  - apply negb_true_iff in Hprocess.
    destruct (forward_graph_and_heap from to O
                (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    pose proof (fr_forward_graph_and_heap
                  from to O (remset_item2forward_t item rmst g) g h)
      as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    inversion Hfri; subst g' h' rh' rmst'; clear Hfri.
    eapply fr_O_from_edge_inv; eauto.
    intros e0 Hedge.
    eapply remset_item2forward_t_edge_source_not_from; eauto.
  - inversion Hfri; subst g' h' rh' rmst'. split; [exact He | reflexivity].
Qed.

Lemma forward_remset_item_fold_from_edge_inv:
  forall from to r g h rh rmst g' h' rh' rmst' e,
    graph_has_gen g to ->
    from <> to ->
    remset_nodup rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    graph_has_e g' e ->
    vgeneration (fst e) = from ->
    graph_has_e g e /\ dst g' e = dst g e.
Proof.
  intros from to r.
  induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' e Hto Hneq Hrnd Hrrsc Hfold
           He Hsrc_gen.
  - simpl in Hfold. inversion Hfold; subst. split; [exact He | reflexivity].
  - cbn [fold_left] in Hfold.
    change ((g', h', rh', rmst') =
            fold_left (forward_remset_item from to) rest
              (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
    unfold remset_and_remset_space_compatible in Hrrsc.
    rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hric_item Hrrsc_rest].
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri2.
    symmetry in Hfri2.
    assert (Hto2: graph_has_gen g2 to) by
        (rewrite <- (forward_remset_item_ghg
                       from to g h rh rmst item g2 h2 rh2 rmst2
                       Hto Hfri2 to); exact Hto).
    assert (Hrnd2: remset_nodup rmst2) by
        (eapply fri_remset_nodup; eauto).
    assert (Hrrsc_rest2: remset_and_remset_space_compatible
                            g2 from rmst2 rest). {
      unfold remset_and_remset_space_compatible in *.
      rewrite Forall_forall in Hrrsc_rest |- *.
      intros item' Hin.
      specialize (Hrrsc_rest _ Hin).
      eapply (fri_remset_item_compatible
                g h rh rmst from to item' g2 h2 rh2 rmst2 item);
        eauto.
    }
    destruct (IH g2 h2 rh2 rmst2 g' h' rh' rmst' e
                 Hto2 Hneq Hrnd2 Hrrsc_rest2 Hfold He Hsrc_gen)
      as [He2 Hdst2].
    destruct (forward_remset_item_from_edge_inv
                from to g h rh rmst item g2 h2 rh2 rmst2 e
                Hto Hneq Hric_item Hfri2 He2 Hsrc_gen)
      as [He1 Hdst1].
    split; [exact He1 |].
    rewrite Hdst2, Hdst1.
    reflexivity.
Qed.

Lemma forward_remset_gh_from_edge_inv:
  forall from to g h rh rmst g' h' rh' rmst' e,
    graph_has_gen g to ->
    from <> to ->
    remset_graph_state g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    graph_has_e g' e ->
    vgeneration (fst e) = from ->
    graph_has_e g e /\ dst g' e = dst g e.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' e
         Hto Hneq Hstate Hfrg He Hsrc_gen.
  destruct Hstate as [[Hrnd [_ Hrrhc]] _].
  unfold forward_remset_gh in Hfrg.
  eapply forward_remset_item_fold_from_edge_inv; eauto.
  eapply rrhc_forall_rrsc; exact Hrrhc.
Qed.

Lemma remset_semi_iso_marked_ready_root:
  forall base current from to l roots v,
    from <> to ->
    vertex_valid base ->
    gc_graph_remset_semi_iso base current from to l ->
    raw_mark (vlabel current v) = true ->
    vvalid current v ->
    vgeneration v = from ->
    In (ExteriorVertex (list_bi_map l v))
       (remset_ready_roots l ++ roots).
Proof.
  intros base current from to l roots v Hneq Hvv Hsemi Hmark Hvalid Hgen.
  apply in_or_app. left.
  unfold roots_map.
  change (ExteriorVertex (list_bi_map l v))
    with (exterior_map (list_bi_map l) (ExteriorVertex v)).
  apply in_map.
  apply in_map.
  eapply remset_semi_iso_marked_in_map_fst; eauto.
Qed.

Lemma remset_semi_iso_from_edge_reachable_or_marked:
  forall from to roots base current l e,
    from <> to ->
    sound_gc_graph base ->
    sound_gc_graph current ->
    no_dangling_dst base ->
    gc_graph_remset_semi_iso base current from to l ->
    no_unmarked_old_nonfrom_dst base current from ->
    evalid base e ->
    vgeneration (fst e) = from ->
    vgeneration (dst base e) = from ->
    let ready := remset_ready_roots l in
    reachable_or_marked from current (ready ++ roots) (fst e) ->
    reachable_or_marked from current (ready ++ roots) (dst base e).
Proof.
  intros from to roots base current l e Hneq Hsound_base Hsound_current
         Hndd Hsemi Hclosed Hevalid Hsrc_gen Hdst_gen.
  cbn zeta.
  intros Hrom.
  assert (Hge_base: graph_has_e base e) by
      (destruct Hsound_base as [_ [Hev _]]; apply (proj1 (Hev _)); exact Hevalid).
  assert (Hdst_valid_base: vvalid base (dst base e)) by
      (destruct Hsound_base as [Hvv _]; apply (proj2 (Hvv _));
       destruct Hge_base as [Hsrc Hfield]; eapply Hndd; eauto).
  assert (Hdst_valid_current: vvalid current (dst base e)) by
      (eapply remset_semi_iso_old_valid; eauto).
  split; [exact Hdst_gen |].
  destruct (raw_mark (vlabel current (fst e))) eqn:Hsrc_mark.
  - destruct (raw_mark (vlabel current (dst base e))) eqn:Hdst_mark.
    + right. split; [exact Hdst_valid_current | reflexivity].
    + left.
      assert (Hsrc_valid_current: vvalid current (fst e)). {
        destruct Hrom as [_ [Hreach | [Hvalid _]]].
        - eapply reachable_through_set_foot_valid; eauto.
        - exact Hvalid.
      }
      assert (Hin_ready:
                In (ExteriorVertex (list_bi_map l (fst e)))
                   (remset_ready_roots l ++ roots)) by
          (eapply remset_semi_iso_marked_ready_root; eauto;
           destruct Hsound_base as [Hvv _]; exact Hvv).
      assert (Hin_fst: In (fst e) (map fst l)) by
          (eapply remset_semi_iso_marked_in_map_fst; eauto;
           destruct Hsound_base as [Hvv _]; exact Hvv).
      rewrite In_map_fst_iff in Hin_fst.
      destruct Hin_fst as [src_to Hpair].
      assert (Hdd: DoubleNoDup l) by
          (eapply remset_semi_iso_DoubleNoDup; eauto).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hdd Hpair) as [Hsrc_map _].
      pose proof Hsemi as Hsemi_copy.
      destruct Hsemi_copy as [Hcopy Hspec].
      specialize (Hcopy _ _ Hpair).
      destruct Hcopy as [_ [Hlabel Hdst_copy]].
      destruct (split l) as [from_l to_l] eqn:Hsplit.
      destruct Hspec as [[_ Hfrom] [[_ [Hto_valid _]] _]].
      assert (Hsrc_to_valid: vvalid current src_to). {
        assert (Hin_to: In src_to to_l). {
          apply In_map_snd in Hpair.
          now rewrite map_snd_split, Hsplit in Hpair.
        }
        apply Hto_valid in Hin_to.
        tauto.
      }
      assert (Hidx: In (snd e) (map snd (get_edges base (fst e)))).
      {
        destruct e as [src idx]. simpl in *.
        destruct Hge_base as [_ Hfield].
        now rewrite get_edges_In in Hfield.
      }
      specialize (Hdst_copy _ Hidx).
      assert (Hdst_not_in: ~ InEither (dst base e) l). {
        unfold InEither.
        rewrite Hsplit, in_app_iff.
        intros [Hin_from | Hin_to].
        - rewrite <- Hfrom in Hin_from.
          destruct Hin_from as [Hmark _].
          rewrite Hdst_mark in Hmark. discriminate.
        - rewrite Hto_valid in Hin_to.
          tauto.
      }
      replace (dst base (fst e, snd e)) with (dst base e) in Hdst_copy
        by (destruct e; reflexivity).
      rewrite list_bi_map_not_In in Hdst_copy by exact Hdst_not_in.
      assert (Hedge_current:
                graph_has_e current (list_bi_map l (fst e), snd e)). {
        rewrite Hsrc_map.
        eapply graph_has_e_from_same_fields.
        - destruct Hsound_current as [Hvv _].
          apply (proj1 (Hvv _)); exact Hsrc_to_valid.
        - exact Hlabel.
        - exact Hidx.
      }
      rewrite <- Hsrc_map in Hdst_copy.
      assert (Hsrc_mapped_valid: vvalid current (list_bi_map l (fst e))). {
        destruct Hsound_current as [Hvv _].
        apply (proj2 (Hvv _)).
        destruct Hedge_current as [Hgv _].
        exact Hgv.
      }
      assert (Hstep: current |= (list_bi_map l (fst e)) ~> (dst base e)). {
        destruct Hdst_copy as [Hdst_eq | Hdst_eq].
        - unfold edge.
          split; [exact Hsrc_mapped_valid |].
          split; [exact Hdst_valid_current |].
          replace (dst base e)
            with (dst current (list_bi_map l (fst e), snd e))
            by exact Hdst_eq.
          exact (graph_has_e_step current (list_bi_map l (fst e), snd e)
                   Hsound_current Hedge_current).
        - unfold edge.
          split; [exact Hsrc_mapped_valid |].
          split; [exact Hdst_valid_current |].
          replace (dst base e)
            with (dst current (list_bi_map l (fst e), snd e))
            by exact Hdst_eq.
          exact (graph_has_e_step current (list_bi_map l (fst e), snd e)
                   Hsound_current Hedge_current).
      }
      exists (list_bi_map l (fst e)).
      split.
      * rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
        exact Hin_ready.
      * eapply reachable_edge.
        -- apply reachable_refl.
           destruct Hsound_current as [Hvv _].
           apply (proj2 (Hvv _)).
           destruct Hedge_current as [Hgv _].
           exact Hgv.
        -- exact Hstep.
  - destruct Hrom as [_ [Hreach | [_ Hmark]]]; [|rewrite Hsrc_mark in Hmark; discriminate].
    left.
    pose proof Hsemi as Hsemi_copy.
    destruct Hsemi_copy as [_ Hspec].
    destruct (split l) as [from_l to_l] eqn:Hsplit.
    destruct Hspec as [_ [_ [_ Hpartial]]].
    unfold remset_partial_graph in Hpartial.
    destruct Hpartial as [_ [_ Hunmarked_edges]].
    destruct (Hunmarked_edges e Hevalid Hsrc_gen Hsrc_mark)
      as [He_current [Hsrc_eq Hdst_eq]].
    assert (Hstep: current |= (fst e) ~> (dst base e)). {
      unfold edge.
      split.
      - eapply reachable_through_set_foot_valid; eauto.
      - split; [exact Hdst_valid_current |].
        rewrite step_spec.
        exists e.
        split; [exact He_current |].
        split.
        + rewrite Hsrc_eq.
          destruct Hsound_base as [_ [_ [Hsrc_base _]]].
          now rewrite Hsrc_base.
        + exact Hdst_eq.
    }
    eapply reachable_through_set_edge; eauto.
Qed.

Lemma forward_remset_gh_augmented_reachable_or_marked:
  forall from to roots g h rh rmst g_rem h_rem rh' rmst' l v,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    gc_graph_remset_semi_iso g g_rem from to l ->
    no_unmarked_old_nonfrom_dst g g_rem from ->
    roots_reachable_in_gen
      g (remset_augmented_roots g rmst rh from roots) from v ->
    let ready := remset_ready_roots l in
    reachable_or_marked from g_rem (ready ++ roots) v.
Proof.
  intros from to roots g h rh rmst g_rem h_rem rh' rmst' l v
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate Hfrg
         Hsemi Hclosed Hreach.
  cbn zeta.
  destruct Hreach as [Hthrough Hgenv].
  destruct Hthrough as [s [Hsroot Hreach]].
  unfold reachable, reachable_by in Hreach.
  destruct Hreach as [[s0 p] Hpath].
  destruct Hpath as [[Hhead Hfoot] [Hvalid _]].
  simpl in Hhead. subst s0.
  assert (Hsound_rem: sound_gc_graph g_rem) by
      (eapply forward_remset_gh_sound; eauto).
  assert (Hpath_step:
            forall cur p0,
              valid_path g (cur, p0) ->
              (vgeneration cur = from ->
               reachable_or_marked
                 from g_rem
                 (remset_ready_roots l ++ roots)
                 cur) ->
              vgeneration (pfoot g (cur, p0)) = from ->
              reachable_or_marked
                from g_rem
                (remset_ready_roots l ++ roots)
                (pfoot g (cur, p0))). {
    intros cur0 p0.
    revert cur0.
    induction p0 as [|e p0 IH]; intros cur0 Hvalid_path Hcur_rom Hfoot_gen.
    - simpl in Hfoot_gen |- *.
      apply Hcur_rom. exact Hfoot_gen.
    - rewrite valid_path_cons_iff in Hvalid_path.
      destruct Hvalid_path as [Hsrc [Hstrong Htail]].
      rewrite pfoot_cons in Hfoot_gen |- *.
      apply IH; [exact Htail | | exact Hfoot_gen].
      intros Hdst_gen.
      destruct Hstrong as [Hevalid [Hsrc_valid Hdst_valid]].
      assert (Hge: graph_has_e g e) by
          (destruct Hsound as [_ [Hev _]]; apply (proj1 (Hev _)); exact Hevalid).
      assert (Hfst_cur: fst e = cur0). {
        destruct Hsound as [_ [_ [Hsrc_sound _]]].
        rewrite <- Hsrc_sound.
        symmetry.
        exact Hsrc.
      }
      destruct (Nat.eq_dec (vgeneration cur0) from) as [Hcur_gen | Hcur_not_gen].
      + eapply (remset_semi_iso_from_edge_reachable_or_marked
                  from to roots g g_rem l e); eauto.
        * now rewrite Hfst_cur.
        * rewrite Hfst_cur.
          apply Hcur_rom. exact Hcur_gen.
      + eapply (forward_remset_gh_augmented_root_reachable_or_marked
                  from to roots g h rh rmst g_rem h_rem rh' rmst' l
                  (dst g e)); eauto.
        * eapply old_nonfrom_edge_dst_in_remset_augmented_roots; eauto.
          -- rewrite Hfst_cur. exact Hcur_not_gen.
  }
  rewrite <- Hfoot.
  eapply (Hpath_step s p); [exact Hvalid | |].
  - intros Hs_gen.
    eapply (forward_remset_gh_augmented_root_reachable_or_marked
              from to roots g h rh rmst g_rem h_rem rh' rmst' l s);
      try exact Hneq; try exact Hsound; try exact Hto; try exact Hun;
      try exact Hroots; try exact Hndd; try exact Hfirst; try exact Hunrec;
      try exact Hstate; try exact Hfrg; try exact Hsemi.
    + apply (proj2 (filter_proj_In_iff exterior_proj_vertex_spec s _)).
      exact Hsroot.
    + exact Hs_gen.
  - rewrite Hfoot.
    exact Hgenv.
Qed.

Lemma reachable_to_from_via_edge_bridge:
  forall base current roots_base roots_current from v,
    sound_gc_graph current ->
    (forall root,
        In root roots_current ->
        vgeneration root = from ->
        roots_reachable_in_gen base roots_base from root) ->
    (forall e,
        graph_has_e current e ->
        vgeneration (dst current e) = from ->
        (vgeneration (fst e) = from ->
         roots_reachable_in_gen base roots_base from (fst e)) ->
        roots_reachable_in_gen base roots_base from (dst current e)) ->
    reachable_through_set current roots_current v ->
    vgeneration v = from ->
    roots_reachable_in_gen base roots_base from v.
Proof.
  intros base current roots_base roots_current from v Hsound Hroot Hedge
         Hreach Hgenv.
  destruct Hreach as [s [Hsroot Hreach]].
  unfold reachable, reachable_by in Hreach.
  destruct Hreach as [[s0 p] Hpath].
  destruct Hpath as [[Hhead Hfoot] [Hvalid _]].
  simpl in Hhead. subst s0.
  assert (Hpath_step:
            forall cur p0,
              valid_path current (cur, p0) ->
              (vgeneration cur = from ->
               roots_reachable_in_gen base roots_base from cur) ->
              vgeneration (pfoot current (cur, p0)) = from ->
              roots_reachable_in_gen
                base roots_base from (pfoot current (cur, p0))). {
    intros cur p0.
    revert cur.
    induction p0 as [|e p0 IH]; intros cur Hvalid_path Hcur Hfoot_gen.
    - simpl in Hfoot_gen |- *.
      apply Hcur. exact Hfoot_gen.
    - rewrite valid_path_cons_iff in Hvalid_path.
      destruct Hvalid_path as [Hsrc [Hstrong Htail]].
      rewrite pfoot_cons in Hfoot_gen |- *.
      apply IH; [exact Htail | | exact Hfoot_gen].
      intros Hdst_gen.
      destruct Hstrong as [Hevalid _].
      assert (Hge: graph_has_e current e) by
          (destruct Hsound as [_ [Hev _]]; apply (proj1 (Hev _)); exact Hevalid).
      eapply Hedge; eauto.
      intros Hsrc_gen.
      assert (Hfst_cur: fst e = cur). {
        destruct Hsound as [_ [_ [Hsrc_sound _]]].
        rewrite <- Hsrc_sound.
        symmetry.
        exact Hsrc.
      }
      rewrite Hfst_cur.
      apply Hcur.
      now rewrite <- Hfst_cur.
  }
  rewrite <- Hfoot.
  eapply (Hpath_step s p); [exact Hvalid | |].
  - intros Hs_gen.
    apply Hroot; assumption.
  - rewrite Hfoot.
    exact Hgenv.
Qed.

Lemma roots_have_no_gen_app:
  forall roots1 roots2 gen,
    roots_have_no_gen (roots1 ++ roots2) gen <->
    roots_have_no_gen roots1 gen /\ roots_have_no_gen roots2 gen.
Proof.
  unfold roots_have_no_gen.
  intros roots1 roots2 gen.
  split; intros H.
  - split; intros v Hin; apply H; apply in_or_app; auto.
  - destruct H as [H1 H2].
    intros v Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma frr_dsr_reachable_or_marked_iff_marked_ready_from_backward_start:
  forall from to ready roots1 roots2 start g1 g2 g3,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    gen_unmarked g1 to ->
    roots_graph_compatible (ready ++ roots1) g1 ->
    roots_have_no_gen ready from ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to ->
    copy_compatible g1 -> backward_edge_prop g1 (ready ++ roots1) from to ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    do_scan_relation from to start g2 g3 ->
    no_edge2gen g3 from ->
    forall v,
      reachable_or_marked from g1 (ready ++ roots1) v <->
      marked_in_gen g1 g3 from v.
Proof.
  unfold marked_in_gen.
  intros from to ready roots1 roots2 start g1 g2 g3 Hneq Hsound Hto Hun_to
         Hrgc_all Hready_no_from Hndd Hcvp Hcc Hbep Hfrr Hscan Hnoedge v.
  rewrite roots_graph_compatible_app in Hrgc_all.
  destruct Hrgc_all as [Hrgc_ready Hrgc_roots].
  pose proof (frr_rom_aux from to roots1 roots2 g1 g2 Hneq Hsound Hto
                Hrgc_roots Hndd Hcvp Hcc Hfrr ready v Hrgc_ready)
    as Hrom_frr.
  pose proof Hscan as Hscan_loop.
  destruct Hscan_loop as [n [Hsvwl_loop Hbound]].
  assert (Hsound2: sound_gc_graph g2) by (eapply frr_sound; eauto).
  assert (Hto2: graph_has_gen g2 to) by (rewrite <- frr_graph_has_gen; eauto).
  destruct (frr_rgc_aux from to roots1 g1 roots2 g2 Hneq Hto Hcc
              Hrgc_roots Hfrr ready Hrgc_ready) as [Hrgc_ready2 Hrgc_roots2].
  assert (Hrgc_all2: roots_graph_compatible (ready ++ roots2) g2) by
      (rewrite roots_graph_compatible_app; split; assumption).
  assert (Hndd2: no_dangling_dst g2) by
      (eapply (frr_no_dangling_dst _ _ _ g1); eauto).
  assert (Hcvp2: copied_vertex_prop g2 from to) by
      (eapply (frr_copied_vertex_prop _ _ _ _ g1 g2); eauto).
  assert (Hcc2: copy_compatible g2) by
      (eapply (frr_copy_compatible _ _ _ g1); eauto).
  assert (Hun2_to: gen_unmarked g2 to) by
      (eapply (frr_gen_unmarked from to _ g1); eauto).
  assert (Hbep2: backward_edge_prop g2 (ready ++ roots2) from to) by
      (eapply (frr_bep_aux from to roots1 roots2 g1 g2); eauto).
  pose proof (svwl_reachable_or_marked
                from to (ready ++ roots2)
                (seq start n) g2 g3
                Hneq Hsound2 Hto2 Hun2_to Hrgc_all2 Hndd2 Hcvp2 Hcc2
                Hbep2 Hsvwl_loop v) as Hrom_scan_loop.
  rewrite <- Hrom_frr in Hrom_scan_loop.
  assert (Hsound3: sound_gc_graph g3) by (eapply dsr_sound; eauto).
  assert (Hvalid_from:
            forall v0,
              vvalid g1 v0 /\ vgeneration v0 = from <->
              vvalid g3 v0 /\ vgeneration v0 = from). {
    destruct Hsound as [Hvv1 _].
    destruct Hsound3 as [Hvv3 _].
    red in Hvv1, Hvv3.
    intros v0. split; intros [Hv Hgen]; split; auto.
    - rewrite Hvv1 in Hv.
      eapply frr_graph_has_v in Hv; eauto.
      eapply svwl_graph_has_v in Hv; eauto.
      now rewrite Hvv3.
    - rewrite Hvv3 in Hv.
      pose proof Hscan as Hscan_loop'.
      destruct Hscan_loop' as [n' [Hsvwl_loop' _]].
      apply svwl_graph_has_v_inv with (v := v0) in Hsvwl_loop'; auto.
      destruct Hsvwl_loop' as [Hv2 | [Hgen_to _]].
      2: (rewrite Hgen_to in Hgen; exfalso; apply Hneq; symmetry; exact Hgen).
      pose proof Hfrr as Hfrr_inv.
      apply frr_graph_has_v_inv with (v := v0) in Hfrr_inv; auto.
      destruct Hfrr_inv as [Hv1 | [Hgen_to _]].
      2: (rewrite Hgen_to in Hgen; exfalso; apply Hneq; symmetry; exact Hgen).
      now rewrite Hvv1.
  }
  assert (Hroots2_no_from: roots_have_no_gen roots2 from) by
      (exact (frr_not_pointing from to roots1 g1 roots2 g2
                Hcc Hrgc_roots Hneq Hto Hfrr)).
  assert (Hall_no_from: roots_have_no_gen (ready ++ roots2) from) by
      (rewrite roots_have_no_gen_app; split; assumption).
  rewrite Hrom_scan_loop.
  rewrite reachable_or_marked_iff_marked; eauto.
  pose proof (Hvalid_from v) as Hvalid_v.
  split.
  - intros [Hmark Hvgen].
    split; [exact Hmark |].
    apply (proj2 Hvalid_v). exact Hvgen.
  - intros [Hmark Hvgen].
    split; [exact Hmark |].
    apply (proj1 Hvalid_v). exact Hvgen.
Qed.

Lemma ngr_graph_unmarked: forall g1 g2 gen,
    graph_unmarked g1 -> new_gen_relation gen g1 g2 -> graph_unmarked g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold graph_unmarked in *. intros.
    apply ang_graph_has_v_inv in H1; auto. simpl. now apply H.
Qed.

Lemma ngr_roots_graph_compatible: forall g1 g2 roots gen,
    roots_graph_compatible roots g1 -> new_gen_relation gen g1 g2 ->
    roots_graph_compatible roots g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold roots_graph_compatible in *.
    rewrite Forall_forall in *. intros. apply ang_graph_has_v. apply H; auto.
Qed.

Lemma ngr_remset_graph_compatible: forall g1 g2 rmst gen,
    remset_graph_compatible g1 rmst -> new_gen_relation gen g1 g2 ->
    remset_graph_compatible g2 rmst.
Proof.
  intros g1 g2 rmst gen Hrgc Hngr.
  red in Hngr. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct Hngr as [gen_i [_ Hg2]]. subst g2.
    unfold remset_graph_compatible in *.
    rewrite Forall_forall in *. intros re Hin.
    specialize (Hrgc _ Hin).
    destruct re; simpl in *; auto.
    apply ang_graph_has_v. exact Hrgc.
Qed.

Lemma ngr_remset_item_compatible: forall g1 g2 from rmst item gen,
    remset_item_compatible g1 from rmst item ->
    new_gen_relation gen g1 g2 ->
    remset_item_compatible g2 from rmst item.
Proof.
  intros g1 g2 from rmst item gen Hitem Hngr.
  red in Hngr. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct Hngr as [gen_i [_ Hg2]]. subst g2.
    destruct item as [addr | [v pos]]; simpl in *; auto.
    destruct Hitem as [Hv [Hpos Hmark]].
    split; [apply ang_graph_has_v; exact Hv |].
    split; [exact Hpos | exact Hmark].
Qed.

Lemma ngr_remset_and_remset_heap_compatible:
  forall g1 g2 from rmst rh gen,
    remset_and_remset_heap_compatible g1 from rmst rh ->
    new_gen_relation gen g1 g2 ->
    remset_and_remset_heap_compatible g2 from rmst rh.
Proof.
  intros g1 g2 from rmst rh gen Hrrhc Hngr.
  unfold remset_and_remset_heap_compatible in *.
  rewrite Forall_forall in *.
  intros r Hin.
  specialize (Hrrhc _ Hin).
  unfold remset_and_remset_space_compatible in *.
  rewrite Forall_forall in *.
  intros item Hitem.
  eapply ngr_remset_item_compatible; eauto.
Qed.

Lemma ngr_no_dangling_dst: forall g1 g2 gen,
    no_dangling_dst g1 -> new_gen_relation gen g1 g2 -> no_dangling_dst g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold no_dangling_dst in *. intros.
    simpl in *. apply ang_graph_has_v_inv in H1; auto. apply ang_graph_has_v.
    rewrite <- ang_get_edges in H2. eapply H; eauto.
Qed.

Lemma ngr_iso: forall g1 g2 roots gen,
    new_gen_relation gen g1 g2 -> gc_graph_iso g1 roots g2 roots.
Proof.
  intros. red in H. destruct (graph_has_gen_dec g1 gen).
  - subst. apply gc_graph_iso_refl.
  - destruct H as [gen_i [? ?]]. subst g2. red. exists id, id, id, id.
    rewrite exterior_map_id, map_id. split; easy.
Qed.

Lemma ngr_firstn_gen_clear: forall g1 g2 gen to,
    graph_has_gen g1 to -> firstn_gen_clear g1 to -> new_gen_relation gen g1 g2 ->
    firstn_gen_clear g2 to.
Proof.
  intros. red in H1. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H1 as [gen_i [? ?]]. subst g2. rewrite <- (Nat2Z.id to) in *.
    apply firstn_gen_clear_add; auto.
Qed.

Lemma new_gen_heap_graph_unmarked: forall g1 h1 g2 h2 gen,
    graph_unmarked g1 -> new_gen_heap_relation gen g1 h1 g2 h2 ->
    graph_unmarked g2.
Proof.
  intros. eapply ngr_graph_unmarked; eauto.
  eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma new_gen_heap_roots_graph_compatible: forall g1 h1 g2 h2 roots gen,
    roots_graph_compatible roots g1 ->
    new_gen_heap_relation gen g1 h1 g2 h2 ->
    roots_graph_compatible roots g2.
Proof.
  intros. eapply ngr_roots_graph_compatible; eauto.
  eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma new_gen_heap_no_dangling_dst: forall g1 h1 g2 h2 gen,
    no_dangling_dst g1 -> new_gen_heap_relation gen g1 h1 g2 h2 ->
    no_dangling_dst g2.
Proof.
  intros. eapply ngr_no_dangling_dst; eauto.
  eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma new_gen_heap_firstn_gen_clear: forall g1 h1 g2 h2 gen to,
    graph_has_gen g1 to -> firstn_gen_clear g1 to ->
    new_gen_heap_relation gen g1 h1 g2 h2 -> firstn_gen_clear g2 to.
Proof.
  intros. eapply ngr_firstn_gen_clear; eauto.
  eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma new_gen_heap_remset_forward_compatible:
  forall g1 h1 g2 h2 gen from rmst rh,
    remset_forward_compatible g1 from rmst rh ->
    new_gen_heap_relation gen g1 h1 g2 h2 ->
    remset_forward_compatible g2 from rmst rh.
Proof.
  intros g1 h1 g2 h2 gen from rmst rh [Hrnd [Hrgc Hrrhc]] Hrel.
  split; [exact Hrnd | split].
  - eapply ngr_remset_graph_compatible; eauto.
    eapply new_gen_heap_new_gen_relation; eauto.
  - eapply ngr_remset_and_remset_heap_compatible; eauto.
    eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma new_gen_heap_remset_graph_state:
  forall g1 h1 g2 h2 gen from rmst rh,
    remset_graph_state g1 from rmst rh ->
    new_gen_heap_relation gen g1 h1 g2 h2 ->
    remset_graph_state g2 from rmst rh.
Proof.
  intros g1 h1 g2 h2 gen from rmst rh [Hfw Hgen] Hrel.
  split; [|exact Hgen].
  eapply new_gen_heap_remset_forward_compatible; eauto.
Qed.

Lemma new_gen_heap_graph_generation_bound:
  forall g1 h1 g2 h2 gen,
    graph_generation_bound g1 ->
    new_gen_heap_relation gen g1 h1 g2 h2 ->
    graph_generation_bound g2.
Proof.
  unfold graph_generation_bound, new_gen_heap_relation.
  intros g1 h1 g2 h2 gen Hbound Hrel k Hk.
  destruct (graph_has_gen_dec g1 gen) as [Hhas | Hnot].
  - destruct Hrel as [Hg _]. subst g2. apply Hbound. exact Hk.
  - destruct Hrel as [gi [sp [i [Hs [Hgen [_ [_ [_ [_ [Hg2 _]]]]]]]]]].
    subst g2. rewrite ang_graph_has_gen in Hk.
    destruct Hk as [Hk | Hk].
    + apply Hbound. exact Hk.
    + subst k.
      assert (Hle: (length (g_gen (glabel g1)) <= gen)%nat) by
          (unfold graph_has_gen in Hnot; lia).
      apply Nat2Z.inj_le in Hle.
      assert (Hlt_gen: Z.of_nat gen < MAX_SPACES) by
          (rewrite <- Hgen; rewrite Z2Nat.id by lia; lia).
      lia.
Qed.

Lemma new_gen_heap_remset_heap_covers_graph:
  forall g1 h1 g2 h2 gen rh,
    remset_heap_covers_graph g1 rh ->
    new_gen_heap_relation gen g1 h1 g2 h2 ->
    remset_heap_covers_graph g2 rh.
Proof.
  intros g1 h1 g2 h2 gen rh [Hlen Hbound] Hrel.
  split; [exact Hlen |].
  eapply new_gen_heap_graph_generation_bound; eassumption.
Qed.

Lemma forward_remset_item_fold_rh_Zlength_same:
  forall from to r g h rh rmst g' h' rh' rmst',
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    Zlength rh = Zlength rh'.
Proof.
  intros from to r. induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' Hfold.
  - simpl in Hfold. inversion Hfold. reflexivity.
  - Opaque forward_remset_item.
    simpl in Hfold.
    Transparent forward_remset_item.
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    transitivity (Zlength rh2).
    + eapply fri_rh_Zlength_same; exact Hfri.
    + eapply IH; exact Hfold.
Qed.

Lemma forward_remset_gh_rh_Zlength_same:
  forall from to g h rh rmst g' h' rh' rmst',
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    Zlength rh = Zlength rh'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' Hfrg.
  unfold forward_remset_gh in Hfrg.
  eapply forward_remset_item_fold_rh_Zlength_same; exact Hfrg.
Qed.

Lemma do_generation_relation_remset_heap_covers_graph:
  forall from to roots roots' g h rh rmst rg rhh rh' rmst' g' h',
    graph_has_gen g to ->
    remset_heap_covers_graph g rh ->
    do_generation_relation from to roots roots' g h rh rmst
      rg rhh rh' rmst' g' h' ->
    remset_heap_covers_graph g' (reset_nth_remset_heap from rh').
Proof.
  intros from to roots roots' g h rh rmst rg rhh rh' rmst' g' h'
         Hto [Hlen Hbound] Hrel.
  pose proof Hrel as Hrel0.
  destruct Hrel as [[g1 [g2 [Hfrg _]]] _].
  split.
  - rewrite Zlength_correct, reset_nth_remset_heap_length.
    rewrite <- Zlength_correct.
    pose proof (forward_remset_gh_rh_Zlength_same
                  from to g h rh rmst rg rhh rh' rmst' Hfrg) as Hlen_fr.
    rewrite <- Hlen_fr. exact Hlen.
  - unfold graph_generation_bound in *.
    intros gen Hgen.
    apply Hbound.
    rewrite (do_generation_relation_graph_has_gen
               from to roots roots' g h rh rmst rg rhh rh' rmst' g' h'
               Hto Hrel0 gen).
    exact Hgen.
Qed.

Lemma upd_remset_heap_rrhc_range:
  forall g h from to item rmst rh g' h',
    0 <= Z.of_nat to < Zlength rh ->
    graph_has_gen g to ->
    remset_nodup rmst ->
    remset_item_compatible g from rmst item ->
    remset_and_remset_heap_compatible g from rmst rh ->
    forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h =
      (g', h') ->
    remset_and_remset_heap_compatible g' from
      (upd_remset from to g item rmst) (upd_remset_heap item rh to).
Proof.
  intros g h from to item rmst rh g' h' Hrange Hto Hrnd Hitem Hrrhc Hfgh.
  unfold remset_and_remset_heap_compatible in *.
  rewrite Forall_forall in Hrrhc |- *.
  intros rs Hin.
  apply upd_remset_heap_In in Hin.
  destruct Hin as [Hin | Hin].
  - specialize (Hrrhc _ Hin).
    unfold remset_and_remset_space_compatible in *.
    rewrite Forall_forall in Hrrhc |- *.
    intros x Hinx. specialize (Hrrhc _ Hinx).
    eapply forward_graph_and_heap_ric; eassumption.
  - subst rs.
    unfold remset_and_remset_space_compatible.
    rewrite Forall_forall. intros x Hinx.
    simpl in Hinx. destruct Hinx as [Hinx | Hinx].
    + subst x. eapply forward_graph_and_heap_ric; eassumption.
    + assert (Hin_to: In (Znth (Z.of_nat to) rh) rh) by
          (apply Znth_In; exact Hrange).
      specialize (Hrrhc _ Hin_to).
      unfold remset_and_remset_space_compatible in Hrrhc.
      rewrite Forall_forall in Hrrhc.
      specialize (Hrrhc _ Hinx).
      eapply forward_graph_and_heap_ric; eassumption.
Qed.

Lemma forward_remset_item_rrhc_range:
  forall from to g h rh rmst item g' h' rh' rmst',
    0 <= Z.of_nat to < Zlength rh ->
    graph_has_gen g to ->
    remset_nodup rmst ->
    remset_item_compatible g from rmst item ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    remset_and_remset_heap_compatible g' from rmst' rh'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst'
         Hrange Hto Hrnd Hitem Hrrhc Hfri.
  Opaque forward_graph_and_heap.
  simpl in Hfri.
  Transparent forward_graph_and_heap.
  destruct (negb (remset_item_in_gen item rmst g from)).
  2: (inversion Hfri; subst; exact Hrrhc).
  destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
    as [newg newh] eqn:Hfgh.
  inversion Hfri; subst; clear Hfri.
  eapply upd_remset_heap_rrhc_range; eassumption.
Qed.

Lemma forward_remset_item_fold_rrhc_range:
  forall from to r g h rh rmst g' h' rh' rmst',
    from <> to ->
    0 <= Z.of_nat to < Zlength rh ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    remset_and_remset_heap_compatible g' from rmst' rh'.
Proof.
  intros from to r. induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' Hneq Hrange Hto Hcc Hrnd Hrgc
           Hrrsc Hrrhc Hfold.
  - simpl in Hfold. inversion Hfold; subst. exact Hrrhc.
  - Opaque forward_remset_item.
    simpl in Hfold.
    Transparent forward_remset_item.
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hitem Hrrsc_tail].
    assert (Hrange2: 0 <= Z.of_nat to < Zlength rh2) by
        (pose proof (fri_rh_Zlength_same from to g h rh rmst item
                       g2 h2 rh2 rmst2 Hfri); lia).
    destruct (forward_remset_item_step_state_with_tail
                from to g h rh rmst item rest g2 h2 rh2 rmst2
                Hneq Hto Hcc Hrnd Hrgc Hitem Hrrsc_tail Hfri)
      as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
    assert (Hrrhc2: remset_and_remset_heap_compatible g2 from rmst2 rh2) by
        exact (forward_remset_item_rrhc_range from to g h rh rmst item
                 g2 h2 rh2 rmst2 Hrange Hto Hrnd Hitem Hrrhc Hfri).
    eapply (IH g2 h2 rh2 rmst2 g' h' rh' rmst'); eauto.
Qed.

Lemma forward_remset_gh_rrhc_range:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    0 <= Z.of_nat to < Zlength rh ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    remset_and_remset_heap_compatible g' from rmst' rh'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst'
         Hneq Hrange Hto Hcc Hrnd Hrgc Hrrhc Hfrg.
  unfold forward_remset_gh in Hfrg.
  rewrite <- nth_remset_space_Znth in Hfrg.
  eapply forward_remset_item_fold_rrhc_range; eauto.
  rewrite nth_remset_space_Znth.
  eapply rrhc_forall_rrsc; exact Hrrhc.
Qed.

Lemma forward_remset_item_fold_remset_graph_compatible:
  forall from to r g h rh rmst g' h' rh' rmst',
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    remset_graph_compatible g' rmst'.
Proof.
  intros from to r. induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' Hneq Hto Hcc Hrnd Hrgc Hrrsc Hfold.
  - simpl in Hfold. inversion Hfold; subst. exact Hrgc.
  - Opaque forward_remset_item.
    simpl in Hfold.
    Transparent forward_remset_item.
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hitem Hrrsc_tail].
    destruct (forward_remset_item_step_state_with_tail
                from to g h rh rmst item rest g2 h2 rh2 rmst2
                Hneq Hto Hcc Hrnd Hrgc Hitem Hrrsc_tail Hfri)
      as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
    eapply (IH g2 h2 rh2 rmst2 g' h' rh' rmst'); eauto.
Qed.

Lemma forward_remset_gh_remset_nodup:
  forall from to g h rh rmst g' h' rh' rmst',
    remset_nodup rmst ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    remset_nodup rmst'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' Hrnd Hfrg.
  unfold forward_remset_gh in Hfrg.
  eapply fri_remset_nodup_fold; eassumption.
Qed.

Lemma forward_remset_gh_remset_graph_compatible_pres:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    remset_graph_compatible g' rmst'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst'
         Hneq Hto Hcc Hrnd Hrgc Hrrhc Hfrg.
  unfold forward_remset_gh in Hfrg.
  rewrite <- nth_remset_space_Znth in Hfrg.
  eapply forward_remset_item_fold_remset_graph_compatible; eauto.
  rewrite nth_remset_space_Znth.
  eapply rrhc_forall_rrsc; exact Hrrhc.
Qed.

Lemma do_generation_relation_remset_graph_compatible_simple:
  forall from to roots roots' g h rh rmst rg rhh rh' rmst' g' h',
    graph_has_gen rg to ->
    do_generation_relation from to roots roots' g h rh rmst
      rg rhh rh' rmst' g' h' ->
    (forall v addr, In (RemSetVertex v addr) rmst' -> vgeneration v <> from) ->
    remset_graph_compatible rg rmst' ->
    remset_graph_compatible g' rmst'.
Proof.
  intros from to roots roots' g h rh rmst rg rhh rh' rmst' g' h'
         Hto Hrel Hnofrom Hrgc.
  unfold remset_graph_compatible in *.
  rewrite Forall_forall in Hrgc |- *.
  intros re Hin. specialize (Hrgc _ Hin).
  destruct re as [p addr | v addr]; simpl in *; auto.
  eapply do_generation_relation_graph_has_v_preserve; eauto.
Qed.

Lemma do_generation_relation_reset_remset_graph_state:
  forall from roots roots' g h rh rmst rg rhh rh' rmst' g' h',
    graph_has_gen g (S from) ->
    graph_unmarked g ->
    copy_compatible g ->
    remset_heap_covers_graph g rh ->
    remset_graph_state g from rmst rh ->
    do_generation_relation from (S from) roots roots' g h rh rmst
      rg rhh rh' rmst' g' h' ->
    remset_graph_state g' (S from) rmst' (reset_nth_remset_heap from rh').
Proof.
  intros from roots roots' g h rh rmst rg rhh rh' rmst' g' h'
         Hto Hun Hcc Hcover Hstate Hrel.
  pose proof Hrel as Hrel0.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] Hremgen].
  destruct Hrel as [[g1 [g2 [Hfrg _]]] _].
  assert (Hrange: 0 <= Z.of_nat (S from) < Zlength rh) by
      (eapply remset_heap_covers_graph_range; eauto).
  assert (Hct: copied_to_compatible from (S from) g) by
      (apply graph_unmarked_copied_to_compatible; exact Hun).
  assert (Hrnd_rem: remset_nodup rmst') by
      (eapply forward_remset_gh_remset_nodup; eauto).
  assert (Hrgc_rem: remset_graph_compatible rg rmst') by
      (exact (forward_remset_gh_remset_graph_compatible_pres
                from (S from) g h rh rmst rg rhh rh' rmst'
                ltac:(lia) Hto Hcc Hrnd Hrgc Hrrhc Hfrg)).
  assert (Hrrhc_rem: remset_and_remset_heap_compatible rg from rmst' rh') by
      (exact (forward_remset_gh_rrhc_range
                from (S from) g h rh rmst rg rhh rh' rmst'
                ltac:(lia) Hrange Hto Hcc Hrnd Hrgc Hrrhc Hfrg)).
  assert (Hremgen_reset:
            remset_generation_compatible (S from) rmst'
              (reset_nth_remset_heap from rh')) by
      (exact (do_generation_relation_reset_remset_generation_compatible
                from roots roots' g h rh rmst rg rhh rh' rmst' g' h'
                Hto Hcc Hrnd Hrgc Hrrhc Hct Hremgen Hrange Hrel0)).
  assert (Hnofrom: forall v addr,
             In (RemSetVertex v addr) rmst' -> vgeneration v <> from) by
      (exact (do_generation_relation_no_from_vertices
                from roots roots' g h rh rmst rg rhh rh' rmst' g' h'
                Hto Hcc Hrnd Hrgc Hrrhc Hct Hremgen Hrel0)).
  assert (Hto_rg: graph_has_gen rg (S from)) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from (S from) g h rh rmst rg rhh rh' rmst'
                     Hto Hfrg (S from));
       exact Hto).
  split.
  - split; [exact Hrnd_rem | split].
    + eapply do_generation_relation_remset_graph_compatible_simple; eauto.
    + eapply do_generation_relation_remset_and_remset_heap_compatible_reset; eauto.
  - exact Hremgen_reset.
Qed.

Lemma new_gen_heap_iso: forall g1 h1 g2 h2 roots gen,
    new_gen_heap_relation gen g1 h1 g2 h2 -> gc_graph_iso g1 roots g2 roots.
Proof.
  intros. eapply ngr_iso.
  eapply new_gen_heap_new_gen_relation; eauto.
Qed.

Lemma do_generation_relation_sound:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h',
    sound_gc_graph g -> graph_has_gen g to ->
    do_generation_relation from to roots roots' g h rh rmst
      g_rem h_rem rh' rmst' g' h' ->
    sound_gc_graph g'.
Proof.
  intros. eapply (do_generation_relation_P_holds sound_gc_graph); eauto.
  - intros. eapply fr_O_sound; eauto.
  - intros. apply reset_sound. assumption.
  - intros. eapply forward_remset_gh_sound; eauto.
Qed.

Lemma forward_remset_item_copied_vertex_prop:
  forall from to g h rh rmst item g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    no_dangling_dst g ->
    remset_graph_compatible g rmst ->
    remset_item_compatible g from rmst item ->
    copied_vertex_prop g from to ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    copied_vertex_prop g' from to.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst'
         Hneq Hsound Hto Hndd Hrgc Hric Hcvp Hfri.
  destruct (remset_item_in_gen item rmst g from) eqn:Hin_gen.
  - unfold forward_remset_item in Hfri.
    rewrite Hin_gen in Hfri. simpl in Hfri. inversion Hfri; subst.
    exact Hcvp.
  - eapply fr_O_copied_vertex_prop; eauto.
    + eapply remset_item2forward_p_compatible'; eauto.
    + eapply forward_remset_item_forward_p_relation; eauto.
Qed.

Lemma forward_remset_item_fold_copied_vertex_prop:
  forall from to r g h rh rmst g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    copied_vertex_prop g from to ->
    (g', h', rh', rmst') =
      fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    copied_vertex_prop g' from to.
Proof.
  intros from to r.
  induction r as [|item rest IH];
    intros g h rh rmst g' h' rh' rmst' Hneq Hsound Hto Hcc Hndd
           Hrnd Hrgc Hrrsc Hcvp Hfold.
  - simpl in Hfold. inversion Hfold; subst. exact Hcvp.
  - change (fold_left (forward_remset_item from to) (item :: rest) (g, h, rh, rmst))
      with (fold_left (forward_remset_item from to) rest
              (forward_remset_item from to (g, h, rh, rmst) item)) in Hfold.
    destruct (forward_remset_item from to (g, h, rh, rmst) item)
      as [[[g2 h2] rh2] rmst2] eqn:Hfri.
    symmetry in Hfri.
    hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc.
    destruct Hrrsc as [Hric Hrrsc_tail].
    assert (Hsound2: sound_gc_graph g2) by
        (eapply forward_remset_item_P_holds;
         [intros; eapply fr_O_sound; eauto | exact Hsound | exact Hto | exact Hfri]).
    destruct (forward_remset_item_step_state_with_tail
                from to g h rh rmst item rest g2 h2 rh2 rmst2
                Hneq Hto Hcc Hrnd Hrgc Hric Hrrsc_tail Hfri)
      as [Hto2 [Hcc2 [Hrnd2 [Hrgc2 Hrrsc2]]]].
    assert (Hndd2: no_dangling_dst g2) by
        exact (fri_no_dangling_dst from to g h rh rmst item g2 h2 rh2 rmst2
                 Hto Hcc Hrgc Hric Hndd Hfri).
    assert (Hcvp2: copied_vertex_prop g2 from to) by
        exact (forward_remset_item_copied_vertex_prop
                 from to g h rh rmst item g2 h2 rh2 rmst2
                 Hneq Hsound Hto Hndd Hrgc Hric Hcvp Hfri).
    eapply (IH g2 h2 rh2 rmst2 g' h' rh' rmst'); eauto.
Qed.

Lemma forward_remset_gh_copied_vertex_prop:
  forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    copied_vertex_prop g from to ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    copied_vertex_prop g' from to.
Proof.
  intros from to g h rh rmst g' h' rh' rmst'
         Hneq Hsound Hto Hcc Hndd Hrnd Hrgc Hrrhc Hcvp Hfrg.
  unfold forward_remset_gh in Hfrg.
  rewrite <- nth_remset_space_Znth in Hfrg.
  eapply forward_remset_item_fold_copied_vertex_prop; eauto.
  rewrite nth_remset_space_Znth.
  eapply rrhc_forall_rrsc; exact Hrrhc.
Qed.

Lemma forward_remset_gh_basic_facts:
  forall from to roots g h rh rmst g_rem h_rem rh' rmst',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    copy_compatible g ->
    gen_unmarked g to ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    sound_gc_graph g_rem /\
    graph_has_gen g_rem to /\
    copy_compatible g_rem /\
    no_dangling_dst g_rem /\
    roots_graph_compatible roots g_rem /\
    gen_unmarked g_rem to.
Proof.
  intros from to roots g h rh rmst g_rem h_rem rh' rmst'
         Hneq Hsound Hto Hcc Hun_to Hroots Hndd Hstate Hfrg.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  split.
  - eapply forward_remset_gh_sound; eauto.
  - split.
    + rewrite <- (forward_remset_gh_graph_has_gen
                    from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to).
      exact Hto.
    + split.
      * exact (forward_remset_gh_copy_compatible
                 from to g h rh rmst g_rem h_rem rh' rmst'
                 Hneq Hto Hcc Hfrg).
      * split.
        -- unfold forward_remset_gh in Hfrg.
           eapply (fri_no_dangling_dst_fold
                     from to g h rh rmst (Znth (Z.of_nat from) rh)
                     g_rem h_rem rh' rmst'); eauto.
           eapply rrhc_forall_rrsc; exact Hrrhc.
        -- split.
           ++ exact (forward_remset_gh_roots_graph_compatible
                       from to g h rh rmst g_rem h_rem rh' rmst' roots
                       Hto Hfrg Hroots).
           ++ exact (forward_remset_gh_gen_unmarked
                       from to g h rh rmst g_rem h_rem rh' rmst' to
                       Hto Hneq Hfrg Hun_to).
Qed.

Lemma frr_basic_facts:
  forall from to roots roots' g_rem g1,
    from <> to ->
    graph_has_gen g_rem to ->
    copy_compatible g_rem ->
    no_dangling_dst g_rem ->
    roots_graph_compatible roots g_rem ->
    gen_unmarked g_rem to ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    graph_has_gen g1 to /\
    copy_compatible g1 /\
    no_dangling_dst g1 /\
    roots_graph_compatible roots' g1 /\
    gen_unmarked g1 to.
Proof.
  intros from to roots roots' g_rem g1 Hneq Hto Hcc Hndd Hroots Hun Hfrr.
  split.
  - rewrite <- (frr_graph_has_gen from to roots g_rem roots' g1 Hto Hfrr to).
    exact Hto.
  - split.
    + exact (frr_copy_compatible from to roots g_rem roots' g1
               Hneq Hto Hfrr Hcc).
    + split.
      * exact (frr_no_dangling_dst from to roots g_rem roots' g1
                 Hto Hcc Hneq Hroots Hfrr Hndd).
      * split.
        -- exact (frr_roots_graph_compatible from to roots g_rem roots' g1
                    Hneq Hto Hcc Hroots Hfrr).
        -- exact (frr_gen_unmarked from to roots g_rem roots' g1
                    Hto Hfrr to (not_eq_sym Hneq) Hun).
Qed.

Lemma forward_remset_gh_frr_no_edge2gen_before_scan:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    (gen_v_num g to <= gen_v_num g1 to)%nat /\
    (forall (vidx eidx: nat),
        (vidx < gen_v_num g to)%nat ->
        graph_has_e g1 (to, vidx, eidx) ->
        vgeneration (dst g1 (to, vidx, eidx)) <> from) /\
    (forall another, another <> from -> another <> to ->
       gen2gen_no_edge g1 another from).
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate Hfrg Hfrr.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  destruct (forward_remset_gh_frr_remset_semi_iso
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1
              Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec
              Hrnd Hrgc Hrrhc Hfrg Hfrr)
    as [l [Hsemi [_ Hclosed]]].
  assert (Hsound_rem: sound_gc_graph g_rem) by
      (eapply forward_remset_gh_sound; eauto).
  assert (Hto_rem: graph_has_gen g_rem to) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to);
       exact Hto).
  assert (Hsound1: sound_gc_graph g1) by
      (exact (frr_sound g_rem g1 from to roots roots'
                Hsound_rem Hto_rem Hfrr)).
  assert (Hbound: (gen_v_num g to <= gen_v_num g1 to)%nat). {
    pose proof (forward_remset_gh_gen_v_num_to
                  from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg)
      as Hbound_rem.
    pose proof (frr_gen_v_num_to from to roots g_rem roots' g1
                  Hto_rem Hfrr) as Hbound_frr.
    lia.
  }
  split; [exact Hbound |].
  split.
  - intros vidx eidx Hvidx He.
    assert (Hsrc_valid_base: vvalid g (to, vidx)). {
      destruct Hsound as [Hvv _].
      apply (proj2 (Hvv _)).
      split; simpl.
      + exact Hto.
      + unfold gen_has_index, gen_v_num in *. simpl in *. exact Hvidx.
    }
    exact (remset_semi_iso_current_old_nonfrom_edge_dst_not_from
             g g1 from to l (to, vidx, eidx)
             Hneq Hsound Hsound1 Hndd Hsemi Hclosed He Hsrc_valid_base
             ltac:(simpl; exact (not_eq_sym Hneq))).
  - intros another Hanother Hnot_to.
    unfold gen2gen_no_edge.
    intros vidx eidx He.
    exact (remset_semi_iso_current_non_to_edge_dst_not_from
             g g1 from to l (another, vidx, eidx)
             Hneq Hsound Hsound1 Hndd Hsemi Hclosed He
             ltac:(simpl; exact Hanother)
             ltac:(simpl; exact Hnot_to)).
Qed.

Lemma forward_remset_gh_frr_dsr_no_edge2gen:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (gen_v_num g to) g1 g_scan ->
    no_edge2gen g_scan from.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1 g_scan
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate Hfrg Hfrr Hscan.
  pose proof Hstate as Hstate0.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hun_to: gen_unmarked g to) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  destruct (forward_remset_gh_basic_facts
              from to roots g h rh rmst g_rem h_rem rh' rmst'
              Hneq Hsound Hto Hcc Hun_to Hroots Hndd Hstate0 Hfrg)
    as [Hsound_rem [Hto_rem [Hcc_rem [Hndd_rem
        [Hroots_rem Hun_rem_to]]]]].
  destruct (frr_basic_facts
              from to roots roots' g_rem g1
              Hneq Hto_rem Hcc_rem Hndd_rem Hroots_rem Hun_rem_to Hfrr)
    as [Hto1 [Hcc1 [Hndd1 [Hroots1 Hun1_to]]]].
  destruct (forward_remset_gh_frr_no_edge2gen_before_scan
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g1
              Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate0 Hfrg Hfrr)
    as [Hbound [Hprefix Hother]].
  eapply do_scan_prefix_no_edge2gen; eauto.
Qed.

Lemma do_generation_relation_roots_graph_compatible_simple:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h',
    from <> to -> graph_has_gen g to -> copy_compatible g ->
    roots_graph_compatible roots g ->
    do_generation_relation from to roots roots' g h rh rmst
      g_rem h_rem rh' rmst' g' h' ->
    roots_graph_compatible roots' g'.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h'
         Hneq Hto Hcc Hrgc Hrel.
  destruct Hrel as [[g1 [g2 [Hfrg [Hfrr [Hscan Hreset]]]]] _].
  subst g'.
  assert (Hrgc_rem: roots_graph_compatible roots g_rem) by
      exact (forward_remset_gh_roots_graph_compatible
               from to g h rh rmst g_rem h_rem rh' rmst' roots
               Hto Hfrg Hrgc).
  assert (Hto_rem: graph_has_gen g_rem to) by
      (rewrite <- (forward_remset_gh_graph_has_gen
                     from to g h rh rmst g_rem h_rem rh' rmst' Hto Hfrg to);
       exact Hto).
  assert (Hcc_rem: copy_compatible g_rem) by
      exact (forward_remset_gh_copy_compatible
               from to g h rh rmst g_rem h_rem rh' rmst'
               Hneq Hto Hcc Hfrg).
  assert (Hto1: graph_has_gen g1 to) by
      (rewrite <- (frr_graph_has_gen from to roots g_rem roots' g1
                     Hto_rem Hfrr to); exact Hto_rem).
  assert (Hrgc1: roots_graph_compatible roots' g1) by
      exact (frr_roots_graph_compatible from to roots g_rem roots' g1
               Hneq Hto_rem Hcc_rem Hrgc_rem Hfrr).
  apply rgc_reset.
  - destruct Hscan as [n [Hscan _]].
    eapply (svwl_roots_graph_compatible
              from to roots' (seq (number_of_vertices (nth_gen g to)) n) g1 g2);
      eauto.
  - exact (frr_not_pointing from to roots g_rem roots' g1
             Hcc_rem Hrgc_rem Hneq Hto_rem Hfrr).
Qed.

Definition remset_ready_marked_state
    (from to: nat) (roots: roots_t) (g: LGraph)
    (rh: remset_heap) (rmst: remset) (g_rem: LGraph)
    (l: list (VType * VType)) (marked: VType -> Prop): Prop :=
  gc_graph_remset_semi_iso g g_rem from to l /\
  no_unmarked_old_nonfrom_dst g g_rem from /\
  (forall v,
      In v (map fst l) ->
      In (ExteriorVertex v) (effective_remset_roots g rmst rh from)) /\
  roots_graph_compatible (remset_ready_roots l) g_rem /\
  roots_have_no_gen (remset_ready_roots l) from /\
  backward_edge_prop g_rem (remset_ready_roots l) from to /\
  forall v,
    reachable_or_marked from g_rem (remset_ready_roots l ++ roots) v <->
    marked v.

Definition remset_ready_marked_bridge
    (from to: nat) (roots: roots_t) (g: LGraph)
    (rh: remset_heap) (rmst: remset) (g_rem g_scan: LGraph): Prop :=
  exists l,
    remset_ready_marked_state from to roots g rh rmst g_rem l
      (fun v => marked_in_gen g_rem g_scan from v).

Definition remset_ready_marked_base_bridge
    (from to: nat) (roots: roots_t) (g: LGraph)
    (rh: remset_heap) (rmst: remset) (g_rem g_scan: LGraph): Prop :=
  exists l,
    remset_ready_marked_state from to roots g rh rmst g_rem l
      (fun v => marked_in_gen g g_scan from v).

Lemma remset_ready_marked_bridge_base:
  forall from to roots g rh rmst g_rem g_scan,
    from <> to ->
    sound_gc_graph g ->
    remset_ready_marked_bridge from to roots g rh rmst g_rem g_scan ->
    remset_ready_marked_base_bridge from to roots g rh rmst g_rem g_scan.
Proof.
  intros from to roots g rh rmst g_rem g_scan Hneq Hsound [l Hready].
  exists l.
  unfold remset_ready_marked_state in Hready |- *.
  destruct Hready as [Hsemi [Hclosed [Hprov [Hready_rgc
                       [Hready_no_gen [Hbep Hmarked]]]]]].
  split; [exact Hsemi |].
  split; [exact Hclosed |].
  split; [exact Hprov |].
  split; [exact Hready_rgc |].
  split; [exact Hready_no_gen |].
  split; [exact Hbep |].
  intros v.
  rewrite Hmarked.
  unfold marked_in_gen.
  split.
  - intros [Hmark [Hvalid Hgen]].
    split; [exact Hmark |].
    split; [|exact Hgen].
    apply (proj1 (remset_semi_iso_from_valid_iff
                    g g_rem from to l v Hneq Hsound Hsemi Hgen)).
    exact Hvalid.
  - intros [Hmark [Hvalid Hgen]].
    split; [exact Hmark |].
    split; [|exact Hgen].
    apply (proj2 (remset_semi_iso_from_valid_iff
                    g g_rem from to l v Hneq Hsound Hsemi Hgen)).
    exact Hvalid.
Qed.

Lemma forward_remset_gh_frr_dsr_mapped_ready_marked:
  forall from to roots roots' start g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    copied_vertex_prop g_rem from to ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to start g1 g_scan ->
    no_edge2gen g_scan from ->
    remset_ready_marked_bridge from to roots g rh rmst g_rem g_scan.
Proof.
  intros from to roots roots' start g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate
         Hfrg Hcvp_rem Hfrr Hscan Hnoedge.
  pose proof Hstate as Hstate0.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] Hremgen].
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hun_from: gen_unmarked g from) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  assert (Hun_to: gen_unmarked g to) by
      (rewrite graph_gen_unmarked_iff in Hun; apply Hun).
  assert (Hct: copied_to_compatible from to g) by
      (apply graph_unmarked_copied_to_compatible; exact Hun).
  destruct (forward_remset_gh_backward_edge_prop_mapped_roots_effective
              from to g h rh rmst g_rem h_rem rh' rmst'
              Hneq Hsound Hto Hcc Hct Hrnd Hrgc Hrrhc Hndd Hun_from
              Hfirst Hunrec Hfrg)
    as [l [Hsemi [Hclosed [Hprov [Hready_rgc [Hready_no_gen Hbep]]]]]].
  destruct (forward_remset_gh_basic_facts
              from to roots g h rh rmst g_rem h_rem rh' rmst'
              Hneq Hsound Hto Hcc Hun_to Hroots Hndd Hstate0 Hfrg)
    as [Hsound_rem [Hto_rem [Hcc_rem [Hndd_rem
        [Hroots_rem Hun_rem_to]]]]].
  exists l.
  unfold remset_ready_marked_state.
  split; [exact Hsemi |].
  split; [exact Hclosed |].
  split; [exact Hprov |].
  split; [exact Hready_rgc |].
  split; [exact Hready_no_gen |].
  split; [exact Hbep |].
  intros v.
  eapply (frr_dsr_reachable_or_marked_iff_marked_ready_from_backward_start
            from to (remset_ready_roots l)
            roots roots' start g_rem g1 g_scan); eauto.
  rewrite roots_graph_compatible_app.
  split; assumption.
  eapply backward_edge_prop_incl; [|exact Hbep].
  intros x Hin. apply in_or_app. left. exact Hin.
Qed.

Lemma forward_remset_gh_frr_dsr_mapped_ready_marked_state:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (gen_v_num g to) g1 g_scan ->
    remset_ready_marked_bridge from to roots g rh rmst g_rem g_scan.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate
         Hfrg Hfrr Hscan.
  pose proof Hstate as Hstate0.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  assert (Hcc: copy_compatible g) by
      (apply graph_unmarked_copy_compatible; exact Hun).
  assert (Hcvp: copied_vertex_prop g from to) by
      (apply graph_unmarked_copied_vertex_prop; exact Hun).
  assert (Hcvp_rem: copied_vertex_prop g_rem from to) by
      exact (forward_remset_gh_copied_vertex_prop
               from to g h rh rmst g_rem h_rem rh' rmst'
               Hneq Hsound Hto Hcc Hndd Hrnd Hrgc Hrrhc Hcvp Hfrg).
  assert (Hnoedge: no_edge2gen g_scan from) by
      (eapply forward_remset_gh_frr_dsr_no_edge2gen; eauto).
  eapply (forward_remset_gh_frr_dsr_mapped_ready_marked
            from to roots roots' (gen_v_num g to)
            g h rh rmst g_rem h_rem rh' rmst' g1 g_scan);
    eauto.
Qed.

Lemma forward_remset_gh_frr_dsr_mapped_ready_marked_base_state:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (gen_v_num g to) g1 g_scan ->
    remset_ready_marked_base_bridge from to roots g rh rmst g_rem g_scan.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate
         Hfrg Hfrr Hscan.
  eapply remset_ready_marked_bridge_base; eauto.
  eapply (forward_remset_gh_frr_dsr_mapped_ready_marked_state
            from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
            g1 g_scan); eauto.
Qed.

Lemma do_generation_relation_no_dangling_dst_noedge_state:
  forall g h rh rmst g_rem h_rem rh' rmst' g' h' roots roots' i,
    sound_gc_graph g ->
    graph_has_gen g (S i) ->
    graph_unmarked g ->
    copy_compatible g ->
    no_dangling_dst g ->
    roots_graph_compatible roots g ->
    firstn_gen_clear g i ->
    no_unrecorded_backward_edge_from i g rh ->
    remset_graph_state g i rmst rh ->
    do_generation_relation i (S i) roots roots' g h rh rmst
      g_rem h_rem rh' rmst' g' h' ->
    no_dangling_dst g'.
Proof.
  intros g h rh rmst g_rem h_rem rh' rmst' g' h' roots roots' i
         Hsound Hto Hungraph Hcc Hndd Hrgc Hfirst Hunrec Hstate Hrel.
  pose proof Hstate as Hstate0.
  destruct Hstate as [[Hrnd [Hremgc Hrrhc]] Hrgenc].
  destruct Hrel as [[g1 [g2 [Hfrg [Hfrr [Hscan Hreset]]]]] _].
  assert (Hneq: i <> S i) by lia.
  assert (Hun_to: gen_unmarked g (S i)) by
      (rewrite graph_gen_unmarked_iff in Hungraph; apply Hungraph).
  destruct (forward_remset_gh_basic_facts
              i (S i) roots g h rh rmst g_rem h_rem rh' rmst'
              Hneq Hsound Hto Hcc Hun_to Hrgc Hndd Hstate0 Hfrg)
    as [_ [Hto_rem [Hcc_rem [Hndd_rem [Hrgc_rem Hun_rem]]]]].
  destruct (frr_basic_facts
              i (S i) roots roots' g_rem g1
              Hneq Hto_rem Hcc_rem Hndd_rem Hrgc_rem Hun_rem Hfrr)
    as [Hto1 [Hcc1 [Hndd1 [Hrgc1 Hun1]]]].
  assert (Hndd2: no_dangling_dst g2). {
    destruct Hscan as [n [Hscan _]].
    eapply (svwl_no_dangling_dst i (S i)
              (seq (gen_v_num g (S i)) n) g1 g2); eauto.
  }
  assert (Hnoedge2: no_edge2gen g2 i). {
    change (number_of_vertices (nth_gen g (S i))) with
      (gen_v_num g (S i)) in Hscan.
    eapply (forward_remset_gh_frr_dsr_no_edge2gen
              i (S i) roots roots' g h rh rmst
              g_rem h_rem rh' rmst' g1 g2); eauto.
  }
  subst g'. eapply no_dangling_dst_reset; eauto.
Qed.

Lemma do_generation_relation_no_unrecorded_backward_edge_reset_state:
  forall from roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h',
    graph_has_gen g (S from) ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    remset_heap_covers_graph g rh ->
    firstn_gen_clear g' (S from) ->
    no_dangling_dst g' ->
    do_generation_relation from (S from) roots roots' g h rh rmst
      g_rem h_rem rh' rmst' g' h' ->
    no_unrecorded_backward_edge_from (S from) g' (reset_nth_remset_heap from rh').
Proof.
  intros from roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h'
         Hto Hun Hroots Hndd Hfirst Hunrec Hstate Hcover Hfirst' Hndd' Hrel.
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  eapply do_generation_relation_no_unrecorded_backward_edge_reset_core; eauto.
  - apply graph_unmarked_copy_compatible. exact Hun.
  - eapply remset_heap_covers_graph_range; eauto.
Qed.

Lemma vvalid_reachable_sub_cons:
  forall {roots: roots_t} {g : LGraph} {x: VType} (v : VType),
    vvalid (reachable_sub_labeledgraph g (filter_proj exterior_proj_vertex roots)) x ->
    vvalid (reachable_sub_labeledgraph g (v :: filter_proj exterior_proj_vertex roots)) x.
Proof.
  intros. simpl in *. unfold predicate_vvalid in *. destruct H.
  rewrite !reachable_through_set_eq. split; [auto | right]. assumption.
Qed.

Lemma pregraph_iso_cons_vvalid:
  forall {roots1 roots2 : roots_t} {g1 g2 : LGraph} {v : VType}
    {vmap12 vmap21 : VType -> VType} {emap12 emap21 : EType -> EType},
    pregraph_isomorphism_explicit
      (reachable_sub_labeledgraph g1 (v :: filter_proj exterior_proj_vertex roots1))
      (reachable_sub_labeledgraph g2 (vmap12 v :: filter_proj exterior_proj_vertex roots2))
      vmap12 vmap21 emap12 emap21 ->
    roots2 = map (exterior_map vmap12) roots1 ->
    forall v0 : VType,
      vvalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) v0 ->
      vvalid (reachable_sub_labeledgraph g2 (filter_proj exterior_proj_vertex roots2))
        (vmap12 v0).
Proof.
  intros roots1 roots2 g1 g2 v vmap12 vmap21 emap12 emap21 lp_pregraph_iso Hrest.
  intros v0 Hv. pose proof (vvalid_reachable_sub_cons v Hv) as Hr1.
  destruct lp_pregraph_iso. simpl in *. unfold predicate_vvalid, predicate_evalid in *.
  hnf in *. destruct Hv as [Hv1 Hr].
  destruct (vvalid_bij _ Hr1) as [Hv2 Hr2]. split; auto.
  destruct Hr2 as [s [Hin Hr2]]. simpl in Hin. destruct Hin as [Hin | Hin].
  2: (exists s; split; auto). subst s. destruct Hr as [s [Hin Hr]].
  destruct Hr as [p Hr]. destruct p as [v' p]. destruct Hr as [[Hh Hf] [Hvp _]].
  simpl in Hh. subst v'. exists (vmap12 s). split.
  1: subst roots2; rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hin |- * ;
  rewrite in_map_iff; exists (ExteriorVertex s); split; auto. clear Hr2. destruct Hr1 as [_ Hr1].
  generalize dependent v0. induction p using rev_ind; intros.
  - simpl in Hf. subst v0. apply reachable_refl. assumption.
  - assert (valid_path g1 (s, p)) as Hvp1. {
      rewrite valid_path_app in Hvp. destruct Hvp; assumption. }
    pose proof (pfoot_split _ _ _ _ _ Hvp) as Hfs.
    assert (reachable_through_set g1 (v :: filter_proj exterior_proj_vertex roots1) (src g1 x))
      as Hr1s. {
      exists s. split. 1: simpl; right; assumption. exists (s, p). split; split; simpl; auto.
      constructor; auto. simpl. rewrite Forall_forall. intros; auto. }
    assert (vvalid g1 (src g1 x)) as Hv1s. {
      apply valid_path_valid with (s, p); auto. apply pfoot_in. assumption. }
    destruct (vvalid_bij _ (conj Hv1s Hr1s)) as [Hv2s _].
    specialize (IHp Hvp1 _ Hv1s Hfs Hr1s Hv2s). eapply reachable_edge; eauto.
    do 2 (split; auto). rewrite pfoot_last in Hf. subst v0.
    assert (evalid g1 x) as Hev1. {
      eapply valid_path_evalid. apply Hvp. rewrite in_app_iff. right. left. reflexivity. }
    pose proof (conj Hev1 (conj Hr1s Hr1)) as Hc. destruct (evalid_bij _ Hc) as [Hev2 _].
    specialize (src_bij _ Hc). specialize (dst_bij _ Hc).
    econstructor; eauto.
Qed.

Lemma evalid_reachable_sub_cons:
  forall {roots: roots_t} {g : LGraph} {e: EType} (v : VType),
    evalid (reachable_sub_labeledgraph g (filter_proj exterior_proj_vertex roots)) e ->
    evalid (reachable_sub_labeledgraph g (v :: filter_proj exterior_proj_vertex roots)) e.
Proof.
  intros. simpl in *. unfold predicate_evalid in *.
  rewrite !reachable_through_set_eq. split; [auto | split; right]; intuition.
Qed.

Lemma pregraph_iso_cons_evalid:
  forall (roots1 roots2 : roots_t) (g1 g2 : LGraph) (v : VType)
    (vmap12 vmap21 : VType -> VType) (emap12 emap21 : EType -> EType),
    pregraph_isomorphism_explicit
      (reachable_sub_labeledgraph g1 (v :: filter_proj exterior_proj_vertex roots1))
      (reachable_sub_labeledgraph g2 (vmap12 v :: filter_proj exterior_proj_vertex roots2))
      vmap12 vmap21 emap12 emap21 ->
    roots2 = map (exterior_map vmap12) roots1 ->
    forall e : EType,
      evalid (reachable_sub_labeledgraph g1 (filter_proj exterior_proj_vertex roots1)) e ->
      evalid (reachable_sub_labeledgraph g2 (filter_proj exterior_proj_vertex roots2))
        (emap12 e).
Proof.
  intros roots1 roots2 g1 g2 v vmap12 vmap21 emap12 emap21 lp_pregraph_iso Hrest.
  intros e He1v. pose proof (evalid_reachable_sub_cons v He1v) as Hersd.
  hnf in *. destruct He1v as [He1v [Hr1s Hr1d]].
  rewrite reachable_through_set_iff in Hr1s, Hr1d |- * . rewrite reachable_through_set_iff.
  pose proof (pregraph_iso_cons_vvalid lp_pregraph_iso Hrest _ Hr1s) as Hv2s.
  pose proof (pregraph_iso_cons_vvalid lp_pregraph_iso Hrest _ Hr1d) as Hv2d.
  destruct lp_pregraph_iso. simpl in *. unfold predicate_vvalid, predicate_evalid in *.
  destruct (evalid_bij _ Hersd) as [He2v _].
  specialize (src_bij _ Hersd). specialize (dst_bij _ Hersd).
  rewrite <- src_bij, <- dst_bij. split; [|split]; auto.
Qed.

Lemma gc_graph_iso_cons_roots_inv: forall roots1 roots2 g1 g2 p1 p2,
    gc_graph_iso g1 (p1 :: roots1) g2 (p2 :: roots2) ->
    gc_graph_iso g1 roots1 g2 roots2.
Proof.
  intros. destruct H as [vmap12 [vmap21 [emap12 [emap21 [Hroots Hiso]]]]].
  simpl in Hroots. inversion Hroots as [[Hhead Hrest]]. clear Hroots.
  exists vmap12, vmap21, emap12, emap21. split. 1: reflexivity. simpl in Hiso.
  destruct p1; simpl in Hhead; subst p2. 1, 2: subst; assumption. rewrite <- Hrest.
  destruct Hiso. split.
  - clear - Hrest lp_pregraph_iso.
    assert (v = vmap21 (vmap12 v)) as Hv. {
      destruct lp_pregraph_iso. rewrite surjective; auto. apply bijective_sym. assumption. }
    assert (roots1 = map (exterior_map vmap21) roots2) as Hrest'. {
      eapply map_exterior_map_bijective; eauto. destruct lp_pregraph_iso. assumption. }
    rewrite !filter_proj_cons in lp_pregraph_iso. simpl exterior_proj_vertex in lp_pregraph_iso.
    cbv iota in lp_pregraph_iso. split.
    + destruct lp_pregraph_iso. assumption.
    + destruct lp_pregraph_iso. assumption.
    + eapply pregraph_iso_cons_vvalid; eauto.
    + remember (vmap12 v) as v'. clear Heqv'. subst v.
      apply pregraph_iso_exp_sym in lp_pregraph_iso.
      eapply pregraph_iso_cons_vvalid; eauto.
    + eapply pregraph_iso_cons_evalid; eauto.
    + remember (vmap12 v) as v'. clear Heqv'. subst v.
      apply pregraph_iso_exp_sym in lp_pregraph_iso.
      eapply pregraph_iso_cons_evalid; eauto.
    + intros e Hev. pose proof (evalid_reachable_sub_cons v Hev) as Hersd.
      destruct lp_pregraph_iso. simpl in *. unfold predicate_evalid in *.
      apply src_bij; assumption.
    + intros e Hev. pose proof (evalid_reachable_sub_cons v Hev) as Hersd.
      destruct lp_pregraph_iso. simpl in *. unfold predicate_evalid in *.
      apply dst_bij; assumption.
  - intros v0 Hv. apply vlabel_iso. apply vvalid_reachable_sub_cons. assumption.
  - intros e He. apply elabel_iso. apply evalid_reachable_sub_cons. assumption.
Qed.

Lemma gc_graph_iso_app_roots_inv:
  forall prefix1 prefix2 roots1 roots2 g1 g2,
    length prefix1 = length prefix2 ->
    gc_graph_iso g1 (prefix1 ++ roots1) g2 (prefix2 ++ roots2) ->
    gc_graph_iso g1 roots1 g2 roots2.
Proof.
  induction prefix1 as [|p1 prefix1 IH]; intros prefix2 roots1 roots2 g1 g2 Hlen Hiso.
  - destruct prefix2; [exact Hiso | discriminate].
  - destruct prefix2 as [|p2 prefix2]; [discriminate |].
    simpl in Hlen. apply IH with (prefix2 := prefix2).
    + lia.
    + simpl in Hiso. eapply gc_graph_iso_cons_roots_inv. exact Hiso.
Qed.

Lemma forward_remset_gh_frr_dsr_roots_iso_from_augmented:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_heap_compatible g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g_scan ->
    reachable_iff_marked
      g g_scan (remset_augmented_roots g rmst rh from roots) from ->
    no_edge2gen g_scan from ->
    gc_graph_iso g roots (reset_graph from g_scan) roots'.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst
         Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr Hscan Hreach Hnoedge.
  destruct (forward_remset_gh_frr_dsr_augmented_iso
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
              g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst
              Hunrec Hrnd Hrgc Hrrhc Hfrg Hfrr Hscan Hreach Hnoedge)
    as [l [Hiso Hroots_map]].
  subst roots'.
  unfold remset_augmented_roots in Hiso.
  rewrite roots_map_app in Hiso.
  eapply (gc_graph_iso_app_roots_inv
            (effective_remset_roots g rmst rh from)
            (roots_map l (effective_remset_roots g rmst rh from))).
  - unfold roots_map. rewrite length_map. reflexivity.
  - exact Hiso.
Qed.

Lemma forward_remset_gh_frr_dsr_roots_iso_from_rom_bridge_state:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g_scan ->
    (forall l,
        gc_graph_remset_semi_iso g g_rem from to l ->
        no_unmarked_old_nonfrom_dst g g_rem from ->
        (forall x,
            In x (map fst l) ->
            In (ExteriorVertex x) (effective_remset_roots g rmst rh from)) ->
        let ready := remset_ready_roots l in
        forall v,
          roots_reachable_in_gen
            g (remset_augmented_roots g rmst rh from roots) from v <->
          reachable_or_marked from g_rem (ready ++ roots) v) ->
    gc_graph_iso g roots (reset_graph from g_scan) roots'.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate
         Hfrg Hfrr Hscan Hbridge.
  destruct (forward_remset_gh_frr_dsr_mapped_ready_marked_base_state
              from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
              g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec
              Hstate Hfrg Hfrr Hscan)
    as [l [Hsemi [Hclosed [Hprov [_ [_ [_ Hmarked]]]]]]].
  assert (Hreach:
            reachable_iff_marked
              g g_scan (remset_augmented_roots g rmst rh from roots) from). {
    intros v.
    rewrite (Hbridge l Hsemi Hclosed Hprov v).
    exact (Hmarked v).
  }
  assert (Hnoedge: no_edge2gen g_scan from) by
      (eapply forward_remset_gh_frr_dsr_no_edge2gen; eauto).
  destruct Hstate as [[Hrnd [Hrgc Hrrhc]] _].
  eapply forward_remset_gh_frr_dsr_roots_iso_from_augmented; eauto.
Qed.

Lemma forward_remset_gh_frr_dsr_roots_iso_from_rom_path_bridge_state:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan,
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
    forward_roots_relation from to roots g_rem roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g_scan ->
    (forall l,
        gc_graph_remset_semi_iso g g_rem from to l ->
        no_unmarked_old_nonfrom_dst g g_rem from ->
        (forall x,
            In x (map fst l) ->
            In (ExteriorVertex x) (effective_remset_roots g rmst rh from)) ->
        let ready := remset_ready_roots l in
        (forall v,
            roots_reachable_in_gen
              g (remset_augmented_roots g rmst rh from roots) from v ->
            reachable_or_marked from g_rem (ready ++ roots) v) /\
        (forall v,
            reachable_through_set
              g_rem (filter_proj exterior_proj_vertex (ready ++ roots)) v ->
            vgeneration v = from ->
            roots_reachable_in_gen
              g (remset_augmented_roots g rmst rh from roots) from v)) ->
    gc_graph_iso g roots (reset_graph from g_scan) roots'.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst'
         g1 g_scan Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate
         Hfrg Hfrr Hscan Hpath_bridge.
  eapply forward_remset_gh_frr_dsr_roots_iso_from_rom_bridge_state; eauto.
  intros l Hsemi Hclosed Hprov.
  cbn zeta.
  destruct (Hpath_bridge l Hsemi Hclosed Hprov) as [Hforward Hreachable_inv].
  cbn zeta in Hforward, Hreachable_inv.
  intro target.
  split.
  - apply Hforward.
  - intros Hrom.
    unfold reachable_or_marked in Hrom.
    destruct Hrom as [Hgen [Hreach | [Hvalid Hmark]]].
    + exact (Hreachable_inv target Hreach Hgen).
    + eapply remset_semi_iso_marked_reachable_from_augmented; eauto.
Qed.

Lemma do_generation_relation_roots_iso_from_rom_path_bridge_state:
  forall from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h',
    from <> to ->
    sound_gc_graph g ->
    graph_has_gen g to ->
    graph_unmarked g ->
    roots_graph_compatible roots g ->
    no_dangling_dst g ->
    firstn_gen_clear g from ->
    no_unrecorded_backward_edge_from from g rh ->
    remset_graph_state g from rmst rh ->
    do_generation_relation from to roots roots' g h rh rmst
      g_rem h_rem rh' rmst' g' h' ->
    (forall g1 g_scan l,
        (g_rem, h_rem, rh', rmst') = forward_remset_gh from to g h rh rmst ->
        forward_roots_relation from to roots g_rem roots' g1 ->
        do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g_scan ->
        gc_graph_remset_semi_iso g g_rem from to l ->
        no_unmarked_old_nonfrom_dst g g_rem from ->
        (forall x,
            In x (map fst l) ->
            In (ExteriorVertex x) (effective_remset_roots g rmst rh from)) ->
        let ready := remset_ready_roots l in
        (forall v,
            roots_reachable_in_gen
              g (remset_augmented_roots g rmst rh from roots) from v ->
            reachable_or_marked from g_rem (ready ++ roots) v) /\
        (forall v,
            reachable_through_set
              g_rem (filter_proj exterior_proj_vertex (ready ++ roots)) v ->
            vgeneration v = from ->
            roots_reachable_in_gen
              g (remset_augmented_roots g rmst rh from roots) from v)) ->
    gc_graph_iso g roots g' roots'.
Proof.
  intros from to roots roots' g h rh rmst g_rem h_rem rh' rmst' g' h'
         Hneq Hsound Hto Hun Hroots Hndd Hfirst Hunrec Hstate Hrel Hbridge.
  destruct Hrel as [[g1 [g_scan [Hfrg [Hfrr [Hscan Hreset]]]]] _].
  subst g'.
  eapply forward_remset_gh_frr_dsr_roots_iso_from_rom_path_bridge_state; eauto.
Qed.

Theorem garbage_collect_isomorphism:
  forall roots1 roots2 g1 h1 rh1 rmst1 g2 h2 rh2 rmst2,
    graph_unmarked g1 -> no_unrecorded_backward_edge g1 rh1 -> no_dangling_dst g1 ->
    roots_graph_compatible roots1 g1 ->
    sound_gc_graph g1 ->
    remset_graph_state g1 O rmst1 rh1 ->
    remset_heap_covers_graph g1 rh1 ->
    garbage_collect_relation roots1 roots2 g1 h1 rh1 rmst1 g2 h2 rh2 rmst2 ->
    gc_graph_iso g1 roots1 g2 roots2.
Proof.
  intros roots1 roots2 g1 h1 rh1 rmst1 g2 h2 rh2 rmst2
         Hun Hunrec Hndd Hrgc Hsound Hstate_init Hcover_init Hrel.
  destruct Hrel as [n [Hloop _]].
  unfold nat_inc_list in Hloop.
  pose proof (graph_has_gen_O g1) as Hgen0.
  assert (Hfirst: firstn_gen_clear g1 O) by (red; intros; lia).
  remember O as s.
  change (no_unrecorded_backward_edge_from O g1 rh1) in Hunrec.
  rewrite <- Heqs in Hunrec.
  clear Heqs.
  remember (S n) as m. clear n Heqm. rename m into n.
  revert s roots1 g1 h1 rh1 rmst1 roots2 g2 h2 rh2 rmst2
         Hstate_init Hcover_init Hun Hunrec Hndd Hrgc Hsound Hgen0 Hfirst Hloop.
  induction n; intros s roots1 g1 h1 rh1 rmst1 roots2 g2 h2 rh2 rmst2
                    Hstate Hcover Hun Hunrec Hndd Hrgc Hsound Hgen0 Hfirst Hloop;
    simpl in Hloop; inversion Hloop; subst; clear Hloop.
  - apply gc_graph_iso_refl.
  - assert (Hsound3: sound_gc_graph g3) by (eapply new_gen_heap_sound; eauto).
    assert (Hto3: graph_has_gen g3 (S s)) by
        (eapply new_gen_heap_graph_has_gen; eauto).
    assert (Hun3: graph_unmarked g3) by
        (eapply new_gen_heap_graph_unmarked; eauto).
    assert (Hunrec3: no_unrecorded_backward_edge_from s g3 rh1) by
        (eapply new_gen_heap_unrecorded_from_pres; eauto).
    assert (Hrgc3: roots_graph_compatible roots1 g3) by
        (eapply new_gen_heap_roots_graph_compatible; eauto).
    assert (Hndd3: no_dangling_dst g3) by
        (eapply new_gen_heap_no_dangling_dst; eauto).
    assert (Hstate3: remset_graph_state g3 s rmst1 rh1) by
        (eapply new_gen_heap_remset_graph_state; eauto).
    assert (Hcover3: remset_heap_covers_graph g3 rh1) by
        (eapply new_gen_heap_remset_heap_covers_graph; eauto).
    assert (Hcc3: copy_compatible g3) by
        (apply graph_unmarked_copy_compatible; exact Hun3).
    assert (Hfirst3: firstn_gen_clear g3 s) by
        (eapply new_gen_heap_firstn_gen_clear; eauto).
    assert (Hfirst4: firstn_gen_clear g4 (S s)) by
        (eapply do_generation_relation_firstn_gen_clear; eauto;
         exact Hfirst3).
    assert (Hndd4: no_dangling_dst g4) by
        (eapply (do_generation_relation_no_dangling_dst_noedge_state
                   g3 h3 rh1 rmst1 g_rem h_rem rh3 rmst3
                   g4 h4 roots1 roots3 s); eauto; try lia).
    assert (Hstate4:
              remset_graph_state g4 (S s) rmst3
                (reset_nth_remset_heap s rh3)) by
        (eapply do_generation_relation_reset_remset_graph_state; eauto;
         try lia).
    assert (Hcover4:
              remset_heap_covers_graph g4 (reset_nth_remset_heap s rh3)) by
        (eapply do_generation_relation_remset_heap_covers_graph; eauto).
    assert (Hunrec4:
              no_unrecorded_backward_edge_from (S s) g4
                (reset_nth_remset_heap s rh3)). {
      eapply (do_generation_relation_no_unrecorded_backward_edge_reset_state
                s roots1 roots3 g3 h3 rh1 rmst1
                g_rem h_rem rh3 rmst3 g4 h4); eauto; try lia.
    }
    apply (gc_graph_iso_trans g3 roots1).
    + eapply new_gen_heap_iso; eauto.
    + apply (gc_graph_iso_trans g4 roots3).
      * eapply do_generation_relation_roots_iso_from_rom_path_bridge_state;
          eauto; try lia.
        intros g_forward g_scan l Hfrg' Hfrr' Hscan' Hsemi Hclosed Hprov.
        cbn zeta.
        split.
        -- intros v Hreach.
           eapply forward_remset_gh_augmented_reachable_or_marked; eauto.
        -- intros v Hreach Hgenv.
           eapply (reachable_to_from_via_edge_bridge
                     g3 g_rem (remset_augmented_roots g3 rmst1 rh1 s roots1)
                     (filter_proj exterior_proj_vertex
                        (remset_ready_roots l ++ roots1))
                     s v).
           ++ eapply forward_remset_gh_sound; eauto.
           ++ intros root Hin_root Hroot_gen.
              rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in Hin_root.
              apply in_app_or in Hin_root.
              destruct Hin_root as [Hin_ready | Hin_roots].
              ** exfalso.
                 pose proof (remset_semi_iso_mapped_roots_have_no_gen
                               g3 g_rem s (S s) l ltac:(lia) Hsemi)
                   as Hready_no_gen.
                 exact (Hready_no_gen root Hin_ready Hroot_gen).
              ** split; [|exact Hroot_gen].
                 exists root.
                 split.
                 --- rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
                     unfold remset_augmented_roots.
                     apply in_or_app. right. exact Hin_roots.
                 --- apply reachable_refl.
                     destruct Hsound3 as [Hvv3 _].
                     apply (proj2 (Hvv3 _)).
                     unfold roots_graph_compatible in Hrgc3.
                     rewrite Forall_forall in Hrgc3.
                     apply Hrgc3.
                     rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
                     exact Hin_roots.
           ++ intros e He Hdst Hsrc_reach.
              assert (Hsound_rem: sound_gc_graph g_rem) by
                  (eapply forward_remset_gh_sound; eauto).
              destruct (Nat.eq_dec (vgeneration (fst e)) s)
                as [Hsrc_from | Hsrc_not_from];
                [ destruct (forward_remset_gh_from_edge_inv
                              s (S s) g3 h3 rh1 rmst1 g_rem h_rem
                              rh3 rmst3 e Hto3 ltac:(lia) Hstate3
                              Hfrg' He Hsrc_from)
                    as [He_base Hdst_eq];
                  rewrite Hdst_eq in Hdst;
                  rewrite Hdst_eq;
                  eapply roots_reachable_in_gen_edge; eauto
                | destruct (Nat.eq_dec (vgeneration (fst e)) (S s))
                    as [Hsrc_to | Hsrc_not_to];
                  [ assert (Hsrc_valid_rem: vvalid g_rem (fst e)) by
                        (destruct Hsound_rem as [Hvv _];
                         apply (proj2 (Hvv _));
                         destruct He as [Hsrc _]; exact Hsrc);
                    pose proof Hsound3 as Hsound3_full;
                    destruct Hsound3_full as [Hvv3 _];
                    destruct (vvalid_lcm g3 (fst e) Hvv3)
                      as [Hsrc_valid_base | Hsrc_not_base];
                    [ exfalso;
                      eapply (remset_semi_iso_current_old_nonfrom_edge_dst_not_from
                                g3 g_rem s (S s) l e); eauto; try lia
                    | pose proof Hsemi as Hsemi_parts;
                      destruct Hsemi_parts as [_ Hspec];
                      destruct (split l) as [from_l to_l] eqn:Hsplit;
                      destruct Hspec as [[_ Hfrom] [[_ [Hto_valid _]] _]];
                      assert (Hin_to: In (fst e) to_l) by
                          (rewrite Hto_valid; split; assumption);
                      assert (Hin_snd: In (fst e) (map snd l)) by
                          (rewrite map_snd_split, Hsplit; exact Hin_to);
                      rewrite In_map_snd_iff in Hin_snd;
                      destruct Hin_snd as [x Hpair];
                      assert (Hin_fst: In x (map fst l)) by
                          (eapply In_map_fst; exact Hpair);
                      assert (Hfrom_l: from_l = map fst l) by
                          (rewrite map_fst_split, Hsplit; reflexivity);
                      assert (Hin_from: In x from_l) by
                          (rewrite Hfrom_l; exact Hin_fst);
                      rewrite <- Hfrom in Hin_from;
                      destruct Hin_from as [_ [Hx_valid Hx_gen]];
                      destruct e as [src idx]; simpl in *;
                      destruct (remset_semi_iso_copied_edge_dst_base
                                  g3 g_rem s (S s) l x src idx
                                  ltac:(lia) Hsound3 Hndd3 Hsemi Hpair
                                  He Hdst)
                        as [Hedge_base [Hdst_eq Hdst_base_gen]];
                      rewrite Hdst_eq;
                      eapply roots_reachable_in_gen_edge
                        with (e := (x, idx)); eauto;
                      split; [|exact Hx_gen];
                      exists x;
                      split;
                      [ rewrite <- (filter_proj_In_iff
                                       exterior_proj_vertex_spec);
                        unfold remset_augmented_roots;
                        apply in_or_app; left;
                        apply Hprov; exact Hin_fst
                      | apply reachable_refl; exact Hx_valid ] ]
                  | exfalso;
                    eapply (remset_semi_iso_current_non_to_edge_dst_not_from
                              g3 g_rem s (S s) l e); eauto; try lia ] ].
           ++ exact Hreach.
           ++ exact Hgenv.
      * eapply (IHn (S s) roots3 g4 h4 (reset_nth_remset_heap s rh3)
                    rmst3 roots2 g2 h2 rh2 rmst2);
          try solve
            [ exact Hstate4
            | exact Hcover4
            | eapply do_generation_relation_graph_unmarked; eauto
            | eapply do_generation_relation_sound; eauto
            | rewrite <- (do_generation_relation_graph_has_gen
                            s (S s) roots1 roots3 g3 h3 rh1 rmst1
                            g_rem h_rem rh3 rmst3 g4 h4 Hto3 H2 (S s));
              exact Hto3
            | exact Hfirst4
            | exact Hunrec4
            | exact Hndd4
            | eapply (do_generation_relation_roots_graph_compatible_simple
                        s (S s) roots1 roots3 g3 h3 rh1 rmst1
                        g_rem h_rem rh3 rmst3 g4 h4);
              [lia | exact Hto3 | apply graph_unmarked_copy_compatible; exact Hun3
               | exact Hrgc3 | exact H2]
            | exact H15 ].
Qed.

Lemma remset_graph_state_from_spec_pre:
  forall g outlier from rmst rh h,
    remset_nodup rmst ->
    remset_compatible g outlier from rmst rh h ->
    remset_generation_compatible from rmst rh ->
    remset_graph_state g from rmst rh.
Proof.
  intros g outlier from rmst rh h Hrnd Hremc Hremgen.
  split; [|exact Hremgen].
  unfold remset_forward_compatible.
  split; [exact Hrnd | split].
  - destruct Hremc as [Hrgoc _].
    now apply remset_graph_outlier_compatible_weakened with (outlier := outlier).
  - destruct Hremc as [_ [Hrrhc _]]. exact Hrrhc.
Qed.

Lemma remset_compatible_remset_heap_covers_graph:
  forall g h rootpairs roots outlier from rmst rh,
    super_compatible g h rootpairs roots outlier ->
    remset_compatible g outlier from rmst rh h ->
    remset_heap_covers_graph g rh.
Proof.
  intros g h rootpairs roots outlier from rmst rh Hsc Hremc.
  split.
  - destruct Hremc as [_ [_ Hrhhc]].
    apply Forall2_length in Hrhhc.
    rewrite Zlength_correct, Hrhhc.
    rewrite <- Zlength_correct.
    apply spaces_size.
  - intros gen Hgen.
    destruct Hsc as [Hghc _].
    eapply gen_range; eauto.
Qed.

Theorem garbage_collect_spec_preconditions_imply_isomorphism:
  forall rootpairs roots roots' g h rh rmst g' h' rh' rmst' outlier,
    super_compatible g h rootpairs roots outlier ->
    garbage_collect_condition g h ->
    no_unrecorded_backward_edge g rh ->
    remset_compatible g outlier O rmst rh h ->
    remset_generation_compatible O rmst rh ->
    remset_nodup rmst ->
    sound_gc_graph g ->
    garbage_collect_relation roots roots' g h rh rmst g' h' rh' rmst' ->
    gc_graph_iso g roots g' roots'.
Proof.
  intros rootpairs roots roots' g h rh rmst g' h' rh' rmst' outlier
         Hsc Hgcc Hunrec Hremc Hremgen Hrnd Hsound Hrel.
  eapply garbage_collect_isomorphism.
  - destruct Hgcc as [Hun _]. exact Hun.
  - exact Hunrec.
  - destruct Hgcc as [_ [Hndd _]]. exact Hndd.
  - destruct Hsc as [_ [_ [[_ Hroots] _]]]. exact Hroots.
  - exact Hsound.
  - eapply remset_graph_state_from_spec_pre; eauto.
  - eapply remset_compatible_remset_heap_covers_graph; eauto.
  - exact Hrel.
Qed.

Lemma mutable_update_remset_heap_and_heap_compatible:
  forall (g: LGraph) (h: part_heap) (rh: remset_heap)
         (x: val) (item: remset_space_item),
    graph_heap_compatible g h ->
    used_space (nth_space h O) < available_space (nth_space h O) ->
    remset_heap_and_heap_compatible rh h ->
    remset_heap_and_heap_compatible
      (if isptr_dec x then upd_remset_heap item rh O else rh)
      (if isptr_dec x then incr_remset_heap h 0 else h).
Proof.
  intros g h rh x item Hghc Hcapacity Hrhhc.
  destruct (isptr_dec x).
  - eapply upd_incr_remset_heap_rhhc; eauto.
    apply graph_has_gen_O.
  - exact Hrhhc.
Qed.

Lemma mutable_update_remset_generation_compatible:
  forall (x: val) (it: interior_t) (rh: remset_heap) (rmst: remset),
    0 <= Z.of_nat O < Zlength rh ->
    remset_generation_compatible O rmst rh ->
    remset_generation_compatible O rmst
      (if isptr_dec x
       then upd_remset_heap (RemSetInterior it) rh O
       else rh).
Proof.
  intros x it rh rmst Hrange Hcompatible.
  destruct (isptr_dec x).
  2: exact Hcompatible.
  destruct Hcompatible as [Hext [Horder _]].
  split.
  - unfold remset_ext_space_compatible in *.
    intros v addr Hin.
    eapply nth_remset_space_upd_remset_heap_old; eauto.
  - split.
    + eapply upd_remset_heap_interior_generation_order; eauto.
      intros. apply Nat.le_0_l.
    + unfold remset_lower_generations_empty.
      intros gen Hlt. lia.
Qed.

#[local] Lemma graph_has_e_iff_raw_internal:
  forall g v n,
    graph_has_v g v ->
    (graph_has_e g (v, n) <->
     0 <= Z.of_nat n < Zlength (raw_fields (vlabel g v)) /\
     Znth (Z.of_nat n) (raw_fields (vlabel g v)) = RawInternal).
Proof.
  intros g v n Hv. split.
  - intro He. pose proof (graph_has_e_Znth g v n He) as [Hrange Hfield].
    split; [exact Hrange|].
    rewrite (Znth_make_fields g v (Z.of_nat n) Hrange) in Hfield.
    destruct (Znth (Z.of_nat n) (raw_fields (vlabel g v)));
      inversion Hfield; reflexivity.
  - intros [Hrange Hraw]. split; [exact Hv|].
    rewrite get_edges_In_iff.
    assert (Hfield: Znth (Z.of_nat n) (make_fields g v) = FieldEdge (v, n)).
    { rewrite (Znth_make_fields g v (Z.of_nat n) Hrange), Hraw, Nat2Z.id.
      reflexivity. }
    rewrite <- Hfield. apply Znth_In.
    rewrite make_fields_eq_length. exact Hrange.
Qed.

Lemma mutable_graph_update_graph_has_e_neq:
  forall g src pos new g' e,
    e <> (src, Z.to_nat pos) ->
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    (graph_has_e g' e <-> graph_has_e g e).
Proof.
  intros g src pos new g' [v n] Hneq Hloc Hupd.
  pose proof Hloc as Hloc'.
  destruct Hloc as [Hv [Hpos [Hmark Htag]]].
  destruct (V_EqDec v src) as [Heq | Hne].
  - hnf in Heq. subst v.
    assert (Hidx: Z.of_nat n <> pos).
    { intro Heq. apply Hneq. f_equal. rewrite <- Heq, Nat2Z.id. reflexivity. }
    pose proof (mutable_graph_update_vlabel_src g src pos new g' Hloc' Hupd) as Hsrc.
    unfold raw_vertex_field_update in Hsrc. destruct Hsrc as [Hfields _].
    rewrite (graph_has_e_iff_raw_internal g' src n).
    2: rewrite (mutable_graph_update_graph_has_v g (InteriorVertexPos src pos)
                  new g' src Hloc' Hupd); exact Hv.
    rewrite (graph_has_e_iff_raw_internal g src n Hv).
    rewrite Hfields, Zlength_upd_Znth.
    rewrite upd_Znth_diff_strong; [reflexivity|exact Hpos|exact Hidx].
  - unfold graph_has_e; simpl fst.
    rewrite (mutable_graph_update_graph_has_v
               g (InteriorVertexPos src pos) new g' v Hloc' Hupd).
    unfold get_edges, make_fields.
    rewrite (mutable_graph_update_vlabel_other
               g src pos new g' v Hne Hloc' Hupd).
    reflexivity.
Qed.

Lemma mutable_graph_update_graph_has_e_target:
  forall g src pos new g',
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    (graph_has_e g' (src, Z.to_nat pos) <->
     exists dstv, new = ExteriorVertex dstv).
Proof.
  intros g src pos new g' Hloc Hupd.
  pose proof Hloc as Hloc'.
  destruct Hloc as [Hv [Hpos [Hmark Htag]]].
  rewrite (graph_has_e_iff_raw_internal g' src (Z.to_nat pos)).
  2: rewrite (mutable_graph_update_graph_has_v g (InteriorVertexPos src pos)
                new g' src Hloc' Hupd); exact Hv.
  rewrite Z2Nat.id by lia.
  pose proof (mutable_graph_update_vlabel_src g src pos new g' Hloc' Hupd) as Hsrc.
  unfold raw_vertex_field_update in Hsrc. destruct Hsrc as [Hfields _].
  rewrite Hfields, Zlength_upd_Znth, upd_Znth_same by exact Hpos.
  destruct new as [z | p | dstv]; simpl.
  - split; [intros [_ H]; discriminate|intros [x H]; discriminate].
  - split; [intros [_ H]; discriminate|intros [x H]; discriminate].
  - split; [intros; now exists dstv|intros; split; [exact Hpos|reflexivity]].
Qed.

Lemma mutable_graph_update_evalid_neq:
  forall g src pos new g' e,
    e <> (src, Z.to_nat pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    (evalid g' e <-> evalid g e).
Proof.
  intros g src pos new g' e Hneq Hupd.
  unfold mutable_graph_update, internal_write_at in Hupd.
  destruct new as [z | p | dstv].
  - destruct Hupd as [rvb' [_ ->]].
    simpl. unfold removeValidFunc. tauto.
  - destruct Hupd as [rvb' [_ ->]].
    simpl. unfold removeValidFunc. tauto.
  - destruct (Znth pos (raw_fields (vlabel g src))) eqn:Hold.
    + subst g'. reflexivity.
    + destruct Hupd as [rvb' [_ ->]].
      simpl. unfold addValidFunc. tauto.
    + destruct Hupd as [rvb' [_ ->]].
      simpl. unfold addValidFunc. tauto.
Qed.

Lemma mutable_graph_update_evalid_target:
  forall g src pos new g',
    sound_gc_graph g ->
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    (evalid g' (src, Z.to_nat pos) <->
     exists dstv, new = ExteriorVertex dstv).
Proof.
  intros g src pos new g' Hsound Hloc Hupd.
  destruct Hloc as [Hv [Hpos [Hmark Htag]]].
  destruct Hsound as [Hvv [Hev [Hsrc Helabel]]].
  unfold mutable_graph_update, internal_write_at in Hupd.
  destruct new as [z | p | dstv].
  - destruct Hupd as [rvb' [_ ->]].
    simpl. unfold removeValidFunc. split; [tauto|intros [x H]; discriminate].
  - destruct Hupd as [rvb' [_ ->]].
    simpl. unfold removeValidFunc. split; [tauto|intros [x H]; discriminate].
  - destruct (Znth pos (raw_fields (vlabel g src))) eqn:Hold.
    + subst g'. split.
      * intros. now exists dstv.
      * intros _. apply Hev.
        apply (proj2 (graph_has_e_iff_raw_internal g src (Z.to_nat pos) Hv)).
        rewrite Z2Nat.id by lia. split; assumption.
    + destruct Hupd as [rvb' [_ ->]].
      split; [intros; now exists dstv|intros; apply add_edge_evalid].
    + destruct Hupd as [rvb' [_ ->]].
      split; [intros; now exists dstv|intros; apply add_edge_evalid].
Qed.

Lemma mutable_graph_update_vvalid:
  forall g it new g' v,
    mutable_graph_update g it new g' ->
    (vvalid g' v <-> vvalid g v).
Proof.
  intros g [src pos] new g' v Hupd.
  unfold mutable_graph_update, internal_write_at in Hupd.
  destruct new as [z | p | dstv].
  - destruct Hupd as [rvb' [_ ->]]. reflexivity.
  - destruct Hupd as [rvb' [_ ->]]. reflexivity.
  - destruct (Znth pos (raw_fields (vlabel g src))).
    + subst g'. reflexivity.
    + destruct Hupd as [rvb' [_ ->]]. reflexivity.
    + destruct Hupd as [rvb' [_ ->]]. reflexivity.
Qed.

Lemma mutable_graph_update_src_edge:
  forall (g: LGraph) it new g',
    src_edge g -> mutable_graph_update g it new g' -> src_edge g'.
Proof.
  intros g [srcv pos] new g' Hsrc Hupd.
  unfold mutable_graph_update, internal_write_at in Hupd.
  destruct new as [z | p | dstv].
  - destruct Hupd as [rvb' [_ ->]]. exact Hsrc.
  - destruct Hupd as [rvb' [_ ->]]. exact Hsrc.
  - destruct (Znth pos (raw_fields (vlabel g srcv))).
    + subst g'. exact Hsrc.
    + destruct Hupd as [rvb' [_ ->]]. intros e.
      simpl. unfold updateEdgeFunc. if_tac.
      * hnf in H. subst e. reflexivity.
      * apply Hsrc.
    + destruct Hupd as [rvb' [_ ->]]. intros e.
      simpl. unfold updateEdgeFunc. if_tac.
      * hnf in H. subst e. reflexivity.
      * apply Hsrc.
Qed.

Lemma mutable_graph_update_edge_label_same:
  forall (g: LGraph) it new g',
    edge_label_same g ->
    mutable_graph_update g it new g' ->
    edge_label_same g'.
Proof.
  intros g [srcv pos] new g' Hlabel Hupd.
  unfold mutable_graph_update, internal_write_at in Hupd.
  destruct new as [z | p | dstv].
  - destruct Hupd as [rvb' [_ ->]]. exact Hlabel.
  - destruct Hupd as [rvb' [_ ->]]. exact Hlabel.
  - destruct (Znth pos (raw_fields (vlabel g srcv))).
    + subst g'. exact Hlabel.
    + destruct Hupd as [rvb' [_ ->]]. intros e.
      simpl. unfold update_elabel. if_tac.
      * hnf in H. subst e. reflexivity.
      * apply Hlabel.
    + destruct Hupd as [rvb' [_ ->]]. intros e.
      simpl. unfold update_elabel. if_tac.
      * hnf in H. subst e. reflexivity.
      * apply Hlabel.
Qed.

Theorem mutable_graph_update_sound:
  forall g src pos new g' outlier,
    sound_gc_graph g ->
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    sound_gc_graph g'.
Proof.
  intros g src pos new g' outlier Hsound Hloc Hext Hupd.
  pose proof Hsound as Hsound'.
  destruct Hsound as [Hvv [Hev [Hsrc Hlabel]]].
  split; [|split; [|split]].
  - intro v.
    rewrite (mutable_graph_update_vvalid g (InteriorVertexPos src pos) new g' v Hupd).
    rewrite (mutable_graph_update_graph_has_v g (InteriorVertexPos src pos)
               new g' v Hloc Hupd).
    apply Hvv.
  - intro e. destruct (E_EqDec e (src, Z.to_nat pos)) as [Heq | Hneq].
    + hnf in Heq. subst e.
      rewrite (mutable_graph_update_evalid_target g src pos new g' Hsound' Hloc Hupd).
      rewrite (mutable_graph_update_graph_has_e_target g src pos new g' Hloc Hupd).
      reflexivity.
    + rewrite (mutable_graph_update_evalid_neq g src pos new g' e Hneq Hupd).
      rewrite (mutable_graph_update_graph_has_e_neq g src pos new g' e Hneq Hloc Hupd).
      apply Hev.
  - eapply mutable_graph_update_src_edge; eassumption.
  - eapply mutable_graph_update_edge_label_same; eassumption.
Qed.

Theorem mutable_graph_update_outlier_compatible:
  forall g src pos new g' outlier,
    outlier_compatible g outlier ->
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    outlier_compatible g' outlier.
Proof.
  intros g src pos new g' outlier Hold Hloc Hext Hupd.
  intros v Hv' p Hin.
  assert (Hv: graph_has_v g v).
  { rewrite <- (mutable_graph_update_graph_has_v g (InteriorVertexPos src pos)
                   new g' v Hloc Hupd). exact Hv'. }
  destruct (V_EqDec v src) as [Heq | Hneq].
  - hnf in Heq. subst v.
    pose proof (mutable_graph_update_vlabel_src g src pos new g' Hloc Hupd) as Hsrc.
    unfold raw_vertex_field_update in Hsrc. destruct Hsrc as [Hfields _].
    rewrite <- (filter_proj_In_iff raw_proj_outlier_spec) in Hin.
    rewrite Hfields in Hin. apply In_upd_Znth in Hin. destruct Hin as [Hnew | Holdin].
    + destruct new as [z | q | dstv]; inversion Hnew; subst. exact Hext.
    + apply (Hold src Hv).
      rewrite <- (filter_proj_In_iff raw_proj_outlier_spec). exact Holdin.
  - apply (Hold v Hv).
    rewrite (mutable_graph_update_vlabel_other g src pos new g' v Hneq Hloc Hupd) in Hin.
    exact Hin.
Qed.

Theorem mutable_graph_update_no_unrecorded_backward_edge:
  forall g src pos new g' outlier rh,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    0 <= Z.of_nat O < Zlength rh ->
    no_unrecorded_backward_edge g rh ->
    no_unrecorded_backward_edge g'
      (if isptr_dec (exterior2val g new)
       then upd_remset_heap (RemSetInterior (InteriorVertexPos src pos)) rh O
       else rh).
Proof.
  intros g src pos new g' outlier rh Hloc Hext Hupd Hrange Hold.
  pose proof Hloc as Hloc'.
  destruct Hloc as [Hv [Hpos [Hmark Htag]]].
  unfold no_unrecorded_backward_edge, no_unrecorded_backward_edge_from in *.
  intros e He' Hback.
  destruct (E_EqDec e (src, Z.to_nat pos)) as [Heq | Hneq].
  - hnf in Heq. subst e.
    apply (mutable_graph_update_graph_has_e_target g src pos new g' Hloc' Hupd) in He'.
    destruct He' as [dstv Hnew]. subst new.
    destruct (isptr_dec (exterior2val g (ExteriorVertex dstv))) as [Hptr | Hnptr].
    2: exfalso; apply Hnptr; simpl; apply graph_has_v_addr_isptr; exact Hext.
    exists O. split.
    + split; lia.
    + unfold remset_heap_records_edge. simpl fst. simpl snd.
      rewrite Z2Nat.id by lia.
      apply nth_remset_space_upd_remset_heap_new. exact Hrange.
  - assert (He: graph_has_e g e).
    { apply (proj1 (mutable_graph_update_graph_has_e_neq
                      g src pos new g' e Hneq Hloc' Hupd)). exact He'. }
    pose proof (mutable_graph_update_dst_neq
                  g src pos new g' e Hneq Hloc' Hupd) as Hdst.
    rewrite Hdst in Hback.
    specialize (Hold e He Hback).
    destruct Hold as [k [Hbounds Hrecord]].
    assert (Hbounds': (O <= k <= vgeneration (dst g' e))%nat).
    { rewrite Hdst. exact Hbounds. }
    exists k. split; [exact Hbounds'|].
    destruct (isptr_dec (exterior2val g new)) as [Hptr | Hnptr].
    + unfold remset_heap_records_edge in *.
      eapply nth_remset_space_upd_remset_heap_old; eauto.
    + exact Hrecord.
Qed.

Lemma mutable_graph_update_raw_mark_tag:
  forall g src pos new g' v,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    raw_mark (vlabel g' v) = raw_mark (vlabel g v) /\
    raw_tag (vlabel g' v) = raw_tag (vlabel g v).
Proof.
  intros g src pos new g' v Hloc Hupd.
  destruct (V_EqDec v src) as [Heq | Hneq].
  - hnf in Heq. subst v.
    pose proof (mutable_graph_update_vlabel_src g src pos new g' Hloc Hupd) as Hsrc.
    unfold raw_vertex_field_update in Hsrc. tauto.
  - rewrite (mutable_graph_update_vlabel_other
               g src pos new g' v Hneq Hloc Hupd).
    split; reflexivity.
Qed.

Lemma mutable_graph_update_remset_ext_compatible:
  forall g it new g' outlier re,
    mutable_location_compatible g it ->
    mutable_graph_update g it new g' ->
    remset_ext_compatible g outlier re ->
    remset_ext_compatible g' outlier re.
Proof.
  intros g it new g' outlier re Hloc Hupd Hold.
  destruct re as [p addr | v addr]; simpl in *.
  - exact Hold.
  - rewrite (mutable_graph_update_graph_has_v g it new g' v Hloc Hupd).
    exact Hold.
Qed.

Lemma mutable_graph_update_remset_graph_outlier_compatible:
  forall g it new g' outlier rmst,
    mutable_location_compatible g it ->
    mutable_graph_update g it new g' ->
    remset_graph_outlier_compatible g outlier rmst ->
    remset_graph_outlier_compatible g' outlier rmst.
Proof.
  intros g it new g' outlier rmst Hloc Hupd Hold.
  unfold remset_graph_outlier_compatible in *.
  eapply Forall_impl; [|exact Hold].
  intros re Hre.
  eapply mutable_graph_update_remset_ext_compatible; eauto.
Qed.

Lemma mutable_graph_update_remset_item_compatible:
  forall g src pos new g' from rmst item,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    remset_item_compatible g from rmst item ->
    remset_item_compatible g' from rmst item.
Proof.
  intros g src pos new g' from rmst item Hloc Hupd Hold.
  destruct item as [addr | [v n]]; simpl in *; [exact Hold|].
  destruct Hold as [Hv [Hn Hscan]].
  split.
  - rewrite (mutable_graph_update_graph_has_v
               g (InteriorVertexPos src pos) new g' v Hloc Hupd).
    exact Hv.
  - split.
    + rewrite (mutable_graph_update_raw_fields_length
                 g (InteriorVertexPos src pos) new g' v Hloc Hupd).
      exact Hn.
    + intros Hgen. specialize (Hscan Hgen). destruct Hscan as [Hmark Htag].
      pose proof (mutable_graph_update_raw_mark_tag
                    g src pos new g' v Hloc Hupd) as [Hmark' Htag'].
      rewrite Hmark', Htag'. split; assumption.
Qed.

Lemma mutable_graph_update_new_remset_item_compatible:
  forall g src pos new g' from rmst,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    remset_item_compatible g' from rmst
      (RemSetInterior (InteriorVertexPos src pos)).
Proof.
  intros g src pos new g' from rmst Hloc Hupd.
  pose proof Hloc as Hloc'.
  destruct Hloc as [Hv [Hpos [Hmark Htag]]].
  simpl. split.
  - rewrite (mutable_graph_update_graph_has_v
               g (InteriorVertexPos src pos) new g' src Hloc' Hupd).
    exact Hv.
  - split.
    + rewrite (mutable_graph_update_raw_fields_length
                 g (InteriorVertexPos src pos) new g' src Hloc' Hupd).
      exact Hpos.
    + intros _.
      pose proof (mutable_graph_update_raw_mark_tag
                    g src pos new g' src Hloc' Hupd) as [Hmark' Htag'].
      rewrite Hmark', Htag'. split; assumption.
Qed.

Lemma mutable_graph_update_remset_space_compatible:
  forall g src pos new g' from rmst items,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    remset_and_remset_space_compatible g from rmst items ->
    remset_and_remset_space_compatible g' from rmst items.
Proof.
  intros g src pos new g' from rmst items Hloc Hupd Hold.
  unfold remset_and_remset_space_compatible in *.
  eapply Forall_impl; [|exact Hold].
  intros item Hitem.
  eapply mutable_graph_update_remset_item_compatible; eauto.
Qed.

Lemma mutable_update_remset_and_remset_heap_compatible:
  forall g src pos new g' from rmst rh x,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    0 <= Z.of_nat O < Zlength rh ->
    remset_and_remset_heap_compatible g from rmst rh ->
    remset_and_remset_heap_compatible g' from rmst
      (if isptr_dec x
       then upd_remset_heap
              (RemSetInterior (InteriorVertexPos src pos)) rh O
       else rh).
Proof.
  intros g src pos new g' from rmst rh x Hloc Hupd Hrange Hold.
  destruct (isptr_dec x) as [Hptr | Hnptr].
  2: {
    unfold remset_and_remset_heap_compatible in *.
    eapply Forall_impl; [|exact Hold].
    intros items Hitems.
    eapply mutable_graph_update_remset_space_compatible; eauto.
  }
  unfold remset_and_remset_heap_compatible in *.
  rewrite Forall_forall in *. intros items Hin.
  apply upd_remset_heap_In in Hin. destruct Hin as [Hin | ->].
  - eapply mutable_graph_update_remset_space_compatible; eauto.
  - constructor.
    + eapply mutable_graph_update_new_remset_item_compatible; eauto.
    + eapply mutable_graph_update_remset_space_compatible; eauto.
      apply Hold. apply Znth_In. exact Hrange.
Qed.

Theorem mutable_update_remset_compatible:
  forall g src pos new g' outlier from rmst rh h,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    graph_heap_compatible g h ->
    used_space (nth_space h O) < available_space (nth_space h O) ->
    remset_compatible g outlier from rmst rh h ->
    remset_compatible g' outlier from rmst
      (if isptr_dec (exterior2val g new)
       then upd_remset_heap
              (RemSetInterior (InteriorVertexPos src pos)) rh O
       else rh)
      (if isptr_dec (exterior2val g new)
       then incr_remset_heap h 0
       else h).
Proof.
  intros g src pos new g' outlier from rmst rh h
         Hloc Hupd Hghc Hcapacity [Hrgoc [Hrrhc Hrhhc]].
  assert (Hrange: 0 <= Z.of_nat O < Zlength rh).
  { eapply gen_range_remset_heap; eauto. apply graph_has_gen_O. }
  split.
  - eapply mutable_graph_update_remset_graph_outlier_compatible; eauto.
  - split.
    + eapply mutable_update_remset_and_remset_heap_compatible; eauto.
    + eapply mutable_update_remset_heap_and_heap_compatible; eauto.
Qed.

Lemma mutable_graph_update_exterior2val_all:
  forall g it new g' ext,
    mutable_location_compatible g it ->
    mutable_graph_update g it new g' ->
    exterior2val g' ext = exterior2val g ext.
Proof.
  intros g it new g' ext Hloc Hupd.
  destruct ext; simpl; try reflexivity.
  eapply mutable_graph_update_vertex_address; eassumption.
Qed.

Lemma mutable_graph_update_rootpairs_compatible:
  forall g it new g' rootpairs roots,
    mutable_location_compatible g it ->
    mutable_graph_update g it new g' ->
    rootpairs_compatible g rootpairs roots ->
    rootpairs_compatible g' rootpairs roots.
Proof.
  intros g it new g' rootpairs roots Hloc Hupd Hcompatible.
  unfold rootpairs_compatible in *.
  rewrite <- Hcompatible. clear Hcompatible rootpairs.
  induction roots as [|ext roots IH]; simpl; [reflexivity|].
  rewrite (mutable_graph_update_exterior2val_all
             g it new g' ext Hloc Hupd), IH.
  reflexivity.
Qed.

Lemma mutable_graph_update_roots_compatible:
  forall g it new g' outlier roots,
    mutable_location_compatible g it ->
    mutable_graph_update g it new g' ->
    roots_compatible g outlier roots ->
    roots_compatible g' outlier roots.
Proof.
  intros g it new g' outlier roots Hloc Hupd [Houtlier Hgraph].
  split; [exact Houtlier|].
  unfold roots_graph_compatible in *.
  eapply Forall_impl; [|exact Hgraph].
  intros v Hv.
  rewrite (mutable_graph_update_graph_has_v g it new g' v Hloc Hupd).
  exact Hv.
Qed.

Lemma mutable_graph_update_graph_unmarked:
  forall g src pos new g',
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    graph_unmarked g ->
    graph_unmarked g'.
Proof.
  intros g src pos new g' Hloc Hupd Hunmarked v Hv'.
  pose proof (mutable_graph_update_raw_mark_tag
                g src pos new g' v Hloc Hupd) as [Hmark _].
  rewrite Hmark. apply Hunmarked.
  rewrite <- (mutable_graph_update_graph_has_v
                 g (InteriorVertexPos src pos) new g' v Hloc Hupd).
  exact Hv'.
Qed.

Lemma mutable_graph_update_no_dangling_dst:
  forall g src pos new g' outlier,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    no_dangling_dst g ->
    no_dangling_dst g'.
Proof.
  intros g src pos new g' outlier Hloc Hext Hupd Hno v Hv' e Hin'.
  assert (Hfst': fst e = v) by (eapply get_edges_fst; exact Hin').
  assert (He': graph_has_e g' e).
  { unfold graph_has_e. rewrite Hfst'. split; assumption. }
  destruct (E_EqDec e (src, Z.to_nat pos)) as [Heq | Hneq].
  - hnf in Heq. subst e.
    apply (mutable_graph_update_graph_has_e_target
             g src pos new g' Hloc Hupd) in He'.
    destruct He' as [dstv Hnew]. subst new.
    rewrite (mutable_graph_update_dst_new g src pos dstv g' Hloc Hupd).
    rewrite (mutable_graph_update_graph_has_v
               g (InteriorVertexPos src pos) (ExteriorVertex dstv)
               g' dstv Hloc Hupd).
    exact Hext.
  - assert (He: graph_has_e g e).
    { apply (proj1 (mutable_graph_update_graph_has_e_neq
                      g src pos new g' e Hneq Hloc Hupd)). exact He'. }
    destruct He as [Hsrc Hin].
    specialize (Hno _ Hsrc _ Hin).
    rewrite (mutable_graph_update_dst_neq
               g src pos new g' e Hneq Hloc Hupd).
    rewrite (mutable_graph_update_graph_has_v
               g (InteriorVertexPos src pos) new g'
               (dst g e) Hloc Hupd).
    exact Hno.
Qed.

Theorem mutable_update_super_compatible:
  forall g src pos new g' h rootpairs roots outlier,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    super_compatible g h rootpairs roots outlier ->
    super_compatible g'
      (if isptr_dec (exterior2val g new)
       then incr_remset_heap h 0
       else h)
      rootpairs roots outlier.
Proof.
  intros g src pos new g' h rootpairs roots outlier
         Hloc Hext Hupd [Hghc [Hrootpairs [Hroots Houtlier]]].
  split; [|split; [|split]].
  - destruct (isptr_dec (exterior2val g new)).
    + apply incr_remset_heap_ghc.
      eapply mutable_graph_update_graph_heap_compatible; eauto.
    + eapply mutable_graph_update_graph_heap_compatible; eauto.
  - eapply mutable_graph_update_rootpairs_compatible; eauto.
  - eapply mutable_graph_update_roots_compatible; eauto.
  - eapply mutable_graph_update_outlier_compatible; eauto.
Qed.

Theorem mutable_update_garbage_collect_condition:
  forall g src pos new g' outlier h,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    garbage_collect_condition g h ->
    garbage_collect_condition g'
      (if isptr_dec (exterior2val g new)
       then incr_remset_heap h 0
       else h).
Proof.
  intros g src pos new g' outlier h Hloc Hext Hupd
         [Hunmarked [Hno_dangling Hsize]].
  split; [|split].
  - eapply mutable_graph_update_graph_unmarked; eauto.
  - eapply mutable_graph_update_no_dangling_dst; eauto.
  - destruct (isptr_dec (exterior2val g new)).
    + eapply weak_heap_relation_size_spec; eauto.
      apply incr_remset_heap_whr.
    + exact Hsize.
Qed.

Lemma incr_remset_heap_rest_gen_size_above_nursery:
  forall h n,
    rest_gen_size (incr_remset_heap h 0) (S n) =
    rest_gen_size h (S n).
Proof.
  intros h n. unfold rest_gen_size.
  rewrite !nth_space_Znth.
  rewrite (irh_Znth_spaces_not_eq h (Z.of_nat (S n)) 0) by lia.
  reflexivity.
Qed.

Theorem mutable_update_safe_to_copy_heap:
  forall g src pos new g' h,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    safe_to_copy_heap g h ->
    safe_to_copy_heap g'
      (if isptr_dec (exterior2val g new)
       then incr_remset_heap h 0
       else h).
Proof.
  intros g src pos new g' h Hloc Hupd Hsafe.
  unfold safe_to_copy_heap in *. intros n Hgen'.
  assert (Hgen: graph_has_gen g (S n)).
  { unfold graph_has_gen in *.
    rewrite (mutable_graph_update_glabel
               g (InteriorVertexPos src pos) new g' Hloc Hupd) in Hgen'.
    exact Hgen'. }
  specialize (Hsafe n Hgen).
  destruct (isptr_dec (exterior2val g new)).
  - unfold safe_to_copy_gen_heap in *.
    unfold total_size.
    rewrite irh_total_space.
    rewrite incr_remset_heap_rest_gen_size_above_nursery.
    exact Hsafe.
  - exact Hsafe.
Qed.

Theorem mutable_update_garbage_collect_model_preconditions:
  forall g src pos new g' h rootpairs roots outlier rmst rh,
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    used_space (nth_space h O) < available_space (nth_space h O) ->
    super_compatible g h rootpairs roots outlier ->
    garbage_collect_condition g h ->
    no_unrecorded_backward_edge g rh ->
    safe_to_copy_heap g h ->
    remset_compatible g outlier O rmst rh h ->
    remset_generation_compatible O rmst rh ->
    let x := exterior2val g new in
    let h' := if isptr_dec x then incr_remset_heap h 0 else h in
    let rh' :=
      if isptr_dec x
      then upd_remset_heap
             (RemSetInterior (InteriorVertexPos src pos)) rh O
      else rh in
    super_compatible g' h' rootpairs roots outlier /\
    garbage_collect_condition g' h' /\
    no_unrecorded_backward_edge g' rh' /\
    safe_to_copy_heap g' h' /\
    remset_compatible g' outlier O rmst rh' h' /\
    remset_generation_compatible O rmst rh'.
Proof.
  intros g src pos new g' h rootpairs roots outlier rmst rh
         Hloc Hext Hupd Hcapacity Hsuper Hgcc Hunrecorded Hsafe Hremset Hremgen.
  simpl.
  assert (Hghc: graph_heap_compatible g h) by exact (proj1 Hsuper).
  assert (Hrhhc: remset_heap_and_heap_compatible rh h).
  { exact (proj2 (proj2 Hremset)). }
  assert (Hrange: 0 <= Z.of_nat O < Zlength rh).
  { eapply gen_range_remset_heap; eauto. apply graph_has_gen_O. }
  split.
  - eapply mutable_update_super_compatible; eauto.
  - split.
    + eapply mutable_update_garbage_collect_condition; eauto.
    + split.
      * eapply mutable_graph_update_no_unrecorded_backward_edge; eauto.
      * split.
        -- eapply mutable_update_safe_to_copy_heap; eauto.
        -- split.
           ++ eapply mutable_update_remset_compatible; eauto.
           ++ eapply mutable_update_remset_generation_compatible; eauto.
Qed.
