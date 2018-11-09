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

Definition sound_gc_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g.

(** Reset is sound *)

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

Lemma reset_sound: forall (g: LGraph) gen,
    sound_gc_graph g -> sound_gc_graph (reset_graph gen g).
Proof.
  intros. destruct H as [? [? ?]]. split; [|split].
  - apply vertex_valid_reset; auto.
  - apply edge_valid_reset; auto.
  - apply src_edge_reset; auto.
Qed.

(** Quasi-Isomorphism to Full-Isomorphism *)

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

Lemma get_edges_snd_NoDup: forall g v, NoDup (map snd (get_edges g v)).
Proof.
  intros. unfold get_edges. unfold make_fields. remember (raw_fields (vlabel g v)).
  clear Heql. remember O. clear Heqn g. revert n. induction l; intros; simpl.
  1: constructor. destruct a; [destruct s|]; simpl; [apply IHl..|].
  rewrite NoDup_cons_iff. split. 2: apply IHl. intro.
  apply list_in_map_inv in H. destruct H as [x [? ?]].
  rewrite <- filter_sum_right_In_iff in H0.
  apply In_nth with (d := field_t_inhabitant) in H0. destruct H0 as [p [? ?]].
  apply make_fields'_edge_depends_on_index in H1. 1: subst x; simpl in H; omega.
  rewrite make_fields'_eq_length in H0. rewrite Zlength_correct. split. 1: omega.
  apply Nat2Z.inj_lt; assumption.
Qed.

Lemma get_edges_map_map: forall g v,
    get_edges g v = map (fun idx => (v, idx)) (map snd (get_edges g v)).
Proof.
  intros. rewrite map_map. unfold get_edges, make_fields.
  remember (raw_fields (vlabel g v)). remember O. clear Heql Heqn. revert n.
  induction l; intros; simpl; auto; destruct a; [destruct s|];
    simpl; rewrite <- IHl; auto.
Qed.

Lemma get_edges_NoDup: forall g v, NoDup (get_edges g v).
Proof.
  intros. rewrite get_edges_map_map, <- combine_repeat_eq_map.
  apply NoDup_combine_r, get_edges_snd_NoDup.
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
  is_partial_graph g1 g2 /\
  exists (l: list (VType * VType)),
    roots2 = map (root_map (list_bi_map l)) roots1 /\
    (forall v1 v2,
        In (v1, v2) l ->
        vlabel g1 v1 = vlabel g2 v2 /\
        forall idx, In idx (map snd (get_edges g1 v1)) ->
                    (dst g2 (v2, idx) = dst g1 (v1, idx) \/
                     dst g2 (v2, idx) = list_bi_map l (dst g1 (v1, idx)))) /\
    let (from_l, to_l) := split l in
    from_gen_spec g1 roots1 from_l from /\ to_gen_spec g1 g2 to_l to /\
    forall v, vvalid g1 v -> ~ In v from_l -> vlabel g1 v = vlabel g2 v.

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

Lemma quasi_iso_reset_iso: forall g1 roots1 g2 roots2 from to,
    from <> to -> gc_graph_quasi_iso g1 roots1 g2 roots2 from to ->
    sound_gc_graph g2 -> sound_gc_graph g1 ->
    no_edge2gen g1 from -> no_edge2gen g2 from -> no_dangling_dst g1 ->
    gc_graph_iso g1 roots1 (reset_graph from g2) roots2.
Proof.
  intros g1 roots1 g2 roots2 from to Hfr H H0 H1 H2 H3 H4.
  red in H. red. destruct H as [? [vpl [? [? ?]]]].
  destruct (split vpl) as [from_l to_l] eqn:? . destruct H7 as [[? ?] [[? [? ?N]] ?N]].
  assert (DoubleNoDup vpl). {
    apply (PairGenNoDup_DoubleNoDup _ from to). 1: omega. red. rewrite Heqp.
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
  destruct (reset_sound _ from H0) as [? [? ?]]. destruct H0 as [? [? ?]].
  destruct H1 as [? [? ?]]. unfold vertex_valid, edge_valid, src_edge in *.
  simpl in H14, H15, H16.
  assert (Hs: forall e, evalid g1 e -> vmap (src g1 e) = src g2 (emap e)). {
    intros. rewrite H19 in H21. destruct H21. rewrite H20 in *. rewrite <- H1 in H21.
    subst vmap emap. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H21 i). destruct H13 as [k [v [? [? ?]]]].
      rewrite H23, H24 in *. subst k. pose proof (gepl_key _ _ _ _ H22 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H23) as [? _]. rewrite H25.
      rewrite H18. simpl. reflexivity.
    - rewrite !list_bi_map_not_In; auto. intro; apply n; apply gepl_InEither in H23.
      auto. }
  assert (Hd: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) e ->
             vmap (dst g1 e) = dst g2 (emap e)). {
    intros. simpl in H21. destruct H21 as [? [? ?]]. pose proof H21.
    rewrite H19 in H21. destruct H21. rewrite H20 in *. rewrite <- H1 in H21.
    assert (~ In (dst g1 e) to_l). {
      intro. rewrite H10 in H26. destruct H26.
      apply reachable_through_set_foot_valid in H23. contradiction. }
    subst vmap emap. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H21 i). destruct H13 as [k [v [? [? ?]]]]. subst k.
      pose proof (gepl_key _ _ _ _ H25 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H27) as [? _]. rewrite H29.
      destruct (H6 _ _ H13) as [? ?]. rewrite get_edges_inv in H25.
      destruct H25 as [idx [? ?]]. rewrite H25 in *. simpl in *.
      specialize (H31 _ H32). destruct H31; auto. rewrite <- H25 in *.
      destruct (InEither_dec (dst g1 e) vpl).
      2: rewrite list_bi_map_not_In; auto. red in i0. rewrite Heqp in i0.
      rewrite in_app_iff in i0. destruct i0. 2: contradiction.
      rewrite <- H8 in H33. destruct H33 as [_ ?]. exfalso.
      assert (graph_has_e g2 (v, idx)). {
        split; simpl.
        - rewrite <- H12 in H13. apply in_combine_r in H13.
          rewrite H10 in H13. destruct H13. rewrite <- H0. assumption.
        - apply In_snd_get_edges. apply vlabel_get_edges_snd in H30.
          rewrite <- H30. assumption. } destruct v as [vgen vidx].
      assert (vgen = to). {
        rewrite <- H12 in H13. apply in_combine_r in H13. apply N in H13.
        simpl in H13. assumption. } subst vgen. assert (to <> from) by omega.
      specialize (H3 _ H35 vidx (snd e)).
      simpl in H3. rewrite H25 in *. simpl in *. apply H3; auto.
      change (prod nat nat) with VType. rewrite H31; auto.
    - assert (~ InEither (dst g1 e) vpl). {
        intro. unfold InEither in H27. rewrite Heqp, in_app_iff in H27.
        destruct H27; auto. rewrite <- H8 in H27. destruct H27 as [_ ?].
        assert (vgeneration (fst e) <> from). {
          intro. apply n. unfold InEither. rewrite Heqp, in_app_iff. left.
          rewrite <- H8. split; auto. }
        assert (graph_has_e g1 e) by (split; [rewrite <- H1|]; auto).
        destruct e as [[vgen vidx] eidx] eqn:? . simpl in H28.
        specialize (H2 _ H28 vidx eidx). simpl in H2. specialize (H2 H29).
        contradiction. } rewrite !list_bi_map_not_In; auto.
      2: intro; apply n; apply gepl_InEither in H28; auto.
      destruct H as [_ [_ [_ ?]]]. apply H; auto.
      apply reachable_through_set_foot_valid in H23. auto. }
  assert (He: forall e,
             evalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) e ->
             evalid (remove_nth_gen_ve g2 from) (emap e)). {
    intros. rewrite Heqemap. simpl in H21. destruct H21 as [? [? ?]]. pose proof H21.
    rewrite H15, graph_has_e_reset. rewrite H19 in H21. destruct H21.
    rewrite <- H1 in H21. destruct (InEither_dec (fst e) vpl).
    - specialize (H13 _ H21 i) as [k [v [? [? ?]]]]. subst k.
      pose proof (gepl_key _ _ _ _ H25 H13).
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H26) as [? _]. rewrite H28.
      unfold graph_has_e, egeneration. simpl. rewrite <- H0. pose proof H13.
      rewrite <- H12 in H13. apply in_combine_r in H13. pose proof H13.
      rewrite H10 in H13. destruct H13 as [? _]. apply N in H30. rewrite H30.
      split; [split|]; [auto | | omega]. rewrite get_edges_inv in H25.
      destruct H25 as [idx [? ?]]. rewrite H25. simpl. apply H6 in H29.
      destruct H29 as [? _]. apply vlabel_get_edges_snd in H29.
      rewrite get_edges_In, <- H29. assumption.
    - rewrite list_bi_map_not_In, <- H17.
      2: intro; apply n; apply gepl_InEither in H26; auto. split.
      1: destruct H as [_ [? _]]; apply H; auto. unfold egeneration. intro.
      apply n. red. rewrite Heqp, in_app_iff, <- H8. left. symmetry in H26.
      rewrite H20 in H22. split; assumption. }
  assert (Hv: forall x,
             vvalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) x ->
             vvalid (remove_nth_gen_ve g2 from) (vmap x)). {
    intros. simpl in H21. destruct H21. rewrite Heqvmap in *. rewrite H14.
    rewrite graph_has_v_reset. destruct (InEither_dec x vpl).
    - specialize (H13 _ H21 i). destruct H13 as [v1 [v2 [? [? ?]]]].
      subst x; rewrite H24. rewrite <- H12 in H13. apply in_combine_r in H13.
      pose proof H13. apply N in H13. rewrite H10 in H23. destruct H23 as [? _].
      rewrite <- H0. split; auto. omega.
    - rewrite list_bi_map_not_In; auto. destruct H as [? _]. rewrite <- H0.
      split. 1: apply H; auto. intro. apply n. clear n. red.
      rewrite Heqp, in_app_iff. left. rewrite <- H8. split; auto. }
  assert (Hp: forall v,
             vvalid (reachable_sub_labeledgraph g1 (filter_sum_right roots1)) v ->
             reachable_through_set (remove_nth_gen_ve g2 from)
                                   (filter_sum_right roots2) (vmap v)). {
    intros. simpl in H21. destruct H21. unfold reachable_through_set in H22 |-* .
    destruct H22 as [s [? ?]].
    assert (forall x, reachable g1 s x ->
                      reachable_through_set g1 (filter_sum_right roots1) x) by
        (intros; exists s; split; assumption).
    rewrite <- filter_sum_right_In_iff in H22.
    apply (in_map (root_map vmap)) in H22. rewrite <- H5 in H22.
    simpl in H22. apply filter_sum_right_In_iff in H22. exists (vmap s).
    split; auto. unfold reachable, reachable_by in H23. destruct H23 as [p ?].
    assert (forall e, In e (snd p) -> evalid (reachable_sub_labeledgraph
                                                g1 (filter_sum_right roots1)) e). {
      intros. simpl. split.
      - destruct H23 as [? [? ?]]. destruct p. eapply valid_path_evalid; eauto.
      - destruct (reachable_path_edge_in _ _ _ _ H23 _ H25).
        apply H24 in H26. apply H24 in H27. split; assumption. }
    destruct H23 as [[? ?] [? ?]]. unfold reachable, reachable_by.
    destruct p. simpl in H23. subst v0. simpl snd in *.
    assert (forall e, In e l -> vmap (src g1 e) = src g2 (emap e) /\
                                vmap (dst g1 e) = dst g2 (emap e)). {
      intros. split; [apply Hs | apply Hd]; auto. apply H25 in H23. simpl in H23.
      destruct H23. assumption. } clear H25. exists (vmap s, map emap l).
    assert (Hvp: valid_path (remove_nth_gen_ve g2 from) (vmap s, map emap l)). {
      clear H22 H26 H28. revert s H23 H24 H27. induction l; intros.
      - simpl in *. apply Hv. split; auto. apply H24, reachable_refl; auto.
      - simpl map. rewrite valid_path_cons_iff in *. destruct H27 as [? [? ?]].
        rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged.
        assert (In a (a :: l)) by (left; reflexivity). apply H23 in H27.
        destruct H27. rewrite H22, H27, <- H28. split; auto. split.
        + red. rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged,<- H27, <- H28.
          destruct H25 as [? [? ?]]. subst s.
          assert (reachable g1 (src g1 a) (src g1 a)) by
              (apply reachable_refl; auto).
          assert (reachable g1 (src g1 a) (dst g1 a)). {
            apply step_reachable with (dst g1 a); auto.
            2: apply reachable_refl; auto. exists a; auto. }
          split; [|split; apply Hv]; [apply He | | ]; simpl; split; auto.
        + apply IHl; auto. 1: intros; apply H23; right; assumption.
          intros. apply H24. apply step_reachable with (dst g1 a); auto.
          2: destruct H25 as [_ [? _]]; subst s; assumption. exists a; auto.
          destruct H25; assumption. } split; split; auto.
    - destruct l. 1: simpl in H26 |-* ; rewrite H26; reflexivity.
      assert (e :: l <> nil) by (intro HS; inversion HS).
      apply exists_last in H25. destruct H25 as [l' [a ?]]. rewrite e0 in *.
      rewrite map_app. simpl map. rewrite pfoot_last in H26 |-* .
      rewrite remove_ve_dst_unchanged. assert (In a (l' +:: a)) by
          (rewrite in_app_iff; right; left; reflexivity). apply H23 in H25.
      destruct H25. rewrite <- H26, H29. reflexivity.
    - rewrite path_prop_equiv; auto. }
  assert (Nv: forall x, from <> vgeneration x -> InEither x vpl ->
                        exists k v, In (k, v) vpl /\ x = v /\ list_bi_map vpl x = k). {
    intros. apply (list_bi_map_In vpl x) in H22. destruct H22 as [k [v [? ?]]].
    exists k, v. destruct H23; auto. destruct H23. subst x. rewrite <- H12 in H22.
    apply in_combine_l in H22. rewrite <- H8 in H22. destruct H22 as [_ ?].
    exfalso. apply H21. subst from. reflexivity. }
  assert (Hv': forall v, vvalid (remove_nth_gen_ve g2 from) v -> vvalid g1 (vmap v)). {
    intros. rewrite H14 in H21. rewrite graph_has_v_reset in H21. destruct H21.
    rewrite <- H0 in H21. subst vmap. destruct (InEither_dec v vpl).
    - specialize (Nv _ H22 i). destruct Nv as [v1 [v2 [? [? ?]]]]. subst v.
      rewrite H25. rewrite <- H12 in H23. apply in_combine_l in H23.
      rewrite <- H8 in H23. destruct H23.
      apply reachable_through_set_foot_valid in H23. assumption.
    - rewrite list_bi_map_not_In; auto.
      destruct (vvalid_lcm _ v H1); auto. exfalso. apply n. red.
      rewrite Heqp, in_app_iff. right. rewrite H10. split; assumption. }
  assert (He': forall e, evalid (remove_nth_gen_ve g2 from) e -> evalid g1 (emap e)). {
    intros. rewrite H15, graph_has_e_reset in H21. destruct H21 as [[? ?] ?].
    rewrite Heqemap. destruct (InEither_dec (fst e) vpl).
    - unfold egeneration in H23. specialize (Nv _ H23 i).
      destruct Nv as [k [v [? [? ?]]]]; subst v. destruct (H6 _ _ H24) as [? _].
      eapply gepl_value in H25; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H25) as [_ ?].
      rewrite H19, H27. split; simpl.
      + rewrite <- H12 in H24. apply in_combine_l in H24. rewrite <- H8 in H24.
        destruct H24. apply reachable_through_set_foot_valid in H24.
        rewrite <- H1. assumption.
      + rewrite get_edges_In. rewrite get_edges_inv in H22.
        destruct H22 as [idx [? ?]]. rewrite H22 in *. simpl in *.
        destruct (H6 _ _ H24) as [? _]. apply vlabel_get_edges_snd in H29.
        rewrite H29. assumption.
    - rewrite <- H0 in H21. destruct (vvalid_lcm _ (fst e) H1).
      2: { exfalso. apply n. red. rewrite Heqp, in_app_iff. right.
           rewrite H10. split; assumption. } rewrite list_bi_map_not_In.
      + rewrite H19. split; simpl. 1: rewrite <- H1. auto.
        rewrite get_edges_inv in H22 |-* . destruct H22 as [idx [? ?]].
        exists idx. split; auto. rewrite (vlabel_get_edges_snd _ (fst e) _ g2); auto.
        apply N0; auto. intro. apply n. red. rewrite Heqp, in_app_iff. left; auto.
      + intro; apply n; apply gepl_InEither in H25; simpl in H25; assumption. }
  assert (Hs': forall e, evalid (remove_nth_gen_ve g2 from) e ->
                         vmap (src g2 e) = src g1 (emap e)). {
    intros. rewrite H15, graph_has_e_reset in H21. destruct H21 as [[? ?] ?].
    rewrite H18. subst vmap emap. unfold egeneration in H23.
    destruct (InEither_dec (fst e) vpl).
    - specialize (Nv _ H23 i). destruct Nv as [k [v [? [? ?]]]]. rewrite <- H25 in *.
      destruct (H6 _ _ H24) as [? _]. eapply gepl_value in H27; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H27) as [_ ?].
      rewrite H20, H26, H28. simpl. reflexivity.
    - rewrite !list_bi_map_not_In; auto. intro. apply gepl_InEither in H24. auto. }
  assert (Hvb: bijective vmap vmap) by (subst; apply bijective_list_bi_map; auto).
  assert (Hd': forall e,
             evalid (reachable_sub_labeledgraph
                       (reset_graph from g2) (filter_sum_right roots2)) e ->
             vmap (dst g2 e) = dst g1 (emap e)). {
    intros. destruct H21 as [? [? ?]]. simpl in H23. pose proof H21. rename H24 into E.
    rewrite remove_ve_dst_unchanged in H23. rewrite H15, graph_has_e_reset in H21.
    apply reachable_through_set_foot_valid in H23. destruct H21 as [[? ?] ?].
    rewrite H14, graph_has_v_reset in H23. destruct H23.
    assert (~ In (dst g2 e) from_l) by
        (intro; rewrite <- H8 in H27; destruct H27 as [_ ?]; auto).
    subst vmap emap. unfold egeneration in H25. destruct (InEither_dec (fst e) vpl).
    - specialize (Nv _ H25 i). destruct Nv as [k [v [? [? ?]]]]. rewrite <- H29 in *.
      destruct (H6 _ _ H28) as [? ?]. pose proof H31. eapply gepl_value in H31; eauto.
      destruct (DoubleNoDup_list_bi_map _ _ _ Hn H31) as [_ ?]. rewrite H34.
      rewrite H29 in *. destruct e as [? idx]. simpl in H29. subst v0. simpl in *.
      rewrite get_edges_In in H24. apply vlabel_get_edges_snd in H33.
      rewrite <- H33 in H24. specialize (H32 _ H24). destruct H32.
      2: rewrite H29, (surjective _ _ Hvb); reflexivity.
      destruct (InEither_dec (dst g2 (v, idx)) vpl).
      2: rewrite list_bi_map_not_In; auto. red in i0. rewrite Heqp, in_app_iff in i0.
      destruct i0. 1: contradiction. rewrite H10 in H32. destruct H32 as [_ ?].
      assert (graph_has_v g1 k). {
        rewrite <- H1. rewrite <- H12 in H28. apply in_combine_l in H28.
        rewrite <- H8 in H28. destruct H28 as [? _].
        apply reachable_through_set_foot_valid in H28. assumption. }
      rewrite <- get_edges_In in H24. specialize (H4 _ H35 _ H24).
      rewrite H29 in H32. rewrite <- H1 in H4. contradiction.
    - assert (~ InEither e (gen_edge_pair_list g1 vpl)) by
          (intro; apply gepl_InEither in H28; auto). apply He' in E.
      rewrite list_bi_map_not_In in E; auto. pose proof E.
      rewrite H19 in H29. destruct H29. specialize (H4 _ H29 _ H30).
      rewrite <- H1 in H4. destruct H as [_ [_ [_ ?]]]. specialize (H _ E H4).
      rewrite <- H. rewrite !list_bi_map_not_In; auto. rewrite H. intro. red in H31.
      rewrite Heqp, in_app_iff in H31. destruct H31; auto. rewrite <- H in H31.
      rewrite H10 in H31. destruct H31. contradiction. }
  assert (Hp': forall v,
             vvalid (reachable_sub_labeledgraph (reset_graph from g2)
                                                (filter_sum_right roots2)) v ->
             reachable_through_set g1 (filter_sum_right roots1) (vmap v)). {
    intros. simpl in H21. destruct H21. unfold reachable_through_set in H22 |-* .
    destruct H22 as [s [? ?]].
    assert (forall x, reachable (remove_nth_gen_ve g2 from) s x ->
                      reachable_through_set (remove_nth_gen_ve g2 from)
                                            (filter_sum_right roots2) x) by
        (intros; exists s; split; assumption).
    rewrite <- filter_sum_right_In_iff in H22. rewrite H5 in H22.
    apply (in_map (root_map vmap)) in H22.
    rewrite (surjective _ _ (bijective_map _ _ (bijective_root_map _ _ Hvb))) in H22.
    simpl in H22. apply filter_sum_right_In_iff in H22. exists (vmap s).
    split; auto. unfold reachable, reachable_by in H23. destruct H23 as [p ?].
    assert (forall e,
               In e (snd p) ->
               evalid (reachable_sub_labeledgraph
                         (remove_nth_gen_ve g2 from) (filter_sum_right roots2)) e). {
      intros. simpl. split.
      - destruct H23 as [? [? ?]]. destruct p. eapply valid_path_evalid; eauto.
      - destruct (reachable_path_edge_in _ _ _ _ H23 _ H25).
        apply H24 in H26. apply H24 in H27. split; assumption. }
    destruct H23 as [[? ?] [? ?]]. unfold reachable, reachable_by.
    destruct p. simpl in H23. subst v0. simpl snd in *.
    assert (forall e, In e l -> vmap (src g2 e) = src g1 (emap e) /\
                                vmap (dst g2 e) = dst g1 (emap e)). {
      intros. split; [apply Hs' | apply Hd']; auto. apply H25 in H23. simpl in H23.
      destruct H23. assumption. } clear H25. exists (vmap s, map emap l).
    assert (Hvp: valid_path g1 (vmap s, map emap l)). {
      clear H22 H26 H28. revert s H23 H24 H27. induction l; intros.
      - simpl in *. apply Hv'; auto.
      - simpl map. rewrite valid_path_cons_iff in *. destruct H27 as [? [? ?]].
        rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged in *.
        assert (In a (a :: l)) by (left; reflexivity). apply H23 in H27.
        destruct H27. rewrite H22, H27, <- H28. split; auto. split.
        + red. rewrite <- H27, <- H28. destruct H25 as [? [? ?]]. subst s.
          rewrite remove_ve_src_unchanged in H29.
          rewrite remove_ve_dst_unchanged in H30.
          assert (reachable (remove_nth_gen_ve g2 from) (src g2 a) (src g2 a)) by
              (apply reachable_refl; auto).
          assert (reachable (remove_nth_gen_ve g2 from) (src g2 a) (dst g2 a)). {
            apply step_reachable with (dst g2 a); auto.
            2: apply reachable_refl; auto. exists a; auto.
            - rewrite remove_ve_src_unchanged. reflexivity.
            - rewrite remove_ve_dst_unchanged. reflexivity. }
          split; [|split; apply Hv']; [apply He' | | ]; auto.
        + apply IHl; auto. 1: intros; apply H23; right; assumption.
          intros. apply H24. apply step_reachable with (dst g2 a); auto.
          * exists a; auto; [destruct H25 | rewrite remove_ve_src_unchanged |
                             rewrite remove_ve_dst_unchanged]; auto.
          * destruct H25 as [_ [? _]]; subst s;
              rewrite remove_ve_src_unchanged in H25; assumption. } split; split; auto.
    - destruct l. 1: simpl in H26 |-* ; rewrite H26; reflexivity.
      assert (e :: l <> nil) by (intro HS; inversion HS).
      apply exists_last in H25. destruct H25 as [l' [a ?]]. rewrite e0 in *.
      rewrite map_app. simpl map. rewrite pfoot_last in H26 |-* .
      rewrite remove_ve_dst_unchanged in H26. assert (In a (l' +:: a)) by
          (rewrite in_app_iff; right; left; reflexivity). apply H23 in H25.
      destruct H25. rewrite <- H26, H29. reflexivity.
    - rewrite path_prop_equiv; auto. }
  exists vmap, vmap, emap, emap. split; auto. constructor; intros.
  - constructor; intros; auto.
    + subst. apply bijective_list_bi_map; assumption.
    + simpl. split; [apply Hv | apply Hp]; assumption.
    + simpl. split; [apply Hv' | apply Hp']; auto. destruct H21; assumption.
    + simpl. split. 1: apply He; assumption.
      rewrite remove_ve_src_unchanged, remove_ve_dst_unchanged, <- Hd, <- Hs; auto.
      2: destruct H21; auto. destruct H21 as [? [? ?]].
      split; apply Hp; simpl; split; auto;
        eapply reachable_through_set_foot_valid; eauto.
    + simpl. split; [apply He' | rewrite <- Hs', <- Hd']; auto;
               destruct H21 as [? [? ?]]; auto. simpl src in H22. simpl dst in H23.
      rewrite remove_ve_src_unchanged in H22. rewrite remove_ve_dst_unchanged in H23.
      split; apply Hp'; simpl; split; auto;
        eapply reachable_through_set_foot_valid; eauto.
    + simpl. rewrite remove_ve_src_unchanged. destruct H21 as [? _]. apply Hs. auto.
    + simpl. rewrite remove_ve_dst_unchanged. apply Hd; auto.
  - simpl in H21. destruct H21. simpl. rewrite remove_ve_vlabel_unchanged.
    subst vmap. destruct (InEither_dec v vpl).
    + specialize (H13 _ H21 i). destruct H13 as [v1 [v2 [? [? ?]]]].
      specialize (H6 _ _ H13). subst v. rewrite H24. destruct H6; auto.
    + rewrite list_bi_map_not_In; auto. apply N0; auto. intro. apply n. red.
      rewrite Heqp, in_app_iff. left; assumption.
  - simpl. destruct (elabel g1 e).
    destruct (elabel (remove_nth_gen_ve g2 from) (emap e)). reflexivity.
Qed.

(** Other graph relation is sound *)

Lemma ngr_graph_has_gen: forall g1 g2 gen,
    graph_has_gen g1 gen -> new_gen_relation (S gen) g1 g2 -> graph_has_gen g2 (S gen).
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 (S gen)). 1: subst; auto.
  destruct H0 as [gen_i [? ?]]. subst. rewrite ang_graph_has_gen. right.
  unfold graph_has_gen in H, n. omega.
Qed.

Lemma gcl_graph_has_gen: forall fi s n g1 g2 r1 r2,
    graph_has_gen g1 s ->
    garbage_collect_loop fi (nat_seq s n) r1 g1 r2 g2 -> graph_has_gen g2 (s + n).
Proof.
  do 3 intro. revert s. induction n; intros; simpl in H0; inversion H0; subst.
  - rewrite Nat.add_0_r. assumption.
  - apply ngr_graph_has_gen in H3; auto. erewrite do_gen_graph_has_gen in H3; eauto.
    apply IHn in H9; auto. rewrite <- Nat.add_succ_comm. assumption.
Qed.

Lemma ngr_vertex_valid: forall g1 g2 gen,
    vertex_valid g1 -> new_gen_relation gen g1 g2 -> vertex_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst. assumption.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold vertex_valid in *. intros. simpl.
    rewrite H. split; intros.
    + apply ang_graph_has_v; assumption.
    + apply ang_graph_has_v_inv in H1; assumption.
Qed.

Lemma ngr_edge_valid: forall g1 g2 gen,
    edge_valid g1 -> new_gen_relation gen g1 g2 -> edge_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst. assumption.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold edge_valid in *. intros. simpl.
    rewrite H. split; intros; destruct H1; split; try assumption.
    + apply ang_graph_has_v; assumption.
    + apply ang_graph_has_v_inv in H1; assumption.
Qed.

Lemma ngr_src_edge: forall g1 g2 gen,
    src_edge g1 -> new_gen_relation gen g1 g2 -> src_edge g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst. assumption.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold src_edge in *. simpl. assumption.
Qed.

Lemma ngr_sound: forall g1 g2 gen,
    sound_gc_graph g1 -> new_gen_relation gen g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? ?]]. split; [|split].
  - eapply ngr_vertex_valid; eauto.
  - eapply ngr_edge_valid; eauto.
  - eapply ngr_src_edge; eauto.
Qed.

Section GENERAL_GRAPH_PROP.

  Hypothesis P: LGraph -> Prop.

  Hypothesis fr_O_P_holds: forall g1 g2 from to p,
      P g1 -> graph_has_gen g1 to -> forward_relation from to O p g1 g2 -> P g2.

  Lemma frl_P_holds: forall from to l g1 g2 r1 r2 fi,
      P g1 -> graph_has_gen g1 to ->
      forward_roots_loop from to fi l r1 g1 r2 g2 -> P g2.
  Proof.
    do 3 intro. induction l; intros; inversion H1; subst; auto.
    eapply (IHl g3); eauto. rewrite <- fr_graph_has_gen; eauto.
  Qed.

  Lemma frr_P_holds: forall from to fi r1 r2 g1 g2,
      P g1 -> graph_has_gen g1 to ->
      forward_roots_relation from to fi r1 g1 r2 g2 -> P g2.
  Proof. intros. red in H1. eapply frl_P_holds; eauto. Qed.

  Lemma svfl_P_holds: forall from to v l g1 g2,
      P g1 -> graph_has_gen g1 to ->
      scan_vertex_for_loop from to v l g1 g2 -> P g2.
  Proof.
    do 4 intro. induction l; intros; inversion H1; subst; auto. apply (IHl g3); auto.
    - eapply fr_O_P_holds; eauto.
    - erewrite <- fr_graph_has_gen; eauto.
  Qed.

  Lemma svwl_P_holds: forall from to l g1 g2,
    P g1 -> graph_has_gen g1 to ->
    scan_vertex_while_loop from to l g1 g2 -> P g2.
  Proof.
    do 3 intro. induction l; intros; inversion H1; subst; auto. 1: eapply IHl; eauto.
    apply (IHl g3); eauto.
    - eapply svfl_P_holds; eauto.
    - erewrite <- svfl_graph_has_gen; eauto.
  Qed.

  Lemma dsr_P_holds: forall g1 g2 from to to_index,
      P g1 -> graph_has_gen g1 to ->
      do_scan_relation from to to_index g1 g2 -> P g2.
  Proof. intros. destruct H1 as [n [? ?]]. eapply svwl_P_holds; eauto. Qed.

  Hypothesis reset_P_holds: forall g gen, P g -> P (reset_graph gen g).

  Lemma do_gen_P_holds: forall from to fi r1 r2 g1 g2,
      P g1 -> graph_has_gen g1 to ->
      do_generation_relation from to fi r1 r2 g1 g2 -> P g2.
  Proof.
    intros. destruct H1 as [g3 [g4 [? [? ?]]]]. subst g2. apply reset_P_holds.
    eapply (dsr_P_holds g3); eauto.
    - eapply frr_P_holds; eauto.
    - rewrite <- frr_graph_has_gen; eauto.
  Qed.

  Hypothesis ngr_P_holds: forall g1 g2 gen, P g1 -> new_gen_relation gen g1 g2 -> P g2.

  Lemma gcl_P_holds: forall fi s n g1 g2 r1 r2,
      P g1 -> graph_has_gen g1 s ->
      garbage_collect_loop fi (nat_seq s n) r1 g1 r2 g2 -> P g2.
  Proof.
    do 3 intro. revert s. induction n; intros; simpl in H1; inversion H1; subst; auto.
    clear H1. assert (graph_has_gen g3 (S s)) by (apply ngr_graph_has_gen in H4; auto).
    eapply (IHn (S s) g4); eauto.
    - eapply (do_gen_P_holds _ _ _ _ _ g3); eauto.
    - erewrite <- (do_gen_graph_has_gen _ _ _ _ _ g3); eauto.
  Qed.

  Lemma gc_P_holds: forall fi r1 r2 g1 g2,
      P g1 -> garbage_collect_relation fi r1 r2 g1 g2 -> P g2.
  Proof.
    intros. red in H0. destruct H0 as [n [? ?]]. unfold nat_inc_list in H0.
    apply gcl_P_holds in H0; auto. apply graph_has_gen_O.
  Qed.

End GENERAL_GRAPH_PROP.

Lemma cvae_vvalid_iff: forall g v' l v0,
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

Lemma pcv_vvalid_iff: forall g v v' new,
    vvalid (pregraph_copy_v g v new) v' <-> vvalid g v' \/ v' = new.
Proof.
  intros. unfold pregraph_copy_v. rewrite cvae_vvalid_iff. simpl.
  unfold addValidFunc. reflexivity.
Qed.

Lemma lcv_graph_has_v_iff: forall (g : LGraph) (v : VType) (to : nat) (x : VType),
  graph_has_gen g to ->
  graph_has_v (lgraph_copy_v g v to) x <-> graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. split; intros.
  - apply lcv_graph_has_v_inv in H0; assumption.
  - destruct H0; [apply lcv_graph_has_v_old | subst x; apply lcv_graph_has_v_new];
      assumption.
Qed.

Lemma lcv_vertex_valid: forall g v to,
    vertex_valid g -> graph_has_gen g to -> vertex_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold vertex_valid in *. intros. simpl.
  rewrite pcv_vvalid_iff, lcv_graph_has_v_iff; auto. rewrite H. reflexivity.
Qed.

Lemma fr_O_vertex_valid: forall g g' from to p,
    vertex_valid g -> graph_has_gen g to -> forward_relation from to 0 p g g' ->
    vertex_valid g'.
Proof.
  intros. inversion H1; subst; try assumption.
  - apply lcv_vertex_valid; assumption.
  - replace (vertex_valid new_g) with
        (vertex_valid (lgraph_copy_v g (dst g e) to)) by (subst new_g; reflexivity).
    apply lcv_vertex_valid; assumption.
Qed.

Lemma lcv_get_edges_old: forall (g: LGraph) v v' to,
    graph_has_v g v' -> graph_has_gen g to ->
    get_edges (lgraph_copy_v g v to) v' = get_edges g v'.
Proof.
  intros. unfold get_edges, make_fields.
  erewrite <- lcv_raw_fields by assumption. reflexivity.
Qed.

Lemma cvae_evalid_iff: forall g v l e,
    evalid (fold_left (copy_v_add_edge v) l g) e <-> evalid g e \/ In e (map fst l).
Proof.
  intros. revert g. induction l; intros; simpl. 1: intuition. rewrite IHl.
  unfold copy_v_add_edge. simpl. unfold addValidFunc. intuition.
Qed.

Lemma pcv_evalid_iff: forall g v new e,
    evalid (pregraph_copy_v g v new) e <->
    evalid g e \/ In e (map (fun x => (new, snd x)) (get_edges g v)).
Proof.
  intros. unfold pregraph_copy_v. rewrite cvae_evalid_iff. rewrite map_fst_combine.
  - replace (length (get_edges g v)) with (length (map snd (get_edges g v))) by
        (rewrite map_length; reflexivity). rewrite combine_repeat_eq_map, map_map.
    reflexivity.
  - unfold EType at 1. rewrite combine_length, repeat_length, !map_length.
    apply Nat.min_id.
Qed.

Lemma lcv_lacv_get_edges: forall g v to new,
    get_edges (lgraph_copy_v g v to) new = get_edges (lgraph_add_copied_v g v to) new.
Proof.
  intros. unfold lgraph_copy_v, get_edges, make_fields. rewrite <- lmc_raw_fields.
  reflexivity.
Qed.

Lemma lcv_edge_valid: forall g v to,
    edge_valid g -> graph_has_gen g to -> edge_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold edge_valid in *. intros. unfold graph_has_e in *. simpl.
  rewrite pcv_evalid_iff, lcv_graph_has_v_iff, H; auto. split; intros.
  - destruct H1 as [[? ?] | ?].
    + split. 1: left; assumption. rewrite lcv_get_edges_old; auto.
    + assert (fst e = new_copied_v g to). {
        apply list_in_map_inv in H1; destruct H1 as [x [? ?]]; subst e; simpl; auto. }
      split. 1: right; assumption. rewrite H2.
      rewrite get_edges_map_map, lcv_lacv_get_edges, lacv_get_edges_new, map_map.
      assumption.
  - destruct H1. destruct H1; [left | right].
    + split; auto. rewrite lcv_get_edges_old in H2; assumption.
    + rewrite H1 in H2.
      rewrite get_edges_map_map, lcv_lacv_get_edges, lacv_get_edges_new, map_map in H2.
      assumption.
Qed.

Lemma fr_O_edge_valid: forall g1 g2 from to p,
    edge_valid g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> edge_valid g2.
Proof.
  intros. inversion H1; subst; try assumption.
  - apply lcv_edge_valid; assumption.
  - replace (edge_valid new_g) with
        (edge_valid (lgraph_copy_v g1 (dst g1 e) to)) by (subst new_g; reflexivity).
    apply lcv_edge_valid; assumption.
Qed.

Lemma flcvae_src_old: forall g new (l: list (EType * VType)) e,
    ~ In e (map fst l) -> src (fold_left (copy_v_add_edge new) l g) e = src g e.
Proof.
  intros. revert g H. induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption. simpl.
  unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

Lemma flcvae_src_new: forall g new (l: list (EType * VType)) e,
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

Lemma lcv_src_edge: forall g v to,
    src_edge g -> src_edge (lgraph_copy_v g v to).
Proof.
  intros. unfold src_edge in *. intros. simpl. unfold pregraph_copy_v.
  remember (new_copied_v g to) as new.
  replace (length (get_edges g v)) with (length (map snd (get_edges g v))) by
      (rewrite map_length; reflexivity). remember (get_edges g v) as el.
  remember (combine (combine (repeat new (Datatypes.length (map snd el))) (map snd el))
                    (map (dst g) el)) as l. destruct (in_dec equiv_dec e (map fst l)).
  - rewrite flcvae_src_new; auto. subst new.
    rewrite combine_repeat_eq_map, map_map, combine_map_join in Heql.
    apply list_in_map_inv in i. destruct i as [x [? ?]]. subst l.
    apply list_in_map_inv in H1. destruct H1 as [x0 [? ?]]. subst x e. simpl. auto.
  - rewrite flcvae_src_old; auto. simpl. apply H.
Qed.

Lemma fr_O_src_edge: forall g1 g2 from to p,
    src_edge g1 -> forward_relation from to O p g1 g2 -> src_edge g2.
Proof.
  intros. inversion H0; subst; try assumption.
  - apply lcv_src_edge; assumption.
  - replace (src_edge new_g) with
        (src_edge (lgraph_copy_v g1 (dst g1 e) to)) by (subst new_g; reflexivity).
    apply lcv_src_edge; assumption.
Qed.

Lemma fr_O_sound: forall g1 g2 from to p,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? ?]]. split; [|split].
  - eapply fr_O_vertex_valid; eauto.
  - eapply fr_O_edge_valid; eauto.
  - eapply fr_O_src_edge; eauto.
Qed.

Lemma gc_sound: forall fi r1 r2 g1 g2,
    sound_gc_graph g1 -> garbage_collect_relation fi r1 r2 g1 g2 ->
    sound_gc_graph g2.
Proof.
  intros. eapply gc_P_holds; eauto;
            [apply fr_O_sound | apply reset_sound | apply ngr_sound].
Qed.

