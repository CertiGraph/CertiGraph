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
  rewrite NoDup_app_iff. do 2 (split; auto). repeat intro. apply H1 in H4.
  apply H3 in H5. rewrite H4 in H5. contradiction.
Qed.

Definition from_gen_quasi_spec
           (g: LGraph) (roots: roots_t) (l: list VType) gen: Prop :=
  NoDup l /\ forall v,
    (reachable_through_set g (filter_sum_right roots) v /\ vgeneration v = gen) <->
    In v l.

Definition to_gen_spec (g1 g2: LGraph) (l: list VType) gen: Prop :=
  NoDup l /\ (forall v, In v l <-> vvalid g2 v /\ ~ vvalid g1 v) /\
  forall v, In v l -> vgeneration v = gen.

Definition roots_map (l: list (VType * VType)): roots_t -> roots_t :=
  map (root_map (list_bi_map l)).

Definition gc_graph_quasi_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t) (from to: nat): Prop :=
  is_partial_graph g1 g2 /\
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
  red in H. red. destruct H as [? [vpl [? [? ?]]]]. unfold roots_map in H5.
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

Lemma pcv_src_old: forall (g : LGraph) (old new : VType) (e : VType * nat),
    fst e <> new -> src (pregraph_copy_v g old new) e = src g e.
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_src_old. 1: now simpl.
  intro. apply H. rewrite map_fst_combine in H0.
  - destruct e. simpl in *. apply in_combine_l, repeat_spec in H0. assumption.
  - unfold EType. now rewrite combine_length, repeat_length, !map_length, Nat.min_id.
Qed.

Lemma pcv_src_new: forall (g : LGraph) (old new : VType) (n : nat),
       In n (map snd (get_edges g old)) ->
       src (pregraph_copy_v g old new) (new, n) = new.
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_src_new; auto.
  rewrite map_fst_combine.
  - replace (length (get_edges g old)) with (length (map snd (get_edges g old))) by
        now rewrite map_length. rewrite combine_repeat_eq_map, map_map.
    apply list_in_map_inv in H. destruct H as [[v idx] [? ?]]. simpl in H. subst idx.
    change (new, n) with ((fun x : VType * nat => (new, snd x)) (v, n)).
    now apply in_map.
  - unfold EType. now rewrite combine_length, repeat_length, !map_length, Nat.min_id.
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

(** Semi-Isomorphism **)

Definition from_gen_semi_spec (g1 g2: LGraph) (l: list VType) (gen: nat): Prop :=
  NoDup l /\ forall v,
    (raw_mark (vlabel g2 v) = true /\ vvalid g1 v /\ vgeneration v = gen) <->
    In v l.

Definition gc_graph_semi_iso
           (g1 g2: LGraph) (from to: nat) (l: list (VType * VType)): Prop :=
  is_partial_graph g1 g2 /\
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
    forall v, vvalid g1 v -> ~ In v from_l -> vlabel g1 v = vlabel g2 v.

Lemma semi_iso_refl: forall g from to,
    sound_gc_graph g -> gen_unmarked g from -> gc_graph_semi_iso g g from to nil.
Proof.
  intros. red. split; [|split]; intros.
  - apply is_partial_graph_refl.
  - inversion H1.
  - destruct (split []) eqn:? . simpl in Heqp. inversion Heqp. subst. clear Heqp.
    split; [|split].
    + red. split. 1: constructor. intros; split; intros. 2: inversion H1.
      destruct H1 as [? [? ?]]. destruct H as [? _]. red in H. rewrite H in H2.
      red in H0. destruct H2. rewrite H3 in *. destruct v as [? idx]. simpl in *.
      subst n. specialize (H0 H2 _ H4). rewrite H1 in H0. inversion H0.
    + red. split. 1: constructor. split; [split|]; intros; intuition.
    + intros. reflexivity.
Qed.

Lemma semi_iso_DoubleNoDup: forall g1 g2 from to l,
    from <> to -> gc_graph_semi_iso g1 g2 from to l -> DoubleNoDup l.
Proof.
  intros. destruct H0 as [_ [_ ?]]. destruct (split l) as [from_l to_l] eqn: ?.
  apply (PairGenNoDup_DoubleNoDup l from to); auto. red. rewrite Heqp.
  destruct H0 as [[? ?] [[? [? ?]] _]]. split; split; intros; auto.
  rewrite <- H1 in H5. destruct H5 as [_ [_ ?]]. assumption.
Qed.

Definition roots_unmarked (g: LGraph) (roots: roots_t): Prop :=
  forall v, In (inr v) roots -> raw_mark (vlabel g v) = false.

Lemma graph_roots_unmarked: forall g roots,
    graph_unmarked g -> roots_graph_compatible roots g -> roots_unmarked g roots.
Proof.
  intros. red in H, H0 |-* . intros. rewrite Forall_forall in H0. apply H, H0.
  rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma root_t_eq_dec: forall r1 r2: root_t, {r1 = r2} + {r1 <> r2}.
Proof.
  intros.
  destruct r1; [destruct s|]; (destruct r2; [destruct s|]); try (right; discriminate).
  - destruct (Z.eq_dec z z0). 1: subst; now left.
    right; intro HS. inversion HS. contradiction.
  - destruct g, g0. destruct (block_eq_dec b b0).
    + subst. destruct (Ptrofs.eq_dec i i0). 1: subst; now left.
      right. intro HS; apply n. inversion HS. reflexivity.
    + right. intros HS; apply n. inversion HS. reflexivity.
  - destruct (equiv_dec v v0); unfold equiv in *. 1: subst; now left.
    right. intro HS. apply c. inversion HS. easy.
Defined.

Lemma fold_left_upd_Znth_Zlength: forall
    {A : Type} {d : Inhabitant A} (f : A -> A) (ps : list Z) (l : list A),
    (forall e : Z, In e ps -> 0 <= e < Zlength l) ->
    Zlength
      (fold_left (fun (il : list A) (i : Z) => upd_Znth i il (f (Znth i il))) ps l) =
    Zlength l.
Proof.
  do 3 intro. induction ps; intros; simpl; auto.
  assert (Zlength (upd_Znth a l (f (Znth a l))) = Zlength l) by
      (rewrite upd_Znth_Zlength; auto; apply H; left; easy).
  rewrite IHps; auto. rewrite H0. intros. apply H. now right.
Qed.

Definition restricted_map {A} {d: Inhabitant A}
           (f: A -> A) (l: list A) (positions: list Z): list A :=
  fold_left (fun il i => upd_Znth i il (f (Znth i il))) positions l.

Lemma restricted_map_Zlength: forall {A} {d: Inhabitant A} f positions l,
    (forall e, In e positions -> 0 <= e < Zlength l) ->
    Zlength (restricted_map f l positions) = Zlength l.
Proof. intros. unfold restricted_map. apply fold_left_upd_Znth_Zlength. easy. Qed.

Lemma fold_left_upd_Znth_diff:
  forall (A : Type) (X : Inhabitant A) (f : A -> A) (ps : list Z) (l : list A) (i : Z),
    (forall e : Z, In e ps -> 0 <= e < Zlength l) -> ~ In i ps -> 0 <= i < Zlength l ->
    Znth i
         (fold_left (fun (il : list A) (i0 : Z) => upd_Znth i0 il (f (Znth i0 il)))
                    ps l) = Znth i l.
Proof.
  do 3 intro. induction ps; intros; simpl; auto.
  assert (Zlength (upd_Znth a l (f (Znth a l))) = Zlength l) by
      (rewrite upd_Znth_Zlength; auto; apply H; now left). rewrite IHps.
  - rewrite upd_Znth_diff; auto. 1: apply H; now left. intro. apply H0. now left.
  - rewrite H2. intros. apply H. now right.
  - intro. apply H0. now right.
  - rewrite H2. assumption.
Qed.

Lemma restricted_map_Znth_diff: forall {A} {d: Inhabitant A} f ps l i,
    (forall e, In e ps -> 0 <= e < Zlength l) -> ~ In i ps ->
    0 <= i < Zlength l -> Znth i (restricted_map f l ps) = Znth i l.
Proof. intros. unfold restricted_map. apply fold_left_upd_Znth_diff; assumption. Qed.

Lemma restricted_map_Znth_same: forall {A} {d: Inhabitant A} f ps l i,
    (forall e, In e ps -> 0 <= e < Zlength l) -> NoDup ps -> In i ps ->
    Znth i (restricted_map f l ps) = f (Znth i l).
Proof.
  do 3 intro. unfold restricted_map. induction ps; intros. 1: inversion H1.
  simpl. simpl in H1. assert (Zlength (upd_Znth a l (f (Znth a l))) = Zlength l). {
    rewrite upd_Znth_Zlength; auto. apply H. now left. } destruct H1.
  - subst i. rewrite fold_left_upd_Znth_diff.
    + rewrite upd_Znth_same; auto. apply H. now left.
    + rewrite H2. intros. apply H. now right.
    + apply NoDup_cons_2 in H0. assumption.
    + rewrite H2. apply H. now left.
  - rewrite IHps; auto.
    + rewrite upd_Znth_diff; auto; [apply H; now right | apply H; now left |].
      apply NoDup_cons_2 in H0. intro. apply H0. subst i. assumption.
    + intros. rewrite H2. apply H. now right.
    + apply NoDup_cons_1 in H0. assumption.
Qed.

Definition restricted_roots_map (index: Z) (f_info: fun_info)
           (roots: roots_t) (l: list (VType * VType)): roots_t :=
  restricted_map (root_map (list_map l)) roots
                 (get_roots_indices index (live_roots_indices f_info)).

Lemma restricted_roots_map_Zlength: forall index f_info roots l,
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Zlength (restricted_roots_map index f_info roots l) = Zlength roots.
Proof.
  intros. unfold restricted_roots_map. rewrite restricted_map_Zlength; auto.
  intros. rewrite get_roots_indices_spec in H0. destruct H0. rewrite <- H in H0. easy.
Qed.

Lemma collect_Z_indices_In_le:
  forall {A} {d: Inhabitant A} eqdec (target: A) (l: list A) (ind: Z) i,
    In i (collect_Z_indices eqdec target l ind) -> ind <= i.
Proof.
  do 4 intro. induction l; intros; simpl in H. 1: easy. if_tac in H.
  - simpl in H. destruct H; [|apply IHl in H]; omega.
  - apply IHl in H. omega.
Qed.

Lemma collect_Z_indices_NoDup:
  forall {A} {d: Inhabitant A} eqdec (target: A) (l: list A) (ind: Z),
    NoDup (collect_Z_indices eqdec target l ind).
Proof.
  do 4 intro. induction l; intros; simpl. 1: constructor. if_tac. 2: apply IHl.
  constructor. 2: apply IHl. intro; apply collect_Z_indices_In_le in H0; omega.
Qed.

Lemma restricted_roots_map_Znth_diff: forall z f_info roots l j,
  0 <= j < Zlength roots ->
  Zlength roots = Zlength (live_roots_indices f_info) ->
  Znth j (live_roots_indices f_info) <> Znth z (live_roots_indices f_info) ->
  Znth j (restricted_roots_map z f_info roots l) = Znth j roots.
Proof.
  intros. unfold restricted_roots_map. rewrite restricted_map_Znth_diff; auto.
  - intros. rewrite get_roots_indices_spec in H2. destruct H2. rewrite H0. easy.
  - intro. rewrite get_roots_indices_spec in H2. destruct H2. easy.
Qed.

Lemma get_roots_indices_NoDup: forall i l, NoDup (get_roots_indices i l).
Proof. intros. unfold get_roots_indices. apply collect_Z_indices_NoDup. Qed.

Lemma restricted_roots_map_Znth_same: forall z f_info roots l j,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
    Znth j (restricted_roots_map z f_info roots l) =
    root_map (list_map l) (Znth j roots).
Proof.
  intros. unfold restricted_roots_map. rewrite restricted_map_Znth_same; auto.
  - intros. rewrite get_roots_indices_spec in H2. destruct H2. rewrite H0. easy.
  - apply get_roots_indices_NoDup.
  - rewrite get_roots_indices_spec. split; [rewrite <- H0 |]; easy.
Qed.

Lemma rrm_non_vertex_id: forall index f_info (roots: roots_t) l,
    (forall v, Znth index roots <> inr v) -> 0 <= index < Zlength roots ->
    roots_fi_compatible roots f_info ->
    restricted_roots_map index f_info roots l = roots.
Proof.
  intros. apply Znth_list_eq. destruct H1. split.
  - rewrite restricted_roots_map_Zlength; easy.
  - intros. rewrite restricted_roots_map_Zlength in H3 by easy.
    destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                       (Znth index (live_roots_indices f_info))).
    + rewrite restricted_roots_map_Znth_same; auto. destruct (Znth j roots) eqn:? .
      * simpl. reflexivity.
      * exfalso. apply (H v). apply H2 in e; auto. rewrite <- e. easy.
    + rewrite restricted_roots_map_Znth_diff; auto.
Qed.

Lemma rrm_not_in_id: forall index f_info (roots: roots_t) l v,
    Znth index roots = inr v -> ~ In v (map fst l) -> 0 <= index < Zlength roots ->
    roots_fi_compatible roots f_info ->
    restricted_roots_map index f_info roots l = roots.
Proof.
  intros. apply Znth_list_eq. destruct H2. split.
  - rewrite restricted_roots_map_Zlength; easy.
  - intros. rewrite restricted_roots_map_Zlength in H4 by easy.
    destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                       (Znth index (live_roots_indices f_info))).
    + rewrite restricted_roots_map_Znth_same; auto. destruct (Znth j roots) eqn:? .
      * simpl. reflexivity.
      * apply H3 in e; auto. rewrite e, H in Heqr. inversion Heqr. subst v0.
        simpl. now rewrite list_map_not_In.
    + now rewrite restricted_roots_map_Znth_diff.
Qed.

Lemma rmm_eq_upd_bunch: forall z f_info (roots: roots_t) k v l,
    Znth z roots = inr k -> In (k, v) l -> 0 <= z < Zlength roots ->
    roots_fi_compatible roots f_info -> NoDup (map fst l) ->
    restricted_roots_map z f_info roots l = upd_bunch z f_info roots (inr v).
Proof.
  intros. destruct H2. apply Znth_list_eq. split.
  - now rewrite restricted_roots_map_Zlength, upd_bunch_Zlength.
  - intros. rewrite restricted_roots_map_Zlength in H5; auto.
    destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                       (Znth z (live_roots_indices f_info))).
    + rewrite restricted_roots_map_Znth_same, upd_bunch_same; auto.
      apply H4 in e; auto. rewrite e, H. simpl. now rewrite (list_map_In _ _ v).
    + rewrite restricted_roots_map_Znth_diff, upd_bunch_diff; auto.
Qed.

Definition semi_roots_map (f_info: fun_info) (l1 l2: list (VType * VType))
           (fp: forward_p_type) (roots: roots_t): roots_t :=
  match fp with
  | inl index => restricted_roots_map index f_info roots l2
  | inr _ => roots_map l2 (roots_map l1 roots)
  end.

Lemma pcv_is_partial_graph: forall (g: LGraph) old new,
    sound_gc_graph g -> ~ vvalid g new ->
    is_partial_graph g (pregraph_copy_v g old new).
Proof.
  intros. destruct H as [? [? ?]]. red in H, H1, H2. split; [|split; [|split]]; intros.
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
  intros. unfold sound_gc_graph in *. destruct H0 as [? [? ?]]. split; [|split].
  - eapply lcv_vertex_valid; eauto.
  - eapply lcv_edge_valid; eauto.
  - eapply lcv_src_edge; eauto.
Qed.

Lemma lcv_semi_iso: forall (from to: nat) (g g1: LGraph) l1 v,
    from <> to -> sound_gc_graph g -> sound_gc_graph g1 ->
    graph_has_gen g1 to -> vvalid g1 v -> vgeneration v = from ->
    raw_mark (vlabel g1 v) = false ->
    no_dangling_dst g -> gc_graph_semi_iso g g1 from to l1 ->
    gc_graph_semi_iso g (lgraph_copy_v g1 v to) from to
                      ((v, new_copied_v g1 to) :: l1).
Proof.
  intros from to g g1 l1 v H H0 H1 H3 H4 H5 H6 H7 H8.
  assert (sound_gc_graph (lgraph_copy_v g1 v to)) by (apply lcv_sound; auto).
  assert (N4: DoubleNoDup l1) by (eapply semi_iso_DoubleNoDup; eauto).
  destruct H8 as [? [? ?]]. destruct (split l1) as [from_l to_l] eqn: ?.
  destruct H10 as [[? ?] [[? [? ?]] ?]]. destruct H0 as [? [? ?]]. red in H0, H16, H17.
  pose proof H1. rename H18 into N1. destruct H1 as [? [? ?]]. red in H1, H18, H19.
  assert (vvalid g v). {
    destruct (vvalid_lcm g v H0); auto. exfalso.
    assert (In v to_l) by (rewrite H13; now split). apply H14 in H21.
    now rewrite H5 in H21. } assert (~ vvalid g1 (new_copied_v g1 to)). {
    intro. rewrite H1 in H21. now apply (graph_has_v_not_eq g1 to) in H21. }
  assert (~ In v from_l) by
      (intro; rewrite <- H11 in H22; destruct H22; now rewrite H6 in H22).
  assert (N2: vlabel g v = vlabel g1 v) by now apply H15.
  assert (N3: ~ In (new_copied_v g1 to) to_l) by
      (intro; apply H13 in H23; now destruct H23).
  assert (N5: DoubleNoDup ((v, new_copied_v g1 to) :: l1)). {
    rewrite DoubleNoDup_cons_iff. split; [|split; [|split]]; auto.
    - intro. unfold new_copied_v in H23. destruct v. inversion H23; subst.
      now simpl in *.
    - intro. red in H23. rewrite Heqp, in_app_iff in H23. destruct H23; [easy|].
      apply H14 in H23. now rewrite H5 in H23.
    - intro. red in H23. rewrite Heqp, in_app_iff in H23. destruct H23; [|easy].
      unfold new_copied_v in H23. rewrite <- H11 in H23. destruct H23 as [_ [_ ?]].
      symmetry in H23. now simpl in H23. }
  split; [|split].
  - apply is_partial_graph_trans with g1; auto. simpl.
    apply pcv_is_partial_graph; auto.
  - intros. simpl in H23. destruct H23.
    + inversion H23. subst v1 v2. split; [|split].
      * simpl. now rewrite ucov_copied_vertex.
      * rewrite lcv_vlabel_new; [easy | now rewrite H5].
      * intros. simpl. rewrite pcv_dst_new. 2: erewrite <- vlabel_get_edges_snd; eauto.
        assert (evalid g (v, idx)). {
          rewrite H16. split; simpl; [now rewrite <- H0 | now rewrite get_edges_In]. }
        destruct H8 as [_ [_ [_ ?]]]. left. symmetry. apply H8; auto. rewrite H0.
        red in H7. apply (H7 v); [now rewrite <- H0 | now rewrite get_edges_In].
    + assert (In v1 from_l) by
          (apply In_map_fst in H23; now rewrite map_fst_split, Heqp in H23).
      assert (In v2 to_l) by
          (apply In_map_snd in H23; now rewrite map_snd_split, Heqp in H23).
      assert (v2 <> new_copied_v g1 to) by (intro HS; now rewrite <- HS in N3).
      split; [|split].
      * simpl. rewrite ucov_not_eq. 2: intro; now subst. rewrite lacv_vlabel_old.
        1: apply (proj1 (H9 _ _ H23)). unfold new_copied_v. rewrite <- H11 in H24.
        destruct H24 as [_ [_ ?]]. destruct v1. simpl in *. intro HS; inversion HS.
        now rewrite H24 in H28.
      * simpl. rewrite ucov_not_eq.
        -- rewrite lacv_vlabel_old; auto. apply H9 in H23.
           now destruct H23 as [_ [? _]].
        -- apply H14 in H25. intro. destruct v, v2.
           inversion H27; subst. now simpl in *.
      * intros. simpl. rewrite pcv_dst_old; auto. apply H9 in H23.
        destruct H23 as [_ [_ ?]]. specialize (H23 _ H27). destruct H23; [now left |].
        destruct (InEither_dec (dst g (v1, idx)) l1).
        -- rewrite list_bi_map_cons_1. 1: now right.
           eapply DoubleNoDup_cons_InEither; eauto.
        -- rewrite list_bi_map_not_In in H23; [now left | easy].
  - red in N5. simpl in *. rewrite Heqp in N5 |-* .
    pose proof (NoDup_app_l _ _ _ N5). pose proof (NoDup_app_r _ _ _ N5).
    split; [|split].
    + split; auto. intros. split; intros.
      * destruct H25 as [? [? ?]]. destruct (equiv_dec v0 v); unfold equiv in *.
        1: now left. rewrite <- lcv_raw_mark in H25; auto.
        -- right. rewrite <- H11. intuition.
        -- rewrite <- H1. destruct H8. now apply H8.
      * destruct (equiv_dec v0 v); unfold equiv in *.
        -- subst. split; [|intuition]. simpl.
           unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; now auto.
        -- unfold complement in c. simpl in H25. destruct H25. 1: intuition.
           rewrite <- lcv_raw_mark; auto; rewrite <- H11 in H25; auto.
           destruct H25 as [_ [? _]]. rewrite <- H1. destruct H8. now apply H8.
    + split; auto. split.
      * intros. destruct H2. red in H2. rewrite H2. rewrite lcv_graph_has_v_iff; auto.
        rewrite <- H1. simpl. rewrite H13. intuition. rewrite H28 in H21. apply H21.
        destruct H8. now apply H8.
      * intros. unfold new_copied_v in H25. simpl in H25.
        destruct H25; [subst v0; now simpl | now apply H14].
    + intros. simpl in H26. apply Decidable.not_or in H26. destruct H26.
      rewrite ucov_not_eq; auto. rewrite lacv_vlabel_old. 1: now apply H15.
      intro. rewrite <- H28 in H21. apply H21. destruct H8. now apply H8.
Qed.

Lemma lgd_semi_iso: forall (from to: nat) (g g1: LGraph) l1 v n e,
    from <> to -> sound_gc_graph g -> sound_gc_graph g1 ->
    graph_has_gen g1 to -> forward_p_compatible (inr (v, n)) nil g1 from ->
    vgeneration (dst g1 e) = from -> Znth n (make_fields g1 v) = inr e ->
    raw_mark (vlabel g1 (dst g1 e)) = true -> ~ vvalid g v ->
    no_dangling_dst g -> gc_graph_semi_iso g g1 from to l1 ->
    gc_graph_semi_iso
      g (labeledgraph_gen_dst g1 e (copied_vertex (vlabel g1 (dst g1 e)))) from to l1.
Proof.
  intros from to g g1 l1 v n e H H0 H1 H2 H3 H4 H5 H6 Hp H7 H8.
  simpl in H3. destruct H3 as [? [? [? ?]]].
  assert (Hd: DoubleNoDup l1) by (now apply (semi_iso_DoubleNoDup g g1 from to)).
  destruct H8 as [? [? ?]]. destruct (split l1) as [from_l to_l] eqn: ?.
  destruct H13 as [[? ?] [[? [? ?]] ?]]. destruct H0 as [? [? ?]]. red in H0, H19, H20.
  destruct H1 as [? [? ?]]. red in H1, H21, H22.
  assert (Hf: from_l = map fst l1) by (rewrite map_fst_split, Heqp; reflexivity).
  assert (Ht: to_l = map snd l1) by (now rewrite map_snd_split, Heqp).
  split; [|split].
  - simpl. destruct H8 as [? [? [? ?]]].
    split; [|split;[|split]]; intros; simpl;
      [now apply H8 | now apply H23 | now apply H24| unfold updateEdgeFunc].
    rewrite if_false; auto. intro. red in H28. subst e0.
    apply make_fields_Znth_edge in H5; auto. subst e. rewrite H19 in H26. destruct H26.
    simpl in H5. now rewrite <- H0 in H5.
  - intros. simpl. pose proof H12. rename H24 into Hi. specialize (H12 _ _ H23).
    destruct H12 as [? [? ?]]. split; [|split]; try easy. intros.
    specialize (H25 _ H26). unfold updateEdgeFunc. if_tac. 2: easy. red in H27.
    subst e. apply make_fields_Znth_edge in H5; auto. inversion H5. subst v.
    rewrite <- H29 in *. assert (vvalid g v1). {
      apply In_map_fst in H23. rewrite map_fst_split, Heqp, <- H14 in H23.
      now destruct H23 as [_ [? _]]. }
    assert (dst g1 (v2, idx) = dst g (v1, idx) -> In (dst g (v1, idx)) from_l). {
      intros. rewrite H28 in *. rewrite <- H14. do 2 (split; auto).
      red in H7. rewrite H0. apply (H7 v1). 2: now rewrite get_edges_In.
      now rewrite <- H0. }
    destruct (equiv_dec (dst g1 (v2, idx)) (dst g (v1, idx))); unfold equiv in *.
    + rewrite e. apply H28 in e. rewrite Hf, In_map_fst_iff in e. destruct e as [b ?].
      destruct (DoubleNoDup_list_bi_map _ _ _ Hd H30) as [? _]. rewrite H31.
      apply Hi in H30. destruct H30 as [? [? ?]]. subst b. now right.
    + unfold complement in c. destruct H25. 1: easy. exfalso.
      destruct (InEither_dec (dst g (v1, idx)) l1).
      2: now rewrite list_bi_map_not_In in H25. red in i.
      rewrite Heqp, in_app_iff in i. destruct i.
      * rewrite Hf, In_map_fst_iff in H30. destruct H30 as [b ?].
        destruct (DoubleNoDup_list_bi_map _ _ _ Hd H30) as [? _]. rewrite H31 in H25.
        rewrite <- H25 in H30. apply In_map_snd in H30. rewrite <- Ht in H30.
        apply H17 in H30. now rewrite H4 in H30.
      * rewrite H16 in H30. destruct H30. red in H7. apply H31. rewrite H0.
        apply (H7 v1); [now rewrite <- H0 | now rewrite get_edges_In].
  - rewrite Heqp. split; [|split]; [split; auto..|]. intros; simpl; now apply H18.
Qed.

Definition special_edge_cond (g: LGraph) (p: forward_p_type): Prop :=
  match p with
  | inl _ => True
  | inr (v, _) => ~ vvalid g v
  end.

Definition special_roots_cond (p: forward_p_type) (roots: roots_t) (gen: nat): Prop :=
  match p with
  | inl _ => True
  | inr _ => roots_have_no_gen roots gen
  end.

Lemma root_map_id: root_map id = id.
Proof. extensionality x. unfold root_map. destruct x; simpl; easy. Qed.

Lemma roots_map_map_cons: forall a l (roots: roots_t),
    DoubleNoDup (a :: l) ->
    roots_map (a :: l) roots = roots_map [a] (roots_map l roots).
Proof.
  intros. induction roots; simpl; auto. rewrite IHroots. f_equal. destruct a0; simpl.
  1: easy. f_equal. clear IHroots. destruct (InEither_dec v (a :: l)).
  - destruct a as [a b]. rewrite DoubleNoDup_cons_iff in H.
    destruct H as [? [? [? ?]]]. rewrite InEither_cons_iff in i. destruct i.
    + red in H3. simpl in H3. destruct H3.
      * subst v. rewrite (list_bi_map_not_In l a); auto.
        unfold list_bi_map. simpl. rewrite if_true. 2: easy. rewrite if_true; easy.
      * subst v. rewrite (list_bi_map_not_In l b); auto.
        unfold list_bi_map. simpl. rewrite if_false. 2: easy. rewrite if_true.
        2: easy. rewrite if_false. 2: easy. rewrite if_true; easy.
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

Lemma roots_map_the_same: forall l (roots: roots_t),
    (forall r, In (inr r) roots -> ~ InEither r l) -> roots_map l roots = roots.
Proof.
  do 2 intro. induction roots; intros; simpl; auto. rewrite IHroots.
  - f_equal. destruct a; simpl; auto. assert (~ InEither v l). {
      apply H. now left. } now rewrite list_bi_map_not_In.
  - intros. apply H. now right.
Qed.

Lemma fr_O_semi_iso: forall (from to : nat) (p : forward_p_type) (g g1 g2 : LGraph)
                            (roots : roots_t) (f_info : fun_info) l1,
    from <> to -> sound_gc_graph g -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g1 ->
    gc_graph_semi_iso g g1 from to l1 -> forward_p_compatible p roots g1 from ->
    no_dangling_dst g -> no_dangling_dst g1 -> special_edge_cond g p ->
    special_roots_cond p roots from ->
    forward_relation from to O (forward_p2forward_t p roots g1) g1 g2 ->
    exists l2, gc_graph_semi_iso g g2 from to l2 /\ incl l1 l2 /\
               upd_roots from to p g1 roots f_info =
               semi_roots_map f_info l1 l2 p roots.
Proof.
  intros from to p g g1 g2 roots f_info l1 H Hs H0 H1 H2 Hg H3 H4 H7 Hd Hp Hr H5.
  assert (DoubleNoDup l1) by (eapply semi_iso_DoubleNoDup; eauto).
  assert (bijective (roots_map l1) (roots_map l1)). {
    unfold roots_map. apply bijective_map, bijective_root_map, bijective_list_bi_map.
    assumption. } destruct p; simpl in H4, H5.
  - destruct (Znth z roots) eqn:? ; [destruct s|]; simpl in *; rewrite Heqr;
      inversion H5; subst.
    + exists l1. split; [easy | split; [apply incl_refl|]].
      rewrite rrm_non_vertex_id; auto. intros. now rewrite Heqr.
    + exists l1. split; [easy | split; [apply incl_refl|]].
      rewrite rrm_non_vertex_id; auto. intros. now rewrite Heqr.
    + exists l1. split; [easy | split; [apply incl_refl|]]. rewrite if_false; auto.
      erewrite rrm_not_in_id; eauto. intro. destruct H3 as [_ [_ ?]].
      rewrite map_fst_split in H9. destruct (split l1). simpl in H9.
      destruct H3 as [[_ ?] _]. rewrite <- H3 in H9. now destruct H9 as [_ [_ ?]].
    + exists l1. split; [easy | split; [apply incl_refl|]].
      rewrite if_true, H12; auto. destruct H3 as [_ [? ?]].
      destruct (split l1) eqn:? . destruct H9 as [[? ?] [[_ [? ?]] _]].
      erewrite rmm_eq_upd_bunch; eauto.
      * assert (In v (map fst l1)). {
          rewrite map_fst_split, Heqp, <- H10. do 2 (split; auto).
          destruct (vvalid_lcm g v (proj1 Hs)). 1: easy. red in Hg.
          rewrite Forall_forall in Hg. assert (graph_has_v g2 v). {
            apply Hg; rewrite <- filter_sum_right_In_iff, <- Heqr;
              now apply Znth_In. } destruct H0 as [? _]. red in H0.
          rewrite <- H0 in H15. assert (In v l0) by now rewrite H11. exfalso.
          now apply H13 in H16. } rewrite In_map_fst_iff in H14. destruct H14 as [b ?].
        destruct (H3 _ _ H14) as [? _]. now subst b.
      * rewrite map_fst_split, Heqp. now simpl.
    + rewrite if_true, H11; auto. exists ((v, (new_copied_v g1 to)) :: l1).
      split; [|split]. 2: apply incl_tl, incl_refl.
      * apply lcv_semi_iso; auto. red in Hg. rewrite Forall_forall in Hg.
        destruct H0. red in H0. rewrite H0. apply Hg.
        rewrite <- filter_sum_right_In_iff, <- Heqr. now apply Znth_In.
      * erewrite rmm_eq_upd_bunch; eauto. 1: now left. simpl.
      destruct H3 as [_ [_ ?]]. destruct (split l1) as [from_l to_l] eqn: ?.
      destruct H3 as [[? ?] _]. rewrite map_fst_split, Heqp. simpl. constructor.
      2: easy. intro. rewrite <- H9 in H10. destruct H10. now rewrite H11 in H10.
  - destruct p as [v n]. destruct H4 as [? [? [? ?]]]. rewrite H10 in H5. simpl in *.
    destruct (Znth n (make_fields g1 v)) eqn:? ; [destruct s|]; simpl in H5;
      inversion H5; subst;
        try (exists l1; split; [easy | split; [apply incl_refl|]];
                    now rewrite (surjective _ _ H8)).
    + exists l1. split; [|split]; [|apply incl_refl | now rewrite (surjective _ _ H8)].
      eapply lgd_semi_iso; eauto. simpl. intuition.
    + exists ((dst g1 e, new_copied_v g1 to) :: l1).
      assert (Hm: gc_graph_semi_iso g (lgraph_copy_v g1 (dst g1 e) to)
                                    (vgeneration (dst g1 e)) to
                                    ((dst g1 e, new_copied_v g1 to) :: l1)). {
        apply lcv_semi_iso; auto. red in Hd. destruct H0. red in H0. rewrite H0.
        apply (Hd v); auto. unfold get_edges. rewrite <- filter_sum_right_In_iff.
        rewrite <- Heqf. apply Znth_In. now rewrite make_fields_eq_length. }
      split; [|split]. 2: apply incl_tl, incl_refl.
      * cut (gc_graph_semi_iso g (lgraph_copy_v g1 (dst g1 e) to)
                               (vgeneration (dst g1 e)) to
                               ((dst g1 e, new_copied_v g1 to) :: l1)). 2: assumption.
        intros. assert (Hfn: fst e <> new_copied_v g1 to). {
          apply make_fields_Znth_edge in Heqf; auto. subst e. simpl.
          destruct v as [gen idx]. red in H4. simpl in H4. destruct H4. red in H13.
          intro. unfold new_copied_v in H15. inversion H15. subst gen idx.
          omega. } eapply (lgd_semi_iso _ _ _ _ _ v n e) in H12; eauto.
        -- subst new_g. simpl dst in H12. rewrite pcv_dst_old in H12; auto.
           simpl in H12. unfold update_copied_old_vlabel, update_vlabel in H12.
           rewrite if_true in H12. 2: easy. simpl in H12. assumption.
        -- now apply lcv_sound.
        -- now rewrite <- lcv_graph_has_gen.
        -- Opaque lgraph_copy_v. simpl. Transparent lgraph_copy_v.
           split; [|split; [|split]]; auto.
           ++ rewrite lcv_graph_has_v_iff; auto.
           ++ rewrite <- lcv_raw_fields; auto.
           ++ rewrite <- lcv_raw_mark; auto. intro. now subst v.
        -- simpl. rewrite pcv_dst_old; auto.
        -- unfold lgraph_copy_v. rewrite lmc_make_fields, lacv_make_fields_not_eq.
              1: easy. apply make_fields_Znth_edge in Heqf; auto. now subst e.
        -- simpl dst. rewrite pcv_dst_old; auto. simpl.
           unfold update_copied_old_vlabel, update_vlabel. rewrite if_true.
           2: easy. now simpl.
      * apply semi_iso_DoubleNoDup in Hm; auto. rewrite roots_map_map_cons; auto.
        rewrite (surjective _ _ H8), roots_map_the_same; auto. intros. red in Hr.
        specialize (Hr _ H12). intro. red in H13. simpl in H13.
        destruct H13 as [? | [? | ?]]; auto.
        -- now rewrite H13 in Hr.
        -- red in Hg. rewrite Forall_forall in Hg.
           rewrite filter_sum_right_In_iff in H12. apply Hg in H12.
           rewrite <- H13 in H12. unfold new_copied_v in H12. destruct H12.
           simpl in H15. red in H15. omega.
Qed.
