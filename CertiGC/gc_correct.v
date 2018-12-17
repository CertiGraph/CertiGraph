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
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.CertiGC.GCGraph.
Import ListNotations.

Local Open Scope Z_scope.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertex_valid (g: LGraph): Prop := forall v, vvalid g v <-> graph_has_v g v.

Definition edge_valid (g: LGraph): Prop := forall e, evalid g e <-> graph_has_e g e.

Definition src_edge (g: PreGraph VType EType): Prop := forall e, src g e = fst e.

Definition sound_gc_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g.

(** Reset is sound *)

Lemma fold_left_remove_edge_vvalid: forall (g: PreGraph VType EType) l v,
    vvalid (fold_left pregraph_remove_edge l g) v <-> vvalid g v.
Proof. now intros; revert g; induction l; [|intros; simpl; rewrite IHl]. Qed.

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
  intros; revert g v; induction l; intros; simpl; [|rewrite IHl, lrvae_vvalid]; intuition.
Qed.

Lemma vertex_valid_reset: forall g gen,
    vertex_valid g -> vertex_valid (reset_graph gen g).
Proof.
  intros. unfold vertex_valid in *. intros. simpl. rewrite graph_has_v_reset.
  unfold remove_nth_gen_ve. rewrite fold_left_lrvae_vvalid. rewrite H. intuition; destruct H2.
  - destruct v as [vgen vidx]. simpl in *. subst vgen.
    change (gen, vidx) with ((fun idx : nat => (gen, idx)) vidx). apply in_map.
    rewrite nat_inc_list_In_iff. destruct H1. now red in H1.   - apply list_in_map_inv in H0. destruct H0 as [? [? _]]; now subst v.  
Qed.

Lemma remove_ve_src_unchanged: forall g gen e,
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

Lemma src_edge_reset: forall (g: LGraph) gen,
    src_edge g -> src_edge (reset_graph gen g).
Proof.
  intros. unfold src_edge in *. intros. 
  simpl. rewrite remove_ve_src_unchanged. apply H.
Qed.

Lemma fold_left_remove_edge_evalid: forall (g: PreGraph VType EType) l e,
    evalid (fold_left pregraph_remove_edge l g) e <-> evalid g e /\ ~ In e l.
Proof.
  intros; revert g; induction l; intros; simpl; [|rewrite IHl, remove_edge_evalid]; intuition.
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
  intros. revert g e. induction l; intros; simpl; [|rewrite IHl, lrvae_evalid]; intuition.
  - subst. contradiction.
  - specialize (H1 _ H4). now apply H1.
  - apply (H1 a); intuition.
  - apply (H1 v); intuition.
Qed.

Lemma edge_valid_reset: forall g gen, edge_valid g -> edge_valid (reset_graph gen g).
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

Lemma reset_sound: forall (g: LGraph) gen,
    sound_gc_graph g -> sound_gc_graph (reset_graph gen g).
Proof.
  intros. destruct H as [? [? ?]].
  now split3;
    [apply vertex_valid_reset | apply edge_valid_reset | apply src_edge_reset]. 
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
  - now destruct x, y; inversion H; [|apply injective in H1; subst].
  - now destruct x; simpl; [|rewrite surjective].
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
    now rewrite H, surjective.
  - now apply lp_graph_iso_exp_sym.
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

Lemma get_edges_snd_NoDup: forall g v, NoDup (map snd (get_edges g v)).
Proof.
  intros. unfold get_edges. unfold make_fields.
  remember (raw_fields (vlabel g v)). remember O.
  clear Heql Heqn g. revert n. induction l; intros; simpl; [constructor|].
  destruct a; [destruct s|]; simpl; [apply IHl..|].
  rewrite NoDup_cons_iff. split; trivial. intro.
  apply list_in_map_inv in H. destruct H as [x [? ?]].
  rewrite <- filter_sum_right_In_iff in H0.
  apply In_nth with (d := field_t_inhabitant) in H0. destruct H0 as [p [? ?]].
  apply make_fields'_edge_depends_on_index in H1; [subst x; simpl in H; omega|].
  rewrite make_fields'_eq_length in H0. rewrite Zlength_correct. split; [omega|].
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
  intros. rewrite get_edges_map_map, <- combine_repeat_eq_map;
            apply NoDup_combine_r, get_edges_snd_NoDup.
Qed.

Lemma gsepl_DoubleNoDup: forall (v1 v2 : VType) (g : LGraph),
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
  - unfold InEither. rewrite combine_split by (rewrite map_length; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + apply NoDup_cons_2 in H0. contradiction.
    + rewrite in_map_iff in H2. destruct H2 as [x [? ?]]. inversion H2. auto.
  - unfold InEither. rewrite combine_split by (rewrite map_length; reflexivity).
    intro. rewrite in_app_iff in H2. destruct H2.
    + specialize (H1 (v2, idx)). simpl in H1. apply H; now rewrite H1; [|right].
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
  induction l; simpl in *; [inversion H|].
  rewrite InEither_cons_iff in H.
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
  rewrite DoubleNoDup_app_iff.
  split3; [apply gsepl_DoubleNoDup | apply IHl|]; trivial. 
  intros. apply gsepl_InEither in H3. intro. apply gepl_InEither in H4. red in H3.
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
  remember (raw_fields (vlabel g2 v2)). remember O.
  clear H Heql Heqn.
  revert n. induction l; intros; simpl; auto.
  now destruct a; [destruct s |]; simpl; rewrite IHl.
Qed.

Lemma gsepl_key: forall e g v,
    In e (get_edges g (fst e)) ->
    In (e, (v, snd e)) (gen_single_edge_pair_list g (fst e, v)).
Proof.
  intros. simpl. remember (get_edges g (fst e)). clear Heql.
  induction l; simpl in *; auto. now destruct H; [left; subst | right; apply IHl].
Qed.

Lemma gsepl_value: forall (e: EType) k (g1 g2: LGraph),
    In e (get_edges g2 (fst e)) -> vlabel g1 k = vlabel g2 (fst e) ->
    In (k, snd e, e) (gen_single_edge_pair_list g1 (k, fst e)).
Proof.
  intros. destruct e as [gen idx]. simpl in *. rewrite get_edges_In in H.
  rewrite get_edges_map_map. apply vlabel_get_edges_snd in H0. rewrite H0.
  remember (map snd (get_edges g2 gen)). rewrite map_map. simpl. clear -H.
  induction l; simpl; [inversion H |].
  now destruct H; [left; subst a | right; apply IHl].
Qed.

Lemma gepl_key: forall (g : LGraph) (vpl : list (VType * VType)) (e : EType) v,
    In e (get_edges g (fst e)) -> In (fst e, v) vpl ->
    In (e, (v, snd e)) (gen_edge_pair_list g vpl).
Proof.
  intros. induction vpl; [inversion H0|]. unfold gen_edge_pair_list. simpl.
  fold (gen_edge_pair_list g vpl). simpl in H0. rewrite in_app_iff.
  destruct H0; [left; subst a; apply gsepl_key | right; apply IHvpl]; auto.
Qed.

Lemma gepl_value: forall (e: EType) k (g1 g2: LGraph) vpl,
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
    right; intro; apply n; destruct H; auto.
  - right; intro; apply n; destruct H; auto. 
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
    apply (PairGenNoDup_DoubleNoDup _ from to); [omega|]. red. rewrite Heqp. 
    now split; split; [| intros; rewrite <- H8 in H11; destruct H11 | |].
  }
  assert (Hn: DoubleNoDup (gen_edge_pair_list g1 vpl)) by
      (apply gepl_DoubleNoDup; auto).
  pose proof (split_combine vpl).
  rewrite Heqp in H12.
  assert (forall x, vvalid g1 x -> InEither x vpl ->
                    exists k v, In (k, v) vpl /\ x = k /\ list_bi_map vpl x = v). {
    intros. apply (list_bi_map_In vpl x) in H14. destruct H14 as [k [v [? ?]]].
    exists k, v. destruct H15; auto. destruct H15. subst x. rewrite <- H12 in H14.
    apply in_combine_r in H14. apply H10 in H14. destruct H14 as [_ ?].
    contradiction. }
  remember (list_bi_map vpl) as vmap.
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
      now rewrite H18.
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
          rewrite <- H30. assumption. }
      destruct v as [vgen vidx].
      assert (vgen = to). {
        rewrite <- H12 in H13. apply in_combine_r in H13. apply N in H13.
        simpl in H13. assumption. }
      subst vgen. assert (to <> from) by omega.
      specialize (H3 _ H35 vidx (snd e)).
      simpl in H3. rewrite H25 in *. simpl in *. apply H3; auto.
      change (prod nat nat) with VType. rewrite H31; auto.
    - assert (~ InEither (dst g1 e) vpl). {
        intro. unfold InEither in H27. rewrite Heqp, in_app_iff in H27.
        destruct H27; auto. rewrite <- H8 in H27. destruct H27 as [_ ?].
        assert (vgeneration (fst e) <> from). {
          intro. apply n. unfold InEither. rewrite Heqp, in_app_iff. left.
          rewrite <- H8. now split. }
        assert (graph_has_e g1 e) by (split; [rewrite <- H1|]; auto).
        destruct e as [[vgen vidx] eidx] eqn:? . simpl in H28.
        specialize (H2 _ H28 vidx eidx). simpl in H2. specialize (H2 H29).
        contradiction. }
      rewrite !list_bi_map_not_In; auto.
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
      destruct H23. assumption. }
    clear H25. exists (vmap s, map emap l).
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
            now apply step_reachable with (dst g1 a);
              [exists a | apply reachable_refl|]. }
          split; [|split; apply Hv]; [apply He | | ]; simpl; split; auto.
        + apply IHl; auto. 1: intros; apply H23; right; assumption.
          intros. apply H24. apply step_reachable with (dst g1 a); auto.
          2: destruct H25 as [_ [? _]]; subst s; assumption. exists a; auto.
          destruct H25; assumption. }
    split; split; auto.
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
      2: now exfalso; apply n; red; rewrite Heqp, in_app_iff; right; rewrite H10. 
      rewrite list_bi_map_not_In.
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
      rewrite H20, H26, H28. reflexivity.
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
      destruct H23. assumption. }
    clear H25. exists (vmap s, map emap l).
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
            apply step_reachable with (dst g2 a); [| apply reachable_refl|]; auto.
            now exists a; [| rewrite remove_ve_src_unchanged | rewrite remove_ve_dst_unchanged]. }
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
  - rewrite Nat.add_0_r; assumption.
  - apply ngr_graph_has_gen in H3; auto. erewrite do_gen_graph_has_gen in H3; eauto.
    apply IHn in H9; auto. rewrite <- Nat.add_succ_comm. assumption.
Qed.

Lemma ngr_vertex_valid: forall g1 g2 gen,
    vertex_valid g1 -> new_gen_relation gen g1 g2 -> vertex_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold vertex_valid in *. intros. simpl.
    rewrite H. now split; intros; [apply ang_graph_has_v | apply ang_graph_has_v_inv in H1].
Qed.

Lemma ngr_edge_valid: forall g1 g2 gen,
    edge_valid g1 -> new_gen_relation gen g1 g2 -> edge_valid g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold edge_valid in *. intros. simpl.
    rewrite H. now split; intros; destruct H1; split;
    [apply ang_graph_has_v | | apply ang_graph_has_v_inv in H1|].
Qed.

Lemma ngr_src_edge: forall (g1 g2: LGraph) gen,
    src_edge g1 -> new_gen_relation gen g1 g2 -> src_edge g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - now subst.
  - destruct H0 as [gen_i [? ?]]. subst g2. now unfold src_edge in *. 
Qed.

Lemma ngr_sound: forall g1 g2 gen,
    sound_gc_graph g1 -> new_gen_relation gen g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? ?]]. split3.
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
  - now apply lcv_graph_has_v_inv in H0.
  - now destruct H0; [apply lcv_graph_has_v_old | subst x; apply lcv_graph_has_v_new].
Qed.

Lemma lcv_vertex_valid: forall g v to,
    vertex_valid g -> graph_has_gen g to -> vertex_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold vertex_valid in *. intros. simpl.
  rewrite pcv_vvalid_iff, lcv_graph_has_v_iff; auto. now rewrite H.
Qed.

Lemma fr_O_vertex_valid: forall g g' from to p,
    vertex_valid g -> graph_has_gen g to -> forward_relation from to 0 p g g' ->
    vertex_valid g'.
Proof.
  intros. inversion H1; subst; try assumption.
  - now apply lcv_vertex_valid.
  - replace (vertex_valid new_g) with
        (vertex_valid (lgraph_copy_v g (dst g e) to)) by (subst new_g; reflexivity).
    now apply lcv_vertex_valid.
Qed.

Lemma lcv_get_edges_old: forall (g: LGraph) v v' to,
    graph_has_v g v' -> graph_has_gen g to ->
    get_edges (lgraph_copy_v g v to) v' = get_edges g v'.
Proof.
  intros. unfold get_edges, make_fields.
  now erewrite <- lcv_raw_fields by assumption.
Qed.

Lemma cvae_evalid_iff: forall g v l e,
    evalid (fold_left (copy_v_add_edge v) l g) e <-> evalid g e \/ In e (map fst l).
Proof.
  intros. revert g. induction l; intros; simpl; [intuition|].
  rewrite IHl. unfold copy_v_add_edge. simpl. unfold addValidFunc. intuition.
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

Lemma fr_O_edge_valid: forall g1 g2 from to p,
    edge_valid g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> edge_valid g2.
Proof.
  intros. inversion H1; subst; try assumption.
  - now apply lcv_edge_valid.
  - replace (edge_valid new_g) with
        (edge_valid (lgraph_copy_v g1 (dst g1 e) to)) by (subst new_g; reflexivity).
    now apply lcv_edge_valid.
Qed.

Lemma flcvae_src_old: forall g new (l: list (EType * VType)) e,
    ~ In e (map fst l) -> src (fold_left (copy_v_add_edge new) l g) e = src g e.
Proof.
  intros. revert g H. induction l; intros; simpl; trivial. 
  rewrite IHl. 2: intro; apply H; simpl; right; assumption.
  simpl. unfold updateEdgeFunc. rewrite if_false; trivial.
  unfold equiv. intro.
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

Lemma pcv_src_edge: forall (g: LGraph) v new,
    src_edge g -> src_edge (pregraph_copy_v g v new).
Proof.
  intros. unfold src_edge in *. intros. unfold pregraph_copy_v.
  replace (length (get_edges g v)) with (length (map snd (get_edges g v))) by
      (rewrite map_length; reflexivity). remember (get_edges g v) as el.
  remember (combine (combine (repeat new (Datatypes.length (map snd el))) (map snd el))
                    (map (dst g) el)) as l. destruct (in_dec equiv_dec e (map fst l)).
  - rewrite flcvae_src_new; auto.
    rewrite combine_repeat_eq_map, map_map, combine_map_join in Heql.
    apply list_in_map_inv in i. destruct i as [x [? ?]]. subst l.
    apply list_in_map_inv in H1. destruct H1 as [x0 [? ?]]. subst x e. simpl. auto.
  - rewrite flcvae_src_old; auto. simpl. apply H.
Qed.

Lemma fr_O_src_edge: forall (g1 g2: LGraph) from to p,
    src_edge g1 -> forward_relation from to O p g1 g2 -> src_edge g2.
Proof.
  intros. inversion H0; subst; try assumption.
  - apply pcv_src_edge; assumption.
  - replace (src_edge new_g) with
        (src_edge (lgraph_copy_v g1 (dst g1 e) to)) by (subst new_g; reflexivity).
    apply pcv_src_edge; assumption.
Qed.

Lemma fr_O_sound: forall g1 g2 from to p,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    forward_relation from to O p g1 g2 -> sound_gc_graph g2.
Proof.
  intros. destruct H as [? [? ?]]. split3.
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
  intros. red. split3; intros; [easy | easy |].
  destruct (split []) eqn:? . simpl in Heqp. inversion Heqp. subst. clear Heqp.
  split3; [| | easy].
  - red. split. 1: constructor. intros; split; intros. 2: inversion H1.
    destruct H1 as [? [? ?]]. destruct H as [? _]. red in H. rewrite H in H2.
    red in H0. destruct H2. rewrite H3 in *. destruct v as [? idx]. simpl in *.
    subst n. specialize (H0 H2 _ H4). rewrite H1 in H0. inversion H0.
  - red. split. 1: constructor. split; [split|]; intros; intuition.
Qed.

Lemma semi_iso_DoubleNoDup: forall g1 g2 from to l,
    from <> to -> gc_graph_semi_iso g1 g2 from to l -> DoubleNoDup l.
Proof.
  intros. destruct H0 as [_ [_ ?]]. destruct (split l) as [from_l to_l] eqn: ?.
  apply (PairGenNoDup_DoubleNoDup l from to); auto. red. rewrite Heqp.
  destruct H0 as [[? ?] [[? [? ?]] _]]. split; split; intros; auto.
  rewrite <- H1 in H5. destruct H5 as [_ [_ ?]]. assumption.
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
  - destruct_eq_dec v v0. 1: subst; now left.
    right. intro HS. apply H. inversion HS. easy.
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

Lemma restricted_map_Znth_same': forall {A} {d: Inhabitant A} f ps l i,
    (forall e, In e ps -> 0 <= e < Zlength l) -> idempotent f -> In i ps ->
    Znth i (restricted_map f l ps) = f (Znth i l).
Proof.
  do 3 intro. unfold restricted_map. induction ps; intros. 1: inversion H1.
  simpl in *. assert (Zlength (upd_Znth a l (f (Znth a l))) = Zlength l). {
    rewrite upd_Znth_Zlength; auto. }
  assert (forall e : Z, In e ps -> 0 <= e < Zlength (upd_Znth a l (f (Znth a l)))) by
      (intros; rewrite H2; apply H; now right). destruct H1.
  - subst i. destruct (in_dec Z.eq_dec a ps).
    + rewrite IHps; auto. rewrite upd_Znth_same; auto.
    + rewrite fold_left_upd_Znth_diff; auto. 2: rewrite H2; auto.
      rewrite upd_Znth_same; auto.
  - rewrite IHps; auto. destruct (Z.eq_dec i a).
    + subst. rewrite upd_Znth_same; auto.
    + rewrite upd_Znth_diff; auto.
Qed.

Definition restricted_roots_map (index: Z) (f_info: fun_info)
           (roots: roots_t) (l: list (VType * VType)): roots_t :=
  restricted_map (root_map (list_map l)) roots
                 (get_indices index (live_roots_indices f_info)).

Lemma restricted_roots_map_Zlength: forall index f_info roots l,
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Zlength (restricted_roots_map index f_info roots l) = Zlength roots.
Proof.
  intros. unfold restricted_roots_map. rewrite restricted_map_Zlength; auto.
  intros. rewrite get_indices_spec in H0. destruct H0. rewrite <- H in H0. easy.
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
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0. easy.
  - intro. rewrite get_indices_spec in H2. destruct H2. easy.
Qed.

Lemma get_indices_NoDup: forall i l, NoDup (get_indices i l).
Proof. intros. unfold get_indices. apply collect_Z_indices_NoDup. Qed.

Lemma restricted_roots_map_Znth_same: forall z f_info roots l j,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
    Znth j (restricted_roots_map z f_info roots l) =
    root_map (list_map l) (Znth j roots).
Proof.
  intros. unfold restricted_roots_map. rewrite restricted_map_Znth_same; auto.
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0. easy.
  - apply get_indices_NoDup.
  - rewrite get_indices_spec. split; [rewrite <- H0 |]; easy.
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
  intros. unfold sound_gc_graph in *. destruct H0 as [? [? ?]]. split3.
  - eapply lcv_vertex_valid; eauto.
  - eapply lcv_edge_valid; eauto.
  - eapply pcv_src_edge; eauto.
Qed.

Lemma ucov_rawmark: forall g old_v new_v,
    raw_mark (update_copied_old_vlabel g old_v new_v old_v) = true.
Proof.
  intros. unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; easy.
Qed.
(*here*)
Lemma lcv_raw_mark_old: forall g v to,
    raw_mark (vlabel (lgraph_copy_v g v to) v) = true.
Proof. intros. simpl. apply ucov_rawmark. Qed.

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
  split3.
  - apply is_partial_graph_trans with g1; auto. simpl.
    apply pcv_is_partial_graph; auto.
  - intros. simpl in H23. destruct H23.
    + inversion H23. subst v1 v2. split3.
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
      split3.
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
    split3.
    + split; auto. intros. split; intros.
      * destruct H25 as [? [? ?]]. destruct_eq_dec v0 v.
        1: now left. rewrite <- lcv_raw_mark in H25; auto.
        -- right. rewrite <- H11. intuition.
        -- rewrite <- H1. destruct H8. now apply H8.
      * destruct_eq_dec v0 v.
        -- subst. split; [|intuition]. apply lcv_raw_mark_old.
        -- simpl in H25. destruct H25. 1: intuition.
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
  split3. 
  - simpl. destruct H8 as [? [? [? ?]]].
    split; [|split;[|split]]; intros; simpl;
      [now apply H8 | now apply H23 | now apply H24 | unfold updateEdgeFunc].
    rewrite if_false; auto. intro. red in H28. subst e0.
    apply make_fields_Znth_edge in H5; auto. subst e. rewrite H19 in H26. destruct H26.
    simpl in H5. now rewrite <- H0 in H5.
  - intros. simpl. pose proof H12. rename H24 into Hi. specialize (H12 _ _ H23).
    destruct H12 as [? [? ?]]. split3; try easy. intros.
    specialize (H25 _ H26). unfold updateEdgeFunc. if_tac. 2: easy. red in H27.
    subst e. apply make_fields_Znth_edge in H5; auto. inversion H5. subst v.
    rewrite <- H29 in *. assert (vvalid g v1). {
      apply In_map_fst in H23. rewrite map_fst_split, Heqp, <- H14 in H23.
      now destruct H23 as [_ [? _]]. }
    assert (dst g1 (v2, idx) = dst g (v1, idx) -> In (dst g (v1, idx)) from_l). {
      intros. rewrite H28 in *. rewrite <- H14. do 2 (split; auto).
      red in H7. rewrite H0. apply (H7 v1). 2: now rewrite get_edges_In.
      now rewrite <- H0. }
    destruct_eq_dec (dst g1 (v2, idx)) (dst g (v1, idx)).
    + rewrite H30. apply H28 in H30. rewrite Hf, In_map_fst_iff in H30.
      destruct H30 as [b ?]. destruct (DoubleNoDup_list_bi_map _ _ _ Hd H30) as [? _].
      rewrite H31. apply Hi in H30. destruct H30 as [? [? ?]]. subst b. now right.
    + destruct H25. 1: easy. exfalso.
      destruct (InEither_dec (dst g (v1, idx)) l1).
      2: now rewrite list_bi_map_not_In in H25. red in i.
      rewrite Heqp, in_app_iff in i. destruct i.
      * rewrite Hf, In_map_fst_iff in H31. destruct H31 as [b ?].
        destruct (DoubleNoDup_list_bi_map _ _ _ Hd H31) as [? _]. rewrite H32 in H25.
        rewrite <- H25 in H31. apply In_map_snd in H31. rewrite <- Ht in H31.
        apply H17 in H31. now rewrite H4 in H31.
      * rewrite H16 in H31. destruct H31. red in H7. apply H32. rewrite H0.
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
Proof. extensionality x. unfold root_map. now destruct x. Qed.

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

Lemma roots_map_the_same: forall l (roots: roots_t),
    (forall r, In (inr r) roots -> ~ InEither r l) -> roots_map l roots = roots.
Proof.
  do 2 intro. induction roots; intros; simpl; auto. rewrite IHroots.
  - f_equal. destruct a; simpl; auto. assert (~ InEither v l). {
      apply H. now left. } now rewrite list_bi_map_not_In.
  - intros. apply H. now right.
Qed.

Definition rf_list_relation (roots: roots_t) (f_info: fun_info)
           (l: list (VType * VType)) (z: Z) (n: nat): Prop :=
  forall j, 0 <= j < Zlength roots ->
            Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
            forall v, Znth j roots = inr v -> vgeneration v = n -> In v (map fst l).

Definition semi_rf_list_relation (roots: roots_t) (f_info: fun_info)
           (l: list (VType * VType)) (p: forward_p_type) (n: nat): Prop :=
  match p with
  | inl z => rf_list_relation roots f_info l z n
  | inr _ => True
  end.

Lemma inl_rf_list_relation: forall (from : nat) (z : Z) (roots : roots_t)
                                   (f_info : fun_info) (l1 : list (VType * VType)) s,
    roots_fi_compatible roots f_info -> 0 <= z < Zlength roots ->
    Znth z roots = inl s -> rf_list_relation roots f_info l1 z from.
Proof.
  intros. destruct H. red. intros. specialize (H2 _ _ H3 H0 H4). rewrite H2, H1 in H5.
  inversion H5.
Qed.

Lemma not_rf_list_relation: forall (from : nat) (z : Z) (roots : roots_t)
                                   (f_info : fun_info) (l : list (VType * VType)) v,
    roots_fi_compatible roots f_info -> 0 <= z < Zlength roots ->
    Znth z roots = inr v -> vgeneration v <> from ->
    rf_list_relation roots f_info l z from.
Proof.
  intros. destruct H. red. intros. specialize (H3 _ _ H4 H0 H5). rewrite H3, H1 in H6.
  inversion H6. subst v0. now rewrite H7 in H2.
Qed.

Lemma roots_map_bijective: forall l,
    DoubleNoDup l -> bijective (roots_map l) (roots_map l).
Proof. intros. now apply bijective_map, bijective_root_map, bijective_list_bi_map. Qed.

Lemma fr_O_semi_iso:
  forall (from to : nat) (p : forward_p_type) (g g1 g2 : LGraph)
         (roots : roots_t) (f_info : fun_info) l1,
    from <> to -> sound_gc_graph g -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g1 ->
    gc_graph_semi_iso g g1 from to l1 -> forward_p_compatible p roots g1 from ->
    no_dangling_dst g -> no_dangling_dst g1 -> special_edge_cond g p ->
    special_roots_cond p roots from ->
    forward_relation from to O (forward_p2forward_t p roots g1) g1 g2 ->
    exists l2, gc_graph_semi_iso g g2 from to (l2 ++ l1) /\
               upd_roots from to p g1 roots f_info =
               semi_roots_map f_info l1 (l2 ++ l1) p roots /\
               semi_rf_list_relation roots f_info (l2 ++ l1) p from.
Proof.
  intros from to p g g1 g2 roots f_info l1 H Hs H0 H1 H2 Hg H3 H4 H7 Hd Hp Hr H5.
  assert (DoubleNoDup l1) by (eapply semi_iso_DoubleNoDup; eauto).
  assert (bijective (roots_map l1) (roots_map l1)) by (now apply roots_map_bijective).
  destruct p; simpl in H4, H5.
  - destruct (Znth z roots) eqn:? ; [destruct s|]; simpl in *; rewrite Heqr;
      inversion H5; subst; [exists []; simpl..|].
    + split; [|split; [rewrite rrm_non_vertex_id|]]; auto. 1: intros; now rewrite Heqr.
      eapply inl_rf_list_relation; eauto.
    + split; [|split; [rewrite rrm_non_vertex_id|]]; auto. 1: intros; now rewrite Heqr.
      eapply inl_rf_list_relation; eauto.
    + split; [|split; [rewrite if_false|]]; auto.
      * erewrite rrm_not_in_id; eauto. simpl. intro. destruct H3 as [_ [_ ?]].
        rewrite map_fst_split in H9. destruct (split l1). simpl in H9.
        destruct H3 as [[_ ?] _]. rewrite <- H3 in H9. now destruct H9 as [_ [_ ?]].
      * eapply not_rf_list_relation; eauto.
    + split; [|rewrite if_true, H12]; auto. destruct H3 as [_ [? ?]].
      destruct (split l1) eqn:? . destruct H9 as [[? ?] [[_ [? ?]] _]].
      assert (In v (map fst l1)). {
        rewrite map_fst_split, Heqp, <- H10. do 2 (split; auto).
        destruct (vvalid_lcm g v (proj1 Hs)); trivial. red in Hg.
        rewrite Forall_forall in Hg. assert (graph_has_v g2 v). {
          apply Hg; rewrite <- filter_sum_right_In_iff, <- Heqr;
            now apply Znth_In. } destruct H0 as [? _]. red in H0.
        rewrite <- H0 in H15. assert (In v l0) by now rewrite H11. exfalso.
        now apply H13 in H16. } split.
      * erewrite rmm_eq_upd_bunch; eauto. 2: rewrite map_fst_split, Heqp; now simpl.
        rewrite In_map_fst_iff in H14. destruct H14 as [b ?].
        destruct (H3 _ _ H14) as [? _]. now subst b.
      * red. intros. destruct H2. specialize (H19 _ _ H15 H4 H16).
        rewrite H19, Heqr in H17. inversion H17. now subst v0.
    + rewrite if_true, H11; auto. exists [(v, (new_copied_v g1 to))].
      simpl. split3.
      * apply lcv_semi_iso; auto. red in Hg. rewrite Forall_forall in Hg.
        destruct H0. red in H0. rewrite H0. apply Hg.
        rewrite <- filter_sum_right_In_iff, <- Heqr. now apply Znth_In.
      * erewrite rmm_eq_upd_bunch; eauto. 1: now left. simpl.
        destruct H3 as [_ [_ ?]]. destruct (split l1) as [from_l to_l] eqn: ?.
        destruct H3 as [[? ?] _]. rewrite map_fst_split, Heqp. simpl. constructor.
        2: easy. intro. rewrite <- H9 in H10. destruct H10. now rewrite H11 in H10.
      * red. intros. simpl. left. destruct H2. specialize (H14 _ _ H9 H4 H10).
        rewrite H14, Heqr in H12. now inversion H12.
  - destruct p as [v n]. destruct H4 as [? [? [? ?]]]. rewrite H10 in H5. simpl in *.
    destruct (Znth n (make_fields g1 v)) eqn:? ; [destruct s|]; simpl in H5;
      inversion H5; subst;
        try (exists []; split; [easy | now rewrite (surjective _ _ H8)]).
    + exists []. split; [| now rewrite (surjective _ _ H8)].
      eapply lgd_semi_iso; eauto. simpl. intuition.
    + exists [(dst g1 e, new_copied_v g1 to)]. simpl.
      assert (Hm: gc_graph_semi_iso g (lgraph_copy_v g1 (dst g1 e) to)
                                    (vgeneration (dst g1 e)) to
                                    ((dst g1 e, new_copied_v g1 to) :: l1)). {
        apply lcv_semi_iso; auto. red in Hd. destruct H0. red in H0. rewrite H0.
        apply (Hd v); auto. unfold get_edges. rewrite <- filter_sum_right_In_iff.
        rewrite <- Heqf. apply Znth_In. now rewrite make_fields_eq_length. } split.
      * cut (gc_graph_semi_iso g (lgraph_copy_v g1 (dst g1 e) to)
                               (vgeneration (dst g1 e)) to
                               ((dst g1 e, new_copied_v g1 to) :: l1)). 2: assumption.
        intros. assert (Hfn: fst e <> new_copied_v g1 to). {
          apply make_fields_Znth_edge in Heqf; auto. subst e. simpl.
          destruct v as [gen idx]. red in H4. simpl in H4. destruct H4. red in H13.
          intro. unfold new_copied_v in H15. inversion H15. subst gen idx.
          omega. } eapply (lgd_semi_iso _ _ _ _ _ v n e) in H12; eauto.
        -- subst new_g. simpl dst in H12. rewrite pcv_dst_old in H12; auto.
           simpl in H12.  rewrite ucov_copied_vertex in H12. easy.
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
        -- simpl dst. rewrite pcv_dst_old; auto. apply lcv_raw_mark_old.
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

Definition gather_indices (il: list Z) (live_indices: list Z) :=
  fold_right (fun z l => get_indices z live_indices ++ l) nil il.

Definition quasi_roots_map (il: list nat) (f_info: fun_info)
           (roots: roots_t) (l: list (VType * VType)): roots_t :=
  restricted_map (root_map (list_map l)) roots
                 (gather_indices (map Z.of_nat il) (live_roots_indices f_info)).

Lemma quasi_roots_map_cons: forall a l f_info roots il,
  quasi_roots_map (a :: l) f_info roots il =
  quasi_roots_map l f_info (restricted_roots_map (Z.of_nat a) f_info roots il) il.
Proof.
  intros. unfold quasi_roots_map. simpl.
  remember (gather_indices (map Z.of_nat l) (live_roots_indices f_info)).
  unfold restricted_roots_map. remember (root_map (list_map il)) as f.
  remember (get_indices (Z.of_nat a) (live_roots_indices f_info)).
  unfold restricted_map. now rewrite fold_left_app.
Qed.

Definition rf_list_pair_relation (roots: roots_t) (f_info: fun_info)
           (l1 l2: list (VType * VType)) (z: Z): Prop :=
  forall j, 0 <= j < Zlength roots ->
            Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
            forall v, Znth j roots = inr v -> In v (map fst (l2 ++ l1)) ->
                      In v (map fst l1).

Lemma restricted_roots_map_incl: forall roots f_info l1 l2 i,
    rf_list_pair_relation roots f_info l1 l2 i -> DoubleNoDup (l2 ++ l1) ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    restricted_roots_map i f_info roots l1 =
    restricted_roots_map i f_info roots (l2 ++ l1).
Proof.
  intros roots f_info l1 l2 i Hr Hd H. apply Znth_list_eq.
  assert (forall l, Zlength (restricted_roots_map i f_info roots l) = Zlength roots)
    by (intros; now rewrite restricted_roots_map_Zlength). split. 1: now rewrite H0.
  intros. rewrite H0 in H1.
  destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                     (Znth i (live_roots_indices f_info))).
  - rewrite !restricted_roots_map_Znth_same; auto.
    destruct (Znth j roots) eqn:? ; simpl; auto. f_equal.
    apply list_map_DoubleNoDup_incl_eq; auto. intros.
    destruct (in_dec equiv_dec v (map fst l1)); auto. eapply Hr in H2; eauto.
  - now rewrite !restricted_roots_map_Znth_diff.
Qed.

Lemma semi_iso_In_map_fst: forall g1 g2 from to l,
    gc_graph_semi_iso g1 g2 from to l ->
    forall v, In v (map fst l) -> vgeneration v = from.
Proof.
  intros. destruct H as [_ [_ ?]]. destruct (split l) eqn:? . destruct H as [[_ ?] _].
  rewrite map_fst_split, Heqp in H0. simpl in H0. rewrite <- H in H0.
  now destruct H0 as [_ [_ ?]].
Qed.

Lemma frl_semi_iso: forall from to f_info g l l1 roots1 roots2 g1 g2,
    from <> to -> sound_gc_graph g -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    (forall i : nat, In i l -> (i < length roots1)%nat) ->
    no_dangling_dst g -> no_dangling_dst g1 -> copy_compatible g1 ->
    gc_graph_semi_iso g g1 from to l1 ->
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 ->
    exists l2, gc_graph_semi_iso g g2 from to (l2 ++ l1) /\
               roots2 = quasi_roots_map l f_info roots1 (l2 ++ l1).
Proof.
  do 4 intro. induction l; intros; inversion H10; subst.
  1: (exists []; split; auto). clear H10.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  change (root2forward (Znth (Z.of_nat a) roots1)) with
      (forward_p2forward_t (inl (Z.of_nat a)) roots1 g1) in H13. pose proof H13.
  assert (0 <= Z.of_nat a < Zlength roots1) by
      (rewrite Zlength_correct; split; [omega | apply inj_lt, H5; now left]).
  eapply (fr_O_semi_iso from to _ g g1) in H13; simpl; eauto.
  destruct H13 as [l3 [? [? ?N]]]. rewrite <- Heqroots3 in H13. simpl in H13.
  eapply IHl in H18; eauto. clear IHl.
  - destruct H18 as [l2 [? ?]]. exists (l2 ++ l3). rewrite <- app_assoc. split; auto.
    subst roots2. rewrite H13. rewrite quasi_roots_map_cons. f_equal.
    assert (DoubleNoDup (l2 ++ l3 ++ l1)) by (eapply semi_iso_DoubleNoDup; eauto).
    assert (Zlength roots1 = Zlength (live_roots_indices f_info)) by (now destruct H3).
    apply restricted_roots_map_incl; auto. simpl in N. red in N. repeat intro.
    apply (N _ H17 H18 _ H19). eapply semi_iso_In_map_fst in H20; eauto.
  - eapply fr_O_sound; eauto.
  - erewrite <- fr_graph_has_gen; eauto.
  - subst roots3; now apply upd_roots_rf_compatible.
  - subst roots3; eapply fr_roots_graph_compatible; eauto.
  - intros. rewrite H13, <- ZtoNat_Zlength. destruct H3.
    rewrite restricted_roots_map_Zlength, ZtoNat_Zlength; auto. apply H5; now right.
  - eapply fr_O_no_dangling_dst; eauto. now simpl.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma In_gather_indices_spec: forall l1 l2 z,
    In z (gather_indices l1 l2) <->
    exists s, In s l1 /\ 0 <= z < Zlength l2 /\ Znth z l2 = Znth s l2.
Proof.
  induction l1; intros; simpl. 1: intuition; now destruct H as [s [? _]].
  rewrite in_app_iff, IHl1, get_indices_spec.
  split; intros; [destruct H|]; [|destruct H as [s [? [? ?]]]..].
  - exists a. intuition.
  - exists s. split; [now right | now split].
  - destruct H; [left; subst a | right; exists s]; intuition.
Qed.

Lemma quasi_roots_map_Zlength: forall l1 f_info roots l2,
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Zlength (quasi_roots_map l1 f_info roots l2) = Zlength roots.
Proof.
  intros. unfold quasi_roots_map. rewrite restricted_map_Zlength; auto. intros.
  rewrite In_gather_indices_spec in H0. destruct H0 as [s [? [? ?]]]. now rewrite H.
Qed.

Lemma root_map_idempotent: forall f, idempotent f -> idempotent (root_map f).
Proof.
  intros. unfold idempotent in *. intros. unfold root_map. destruct x; auto.
  now rewrite H.
Qed.

Lemma semi_iso_In_map_snd: forall (g1 g2 : LGraph) (from to : nat) l,
  gc_graph_semi_iso g1 g2 from to l ->
  forall v : VType, In v (map snd l) -> ~ vvalid g1 v.
Proof.
  intros. destruct H as [_ [_ ?]]. destruct (split l) eqn:? .
  destruct H as [_ [[_ [? _]] _]]. rewrite map_snd_split, Heqp in H0. simpl in H0.
  rewrite H in H0. now destruct H0.
Qed.

Lemma frr_semi_iso: forall (from to : nat) (f_info : fun_info) (roots1 roots2: roots_t)
                           (g1 g2 : LGraph),
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> gen_unmarked g1 from ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> copy_compatible g1 ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    exists l, gc_graph_semi_iso g1 g2 from to l /\ roots2 = roots_map l roots1.
Proof.
  intros. pose proof (semi_iso_refl g1 from to H0 H2). red in H7.
  eapply frl_semi_iso in H7; eauto.
  - destruct H7 as [l2 [? ?]]. rewrite app_nil_r in *. exists l2. split; auto.
    rewrite H9. apply Znth_list_eq. rewrite !quasi_roots_map_Zlength by
        (now destruct H3). split. 1: unfold roots_map; now rewrite Zlength_map.
    intros. unfold quasi_roots_map. destruct H3. rewrite restricted_map_Znth_same'.
    + unfold roots_map. rewrite Znth_map; auto.
      destruct (Znth j roots1) eqn:? ; simpl; auto. f_equal. apply list_map_bi_map.
      intro. eapply semi_iso_In_map_snd in H12; eauto. apply H12. red in H4.
      rewrite Forall_forall in H4. destruct H0. red in H0. rewrite H0. apply H4.
      rewrite <- filter_sum_right_In_iff, <- Heqr. now apply Znth_In.
    + intros. rewrite In_gather_indices_spec in H12. destruct H12 as [_ [_ [? _]]].
      now rewrite H3.
    + apply root_map_idempotent, list_map_idempotent.
      eapply semi_iso_DoubleNoDup; eauto.
    + rewrite In_gather_indices_spec. exists j. rewrite <- H3. split3; auto.
      rewrite <- (Z2Nat.id j) by omega. apply in_map. rewrite nat_inc_list_In_iff.
      rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_lt; omega.
  - intros. now rewrite nat_inc_list_In_iff in H9.
Qed.

Lemma svfl_semi_iso: forall from to v l l1 g1 g2 g3 roots f_info,
    from <> to -> sound_gc_graph g1 -> sound_gc_graph g2 -> graph_has_gen g2 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g2 ->
    no_dangling_dst g1 -> no_dangling_dst g2 -> roots_have_no_gen roots from ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g2 v)))%nat) ->
    ~ vvalid g1 v -> vvalid g2 v -> raw_mark (vlabel g2 v) = false ->
    vgeneration v <> from -> copy_compatible g2 ->
    gc_graph_semi_iso g1 g2 from to l1 ->
    scan_vertex_for_loop from to v l g2 g3 ->
    exists l2, gc_graph_semi_iso g1 g3 from to (l2 ++ l1) /\
               roots = roots_map (l2 ++ l1) (roots_map l1 roots).
Proof.
  do 3 intro. induction l; intros; inversion H15; subst; clear H15.
  - exists []. simpl. split; auto. symmetry. apply surjective, roots_map_bijective.
    eapply (semi_iso_DoubleNoDup _ _ from); eauto.
  - pose proof H18. change (forward_p2forward_t (inr (v, Z.of_nat a)) [] g2) with
                        (forward_p2forward_t (inr (v, Z.of_nat a)) roots g2) in H18.
    assert (forward_p_compatible (inr (v, Z.of_nat a)) roots g2 from). {
      simpl. destruct H1. red in H1. rewrite <- H1. intuition.
      rewrite Zlength_correct. apply inj_lt, H8. now left. }
    eapply (fr_O_semi_iso _ _ _ g1) in H18; eauto.
    destruct H18 as [l3 [? [? _]]]. simpl in H18.
    assert (sound_gc_graph g4) by (eapply fr_O_sound; eauto).
    assert (graph_has_v g2 v) by (destruct H1; red in H1; now rewrite <- H1).
    eapply (IHl (l3 ++ l1) g1) in H21; eauto.
    + destruct H21 as [l2 [? ?]]. exists (l2 ++ l3). rewrite <- app_assoc. split; auto.
      rewrite H22 at 1. f_equal. rewrite H18 at 1.
      apply surjective, roots_map_bijective.
      eapply (semi_iso_DoubleNoDup _ _ from); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_right_roots_graph_compatible; eauto.
    + eapply fr_O_no_dangling_dst; eauto.
    + intros. erewrite <- fr_raw_fields; eauto. apply H8; now right.
    + destruct H19. red in H19. rewrite H19. eapply fr_graph_has_v; eauto.
    + erewrite <- fr_raw_mark; eauto.
    + eapply (fr_copy_compatible O from); eauto.
Qed.

Lemma svwl_semi_iso: forall from to l l1 roots f_info g1 g2 g3,
    from <> to -> sound_gc_graph g1 -> sound_gc_graph g2 -> graph_has_gen g2 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g2 ->
    no_dangling_dst g1 -> no_dangling_dst g2 -> roots_have_no_gen roots from ->
    (forall i, In i l -> ~ gen_has_index g1 to i) -> copy_compatible g2 ->
    gen_unmarked g2 to -> gc_graph_semi_iso g1 g2 from to l1 ->
    scan_vertex_while_loop from to l g2 g3 ->
    exists l2, gc_graph_semi_iso g1 g3 from to (l2 ++ l1) /\
               roots = roots_map (l2 ++ l1) (roots_map l1 roots).
Proof.
  do 3 intro. induction l; intros; inversion H12; subst.
  - exists []; simpl. split; auto. assert (bijective (roots_map l1) (roots_map l1)). {
      apply roots_map_bijective. eapply semi_iso_DoubleNoDup; eauto. }
    symmetry. now apply surjective.
  - eapply IHl; eauto. intros. apply H8. now right.
  - pose proof H17. eapply (svfl_semi_iso _ _ _ _ _ g1) in H17; eauto.
    + destruct H17 as [l3 [? ?]]. eapply (IHl (l3 ++ l1) _ _ g1) in H20; eauto.
      * destruct H20 as [l2 [? ?]]. exists (l2 ++ l3). rewrite <- app_assoc.
        split; auto. rewrite H19 at 1. f_equal. rewrite H17 at 1.
        apply surjective, roots_map_bijective. eapply semi_iso_DoubleNoDup; eauto.
      * eapply svfl_P_holds; eauto. apply fr_O_sound.
      * erewrite <- svfl_graph_has_gen; eauto.
      * red. rewrite Forall_forall. intros. eapply svfl_graph_has_v; eauto.
        red in H4. rewrite Forall_forall in H4. now apply H4.
      * eapply (svfl_no_dangling_dst from to); eauto. 1: split; now simpl. intros.
        now rewrite nat_inc_list_In_iff in H18.
      * intros. apply H8. now right.
      * eapply svfl_copy_compatible; eauto.
      * eapply svfl_gen_unmarked; eauto.
    + intros. now rewrite nat_inc_list_In_iff in H14.
    + destruct H0. red in H0. rewrite H0. intro. destruct H18. simpl in H19.
      apply (H8 a); [left |]; auto.
    + destruct H1. red in H1. rewrite H1. split; now simpl.
Qed.

Lemma frr_roots_graph_compatible: forall from to f_info roots1 g1 roots2 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_graph_compatible roots2 g2.
Proof.
  intros from to f_info roots1 g1 roots2 g2 H H0 H1 Hc H2 H3.
  red in H3. remember (nat_inc_list (Datatypes.length roots1)).
  assert (forall i, In i l -> i < length roots1)%nat by
      (intros; subst l; now rewrite nat_inc_list_In_iff in H4). clear Heql.
  revert g1 roots1 g2 roots2 H0 H1 Hc H2 H3 H4.
  induction l; intros; inversion H3; subst; auto; clear H3.
  assert (forward_p_compatible (inl (Z.of_nat a)) roots1 g1 from). {
    simpl. rewrite Zlength_correct. split; [omega | apply inj_lt].
    apply H4. now left. }
  eapply (fr_roots_graph_compatible O from to (inl (Z.of_nat a)))
    with (f_info := f_info) in H2; eauto.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  eapply (IHl g3 roots3); eauto.
  - erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
  - subst roots3. now apply upd_roots_rf_compatible.
  - intros. subst roots3. rewrite <- ZtoNat_Zlength, upd_roots_Zlength, ZtoNat_Zlength.
    1: apply H4; now right. destruct Hc; auto.
Qed.

Definition marked_in_gen (g1 g2: LGraph) (gen: nat) (v: VType): Prop :=
  raw_mark (vlabel g2 v) = true /\ vvalid g1 v /\ vgeneration v = gen.

Definition roots_reachable_in_gen (g: LGraph) (roots: roots_t)
           (gen: nat) (v: VType): Prop :=
  reachable_through_set g (filter_sum_right roots) v /\ vgeneration v = gen.

Definition reachable_iff_marked (g1 g2: LGraph) (roots: roots_t) (gen: nat): Prop :=
  forall v, roots_reachable_in_gen g1 roots gen v <-> marked_in_gen g1 g2 gen v.

Lemma semi_quasi_iso: forall from to g1 g2 l roots1 roots2,
    reachable_iff_marked g1 g2 roots1 from ->
    gc_graph_semi_iso g1 g2 from to l -> roots2 = roots_map l roots1 ->
    gc_graph_quasi_iso g1 roots1 g2 roots2 from to.
Proof.
  intros from to g1 g2 l roots1 roots2 Hr H H0. destruct H as [? [? ?]]. split; auto.
  exists l. split; auto. split.
  - intros. specialize (H1 _ _ H3). now destruct H1.
  - destruct (split l) as [from_l to_l]. destruct H2 as [? [? ?]].
    split3; auto. destruct H2. split; auto. intros. red in Hr.
    unfold roots_reachable_in_gen, marked_in_gen in Hr. now rewrite Hr, H5.
Qed.

Lemma reachable_from_roots: forall (g: LGraph) (roots: roots_t) v,
    reachable_through_set g (filter_sum_right roots) v <->
    exists i r, 0 <= i < Zlength roots /\ Znth i roots = inr r /\
                reachable g r v.
Proof.
  intros. unfold reachable_through_set. split; intros.
  - destruct H as [s [? ?]]. rewrite <- filter_sum_right_In_iff in H.
    apply In_Znth in H. destruct H as [i [? ?]]. exists i, s. split3; auto.
  - destruct H as [i [r [? [? ?]]]]. exists r. split; auto.
    rewrite <- filter_sum_right_In_iff, <- H0. now apply Znth_In.
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
  intros. destruct H as [? [? ?]]. red in H, H0, H2, H3. rewrite step_spec in H1.
  destruct H1 as [e [? [? ?]]]. rewrite <- H5, H. rewrite H2 in H1. destruct H1.
  now apply (H0 (fst e)).
Qed.

Lemma pcv_edge: forall (g: LGraph) old_v new_v z,
    sound_gc_graph g -> no_dangling_dst g -> vvalid g old_v -> ~ vvalid g new_v ->
    g |= old_v ~> z <-> (pregraph_copy_v g old_v new_v) |= new_v ~> z.
Proof.
  intros g old_v new_v z H0 Hd H H1.
  unfold edge. destruct H0 as [? [? ?]]. red in H0, H2, H3.
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
      destruct Hg as [? [? ?]]. pose proof (pcv_src_edge g old_v new_v H6). red in H7.
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
  pose proof H0. destruct H0 as [? [? ?]]. red in H0, H8, H9.
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

Lemma fr_O_copied_vertex_prop: forall from to p g1 g2 roots,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    forward_p_compatible p roots g1 from ->
    forward_relation from to O (forward_p2forward_t p roots g1) g1 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  intros. destruct p; simpl in H3, H4.
  - destruct (Znth z roots) eqn:? ; [destruct s |]; inversion H4; subst; try easy.
    apply lcv_copied_vertex_prop; auto.
  - destruct p as [v n]. destruct H3 as [? [? [? ?]]]. rewrite H7 in H4. simpl in H4.
    destruct (Znth n (make_fields g1 v)) eqn:? ; [destruct s|]; simpl in H4;
      inversion H4; subst; try easy.
    + subst new_g.
      assert (fst e = v) by (apply make_fields_Znth_edge in Heqf; auto; now subst e).
      assert (evalid g1 e). {
        destruct H1 as [? [? ?]]. red in H1, H10, H11. rewrite H10. split; rewrite H9.
        1: easy. unfold get_edges. rewrite <- filter_sum_right_In_iff, <- Heqf.
        apply Znth_In. now rewrite make_fields_eq_length. }
      apply lgd_copied_vertex_prop; auto. rewrite H9; auto.
    + subst new_g. eapply lcv_copied_vertex_prop in H5; eauto.
      remember (lgraph_copy_v g1 (dst g1 e) to) as g3.
      assert (fst e = v) by (apply make_fields_Znth_edge in Heqf; auto; now subst e).
      assert (dst g1 e = dst g3 e). {
        subst g3. simpl. rewrite pcv_dst_old; auto. rewrite H9.
        now apply graph_has_v_not_eq with (to := to) in H3. }
      assert (new_copied_v g1 to = copied_vertex (vlabel g3 (dst g3 e))). {
        rewrite <- H10. subst g3. simpl. rewrite ucov_copied_vertex. easy. }
      assert (graph_has_e g1 e). { split; rewrite H9.
        1: easy. unfold get_edges. rewrite <- filter_sum_right_In_iff, <- Heqf.
        apply Znth_In. now rewrite make_fields_eq_length. }
      assert (evalid g1 e). {
        destruct H1 as [? [? ?]]. red in H1, H14, H15. now rewrite H14. }
      rewrite H12, H10. apply lgd_copied_vertex_prop; try (now rewrite <- H10).
      * subst g3. apply lcv_no_dangling_dst; auto. red in H2. apply H2 with v; auto.
        destruct H13. now rewrite H9 in H15.
      * subst g3. rewrite <- lcv_graph_has_gen; auto.
      * now rewrite H9, <- H10.
      * rewrite <- H10. subst g3. apply lcv_raw_mark_old.
      * subst g3. destruct H1 as [? [? ?]]. pose proof H0.
        apply (lcv_edge_valid _ (dst g1 e)) in H0; auto. red in H0. rewrite H0.
        split; rewrite H9. 1: apply lcv_graph_has_v_old; auto.
        unfold get_edges, make_fields. rewrite <- lcv_raw_fields; auto.
        fold (make_fields g1 v). fold (get_edges g1 v). destruct H13.
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
  intros. remember (length p) as n. assert (length p <= n)%nat by omega. rewrite Heqn.
  clear Heqn. revert r p H1 H2 H3. induction n; intros.
  - destruct p. 2: simpl in H3; exfalso; omega. destruct H2 as [[_ ?] _]. simpl in H2.
    subst v. left; auto.
  - destruct p. 1: destruct H2 as [[_ ?] _]; simpl in H2; subst v; left; auto.
    assert (g |= (dst g e, p) is dst g e ~o~> v satisfying (fun _ => True)). {
      change (e :: p) with ([] ++ e :: p) in H2.
      apply reachable_by_path_app_cons in H2. now destruct H2. }
    destruct H2 as [_ [? _]]. rewrite valid_path_cons_iff in H2. red in H0.
    destruct H2 as [? [[? [? ?]] ?]]. destruct H as [? [? ?]]. red in H, H9, H10.
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
    + destruct H14. assert (length p <= n)%nat by (simpl in H3; omega).
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
  remember (length p) as n. assert (length p <= n)%nat by omega. rewrite Heqn.
  clear Heqn. revert r p H6 H1 H4 H5. induction n; intros.
  - destruct p. 2: simpl in H6; omega. destruct H5 as [[_ ?] _]. simpl in H5.
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
      destruct H5 as [? [[? [? ?]] ?]]. destruct H as [? [? ?]]. red in H, H16, H17.
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
      * destruct H10. assert (length p <= n)%nat by (simpl in H6; omega).
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
  subst s. remember (length p) as n. assert (length p <= n)%nat by omega. clear Heqn.
  revert r p H4 H3. induction n; intros.
  - destruct p. 2: simpl in H4; omega. destruct H3 as [[_ ?] [? _]]. simpl in *.
    subst v. left. apply reachable_refl. now simpl.
  - destruct (in_dec equiv_dec e p).
    2: left; exists (r, p); rewrite no_edge_gen_dst_equiv; auto.
    change p with (snd (r, p)) in i. eapply reachable_path_unique_edge in i; eauto.
    destruct i as [p1 [p2 [? [? [? ?]]]]]. apply reachable_by_path_app_cons in H5.
    destruct H5. rewrite app_length in H8. simpl in H8.
    eapply copied_vertex_reachable_by_path in H9; eauto. destruct H9.
    1: right; auto. destruct H9 as [p' [? ?]]. assert (length p' <= n)%nat by omega.
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
                   reachable_through_set g (filter_sum_right roots) (fst e).

Definition edge_from_gen_cond (p : forward_p_type) (gen: nat) :=
  match p with
  | inl _ => True
  | inr (v, _) => vgeneration v = gen
  end.

Lemma no_edge2gen_bep: forall g roots from to,
    sound_gc_graph g -> gen2gen_no_edge g to from ->
    backward_edge_prop g roots from to.
Proof.
  intros. red in H0 |-* . intros. destruct e as [[gen vidx] eidx]. simpl in *.
  subst gen. destruct H as [_ [? _]]. red in H. rewrite H in H1. apply H0 in H1.
  unfold VType in *. now rewrite H3 in H1.
Qed.

Lemma fr_O_backward_edge_prop: forall from to p g1 g2 roots f_info,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    roots_fi_compatible roots f_info -> forward_p_compatible p roots g1 from ->
    forward_relation from to O (forward_p2forward_t p roots g1) g1 g2 ->
    copied_vertex_prop g1 from to -> gen_unmarked g1 to ->
    edge_from_gen_cond p to -> backward_edge_prop g1 roots from to ->
    backward_edge_prop g2 (upd_roots from to p g1 roots f_info) from to.
Proof.
  intros from to p g1 g2 roots f_info H H0 H1 H2 H3 H4 H5 H6 Hu Hc H7.
  assert (He: forall e, evalid g1 e -> fst e <> new_copied_v g1 to). {
    intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1 in H8.
    destruct H8. eapply graph_has_v_not_eq in H8; eauto. }
  pose proof H1. destruct H8 as [Hv _]. red in Hv. destruct p; simpl in H4, H5.
  - destruct (Znth z roots) eqn:? ;
      [destruct s|]; simpl in *; rewrite Heqr; inversion H5; subst; clear H5; try easy.
    + now rewrite if_false.
    + rewrite if_true, H11; auto. red in H7 |-* ; intros. specialize (H7 _ H5 H8 H9).
      rewrite reachable_from_roots in *. destruct H7 as [i [r [? [? ?]]]].
      destruct H3. rewrite upd_bunch_Zlength; auto.
      destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                         (Znth z (live_roots_indices f_info))).
      * exists i, (copied_vertex (vlabel g2 v)). rewrite upd_bunch_same; auto.
        do 2 (split; auto). specialize (H13 _ _ H7 H4 e0). rewrite H13, Heqr in H10.
        inversion H10. subst v. pose proof H12. apply reachable_foot_valid in H14.
        eapply copied_vertex_reachable in H12; eauto. destruct H12; auto.
        rewrite Hv in H14. specialize (H6 _ H14 H12). destruct H6 as [_ [_ [? _]]].
        rewrite H6 in H8. now rewrite H8 in H.
      * exists i, r. rewrite upd_bunch_diff; auto.
    + rewrite if_true, H10; auto. red in H7 |-* ; intros. simpl in H5.
      rewrite pcv_evalid_iff in H5. simpl in H9.
      assert (Hi: ~ vvalid g1 (new_copied_v g1 to)). {
        rewrite Hv. intro. now apply (graph_has_v_not_eq _ to) in H11. } destruct H5.
      * rewrite pcv_dst_old in H9. 2: apply He; auto.
        specialize (H7 _ H5 H8 H9). rewrite reachable_from_roots in *.
        destruct H7 as [i [r [? [? ?]]]]. destruct H3. pose proof H12.
        rewrite upd_bunch_Zlength; auto. apply reachable_head_valid in H14.
        destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                           (Znth z (live_roots_indices f_info))).
        -- exists i, (new_copied_v g1 to). rewrite upd_bunch_same; auto.
           do 2 (split; auto). specialize (H13 _ _ H7 H4 e0).
           rewrite H13, Heqr in H11. inversion H11. subst v. simpl.
           pose proof H12. apply reachable_head_valid in H15.
           rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)) in H12; auto.
           destruct H12 as [? | [? ?]]; auto. now rewrite <- H12, H8 in H.
        -- exists i, r. rewrite upd_bunch_diff; auto. do 2 (split; auto). simpl.
           rewrite pcv_reachable_old; auto.
      * rewrite reachable_from_roots. destruct H3. rewrite upd_bunch_Zlength; auto.
        exists z, (new_copied_v g1 to). rewrite upd_bunch_same; auto.
        do 2 (split; auto). simpl. rewrite in_map_iff in H5. destruct H5 as [ve [? ?]].
        subst e. simpl. apply reachable_refl. rewrite pcv_vvalid_iff. now right.
  - simpl. destruct p as [x n]. destruct H4 as [? [? [? ?]]].
    rewrite H9 in H5. simpl in H5.
    assert (forall e, Znth n (make_fields g1 x) = inr e -> fst e = x) by
        (intros; apply make_fields_Znth_edge in H11; auto; now subst e).
    assert (forall e, Znth n (make_fields g1 x) = inr e -> graph_has_e g1 e). {
      destruct H1 as [? [? ?]]. red in H1, H12, H13. intros. split; rewrite H11; auto.
      unfold get_edges. rewrite <- filter_sum_right_In_iff, <- H14.
      apply Znth_In. now rewrite make_fields_eq_length. }
    assert (forall e, Znth n (make_fields g1 x) = inr e -> evalid g1 e). {
      intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1. now apply H12. }
    assert (Ht: forall e, evalid g1 e -> vgeneration (fst e) = to ->
                          raw_mark (vlabel g1 (fst e)) = false). {
      intros. red in Hu. destruct e as [v ?]. simpl in *.
      destruct H1 as [_ [? _]]. red in H1. rewrite H1 in H14. destruct H14.
      simpl in H14. destruct v as [gen idx]. simpl in *. subst gen. destruct H14.
      simpl in *. now specialize (Hu H14 _ H15). }
    destruct (Znth n (make_fields g1 x)) eqn:?;
    [destruct s |]; simpl in H5; inversion H5; subst; clear H5; try easy.
    + red in H7 |-* ; intros. subst new_g. destruct_eq_dec e0 e.
      * exfalso. subst e0. simpl in H15. rewrite updateEdgeFunc_eq in H15.
        assert (graph_has_e g1 e) by (now apply H12). red in H2. destruct H16.
        specialize (H2 _ H16 _ H18). specialize (H6 _ H2 H17).
        destruct H6 as [_ [? _]]. now rewrite <- H15, H6 in H.
      * rewrite reachable_from_roots. simpl in *.
        rewrite updateEdgeFunc_neq in H15; auto. specialize (H7 _ H5 H14 H15).
        rewrite reachable_from_roots in H7. destruct H7 as [i [r [? [? ?]]]].
        eapply copied_vertex_pgd_reachable in H19; eauto. exists i, r.
        do 2 (split; auto). destruct H19; auto. rewrite Ht in H19; auto. easy.
    + red in H7 |-* ; intros. subst new_g. simpl in H5, H15. destruct_eq_dec e0 e.
      * exfalso. subst e0. rewrite updateEdgeFunc_eq in H15.
        unfold new_copied_v in H15. simpl in H15. now rewrite <- H15 in H.
      * rewrite updateEdgeFunc_neq in H15; auto. rewrite reachable_from_roots.
        simpl. rewrite pcv_evalid_iff in H5.
        assert (Hi: ~ vvalid g1 (new_copied_v g1 to)). {
          rewrite Hv. intro. now apply (graph_has_v_not_eq _ to) in H18. }
        assert (He': fst e <> new_copied_v g1 to) by
            (apply He, H13; auto). destruct H5.
        -- rewrite pcv_dst_old in H15. 2: apply He; auto. specialize (H7 _ H5 H14 H15).
           rewrite reachable_from_roots in H7. destruct H7 as [i [r [? [? ?]]]].
           exists i, r. do 2 (split; auto). pose proof H19.
           apply reachable_head_valid in H20.
           rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to))
             in H19; auto.
           assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r (fst e0)) by easy.
           apply (copied_vertex_pgd_reachable _ e to) in H21; simpl in *.
           ++ rewrite pcv_dst_old in H21; auto.
              rewrite ucov_copied_vertex in H21. destruct H21; auto.
              rewrite ucov_not_eq in H21. 2: intro; now rewrite H22, H14 in H.
              rewrite lacv_vlabel_old in H21. 2: apply He; auto.
              rewrite Ht in H21; auto. easy.
           ++ apply lcv_sound; auto.
           ++ rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
           ++ rewrite pcv_evalid_iff. left. apply H13; auto.
           ++ rewrite pcv_dst_old; auto. apply ucov_rawmark.
        -- rewrite in_map_iff in H5. destruct H5 as [ve [? ?]]. subst e0. simpl in *.
           assert (evalid g1 e) by (apply H13; auto).
           assert (vgeneration (fst e) = to). {
             apply make_fields_Znth_edge in Heqf; auto. subst e. now simpl. }
           specialize (H7 _ H5 H19 (eq_refl (vgeneration (dst g1 e)))).
           rewrite reachable_from_roots in H7. destruct H7 as [i [r [? [? ?]]]].
           exists i, r. do 2 (split; auto). pose proof H21.
           apply reachable_head_valid in H22.
           rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to))
             in H21; auto.
           assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r (fst e)) by easy.
           apply (copied_vertex_pgd_reachable _ e to) in H23; simpl in *.
           ++ rewrite pcv_dst_old in H23; auto.
              rewrite ucov_copied_vertex, ucov_not_eq in H23.
              2: intro; now rewrite H24, H19 in H.
              rewrite lacv_vlabel_old in H23; auto.
              rewrite Ht in H23; auto. destruct H23; [|easy].
              apply reachable_trans with (fst e); auto. exists (fst e, [e]).
              split; split; simpl; auto. 3: red; rewrite Forall_forall; intros; auto.
              1: rewrite updateEdgeFunc_eq; auto. destruct H1 as [? [? ?]]. red in H25.
              split. 1: rewrite pcv_src_old; auto. red. simpl. red in H1, H24.
              rewrite updateEdgeFunc_eq. rewrite pcv_src_old; auto. split3.
              ** rewrite pcv_evalid_iff. now left.
              ** rewrite pcv_vvalid_iff, H25. left. rewrite H1. rewrite H24 in H5.
                 now destruct H5.
              ** rewrite pcv_vvalid_iff. now right.
           ++ apply lcv_sound; auto.
           ++ rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
           ++ rewrite pcv_evalid_iff. now left.
           ++ rewrite pcv_dst_old; auto. apply ucov_rawmark.
Qed.

Definition reachable_or_marked (from: nat) (g: LGraph)
           (roots: roots_t) (v: VType): Prop :=
  vgeneration v = from /\ (reachable_through_set g (filter_sum_right roots) v \/
                           vvalid g v /\ raw_mark (vlabel g v) = true).

Definition reachable_or_marked_special_cond (g: LGraph) (roots: roots_t)
           (from to: nat) (p: forward_p_type): Prop :=
  match p with
  | inl _ => True
  | inr (v, _) => vgeneration v = to /\ backward_edge_prop g roots from to
  end.

Lemma fr_O_reachable_or_marked: forall
    (from to : nat) (p : forward_p_type) (g1 g2 : LGraph) (roots : roots_t) f_info,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g1 ->
    copied_vertex_prop g1 from to -> forward_p_compatible p roots g1 from ->
    reachable_or_marked_special_cond g1 roots from to p ->
    forward_relation from to O (forward_p2forward_t p roots g1) g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
              reachable_or_marked from g2 (upd_roots from to p g1 roots f_info) v.
Proof.
  intros from to p g1 g2 roots f_info H H0 H1 Hd H2 H3 H4 H5 Hb H6 v.
  assert (Hr: forall i r, 0 <= i < Zlength roots ->
                            Znth i roots = inr r -> graph_has_v g1 r). {
      intros. red in H3. rewrite Forall_forall in H3. apply H3.
      rewrite <- filter_sum_right_In_iff, <- H8. now apply Znth_In. }
  pose proof H1. destruct H7 as [Hv _]. red in Hv. destruct p; simpl in H5, H6.
  - destruct (Znth z roots) eqn:? ;
      [destruct s|]; simpl in *; rewrite Heqr; inversion H6; subst; clear H6; try easy.
    + now rewrite if_false.
    + rewrite if_true, H10; auto.
      split; intros; red in H6 |-* ; destruct H6; split; auto.
      * destruct H7; [| right]; auto. rewrite reachable_from_roots in H7.
        destruct H7 as [i [r [? [? ?]]]]. destruct H2.
        destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                           (Znth z (live_roots_indices f_info))).
        -- specialize (H11 _ _ H7 H5 e). rewrite H11, Heqr in H8. inversion H8.
           assert (vvalid g2 v) by (apply reachable_foot_valid in H9; auto).
           subst v0. clear H8. eapply copied_vertex_reachable in H9; eauto.
           destruct H9. 2: right; auto. left. rewrite reachable_from_roots.
           exists i, (copied_vertex (vlabel g2 r)).
           rewrite upd_bunch_Zlength, upd_bunch_same; auto.
        -- left. rewrite reachable_from_roots. exists i, r.
           rewrite upd_bunch_Zlength, upd_bunch_diff; auto.
      * destruct H7; [| right]; auto. rewrite reachable_from_roots in H7. destruct H2.
        rewrite upd_bunch_Zlength in H7; auto. destruct H7 as [i [r [? [? ?]]]].
        destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                           (Znth z (live_roots_indices f_info))).
        -- specialize (H8 _ _ H7 H5 e). rewrite upd_bunch_same in H9; auto.
           inversion H9. subst r. clear H9. rename v0 into r. left.
           rewrite reachable_from_roots. exists z, r. do 2 (split; auto).
           eapply copied_vertex_reachable_inv; eauto.
        -- left. rewrite reachable_from_roots. exists i, r.
           rewrite upd_bunch_diff in H9; auto.
    + rewrite if_true, H9; auto.
      assert (Hs: sound_gc_graph (lgraph_copy_v g1 v0 to)) by (now apply lcv_sound).
      assert (~ vvalid g1 (new_copied_v g1 to)). {
        rewrite Hv. intro. now apply graph_has_v_not_eq with (to := to) in H6. }
      split; intros; red in H7 |-* ; destruct H7; split; auto; destruct H8.
      * rewrite reachable_from_roots in H8. destruct H8 as [i [r [? [? ?]]]].
        destruct H2. assert (vvalid g1 r) by (now apply reachable_head_valid in H11).
        destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                           (Znth z (live_roots_indices f_info))).
        -- specialize (H12 _ _ H8 H5 e). rewrite H12, Heqr in H10. inversion H10.
           subst v0. rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)) in H11; auto.
           clear H10. destruct H11; [right | left].
           ++ subst v. rewrite lcv_raw_mark_old. destruct Hs. red in H10. rewrite H10.
              split; auto. apply lcv_graph_has_v_old; auto. now rewrite <- Hv.
           ++ rewrite reachable_from_roots. exists i, (new_copied_v g1 to).
              rewrite upd_bunch_Zlength, upd_bunch_same; auto. do 2 (split; auto).
              simpl. now destruct H8.
        -- left. rewrite reachable_from_roots. exists i, r.
           rewrite upd_bunch_Zlength, upd_bunch_diff; auto. do 2 (split; auto).
           simpl. rewrite pcv_reachable_old; auto.
      * destruct H8. right. destruct Hs. red in H11. rewrite H11.
        assert (graph_has_v g1 v) by (destruct H1; red in H1; now rewrite <- H1).
        split. 1: apply lcv_graph_has_v_old; auto. rewrite <- lcv_raw_mark; auto.
        intro. subst v0. now rewrite H9 in H10.
      * rewrite reachable_from_roots in *. destruct H8 as [i [r [? [? ?]]]].
        destruct H2. rewrite upd_bunch_Zlength in H8; auto.
        destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                           (Znth z (live_roots_indices f_info))).
        -- rewrite upd_bunch_same in H10; auto. specialize (H12 _ _ H8 H5 e).
           inversion H10. subst r. clear H10. simpl in H11. left. exists z, v0.
           rewrite (pcv_reachable_new _ _ (new_copied_v g1 to)); auto.
           2: destruct H1; red in H1; rewrite H1; apply (Hr z); auto.
           do 2 (split; auto). right. split; auto. intro. subst v. rewrite <- H7 in H.
           unfold new_copied_v in H. now simpl in H.
        -- left. rewrite upd_bunch_diff in H10; auto. simpl in H11.
           rewrite pcv_reachable_old in H11; auto. 1: exists i, r; auto.
           rewrite Hv. eapply Hr; eauto.
      * destruct H8. destruct_eq_dec v v0.
        -- subst v0. left. rewrite reachable_from_roots. exists z, v.
           do 2 (split; auto). apply reachable_refl. rewrite Hv. eapply Hr; eauto.
        -- right. destruct Hs. red in H12.
           rewrite H12, lcv_graph_has_v_iff in H8; auto. destruct H8.
           2: subst v; rewrite <- H7 in H; unfold new_copied_v in H; now simpl in H.
           split. 1: now rewrite <- Hv in H8. rewrite <- lcv_raw_mark in H10; auto.
  - simpl. destruct p as [x n]. destruct H5 as [? [? [? ?]]].
    rewrite H8 in H6. simpl in H6.
    assert (forall e, Znth n (make_fields g1 x) = inr e -> fst e = x) by
        (intros; apply make_fields_Znth_edge in H10; auto; now subst e).
    assert (forall e, Znth n (make_fields g1 x) = inr e -> graph_has_e g1 e). {
      destruct H1 as [? [? ?]]. red in H1, H11, H12. intros. split; rewrite H10; auto.
      unfold get_edges. rewrite <- filter_sum_right_In_iff, <- H13.
      apply Znth_In. now rewrite make_fields_eq_length. }
    assert (forall e, Znth n (make_fields g1 x) = inr e -> evalid g1 e). {
      intros. destruct H1 as [_ [? _]]. red in H1. rewrite H1. now apply H11. }
    destruct (Znth n (make_fields g1 x)) eqn:? ; [destruct s |]; simpl in H6;
      inversion H6; subst; try easy.
    + split; intros; red in H13 |-* ; destruct H13; split; auto; destruct H14.
      * rewrite reachable_from_roots in *. destruct H14 as [i [r [? [? ?]]]].
        subst new_g. simpl. assert (evalid g1 e) by (now apply H12).
        assert (vvalid g1 v) by (now apply reachable_foot_valid in H17).
        eapply copied_vertex_pgd_reachable in H17; eauto. destruct H17. 2: now right.
        left. exists i, r. auto.
      * subst new_g. simpl. now right.
      * rewrite reachable_from_roots in *. destruct H14 as [i [r [? [? ?]]]].
        subst new_g. simpl in *. left. exists i, r. do 2 (split; auto).
        eapply copied_vertex_pgd_reachable_inv in H17; eauto.
      * subst new_g. simpl in H14. now right.
    + assert (Hs: sound_gc_graph (lgraph_copy_v g1 (dst g1 e) to)) by
          (now apply lcv_sound). assert (~ vvalid g1 (new_copied_v g1 to)). {
        rewrite Hv. intro. now apply graph_has_v_not_eq with (to := to) in H13. }
      split; intros; red in H14 |-* ; destruct H14; split; auto; destruct H16.
      * rewrite reachable_from_roots in *. destruct H16 as [i [r [? [? ?]]]].
        subst new_g. simpl. assert (vvalid g1 r) by
            (now apply reachable_head_valid in H18).
        rewrite <- (pcv_reachable_old _ (dst g1 e) (new_copied_v g1 to)) in H18; auto.
        assert (reachable (lgraph_copy_v g1 (dst g1 e) to) r v) by (now simpl).
        assert (fst e <> new_copied_v g1 to) by
            (rewrite H10; auto; intro; subst x; now rewrite <- Hv in H5).
        apply (copied_vertex_pgd_reachable _ e to) in H20; auto; simpl in *.
        -- rewrite pcv_dst_old, ucov_copied_vertex in H20; auto. destruct H20.
           ++ left. exists i, r. auto.
           ++ right; split; auto. apply reachable_foot_valid in H18. auto.
        -- rewrite pcv_dst_old; auto. apply lcv_copied_vertex_prop; auto.
        -- rewrite pcv_evalid_iff. left. now apply H12.
        -- rewrite pcv_dst_old; auto. apply ucov_rawmark.
      * destruct H16. right. subst new_g. simpl. split.
        -- rewrite pcv_vvalid_iff. now left.
        -- rewrite ucov_not_eq. 2: intro; subst v; now rewrite H15 in H17.
           rewrite lacv_vlabel_old; auto. intro. now subst v.
      * rewrite reachable_from_roots in *. destruct H16 as [i [r [? [? ?]]]].
        subst new_g. remember (lgraph_copy_v g1 (dst g1 e) to) as g3.
        assert (fst e <> new_copied_v g1 to) by
            (rewrite H10; auto; intro; subst x; now rewrite <- Hv in H5).
        assert (dst g1 e = dst g3 e) by
            (subst g3; simpl; rewrite pcv_dst_old; auto).
        assert (new_copied_v g1 to = copied_vertex (vlabel g3 (dst g3 e))). {
          rewrite <- H20. subst g3. simpl. rewrite ucov_copied_vertex. easy. }
        rewrite H21 in H18. apply copied_vertex_pgd_reachable_inv with (to := to)
          in H18; try (now rewrite <- H20); try (now subst g3).
        -- rewrite Heqg3 in H18. simpl in H18. assert (vvalid g1 r) by
               (rewrite Hv; apply Hr with i; auto). left. exists i, r.
           rewrite pcv_reachable_old in H18; auto.
        -- rewrite <- H20. subst g3. apply lcv_copied_vertex_prop; auto.
        -- subst g3. apply lcv_no_dangling_dst; auto. red in Hd.
           assert (graph_has_e g1 e) by (now apply H11). destruct H22.
           apply Hd with (fst e); auto.
        -- subst g3. simpl. rewrite pcv_evalid_iff. left. now apply H12.
        -- rewrite <- H20. subst g3. apply lcv_raw_mark_old.
      * destruct H16. subst new_g. simpl in *. rewrite pcv_vvalid_iff in H16.
        assert (v <> new_copied_v g1 to). {
          intro. subst. unfold new_copied_v in *. simpl in *.
          now rewrite <- H14 in H. } destruct H16. 2: easy.
        destruct_eq_dec (dst g1 e) v.
        -- subst v. rewrite ucov_rawmark in H17. left. destruct Hb as [He Hb].
           red in Hb. assert (evalid g1 e) by (apply H12; auto).
           assert (vgeneration (fst e) = to). {
             apply make_fields_Znth_edge in Heqf; auto. subst e. now simpl. }
           specialize (Hb _ H19 H20 H14). rewrite reachable_from_roots in *.
           destruct Hb as [i [r [? [? ?]]]]. exists i, r. do 2 (split; auto).
           apply reachable_trans with (fst e); auto. destruct H1 as [? [? ?]].
           red in H1, H24, H25. exists (fst e, [e]). split; split; simpl; auto.
           2: red; rewrite Forall_forall; intros; auto. rewrite H25. split; auto.
           red. do 2 (split; auto). rewrite H25. rewrite H24 in H19. destruct H19.
           rewrite <- H1 in H19. easy.
        -- rewrite ucov_not_eq in H17; auto. rewrite lacv_vlabel_old in H17; auto.
Qed.

Lemma frr_reachable_or_marked: forall from to f_info (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, reachable_or_marked from g1 roots1 v <->
              reachable_or_marked from g2 roots2 v.
Proof.
  intros. red in H7. remember (nat_inc_list (Datatypes.length roots1)) as l.
  assert (forall i : nat, In i l -> (i < length roots1)%nat). {
    intros. subst l. now rewrite nat_inc_list_In_iff in H8. } clear Heql.
  revert g1 g2 roots1 roots2 H0 H1 H2 H3 H4 H5 H6 H7 H8.
  induction l; intros; inversion H7; subst; clear H7; try easy.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  change (root2forward (Znth (Z.of_nat a) roots1)) with
      (forward_p2forward_t (inl (Z.of_nat a)) roots1 g1) in H11. pose proof H11.
  assert (0 <= Z.of_nat a < Zlength roots1) by
      (rewrite Zlength_correct; split; [omega | apply inj_lt, H8; now left]).
  eapply fr_O_reachable_or_marked with (v := v) in H11; eauto. 2: easy. rewrite H11.
  rewrite <- Heqroots3 in *. apply IHl; auto.
  - eapply fr_O_sound; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - subst roots3. apply upd_roots_rf_compatible; auto.
  - subst. eapply fr_roots_graph_compatible; eauto.
  - eapply fr_O_no_dangling_dst; eauto. now simpl.
  - eapply fr_O_copied_vertex_prop; eauto. now simpl.
  - eapply fr_copy_compatible; eauto.
  - intros. subst. destruct H2. rewrite <- ZtoNat_Zlength, upd_roots_Zlength; auto.
    rewrite ZtoNat_Zlength. apply H8. now right.
Qed.

Lemma svfl_reachable_or_marked: forall from to f_info (roots: roots_t) r l g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> graph_has_v g1 r ->
    raw_mark (vlabel g1 r) = false -> vgeneration r = to -> gen_unmarked g1 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 r)))%nat) ->
    backward_edge_prop g1 roots from to -> scan_vertex_for_loop from to r l g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
              reachable_or_marked from g2 roots v.
Proof.
  intros until l. induction l; intros; inversion H13; subst; clear H13; try easy.
  change (forward_p2forward_t (inr (r, Z.of_nat a)) [] g1)
    with (forward_p2forward_t (inr (r, Z.of_nat a)) roots g1) in H16. pose proof H16.
  assert (forward_p_compatible (inr (r, Z.of_nat a)) roots g1 from). {
    simpl. do 3 (split; auto). 1: omega. rewrite Zlength_correct. apply inj_lt, H11.
    now left. } eapply fr_O_reachable_or_marked with (v := v) in H4; eauto.
  2: simpl; split; auto. remember (vgeneration r) as to. simpl in H4. rewrite H4.
  apply IHl; auto.
  - eapply fr_O_sound; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto. subst to; auto.
  - eapply fr_gen_unmarked; eauto.
  - eapply fr_right_roots_graph_compatible; eauto.
  - eapply fr_O_no_dangling_dst; eauto.
  - eapply fr_O_copied_vertex_prop; eauto.
  - eapply fr_copy_compatible; eauto.
  - erewrite <- fr_raw_fields; eauto. intros. apply H11. now right.
  - eapply fr_O_backward_edge_prop with (f_info := f_info) in H16; eauto. now simpl.
Qed.

Definition null_fun_info: fun_info.
Proof.
  apply (Build_fun_info 0 nil).
  - intros. inversion H.
  - rewrite Zlength_nil. rep_omega.
  - rep_omega.
Qed.

Lemma svfl_roots_graph_compatible: forall from to roots v l g1 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 ->
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 v)))%nat) ->
    roots_graph_compatible roots g1 -> scan_vertex_for_loop from to v l g1 g2 ->
    roots_graph_compatible roots g2.
Proof.
  intros until l. induction l; intros; inversion H7; subst; clear H7; try easy.
  change (forward_p2forward_t (inr (v, Z.of_nat a)) [] g1)
    with (forward_p2forward_t (inr (v, Z.of_nat a)) roots g1) in H10. pose proof H10.
  assert (forward_p_compatible (inr (v, Z.of_nat a)) roots g1 from). {
    simpl. do 3 (split; auto). 1: omega. rewrite Zlength_correct. apply inj_lt, H5.
    now left. }
  eapply fr_roots_graph_compatible with (f_info := null_fun_info) in H6; eauto.
  simpl in H6. apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply (fr_copy_compatible O from to); eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto.
  - intros. erewrite <- fr_raw_fields; eauto. apply H5. now right.
Qed.

Lemma svfl_copied_vertex_prop: forall from to v l g1 g2,
    from <> to -> graph_has_gen g1 to -> sound_gc_graph g1 -> no_dangling_dst g1 ->
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 v)))%nat) ->
    copy_compatible g1 -> scan_vertex_for_loop from to v l g1 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  intros until l. induction l; intros; inversion H8; subst; clear H8; try easy.
  pose proof H12. assert (forward_p_compatible (inr (v, Z.of_nat a)) [] g1 from). {
    simpl. do 3 (split; auto). 1: omega. rewrite Zlength_correct. apply inj_lt, H6.
    now left. } eapply (fr_O_copied_vertex_prop _ _ _ g1 g3) in H9; eauto.
  apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_O_sound; eauto.
  - eapply fr_O_no_dangling_dst; eauto. red. simpl. constructor.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto.
  - intros. erewrite <- fr_raw_fields; eauto. apply H6. now right.
  - eapply (fr_copy_compatible O from to); eauto.
Qed.

Lemma svfl_backward_edge_prop: forall from to roots f_info v l g1 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 -> sound_gc_graph g1 ->
    no_dangling_dst g1 -> roots_fi_compatible roots f_info -> gen_unmarked g1 to ->
    copied_vertex_prop g1 from to ->  roots_graph_compatible roots g1 ->
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v = to ->
    (forall i : nat, In i l -> (i < length (raw_fields (vlabel g1 v)))%nat) ->
    backward_edge_prop g1 roots from to -> scan_vertex_for_loop from to v l g1 g2 ->
    backward_edge_prop g2 roots from to.
Proof.
  intros until l. induction l; intros; inversion H13; subst; clear H13; try easy.
  change (forward_p2forward_t (inr (v, Z.of_nat a)) [] g1)
    with (forward_p2forward_t (inr (v, Z.of_nat a)) roots g1) in H16. pose proof H16.
  assert (forward_p_compatible (inr (v, Z.of_nat a)) roots g1 from). {
    simpl. do 3 (split; auto). 1: omega. rewrite Zlength_correct. apply inj_lt, H11.
    now left. }
  eapply fr_O_backward_edge_prop with (f_info := f_info) in H10; eauto. 2: now simpl.
  simpl in H10. remember (vgeneration v) as to. apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
  - eapply fr_O_sound; eauto.
  - eapply fr_O_no_dangling_dst; eauto.
  - eapply fr_gen_unmarked; eauto.
  - eapply fr_O_copied_vertex_prop; eauto.
  - eapply fr_roots_graph_compatible with (f_info := f_info) in H16; eauto.
  - eapply fr_graph_has_v; eauto.
  - erewrite <- fr_raw_mark; eauto. subst to. auto.
  - intros. erewrite <- fr_raw_fields; eauto. apply H11. now right.
Qed.

Lemma svwl_reachable_or_marked: forall from to f_info (roots: roots_t) l g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> gen_unmarked g1 to ->
    roots_fi_compatible roots f_info -> roots_graph_compatible roots g1 ->
    no_dangling_dst g1 -> copied_vertex_prop g1 from to -> copy_compatible g1 ->
    backward_edge_prop g1 roots from to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v, reachable_or_marked from g1 roots v <->
              reachable_or_marked from g2 roots v.
Proof.
  do 4 intro. induction l; intros; inversion H9; subst; clear H9; try easy.
  1: apply IHl; auto. pose proof H14.
  eapply svfl_reachable_or_marked with (v := v) in H9; eauto.
  2: split; simpl; auto. 2: intros; now rewrite nat_inc_list_In_iff in H10.
  rewrite H9. assert (graph_has_v g1 (to, a)) by (now split).
  assert (forall i : nat,
             In i (nat_inc_list (length (raw_fields (vlabel g1 (to, a))))) ->
             (i < length (raw_fields (vlabel g1 (to, a))))%nat). {
    intros. rewrite nat_inc_list_In_iff in H11; auto. } apply IHl; auto.
  - eapply svfl_P_holds; eauto. apply fr_O_sound.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_gen_unmarked; eauto.
  - eapply svfl_roots_graph_compatible; eauto.
  - eapply (svfl_no_dangling_dst from to); eauto.
  - eapply svfl_copied_vertex_prop; eauto.
  - eapply svfl_copy_compatible; eauto.
  - eapply svfl_backward_edge_prop; eauto.
Qed.

Lemma frr_copied_vertex_prop: forall from to f_info (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> no_dangling_dst g1 ->
    copy_compatible g1 -> roots_graph_compatible roots1 g1 ->
    roots_fi_compatible roots1 f_info ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    copied_vertex_prop g1 from to -> copied_vertex_prop g2 from to.
Proof.
  intros. red in H6. remember (nat_inc_list (length roots1)) as l.
  assert (forall i : nat, In i l -> (i < length roots1)%nat). {
    intros. subst l. now rewrite nat_inc_list_In_iff in H8. } clear Heql.
  revert g1 g2 roots1 roots2 H0 H1 H2 H3 H4 H5 H6 H7 H8.
  induction l; intros; inversion H6; subst; clear H6; try easy.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  change (root2forward (Znth (Z.of_nat a) roots1)) with
      (forward_p2forward_t (inl (Z.of_nat a)) roots1 g1) in H11. pose proof H11.
  assert (0 <= Z.of_nat a < Zlength roots1) by
      (rewrite Zlength_correct; split; [omega | apply inj_lt, H8; now left]).
  apply fr_O_copied_vertex_prop in H11; auto. eapply (IHl g3 _ roots3); eauto.
  - eapply fr_O_sound; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_O_no_dangling_dst; eauto. now simpl.
  - eapply fr_copy_compatible; eauto.
  - subst roots3. eapply fr_roots_graph_compatible; eauto.
  - subst roots3. apply upd_roots_rf_compatible; auto.
  - intros. subst. destruct H5. rewrite <- ZtoNat_Zlength, upd_roots_Zlength; auto.
    rewrite ZtoNat_Zlength. apply H8. now right.
Qed.

Lemma frr_backward_edge_prop: forall from to f_info (roots1 roots2: roots_t) g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> no_dangling_dst g1 ->
    copy_compatible g1 -> roots_graph_compatible roots1 g1 ->
    copied_vertex_prop g1 from to ->
    roots_fi_compatible roots1 f_info -> gen_unmarked g1 to ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    backward_edge_prop g1 roots1 from to -> backward_edge_prop g2 roots2 from to.
Proof.
  intros. red in H8. remember (nat_inc_list (length roots1)) as l.
  assert (forall i : nat, In i l -> (i < length roots1)%nat). {
    intros. subst l. now rewrite nat_inc_list_In_iff in H10. } clear Heql.
  revert g1 g2 roots1 roots2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  induction l; intros; inversion H8; subst; clear H8; try easy.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  change (root2forward (Znth (Z.of_nat a) roots1)) with
      (forward_p2forward_t (inl (Z.of_nat a)) roots1 g1) in H13. pose proof H13.
  assert (0 <= Z.of_nat a < Zlength roots1) by
      (rewrite Zlength_correct; split; [omega | apply inj_lt, H10; now left]).
  eapply fr_O_backward_edge_prop in H13; eauto. rewrite <- Heqroots3 in *.
  2: simpl; auto. apply (IHl g3 _ roots3); auto.
  - eapply fr_O_sound; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_O_no_dangling_dst; eauto. now simpl.
  - eapply fr_copy_compatible; eauto.
  - subst roots3. eapply fr_roots_graph_compatible; eauto.
  - eapply fr_O_copied_vertex_prop; eauto. simpl; auto.
  - subst roots3. apply upd_roots_rf_compatible; auto.
  - eapply fr_gen_unmarked; eauto.
  - intros. subst. destruct H6. rewrite <- ZtoNat_Zlength, upd_roots_Zlength; auto.
    rewrite ZtoNat_Zlength. apply H10. now right.
Qed.

Lemma reachable_or_marked_iff_reachable: forall g roots from v,
    sound_gc_graph g -> graph_unmarked g ->
    reachable_or_marked from g roots v <->
    reachable_through_set g (filter_sum_right roots) v /\ vgeneration v = from.
Proof.
  intros. unfold reachable_or_marked. split; intros; destruct H1; split; auto.
  destruct H2 as [? | [? ?]]; auto. rewrite graph_gen_unmarked_iff in H0.
  destruct H as [? _]. red in H. rewrite H in H2. destruct v as [gen idx].
  destruct H2. simpl in *. subst gen. red in H0. rewrite H0 in H3; easy.
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
  remember (length p) as n. assert (length p <= n)%nat by omega. clear Heqn.
  revert r p H3 H1 H6. induction n; intros.
  - destruct p. 2: simpl in H3; omega. destruct H1 as [[_ ?] _]. simpl in H1.
    subst v. now rewrite H2 in H6.
  - destruct p.
    + destruct H1 as [[_ ?] _]. simpl in H1. subst v. now rewrite H2 in H6.
    + pose proof H1. change (e :: p) with (nil ++ e :: p) in H1.
      apply reachable_by_path_app_cons in H1. destruct H1 as [_ ?].
      assert (length p <= n)%nat by (simpl in H3; omega). specialize (IHn _ _ H5 H1).
      apply IHn. red in H0. unfold gen2gen_no_edge in H0.
      destruct H4 as [_ [? _]]. rewrite valid_path_cons_iff in H4.
      destruct H4 as [? [[? _] _]]. destruct H as [? [? ?]]. red in H, H8, H9.
      rewrite H9 in *. destruct e as [[gen vidx] eidx]. simpl in *. subst r.
      simpl in *. rewrite H8 in H7. apply H0; auto.
Qed.

Lemma frr_sound: forall (g1 g2 : LGraph) from to f_info roots1 roots2,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 -> sound_gc_graph g2.
Proof. intros. eapply frr_P_holds; eauto. apply fr_O_sound. Qed.

Lemma dsr_sound: forall (g1 g2 : LGraph) from to to_index,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    do_scan_relation from to to_index g1 g2 -> sound_gc_graph g2.
Proof. intros. eapply dsr_P_holds; eauto. apply fr_O_sound. Qed.

Lemma frr_dsr_reachable_iff_marked : forall from to f_info roots1 roots2 g1 g2 g3,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> graph_unmarked g1 ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> no_edge2gen g1 from ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    do_scan_relation from to (number_of_vertices (nth_gen g1 to)) g2 g3 ->
    forall v,
      reachable_through_set g1 (filter_sum_right roots1) v /\ vgeneration v = from <->
      raw_mark (vlabel g3 v) = true /\ vvalid g3 v /\ vgeneration v = from.
Proof.
  intros from to f_info roots1 roots2 g1 g2 g3 H H0 H1 H2 H3 H4 H5 He H6 H7 v.
  assert (copied_vertex_prop g1 from to) by
      (now apply graph_unmarked_copied_vertex_prop).
  assert (copy_compatible g1) by (now apply graph_unmarked_copy_compatible).
  pose proof H6. apply frr_reachable_or_marked with (v := v) in H10; auto.
  pose proof H7. destruct H11 as [n [? ?]].
  assert (backward_edge_prop g1 roots1 from to) by (apply no_edge2gen_bep; auto).
  assert (gen_unmarked g1 to) by (rewrite graph_gen_unmarked_iff in H2; apply H2).
  assert (sound_gc_graph g2) by (eapply frr_sound; eauto).
  assert (graph_has_gen g2 to) by (rewrite <- frr_graph_has_gen; eauto).
  eapply (svwl_reachable_or_marked _ _ f_info roots2) in H11; eauto.
  instantiate (1 := v) in H11.
  - rewrite <- H10 in H11. assert (no_edge2gen g3 from) by
        (destruct H3; eapply (frr_dsr_no_edge2gen _ _ _ _ _ g1 g2 g3); eauto).
    assert (roots_have_no_gen roots2 from) by (eapply frr_not_pointing; eauto).
    rewrite <- reachable_or_marked_iff_reachable; auto.
    rewrite <- reachable_or_marked_iff_marked; eauto. eapply dsr_sound; eauto.
  - eapply (frr_gen_unmarked from to _ _ g1); eauto.
  - eapply frr_roots_fi_compatible; eauto.
  - eapply (frr_roots_graph_compatible _ _ _ _ g1); eauto.
  - destruct H3. eapply (frr_no_dangling_dst _ _ _ _ g1); eauto.
  - eapply (frr_copied_vertex_prop _ _ _ _ _ g1 g2); eauto.
  - eapply (frr_copy_compatible _ _ _ _ g1); eauto.
  - eapply (frr_backward_edge_prop _ _ _ _ _ g1 g2); eauto.
Qed.

Lemma frr_dsr_quasi_iso: forall from to f_info roots1 roots2 g1 g2 g3,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> graph_unmarked g1 ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    do_scan_relation from to (number_of_vertices (nth_gen g1 to)) g2 g3 ->
    no_edge2gen g1 from -> gc_graph_quasi_iso g1 roots1 g3 roots2 from to.
Proof.
  intros from to f_info roots1 roots2 g1 g2 g3 H H0 H1 H2 H3 H4 H5 H6 H7 Hn.
  pose proof H6. assert (Hc: copy_compatible g1) by
      (now apply graph_unmarked_copy_compatible). apply frr_semi_iso in H6; auto.
  2: rewrite graph_gen_unmarked_iff in H2; apply H2. destruct H6 as [l1 [? ?]].
  assert (sound_gc_graph g2) by (eapply frr_sound; eauto).
  pose proof H7. destruct H7 as [n [? ?]].
  eapply (svwl_semi_iso _ _ _ _ roots2 f_info g1) in H7; eauto.
  - destruct H7 as [l2 [? ?]]. rewrite H9 in H13 at 2.
    rewrite (surjective (roots_map l1) (roots_map l1)) in H13.
    2: apply roots_map_bijective; eapply semi_iso_DoubleNoDup; eauto.
    assert (graph_has_gen g2 to) by (rewrite <- frr_graph_has_gen; eauto).
    assert (sound_gc_graph g3) by (eapply dsr_P_holds; eauto; apply fr_O_sound).
    assert (forall v, vvalid g1 v /\ vgeneration v = from <->
                      vvalid g3 v /\ vgeneration v = from). {
      destruct H0 as [? _]. red in H0. destruct H15 as [? _]. red in H15.
      destruct H11 as [? [? ?]]. intros; split; intros; destruct H17; split; auto.
      - rewrite H0 in H17. eapply frr_graph_has_v in H17; eauto.
        eapply svwl_graph_has_v in H17; eauto. now rewrite H15.
      - rewrite H15 in H17. apply svwl_graph_has_v_inv with (v := v) in H11; auto.
        destruct H11 as [? | [? ?]]. 2: rewrite H11 in H18; now rewrite H18 in H.
        apply frr_graph_has_v_inv with (v := v) in H8; auto. destruct H8 as [?|[? ?]].
        2: rewrite H8 in H18; now rewrite H18 in H. now rewrite H0. }
    eapply semi_quasi_iso; eauto. red. intros.
    unfold roots_reachable_in_gen, marked_in_gen. rewrite H16.
    eapply frr_dsr_reachable_iff_marked; eauto.
  - rewrite <- frr_graph_has_gen; eauto.
  - eapply frr_roots_fi_compatible; eauto.
  - eapply frr_roots_graph_compatible; eauto.
  - destruct H3. eapply frr_no_dangling_dst; eauto.
  - eapply frr_not_pointing; eauto.
  - intros. rewrite nat_seq_In_iff in H13. unfold gen_has_index. omega.
  - eapply frr_copy_compatible; eauto.
  - eapply frr_gen_unmarked; eauto. rewrite graph_gen_unmarked_iff in H2; apply H2.
Qed.

Lemma do_gen_iso: forall from to f_info roots1 roots2 g1 g2,
    from <> to -> sound_gc_graph g1 -> graph_has_gen g1 to -> graph_unmarked g1 ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    no_dangling_dst g1 -> no_edge2gen g1 from ->
    do_generation_relation from to f_info roots1 roots2 g1 g2 ->
    gc_graph_iso g1 roots1 g2 roots2.
Proof.
  intros. destruct H7 as [g3 [g4 [? [? ?]]]]. subst g2.
  apply (quasi_iso_reset_iso _ _ _ _ _ to); auto.
  - eapply frr_dsr_quasi_iso; eauto.
  - eapply (dsr_sound g3 g4); eauto.
    + eapply frr_sound; eauto.
    + rewrite <- frr_graph_has_gen; eauto.
  - eapply frr_dsr_no_edge2gen; eauto.
    + rewrite graph_gen_unmarked_iff in H2. apply H2.
    + apply graph_unmarked_copy_compatible; auto.
    + destruct H3; auto.
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

Lemma ngr_no_dangling_dst: forall g1 g2 gen,
    no_dangling_dst g1 -> new_gen_relation gen g1 g2 -> no_dangling_dst g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold no_dangling_dst in *. intros.
    simpl in *. apply ang_graph_has_v_inv in H1; auto. apply ang_graph_has_v.
    rewrite <- ang_get_edges in H2. eapply H; eauto.
Qed.

Lemma ngr_no_edge2gen: forall g1 g2 gen to,
    no_edge2gen g1 to -> new_gen_relation gen g1 g2 -> no_edge2gen g2 to.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. unfold no_edge2gen, gen2gen_no_edge in *.
    intros. simpl in *. destruct H2. simpl in *. apply ang_graph_has_v_inv in H2; auto.
    rewrite <- ang_get_edges in H3. apply H; auto. split; auto.
Qed.

Lemma ngr_iso: forall g1 g2 roots gen,
    new_gen_relation gen g1 g2 -> gc_graph_iso g1 roots g2 roots.
Proof.
  intros. red in H. destruct (graph_has_gen_dec g1 gen).
  - subst. apply gc_graph_iso_refl.
  - destruct H as [gen_i [? ?]]. subst g2. red. exists id, id, id, id.
    rewrite root_map_id, map_id. split; easy.
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

Lemma ngr_no_backward_edge: forall g1 g2 gen,
    no_backward_edge g1 -> new_gen_relation gen g1 g2 -> no_backward_edge g2.
Proof.
  intros. red in H0. destruct (graph_has_gen_dec g1 gen).
  - subst; auto.
  - destruct H0 as [gen_i [? ?]]. subst g2. apply no_backward_edge_add; auto.
Qed.

Lemma do_gen_sound: forall from to fi r1 r2 g1 g2,
    sound_gc_graph g1 -> graph_has_gen g1 to ->
    do_generation_relation from to fi r1 r2 g1 g2 -> sound_gc_graph g2.
Proof. intros. eapply do_gen_P_holds; eauto. apply fr_O_sound. apply reset_sound. Qed.

Lemma svwl_roots_graph_compatible: forall from to roots l g1 g2,
    from <> to -> graph_has_gen g1 to -> copy_compatible g1 -> gen_unmarked g1 to ->
    roots_graph_compatible roots g1 -> scan_vertex_while_loop from to l g1 g2 ->
    roots_graph_compatible roots g2.
Proof.
  intros until l. induction l; intros; inversion H4; subst; clear H4; try easy.
  1: eapply IHl; eauto. pose proof H9. eapply svfl_roots_graph_compatible in H9; eauto.
  - apply (IHl g3); auto.
    + rewrite <- svfl_graph_has_gen; eauto.
    + eapply svfl_copy_compatible; eauto.
    + eapply svfl_gen_unmarked; eauto.
  - split; auto.
  - intros. rewrite nat_inc_list_In_iff in H5. auto.
Qed.

Lemma do_gen_roots_graph_compatible: forall g1 g2 roots1 roots2 f_info from to,
    graph_has_gen g1 to -> copy_compatible g1 -> gen_unmarked g1 to ->
    from <> to -> roots_graph_compatible roots1 g1 ->
    roots_fi_compatible roots1 f_info ->
    do_generation_relation from to f_info roots1 roots2 g1 g2 ->
    roots_graph_compatible roots2 g2.
Proof.
  intros. destruct H5 as [g3 [g4 [? [? ?]]]]. subst g2. apply rgc_reset.
  - destruct H6 as [n [? ?]]. eapply svwl_roots_graph_compatible in H6; eauto.
    + rewrite <- frr_graph_has_gen; eauto.
    + eapply frr_copy_compatible; eauto.
    + eapply frr_gen_unmarked; eauto.
    + eapply frr_roots_graph_compatible; eauto.
  - eapply frr_not_pointing; eauto.
Qed.

Theorem garbage_collect_isomorphism: forall f_info roots1 roots2 g1 g2,
    graph_unmarked g1 -> no_backward_edge g1 -> no_dangling_dst g1 ->
    roots_fi_compatible roots1 f_info -> roots_graph_compatible roots1 g1 ->
    sound_gc_graph g1 -> garbage_collect_relation f_info roots1 roots2 g1 g2 ->
    gc_graph_iso g1 roots1 g2 roots2.
Proof.
  intros. destruct H5 as [n [? ?]]. clear H6. unfold nat_inc_list in H5.
  pose proof (graph_has_gen_O g1).
  assert (firstn_gen_clear g1 O) by (red; intros; omega). remember O as s. clear Heqs.
  remember (S n) as m. clear n Heqm. rename m into n.
  revert s g1 roots1 g2 roots2 H H0 H1 H2 H3 H4 H5 H6 H7.
  induction n; intros; simpl in *; inversion H5; subst; clear H5.
  1: apply gc_graph_iso_refl. pose proof H11.
  assert (sound_gc_graph g3) by (eapply ngr_sound; eauto).
  assert (graph_has_gen g3 (S s)) by (eapply ngr_graph_has_gen; eauto).
  assert (graph_unmarked g3) by (eapply ngr_graph_unmarked; eauto).
  assert (roots_graph_compatible roots1 g3) by
      (eapply ngr_roots_graph_compatible; eauto).
  assert (no_dangling_dst g3) by (eapply ngr_no_dangling_dst; eauto).
  assert (no_edge2gen g3 s) by
      (eapply ngr_no_edge2gen; eauto; apply fgc_nbe_no_edge2gen; auto).
  apply do_gen_iso in H11; auto. apply (gc_graph_iso_trans g3 roots1).
  1: eapply ngr_iso; eauto. apply (gc_graph_iso_trans g4 roots3); auto.
  assert (gen_unmarked g3 (S s)) by (rewrite graph_gen_unmarked_iff in H12; apply H12).
  assert (firstn_gen_clear g3 s) by (eapply ngr_firstn_gen_clear; eauto).
  assert (no_backward_edge g3) by (eapply ngr_no_backward_edge; eauto).
  assert (copy_compatible g3) by (apply graph_unmarked_copy_compatible; auto).
  assert (no_dangling_dst g4). {
    eapply do_gen_no_dangling_dst; eauto. destruct H2; auto. } apply (IHn (S s)); auto.
  - eapply (do_gen_graph_unmarked s (S s)); eauto.
  - eapply do_gen_no_backward_edge; eauto.
  - destruct H5 as [? [? [? _]]]. eapply frr_roots_fi_compatible; eauto.
  - eapply do_gen_roots_graph_compatible; eauto.
  - eapply do_gen_sound; eauto.
  - rewrite <- do_gen_graph_has_gen; eauto.
  - eapply do_gen_firstn_gen_clear; eauto.
Qed.
