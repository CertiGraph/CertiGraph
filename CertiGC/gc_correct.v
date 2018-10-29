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
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_isomorphism.
Require Import RamifyCoq.CertiGC.GCGraph.
Import ListNotations.

Local Open Scope Z_scope.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertex_valid (g: LGraph): Prop :=
  forall v,  vvalid g v <-> graph_has_v g v.

Definition field_decided_edges (g: LGraph): Prop :=
  forall v e,
    vvalid g v -> (src g e = v /\ evalid g e <-> In e (get_edges g v)).

Class SoundGCGraph (g: LGraph) :=
  {
    field_decided_edges_sgcg: field_decided_edges g;
    vertex_valid_sgcg: vertex_valid g;
    (* Other constraints would be added later *)
  }.

Definition Graph :=
  GeneralGraph VType EType raw_vertex_block unit graph_info (fun g => SoundGCGraph g).

Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

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

Lemma sound_fr_vv_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    vertex_valid g'.
Proof.
  intros. destruct H as [H2 H3]; inversion H1; subst; try assumption.
  - apply sound_fr_lcv_vv; assumption.
  - replace (vertex_valid new_g) with
        (vertex_valid (lgraph_copy_v g (dst g e) to)) by (subst new_g; reflexivity).
    apply sound_fr_lcv_vv; assumption.
Qed.

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
    (* some conditions, like noDup *)
    src g e = v ->
    src (fold_left (copy_v_add_edge new) l g) e = v.
Proof.
  intros. revert g H. induction l.
  1: simpl; intros; assumption.
  intros. simpl.
  apply IHl. simpl. unfold updateEdgeFunc.
  rewrite H. apply if_false.
  intro.
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

Lemma pcv_evalid: forall g old new e ,
    (* graph_has_v g v -> *)
    (* v = src g e -> *)
    evalid (pregraph_copy_v g old new) e ->
    evalid g e.
Proof.
  intros. unfold pregraph_copy_v in H.
  remember (combine (combine (repeat new (Datatypes.length (get_edges g old)))
                             (map snd (get_edges g old))) (map (dst g)
                                                               (get_edges g old))).
  clear Heql.
  induction l.
  - simpl; intros. assumption.
  - intros. simpl in H. apply IHl. clear IHl.
    unfold copy_v_add_edge in H at 2.
    destruct a; simpl in H.
    admit.
Abort.

Lemma sound_fr_O_fde_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    field_decided_edges g'.
Proof.
  intros. destruct H as [?H ?H]. inversion H1; subst; try assumption.
  - unfold field_decided_edges in *. intros ve e ?.
    pose proof (sound_fr_lcv_vv _ v _ H2 H0). red in H5. rewrite H5 in H3. clear H5.
    apply lcv_graph_has_v_inv in H3. 2: assumption.
    split; intros.
    + destruct H5. simpl in H5.
      apply pcv_src_disj in H5. destruct H3; destruct H5.
      * exfalso; apply (graph_has_v_not_eq _ to) in H3;
          unfold not in H3; apply (H3 H5).
      * rewrite lcv_get_edges by assumption.
        unfold vertex_valid in H2; rewrite <- H2 in H3.
        apply (H _ _ H3).
        split; [symmetry; assumption|].
        unfold lgraph_copy_v in H6. simpl in H6.
        rewrite H2 in H3. admit.
      * rewrite H5. unfold lgraph_copy_v. admit.
      * exfalso.
        assert (~ graph_has_v g ve). {
          intro. apply (graph_has_v_not_eq _ to) in H7.
          unfold not in H7; apply H7; assumption.
        }
        (* can get contradiction from these? *)
        admit.
    + split.
      * destruct H3.
        -- rewrite lcv_get_edges in H5 by assumption.
           unfold vertex_valid in H2.
           rewrite <- H2 in H3.
           rewrite <- H in H5 by assumption.
           destruct H5.
           unfold lgraph_copy_v. simpl.
           unfold pregraph_copy_v.
           remember (combine
          (combine (repeat (new_copied_v g to) (Datatypes.length (get_edges g v)))
                   (map snd (get_edges g v))) (map (dst g) (get_edges g v))).
           remember (pregraph_add_vertex g (new_copied_v g to)) as g'. admit.
        -- unfold lgraph_copy_v. simpl. rewrite H3.
           unfold pregraph_copy_v. apply cvae_src_new.
           admit.
      * destruct H3.
        -- rewrite lcv_get_edges in H5 by assumption.
           rewrite <- H in H5. destruct H5.
           ++ unfold lgraph_copy_v. simpl. unfold pregraph_copy_v.
              admit.
           ++ unfold vertex_valid in H2; rewrite <- H2 in H3; assumption.
        -- admit.
  - admit.
Abort.

Lemma sound_fr_fde_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    field_decided_edges g'.
Proof.
  intros. destruct H as [H2 H3]; inversion H1; subst; try assumption.
  - unfold field_decided_edges in H2.
    split; intros.
    + destruct H5.
      (* pose proof (sound_fr_lcv_vv g v to H3 H0). *)
      (* unfold vertex_valid in H7. *)
      (* rewrite H7 in H. *)
      rewrite lcv_vvalid_disj in H. destruct H.
      * assert (graph_has_v g v0) by (unfold vertex_valid in H3; rewrite H3 in H; assumption).
        rewrite lcv_get_edges by assumption.
        apply H2; try assumption.
        simpl in H5. split.
        -- admit.
        -- unfold lgraph_copy_v in H6. simpl in H6.
           unfold pregraph_copy_v in H6.
           (* dead? *)
           admit.
      * admit.
    + admit.
  (* split. *)
  (* * rewrite lcv_vvalid_disj in H. destruct H. *)
  (* addVertex_preserve_evalid: *)
  (* forall (V E : Type) (EV : EqDec V eq) (EE : EqDec E eq)  *)
  (*     (g : PreGraph V E) (e : E) (v : V), *)
  (*   evalid g e -> evalid (pregraph_add_vertex g v) e *)
  (* Lemma lcv_src: forall g e v v' to v0, *)
  (*     (* vvalid g v0 -> *) *)
  (*     src (pregraph_copy_v g v v0) e = v' -> *)
  (*     src g e = v' \/ src (pregraph_copy_v g v v0) e = new_copied_v g to. *)        
  - replace (field_decided_edges new_g) with
      (field_decided_edges (lgraph_copy_v g (dst g e) to)) by
        (subst new_g; reflexivity).
    (* potential for reuse of the first branch *)
    admit.
Abort.

Lemma sound_fr_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    SoundGCGraph g'.
Proof.
  intros.
  admit.
  (* split; [apply (sound_fr_fde_correct _ _ _ _ _ H H0 H1) | *)
  (* apply (sound_fr_vv_correct _ _ _ _ _ H H0 H1)]. *)
Abort.

Lemma sound_frl_correct: forall g g' from to r1 r2 fi il,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_roots_loop from to fi il r1 g r2 g' ->
    SoundGCGraph g'.
Proof.
  intros. revert r1 r2 g g' fi H H0 H1.
  induction il.
  - intros. inversion H1; subst; assumption.
  - intros. inversion H1; subst.
    (* pose proof (sound_fr_correct _ _ _ _ _ H H0 H4). *)
    assert (SoundGCGraph g2) by admit.
    rewrite (fr_graph_has_gen _ _ _ _ _ _ H0 H4 to) in H0.
    apply (IHil (upd_roots from to (inl (Z.of_nat a)) g r1 fi) r2 g2 g' fi H2 H0 H9).
Abort. (* works, but Aborting because it uses an admit *)

Lemma sound_frr_correct: forall g g' from to fi r1 r2,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_roots_relation from to fi r1 g r2 g' ->
    SoundGCGraph g'.
Proof.
  intros. inversion H1. subst; try assumption.
  assert (SoundGCGraph g2) by admit.
  (* pose proof (sound_fr_correct _ _ _ _ _ H H0 H3). *)
  rewrite (fr_graph_has_gen _ _ _ _ _ _ H0 H3 to) in H0.
  (* apply (sound_frl_correct _ _ _ _ _ _ _ _ H9 H0 H4). *)
Abort. (* works, but Aborting because it uses an admit *)

Lemma sound_dsr_correct: forall g g' from to to_index,
    SoundGCGraph g ->
    graph_has_gen g to ->
    do_scan_relation from to to_index g g' ->
    SoundGCGraph g'.
Proof.
  intros. destruct H1 as [? [? ?]].
  inversion H1; subst; try assumption.
  admit. admit.
Abort.

Lemma rngg_sound: forall g gen,
    SoundGCGraph g -> SoundGCGraph (reset_nth_gen_graph gen g).
Proof.
  intros. destruct H as [H1 H2]; split.
  - unfold field_decided_edges; simpl. intros.
    replace (get_edges (reset_nth_gen_graph gen g) v) with
        (get_edges g v) by reflexivity.
    apply (H1 _ _ H).
  - unfold vertex_valid in *. simpl. intros.
    rewrite graph_has_v_reset.
    (* oops, dead! *)
    admit.
Abort.

Lemma sound_dgr_correct: forall g g' from to fi r1 r2,
    SoundGCGraph g ->
    graph_has_gen g to ->
    do_generation_relation from to fi r1 r2 g g' ->
    SoundGCGraph g'.
Proof.
  intros.
  destruct H1 as [? [? [? [? ?]]]].
  subst.
  (* apply rngg_sound. *)
  replace (SoundGCGraph (reset_nth_gen_graph from x0)) with (SoundGCGraph x0) by admit.
  (* pose proof (sound_frr_correct _ _ _ _ _ _ _ H H0 H1). *)
  (* rewrite (frr_graph_has_gen _ _ _ _ _ _ _ H0 H1 to) in H0. *)
  (* apply (sound_dsr_correct _ _ _ _ _ H3 H0 H2). *)
Abort.

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
