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

Definition injective {A B} (f: A -> B): Prop := forall x y, f x = f y -> x = y.

Definition surjective {A B} (f: A -> B): Prop := forall y, exists x, f x = y.

Definition bijective {A B} (f : A -> B): Prop := injective f /\ surjective f.

(* graph_iso defines graph isomorphism between two graphs *)

Definition graph_iso (g1 g2: LGraph)
           (vmap: VType -> VType) (emap: EType -> EType): Prop :=
  bijective vmap /\ bijective emap /\
  (forall v: VType, vvalid g1 v <-> vvalid g2 (vmap v)) /\
  (forall e: EType, evalid g1 e <-> evalid g2 (emap e)) /\
  (forall (e: EType) (v: VType),
      evalid g1 e -> src g1 e = v -> src g2 (emap e) = vmap v) /\
  (forall (e: EType) (v: VType),
      evalid g1 e -> dst g1 e = v -> dst g2 (emap e) = vmap v).

Definition root_eq (vmap: VType -> VType) (root_pair: root_t * root_t): Prop :=
  let (root1, root2) := root_pair in
  match root1 with
  | inl (inl z) => root2 = inl (inl z)
  | inl (inr gc) => root2 = inl (inr gc)
  | inr r => root2 = inr (vmap r)
  end.

Definition gc_graph_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t): Prop :=
  let vertices1 := filter_sum_right roots1 in
  let vertices2 := filter_sum_right roots2 in
  let sub_g1 := reachable_sub_labeledgraph g1 vertices1 in
  let sub_g2 := reachable_sub_labeledgraph g2 vertices2 in
  length roots1 = length roots2 /\
  exists vmap emap,
    Forall (root_eq vmap) (combine roots1 roots2) /\
    (forall v, vvalid sub_g1 v -> vlabel sub_g1 v = vlabel sub_g2 (vmap v)) /\
    graph_iso sub_g1 sub_g2 vmap emap.

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

Lemma frl_vv_correct: forall from to fi il r1 r2 g g',
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_roots_loop from to fi il r1 g r2 g' ->
    vertex_valid g'.
Proof.
  intros.
  revert r1 r2 g g' fi H H0 H1.
  induction il.
  - intros. destruct H as [H2 H3]; inversion H1; subst; assumption.
  - intros. assert (H' := H); destruct H as [H2 H3]. inversion H1; subst.
    assert (SoundGCGraph g2) by admit.
    (* this will be reasonable to get eventually *)
    pose proof (fr_graph_has_gen _ _ _ _ _ _ H0 H5 to).
    pose proof (sound_fr_vv_correct _ _ _ _ _ H' H0 H5).
    rewrite H4 in H0.
    apply (IHil (upd_roots from to (inl (Z.of_nat a)) g r1 fi) r2 g2 g' fi H H0 H10).
Abort. (* it works, just Aborting because of the admit. *)

Lemma sound_frr_vv_correct: forall g g' from to fi r1 r2,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_roots_relation from to fi r1 g r2 g' ->
    vertex_valid g'.
Proof.
  intros. assert (H' := H). destruct H as [H2 H3].
  inversion H1; subst; try assumption.
  pose proof (sound_fr_vv_correct _ _ _ _ _ H' H0 H4).
  assert (SoundGCGraph g2) by admit.
  pose proof (fr_graph_has_gen _ _ _ _ _ _ H0 H4 to).
  rewrite H8 in H0.
  (* apply (frl_vv_correct _ _ _ _ _ _ _ _ H7 H0 H5). *)
  (* will work fine once the above is Qed. *)
Abort.

Lemma sound_fr_fde_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    field_decided_edges g'.
Proof.
  intros. destruct H as [H2 H3]; inversion H1; subst; try assumption.
  - unfold field_decided_edges in H2.
    (* unfold vertex_valid in H3. *)
    split; intros.
    + destruct H5.
      (* reminder, I can get vertex_valid g' if I want *)
      assert (graph_has_v (lgraph_copy_v g v to) v0). {
        pose proof (sound_fr_lcv_vv g v to H3 H0).
        unfold vertex_valid in H7.
        rewrite H7 in H; assumption.
      }
      rewrite lcv_vvalid_disj in H. destruct H.
      * assert (graph_has_v g v0) by (unfold vertex_valid in H3; rewrite H3 in H; assumption).
        rewrite lcv_get_edges by assumption.
        apply H2; try assumption.
        simpl in H5.
        (* stuck here because I don't know anything useful about src or evalid. *)
        admit.

(* Lemma lcv_src: forall g e v v' to v0, *)
(*     (* vvalid g v0 -> *) *)
(*     src (pregraph_copy_v g v v0) e = v' -> *)
(*     src g e = v' \/ src (pregraph_copy_v g v v0) e = new_copied_v g to. *)
        
      * admit.
    + admit.
  - replace (field_decided_edges new_g) with
        (field_decided_edges (lgraph_copy_v g (dst g e) to)) by
        (subst new_g; reflexivity).
    admit.
     (* potential for reuse of the first branch, if forward_relation isn't needed in the subproof. *)
Abort.

Lemma sound_dsr_vv_correct: forall g g' from to to_index,
    SoundGCGraph g ->
    graph_has_gen g to ->
    do_scan_relation from to to_index g g' ->
    vertex_valid g'.
Proof.
  intros ? ? ? ? ? [H1 H2] H3 [? [H4 H5]].
  inversion H4; subst; try assumption.
  - unfold vertex_valid in H2.
    split; intro.
    + apply (svwl_graph_has_v _ _ _ _ _ H3 H4).
      apply H2. (* stuck *) admit.
    + apply (svwl_graph_has_v_inv _ _ _ _ _ H3 H4 _) in H8.
      destruct H8.
      * rewrite <- H2 in H8. (* stuck *) admit.
      * destruct H8.
        admit.
  - admit.
Abort.

Lemma sound_dgr_vv_correct: forall g g' from to fi r1 r2,
    SoundGCGraph g ->
    graph_has_gen g to ->
    do_generation_relation from to fi r1 r2 g g' ->
    vertex_valid g'.
Proof.
  intros. destruct H as [H2 H3].
  destruct H1 as [? [? [? [? ?]]]].
  subst.
  (* In two steps, I can get to "vertex_valid x0". 
     Then we need to show that the reset doesn't change anything. *)
Abort.
