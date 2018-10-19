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
    vertex_valid_sgcg: vertex_valid g
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

Lemma get_edges_raw_fields: forall g g' v,
          raw_fields (vlabel g v) = raw_fields (vlabel g' v) ->
          get_edges g v = get_edges g' v.
Proof.
  intros. unfold get_edges, make_fields, make_fields'.
  rewrite H. reflexivity.
Qed.

Lemma sound_fr_fde_correct: forall g g' from to p,
    SoundGCGraph g ->
    graph_has_gen g to ->
    forward_relation from to 0 p g g' ->
    field_decided_edges g'.
Proof.
  intros. destruct H; inversion H1; subst; try assumption.
  - split; intros.
    + simpl in H3; destruct H3.
      unfold lgraph_copy_v, lgraph_mark_copied, lgraph_add_copied_v. simpl. unfold get_edges, make_fields. simpl.
      unfold update_copied_old_vlabel. simpl. admit.
    + admit.
  - replace (field_decided_edges new_g) with (field_decided_edges (lgraph_copy_v g (dst g e) to)) by (subst new_g; reflexivity). (* potential for reuse, if forward_relation isn't needed in the subproof. *) Abort.

(* apply (fr_graph_has_v _ _ _ _ _ _ H0 H1). *)
(*
Lemma fr_graph_has_v: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> graph_has_v g' v.
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => True) as Q.
  remember (fun g1 g2 v => graph_has_v g1 v -> graph_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
    apply lacv_graph_has_v_old; assumption.
Qed.

Lemma fr_graph_has_v_bi: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v <-> graph_has_v g' v.
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => True) as Q.
  remember (fun g1 g2 v => graph_has_v g1 v -> graph_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  split.
  - apply H1; clear H1; intros; try assumption; try reflexivity.
    + apply H2, H1. assumption.
    + unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
      apply lacv_graph_has_v_old; assumption.
  - pose proof (fr_general_prop depth from to p g' g _ Q P R). subst Q P R.
Qed.
 *)

Lemma cvae_vvalid_eq: forall g e v v',
    vvalid g v <->  vvalid (copy_v_add_edge v' g e) v.
Proof. reflexivity. Qed.

Lemma pregraph_vvalid_eq: forall g v' l v0,
    vvalid (fold_left (copy_v_add_edge v') l g) v0 <-> vvalid g v0.
Proof.
  intros. split; intro.
  - revert g H. induction l; intros; simpl in H; [assumption|].
    apply IHl in H; apply cvae_vvalid_eq; assumption.
  - revert g H. induction l; intros; simpl; [assumption|].
    apply IHl; apply cvae_vvalid_eq; assumption.
Qed.           

Lemma pgav_vvalid_disj: forall (g: LGraph) v to,
    vvalid g v \/ v = new_copied_v g to <->
    vvalid (pregraph_add_vertex g (new_copied_v g to)) v.
Proof.
  intros. split; intros.
  - destruct H.
    + apply addVertex_preserve_vvalid; assumption.
    + subst v; apply addVertex_add_vvalid.
  - simpl in H; unfold addValidFunc in H; assumption.
Qed.

Lemma sound_fr_lcv_vv: forall g v to,
    vertex_valid g ->
    graph_has_gen g to ->
    vertex_valid (lgraph_copy_v g v to).
Proof.
  intros. unfold vertex_valid in H.
  split; intro; unfold lgraph_copy_v in *;
    simpl in *; unfold pregraph_copy_v in *.
  - apply pregraph_vvalid_eq, pgav_vvalid_disj in H1; destruct H1.
    + apply H in H1; apply lcv_graph_has_v_old; assumption.
    + subst v0; apply lcv_graph_has_v_new; assumption.
  - apply pregraph_vvalid_eq, pgav_vvalid_disj.
    simpl; unfold addValidFunc.
    apply lcv_graph_has_v_inv in H1; try assumption;
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
