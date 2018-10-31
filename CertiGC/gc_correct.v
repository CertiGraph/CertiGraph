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
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.graph_isomorphism.
Require Import RamifyCoq.CertiGC.GCGraph.
Import ListNotations.

Local Open Scope Z_scope.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertex_valid (g: LGraph): Prop := forall v,  vvalid g v <-> graph_has_v g v.

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

Lemma sound_fr_vv_correct: forall g g' from to p,
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

Fixpoint look_up (l: list (VType * VType)) (key: VType): option VType :=
  match l with
  | [] => None
  | (k, v) :: l' => if equiv_dec k key then Some v else look_up l' key
  end.

Definition vmap_list (l: list (VType * VType)) (r: VType): VType :=
  match (look_up l r) with
  | Some v => v
  | None => r
  end.

Definition rev_map_list (l: list (VType * VType)) (r: VType): VType :=
  let (left_l, right_l) := split l in
  vmap_list (combine right_l left_l) r.

Definition gc_graph_quasi_iso (g1: LGraph) (roots1: roots_t)
           (g2: LGraph) (roots2: roots_t) (from to: nat): Prop :=
  is_partial_lgraph g1 g2 /\
  exists (l: list (VType * VType)),
    roots2 = map (root_map (vmap_list l)) roots1 /\
    forall v1 v2, In (v1, v2) l ->
                  vvalid g1 v1 /\ vvalid g2 v2 /\ vgeneration v1 = from /\
                  vgeneration v2 = to /\ vlabel g1 v1 = vlabel g2 v2 /\
                  (forall e1, In e1 (get_edges g1 v1) ->
                              let e2 := (v2, snd e1) in
                              In e2 (get_edges g2 v2) /\
                              (dst g2 e2 = vmap_list l (dst g1 e1) \/
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
    gc_graph_iso g1 roots1 (reset_nth_gen_graph gen g2) roots2.
Proof.
  intros.
Abort.
