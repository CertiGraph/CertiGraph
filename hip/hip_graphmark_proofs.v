Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.hip.hip_graphmark.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.GraphBi_Mark.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
Context {sSGG_Bi: sSpatialGraph_Graph_Bi}.
Context {SGSA: SpatialGraphStrongAssum SGP}.

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

Module GraphMark <: Mgraphmark.
  Definition formula : Type := pred.
  Definition node : Type := addr.
  Definition null_node : node := null.
  Definition valid : formula -> Prop := fun f => TT |-- f.
  Definition ptto_node : node -> bool -> node -> node -> formula := fun v d l r => vertex_at v (d, l, r).
  Definition A : Type := Graph.
  Definition graph : node -> A -> formula := fun x g => (@graph _ _ _ _ _ _ SGP _ x (GraphBi.Graph_SpatialGraph g)).
  Definition star : formula -> formula -> formula := sepcon.
  Definition and : formula -> formula -> formula := andp.
  Definition imp : formula -> formula -> formula := imp.
  Definition ext : (bool -> formula) -> formula := exp.
  Definition not : formula -> formula := fun f => prop (f |-- FF).
  Definition eq : node -> node -> formula := fun a b => prop (a = b).
  Definition mwand : formula -> formula -> formula := ewand.
  Definition union : formula -> formula -> formula := ocon.
  Definition neq : bool -> bool -> formula := fun a b => prop (~ a = b).
  Definition mark : A -> node -> A -> formula := fun g1 n g2 => prop (mark n g1 g2).
  Definition eq_notreach : A -> node -> A -> formula :=
    fun g1 n g2 => prop ((unreachable_partial_spatialgraph (GraphBi.Graph_SpatialGraph g1) (n :: nil))
                           -=- (unreachable_partial_spatialgraph (GraphBi.Graph_SpatialGraph g2) (n :: nil))).
  Definition subset_reach : A -> node -> A -> formula := fun g1 n g2 => prop (Included (reachable g1 n) (reachable g2 n)).
  Definition lookup : A -> node -> bool -> node -> node -> formula :=
    fun g x d l r => prop (vlabel g x = d /\ vvalid g x /\ vvalid g l /\ vvalid g r /\ dst g (x, L) = l /\ dst g (x, R) = r).
  Definition update : A -> node -> bool -> node -> node -> A -> formula :=
    fun g1 x d l r g2 => prop (exists (Hn : ~ is_null g1 x) (Hi : graph_gen.in_math g1 x l r), Graph_gen_update g1 x d l r Hi Hn = g2).

  Lemma update_is_mark1: forall (l r: addr) (G G1: A) x,
      vvalid G x ->
      dst G (x, L) = l -> dst G (x, R) = r ->
      (exists (Hn : ~ is_null G x) (Hi : graph_gen.in_math G x l r),
          Graph_gen_update G x true l r Hi Hn = G1) ->
      mark1 x G G1.
  Proof.
    intros. unfold valid in H1. destruct H2 as [Hn [Hi ?]].
    rewrite <- H2. split; [|split]; simpl.
    + split; [|split; [|split]]; simpl; intros; auto.
      - unfold graph_gen.change_vvalid. intuition. subst; auto.
      - unfold graph_gen.change_evalid. intuition.
        rewrite (@only_two_edges _ _ _ _ G _ _ (biGraph G)) in H4.
        destruct H4; rewrite H3;
        [apply (@left_valid _ _ _ _ _ _ _ (biGraph G)) |
         apply (@right_valid _ _ _ _ _ _ _ (biGraph G))]; auto.
      - unfold graph_gen.change_dst. destruct (equiv_dec (src G e) x); auto.
        unfold equiv in e0.
        destruct (left_or_right G (biGraph G) x e e0); subst e; auto.
    + unfold graph_gen.update_vlabel. destruct (equiv_dec x x); intuition.
    + intros. unfold graph_gen.update_vlabel. destruct (equiv_dec x n'); intuition.
  Qed.

  Lemma marked_node_marked: forall (G1: A) (n: addr) (G2: A) (x: addr) (v: bool),
      vlabel G1 x = true ->
      WeakMarkGraph.mark n G1 G2 ->
      vlabel G2 x = true.
  Proof.
    intros. unfold WeakMarkGraph.mark. destruct H0 as [? ?]. specialize (H1 x).
    simpl in H1. symmetry. rewrite H1. left; auto.
  Qed.

  Lemma axiom_5 : forall v G1 G2 G G3 x l r,
      valid (imp (and (lookup G x v l r)
                      (and (update G x true l r G1)
                           (and (neq v true) (and (mark G1 r G2) (mark G2 l G3)))))
                 (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
    intros. unfold valid, imp, and, lookup, neq, mark, update.
    apply imp_andp_adjoint. normalize. destruct H as [? [? [? [? [? ?]]]]].
    assert (mark1 x G G1) by (apply (update_is_mark1 l r); auto).
    apply andp_right; normalize.
    + destruct H0 as [Hn [Hi ?]].
      apply mark1_mark_list_mark with (r :: l :: nil); auto.
      - simpl. unfold Complement. unfold In. clear - H H1. subst v. intuition.
      - apply gamma_step_list' with false; auto. simpl. unfold gamma.
        do 2 (f_equal; auto). subst v. apply Bool.not_true_is_false in H1. auto.
      - hnf. apply (compond_intro (compond_relation Logic.eq (mark1 x)) _ _ G1 _).
        apply (compond_intro Logic.eq (mark1 x) G G G1); auto.
        unfold mark_list. simpl. hnf.
        apply (compond_intro
                 (compond_relation Logic.eq (Graph_Mark.mark r)) _ _ G2 _); auto.
          apply (compond_intro Logic.eq (Graph_Mark.mark r) G1 G1 G2); auto.
    + destruct H2, H3, H9. destruct H12 as [? ?]. split.
      - apply (marked_node_marked G2 l); auto. apply (marked_node_marked G1 r); auto. 
      - assert (G ~=~ G3) by (transitivity G1; auto; transitivity G2; auto).
        destruct H14 as [? [? [? ?]]]. split; [|split; [|split; [|split]]].
        * specialize (H14 x); intuition.
        * specialize (H14 l); intuition.
        * specialize (H14 r); intuition.
        * assert (evalid G (x, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H17 (x, L)).
          specialize (H15 (x, L)). intuition.
        * assert (evalid G (x, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H17 (x, R)).
          specialize (H15 (x, R)). intuition.
  Qed.
  
  Lemma axiom_6 : forall v G1 G2 G G3 x l r,
      valid (imp (and (lookup G x v l r)
                      (and (update G x true l r G1)
                           (and (neq v true) (and (mark G1 l G2) (mark G2 r G3)))))
                 (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
    intros. unfold valid, imp, and, lookup, neq, mark, update.
    apply imp_andp_adjoint. normalize. destruct H as [? [? [? [? [? ?]]]]].
    assert (mark1 x G G1) by (apply (update_is_mark1 l r); auto).
    apply andp_right; normalize.
    + destruct H0 as [Hn [Hi ?]].
      apply mark1_mark_list_mark with (l :: r :: nil); auto.
      - simpl. unfold Complement. unfold In. clear - H H1. subst v. intuition.
      - apply gamma_step_list with false; auto. simpl. unfold gamma.
        do 2 (f_equal; auto). subst v. apply Bool.not_true_is_false in H1. auto.
      - hnf. apply (compond_intro (compond_relation Logic.eq (mark1 x)) _ _ G1 _).
        apply (compond_intro Logic.eq (mark1 x) G G G1); auto.
        unfold mark_list. simpl. hnf.
        apply (compond_intro
                 (compond_relation Logic.eq (Graph_Mark.mark l)) _ _ G2 _); auto.
          apply (compond_intro Logic.eq (Graph_Mark.mark l) G1 G1 G2); auto.
    + destruct H2, H3, H9. destruct H12 as [? ?]. split.
      - apply (marked_node_marked G2 r); auto. apply (marked_node_marked G1 l); auto. 
      - assert (G ~=~ G3) by (transitivity G1; auto; transitivity G2; auto).
        destruct H14 as [? [? [? ?]]]. split; [|split; [|split; [|split]]].
        * specialize (H14 x); intuition.
        * specialize (H14 l); intuition.
        * specialize (H14 r); intuition.
        * assert (evalid G (x, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H17 (x, L)).
          specialize (H15 (x, L)). intuition.
        * assert (evalid G (x, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H17 (x, R)).
          specialize (H15 (x, R)). intuition.
  Qed.

  Lemma axiom_7 : forall v G x G1 y l r,
      valid (imp (and (mark G x G1) (lookup G y v l r))
                 (and (subset_reach G x G1)
                      (and (eq_notreach G x G1)
                           (ext (fun Anon_15 => (lookup G1 y Anon_15 l r)))))).
  Proof.
    intros. unfold valid, imp, and, mark, lookup, subset_reach, eq_notreach.
    apply imp_andp_adjoint. normalize. destruct H0 as [? [? [? [? [? ?]]]]].
    apply andp_right; [|apply andp_right].
    + apply TT_prop_right. destruct H. apply (reachable_ind.si_reachable _ _ x) in H6.
      destruct H6. auto.
    + apply TT_prop_right. destruct H. unfold unreachable_partial_spatialgraph.
      hnf. simpl. unfold predicate_vvalid. unfold predicate_weak_evalid.
      split; [|split]; intros; auto.
      - apply partialgraph_proper; auto. unfold Complement. unfold In. hnf.
        split; intro z; unfold In; rewrite H6; auto.
      - destruct H7, H8. unfold Complement in *. unfold In in *.
        unfold gamma. f_equal;[f_equal |]; [|apply dst_L_eq | apply dst_R_eq]; auto.
        destruct H. simpl in H11.
        assert (~ reachable G x v0) by (intro; apply H9; rewrite reachable_through_set_single; auto).
        destruct (Bool.bool_dec (vlabel G v0) true).
        * rewrite e. apply H11. left; auto.
        * apply Bool.not_true_is_false in n. rewrite n. symmetry.
          apply Bool.not_true_is_false. intro. symmetry in H13. rewrite H11 in H13.
          destruct H13.  clear -n H13. apply Bool.diff_true_false. rewrite H13. rewrite <- n. auto.
          apply reachable_by_is_reachable in H13. exfalso; auto.
    + unfold ext. destruct H as [[? ?] ?]. specialize (H6 y). simpl in H6.
      destruct H7 as [? [? [? ?]]].
      LEM (G |= x ~o~> y satisfying (WeakMarkGraph.unmarked G)).
      - assert (vlabel G1 y = true) by (symmetry; rewrite H6; right; auto).
        apply (exp_right true). normalize. split; [|split;[|split;[|split; [|split]]]]; auto.
        * specialize (H7 y); intuition.
        * specialize (H7 l); intuition.
        * specialize (H7 r); intuition.
        * assert (evalid G (y, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H10 (y, L)).
          specialize (H8 (y, L)). intuition.
        * assert (evalid G (y, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H10 (y, R)).
          specialize (H8 (y, R)). intuition.
      - apply (exp_right v). normalize. split; [|split;[|split;[|split; [|split]]]].
        * destruct (Bool.bool_dec v true).
          1: rewrite e in *; symmetry; rewrite H6; left; auto.
          apply Bool.not_true_is_false in n. rewrite n in *. clear n.
          apply Bool.not_true_is_false. intro. symmetry in H12. rewrite H6 in H12.
          destruct H12; [|intuition]. apply Bool.diff_true_false. clear - H0 H12.
          rewrite H12. rewrite <- H0. auto.
        * specialize (H7 y); intuition.
        * specialize (H7 l); intuition.
        * specialize (H7 r); intuition.
        * assert (evalid G (y, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H10 (y, L)).
          specialize (H8 (y, L)). intuition.
        * assert (evalid G (y, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H10 (y, R)).
          specialize (H8 (y, R)). intuition.
  Qed.

  Lemma axiom_8 : forall l r x G, valid (imp (lookup G x true l r) (mark G x G)).
  Proof.
    intros. unfold valid, imp, lookup, mark. rewrite <- iter_sepcon.prop_impl_imp. normalize.
    destruct H as [? [? [? [? [? ?]]]]]. hnf. split; [|reflexivity].
    split; [|split]; [reflexivity | intros..]; [intuition|destruct H5; auto].
    apply reachable_by_head_prop in H5. simpl in H5. unfold Complement in H5. unfold In in H5.
    exfalso; auto.
  Qed.

  Lemma axiom_9 : forall G, valid (mark G null_node G).
  Proof.
    intros. unfold valid, mark, null_node. normalize. hnf. split; [|reflexivity].
    hnf. split; [|intros; split; intros]; [reflexivity | intuition |]. destruct H; auto.
    exfalso. apply reachable_by_head_valid in H.
    apply (@valid_not_null _ _ _ _ _ (maGraph G) _) in H; auto. rewrite is_null_def. auto.
  Qed.

  Lemma lookup_graph_unfold: forall (G: A) x v l r,
      vlabel G x = v -> vvalid G x -> vvalid G l -> vvalid G r -> dst G (x, L) = l ->
      dst G (x, R) = r -> (graph x G = ptto_node x v l r ⊗ graph l G ⊗ graph r G).
  Proof.
    intros. unfold graph. unfold ptto_node. apply bi_graph_unfold; auto.
    simpl. unfold gamma. f_equal; [f_equal|]; auto.
  Qed.

  Lemma graph_graphs_eq_l:
    forall (G: A) v x l r, vlabel G x = v -> vvalid G x -> vvalid G l -> vvalid G r ->
                           dst G (x, L) = l -> dst G (x, R) = r ->
                           (ptto_node x v l r ⊗ (graph l G ⊗ graph r G)) =
                           graph l G ⊗ graphs (x :: l :: r :: nil)
                                 (GraphBi.Graph_SpatialGraph G).
  Proof.
    intros. simpl. rewrite ocon_emp. do 3 rewrite <- ocon_assoc.
    rewrite (ocon_comm (graph l G) (graph x G)).
    rewrite (ocon_assoc (graph x G) (graph l G) (graph l G)).
    rewrite <- log_normalize.precise_ocon_self.
    2: apply (bi_graph_precise_left _ x); auto.
    rewrite (lookup_graph_unfold _ x v l r); auto.
    rewrite (ocon_assoc (ptto_node x v l r) (graph l G) (graph r G)).
    rewrite ocon_assoc.
    rewrite (ocon_assoc (ptto_node x v l r) (graph l G ⊗ graph r G)
                        (graph l G ⊗ graph r G)).
    rewrite <- log_normalize.precise_ocon_self; auto. apply precise_ocon.
    + apply (bi_graph_precise_left _ x); auto.
    + apply (bi_graph_precise_right _ x); auto.
  Qed.

  Lemma lem_subgraphupdate_l : forall G v G1 x v1 l r,
      valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G)))))
                      (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r)))))
                 (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. unfold valid, imp, and, star, mwand, union, subset_reach, eq_notreach, lookup.
    apply imp_andp_adjoint. normalize. apply precise_wand_ewand.
    + apply precise_graph. apply RGF. left; intuition.
    + destruct H1 as [? [? [? [? [? ?]]]]]. destruct H2 as [? [? [? [? [? ?]]]]].
      rewrite (graph_graphs_eq_l G v x l r); auto. rewrite (graph_graphs_eq_l G1 v1 x l r); auto.
      assert (forall (g: A), graph l g = graphs (l :: nil) (GraphBi.Graph_SpatialGraph g)) by (intros; simpl; rewrite ocon_emp; auto).
      rewrite (H13 G). rewrite (H13 G1). apply subgraph_update; auto. apply RGF. apply RGF. 
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
  Qed.

  Lemma graph_graphs_eq_r:
    forall (G: A) v x l r, vlabel G x = v -> vvalid G x -> vvalid G l -> vvalid G r ->
                           dst G (x, L) = l -> dst G (x, R) = r ->
                           (ptto_node x v l r ⊗ (graph l G ⊗ graph r G)) =
                           graph r G ⊗ graphs (x :: l :: r :: nil)
                                 (GraphBi.Graph_SpatialGraph G).
  Proof.
    intros. simpl. rewrite ocon_emp. do 3 rewrite <- ocon_assoc.
    rewrite (ocon_comm (graph r G) (graph x G)).
    rewrite (ocon_assoc (graph x G) (graph r G) (graph l G)).
    rewrite (ocon_comm (graph r G) (graph l G)).
    rewrite <- (ocon_assoc (graph x G) (graph l G) (graph r G)).
    rewrite (ocon_assoc (graph x G ⊗ graph l G) (graph r G) (graph r G)).
    rewrite <- log_normalize.precise_ocon_self.
    2: apply (bi_graph_precise_right _ x); auto.
    rewrite (lookup_graph_unfold _ x v l r); auto.
    rewrite (ocon_assoc (ptto_node x v l r) (graph l G) (graph r G)).
    rewrite ocon_assoc.
    rewrite (ocon_assoc (ptto_node x v l r) (graph l G ⊗ graph r G)
                        (graph l G ⊗ graph r G)).
    rewrite <- log_normalize.precise_ocon_self; auto. apply precise_ocon.
    + apply (bi_graph_precise_left _ x); auto.
    + apply (bi_graph_precise_right _ x); auto.
  Qed.
  
  Lemma lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. unfold valid, imp, and, star, mwand, union, subset_reach, eq_notreach, lookup.
    apply imp_andp_adjoint. normalize. apply precise_wand_ewand.
    + apply precise_graph. apply RGF. left; intuition.
    + destruct H1 as [? [? [? [? [? ?]]]]]. destruct H2 as [? [? [? [? [? ?]]]]].
      rewrite (graph_graphs_eq_r G v x l r); auto. rewrite (graph_graphs_eq_r G1 v1 x l r); auto.
      assert (forall (g: A), graph r g = graphs (r :: nil) (GraphBi.Graph_SpatialGraph g)) by (intros; simpl; rewrite ocon_emp; auto).
      rewrite (H13 G). rewrite (H13 G1). apply subgraph_update; auto. apply RGF. apply RGF. 
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
  Qed.

  Lemma lem_pttoupdate : forall v G x v1 l r G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 l r G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. unfold valid, imp, and, star, mwand, union, subset_reach, eq_notreach, lookup, update.
    apply imp_andp_adjoint. normalize. apply precise_wand_ewand.
    + unfold ptto_node. apply log_normalize.mapsto_precise.
    + destruct H as [? [? [? [? [? ?]]]]]. rewrite <- ocon_assoc. rewrite <- (lookup_graph_unfold G x v l r); auto.
      destruct H0 as [Hn [Hi ?]]. rewrite <- ocon_assoc.
      assert (vgamma (GraphBi.Graph_SpatialGraph G) x = (v, l, r)). {
        simpl. unfold gamma. f_equal; [f_equal |]; auto.
      } pose proof (Graph_gen_update_spatial_spec  G x v v1 l r Hi Hn H1 H6).
      pose proof (Graph_gen_update_vgamma G x v1 l r Hi Hn). rewrite H0 in H8.
      simpl in H8. unfold gamma in H8. rewrite <- (lookup_graph_unfold G1 x v1 l r);
        [| inversion H8 |rewrite <- H0; simpl; unfold graph_gen.change_vvalid ..|inversion H8|inversion H8]; auto.
      pose proof (graph_vi_eq _ _ x H7). rewrite H0 in H9. unfold graph at 2.
      unfold node in H9 at 1. rewrite H9. apply graph_ramify_aux0; auto. apply RGF.
  Qed.
  
  Lemma axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v true) (and (mark G2 l G3) (update G1 x true l r G2))))) (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
  Admitted.

  Lemma axiom_2 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v true) (and (mark G2 r G3) (update G1 x true l r G2))))) (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
  Admitted.

  Lemma axiom_3 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v true) (and (mark G1 l G2) (update G2 x true l r G3))))) (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
  Admitted.

  Lemma axiom_4 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v true) (and (mark G1 r G2) (update G2 x true l r G3))))) (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
  Admitted.

End GraphMark.
