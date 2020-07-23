Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.Ensembles_ext.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.Relation_ext.
Require Import CertiGraph.hip.hip_graphmark.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.weak_mark_lemmas.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.reachable_computable.
Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.GraphBi.
Require Import CertiGraph.msl_application.Graph_Mark.
Require Import CertiGraph.msl_application.GraphBi_Mark.
Import CertiGraph.msl_ext.seplog.OconNotation.

Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
Context {sSGG_Bi: sPointwiseGraph_Graph_Bi bool unit}.
Context {SGSA: PointwiseGraphStrongAssum SGP}.

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

Module GraphMark <: Mgraphmark.
  Definition formula : Type := pred.
  Definition node : Type := addr.
  Definition null_node : node := null.
  Definition valid : formula -> Prop := fun f => TT |-- f.
  Definition ptto_node : node -> bool -> node -> node -> formula := fun v d l r => vertex_at v (d, l, r).
  Definition A : Type := (@Graph _ bool unit unit).
  Definition graph : node -> A -> formula := fun x g => (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ SGP _ x (Graph_LGraph g)).
  Definition star : formula -> formula -> formula := sepcon.
  Definition and : formula -> formula -> formula := andp.
  Definition imp : formula -> formula -> formula := imp.
  Definition ext : (bool -> formula) -> formula := exp.
  Definition not : formula -> formula := fun f => prop (f |-- FF).
  Definition eq : node -> node -> formula := fun a b => prop (a = b).
  Definition mwand : formula -> formula -> formula := ewand.
  Definition union : formula -> formula -> formula := ocon.
  Definition neq : bool -> bool -> formula := fun a b => prop (~ a = b).
  Definition mark : A -> node -> A -> formula := fun g1 n g2 => prop (mark n (Graph_LGraph g1) (Graph_LGraph g2)).

  Definition eq_notreach : A -> node -> A -> formula :=
    fun g1 n g2 => prop ((predicate_partial_labeledgraph (Graph_LGraph g1) (Complement _ (reachable (pg_lg (Graph_LGraph g1)) n))) ~=~ (predicate_partial_labeledgraph (Graph_LGraph g2) (Complement _ (reachable (pg_lg (Graph_LGraph g2)) n)))%LabeledGraph).

  Definition subset_reach : A -> node -> A -> formula := fun g1 n g2 => prop (Included (reachable (pg_lg (Graph_LGraph g1)) n) (reachable (pg_lg (Graph_LGraph g2)) n)).

  Definition lookup : A -> node -> bool -> node -> node -> formula :=
    fun g x d l r => prop (vlabel (Graph_LGraph g) x = d /\ vvalid (pg_lg (Graph_LGraph g)) x /\
                           vvalid (pg_lg (Graph_LGraph g)) l /\ vvalid (pg_lg (Graph_LGraph g)) r /\
                           dst (pg_lg (Graph_LGraph g)) (x, L) = l /\ dst (pg_lg (Graph_LGraph g)) (x, R) = r).

  Definition update : A -> node -> bool -> A -> formula :=
    fun g1 x d g2 => prop (Graph_vgen g1 x d = g2).

  Lemma update_is_mark1: forall (l r: addr) (G G1: A) x,
      vvalid (pg_lg (Graph_LGraph G)) x ->
      dst (pg_lg (Graph_LGraph G)) (x, L) = l ->
      dst (pg_lg (Graph_LGraph G)) (x, R) = r ->
      Graph_vgen G x true = G1 ->
      mark1 x (Graph_LGraph G) (Graph_LGraph G1).
  Proof.
    intros. unfold valid in H1.
    rewrite <- H2. split; [|split]; simpl.
    + split; [|split; [|split]]; simpl; intros; auto.
      - unfold change_vvalid. intuition.
      - unfold change_evalid. intuition.
    + unfold update_vlabel. destruct (equiv_dec x x); intuition.
    + intros. unfold update_vlabel. destruct (equiv_dec x n'); intuition.
  Qed.

  Lemma marked_node_marked: forall (G1: A) (n: addr) (G2: A) (x: addr) (v: bool),
      vlabel (Graph_LGraph G1) x = true ->
      WeakMarkGraph.mark n (Graph_LGraph G1) (Graph_LGraph G2) ->
      vlabel (Graph_LGraph G2) x = true.
  Proof.
    intros. unfold WeakMarkGraph.mark. destruct H0 as [? ?]. specialize (H1 x).
    simpl in H1. symmetry. rewrite H1. left; auto.
  Qed.

(* (*TODO: delete it *)
  Lemma axiom_5 : forall v G1 G2 G G3 x l r,
      valid (imp (and (lookup G x v l r)
                      (and (update G x true G1)
                           (and (neq v true) (and (mark G1 r G2) (mark G2 l G3)))))
                 (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
    intros. unfold valid, imp, and, lookup, neq, mark, update.
    apply imp_andp_adjoint. normalize. destruct H as [? [? [? [? [? ?]]]]].
    assert (mark1 x (Graph_LGraph G) (Graph_LGraph (Graph_vgen G x true))) by (apply (update_is_mark1 l r); auto).
    apply andp_right; normalize.
    + apply mark1_mark_list_mark with (r :: l :: nil); auto.
      - simpl. unfold Complement. unfold In.
        subst v. clear - H0. intuition.
      - apply gamma_step_list' with false; auto. simpl.
        do 2 (f_equal; auto). subst v. apply Bool.not_true_is_false in H0. auto.
      - hnf. apply (compond_intro (compond_relation Logic.eq (mark1 x)) _ _ (Graph_LGraph (Graph_vgen G x true)) _).
        apply (compond_intro Logic.eq (mark1 x) (Graph_LGraph G) (Graph_LGraph G) (Graph_LGraph (Graph_vgen G x true))); auto.
        unfold mark_list. simpl. hnf.
        apply (compond_intro
                 (compond_relation Logic.eq (Graph_Mark.mark r)) _ _ (Graph_LGraph G2) _); auto.
          apply (compond_intro Logic.eq (Graph_Mark.mark r) (Graph_LGraph (Graph_vgen G x true)) (Graph_LGraph (Graph_vgen G x true)) (Graph_LGraph G2)); auto.
    + destruct H1, H2, H8. destruct H11 as [? ?]. split.
      - apply (marked_node_marked G2 l); auto. apply (marked_node_marked (Graph_vgen G x true) r); auto. 
      - assert ((pg_lg (Graph_LGraph G)) ~=~ (pg_lg (Graph_LGraph G3))) by
            (transitivity (pg_lg (Graph_LGraph (Graph_vgen G x true))); auto; transitivity (pg_lg (Graph_LGraph G2)); auto).
        destruct H13 as [? [? [? ?]]]. split; [|split; [|split; [|split]]].
        * specialize (H13 x); intuition.
        * specialize (H13 l); intuition.
        * specialize (H13 r); intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (x, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H16 (x, L)).
          specialize (H14 (x, L)). intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (x, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H16 (x, R)).
          specialize (H14 (x, R)). intuition.
  Qed.
  *)
  Lemma axiom_1 : forall v G1 G2 G G3 x l r,
      valid (imp (and (lookup G x v l r)
                      (and (update G x true G1)
                           (and (neq v true) (and (mark G1 l G2) (mark G2 r G3)))))
                 (and (mark G x G3) (lookup G3 x true l r))).
  Proof.
    intros. unfold valid, imp, and, lookup, neq, mark, update.
    apply imp_andp_adjoint. normalize. destruct H as [? [? [? [? [? ?]]]]].
    assert (mark1 x (Graph_LGraph G) (Graph_LGraph (Graph_vgen G x true))) by (apply (update_is_mark1 l r); auto).
    apply andp_right; normalize.
    + apply mark1_mark_list_mark with (l :: r :: nil); auto.
      - simpl. unfold Complement. unfold In.
        subst v. clear - H0. intuition.
      - apply gamma_step_list with false; auto. simpl.
        do 2 (f_equal; auto). subst v. apply Bool.not_true_is_false in H0. auto.
      - hnf. apply (compond_intro (compond_relation Logic.eq (mark1 x)) _ _ (Graph_LGraph (Graph_vgen G x true)) _).
        apply (compond_intro Logic.eq (mark1 x) (Graph_LGraph G) (Graph_LGraph G) (Graph_LGraph (Graph_vgen G x true))); auto.
        unfold mark_list. simpl. hnf.
        apply (compond_intro
                 (compond_relation Logic.eq (Graph_Mark.mark l)) _ _ (Graph_LGraph G2) _); auto.
          apply (compond_intro Logic.eq (Graph_Mark.mark l) (Graph_LGraph (Graph_vgen G x true)) (Graph_LGraph (Graph_vgen G x true)) (Graph_LGraph G2)); auto.
    + destruct H1, H2, H8. destruct H11 as [? ?]. split.
      - apply (marked_node_marked G2 r); auto. apply (marked_node_marked (Graph_vgen G x true) l); auto. 
      - assert ((pg_lg (Graph_LGraph G)) ~=~ (pg_lg (Graph_LGraph G3))) by
            (transitivity (pg_lg (Graph_LGraph (Graph_vgen G x true))); auto; transitivity (pg_lg (Graph_LGraph G2)); auto).
        destruct H13 as [? [? [? ?]]]. split; [|split; [|split; [|split]]].
        * specialize (H13 x); intuition.
        * specialize (H13 l); intuition.
        * specialize (H13 r); intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (x, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H16 (x, L)).
          specialize (H14 (x, L)). intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (x, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H16 (x, R)).
          specialize (H14 (x, R)). intuition.
  Qed.

  Lemma axiom_2 : forall v G x G1 y l r, valid (imp (and (mark G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (ext (fun Anon_15 => (lookup G1 y Anon_15 l r)))))).
  Proof.
    intros. unfold valid, imp, and, mark, lookup, subset_reach, eq_notreach.
    apply imp_andp_adjoint. normalize. destruct H0 as [? [? [? [? [? ?]]]]].
    apply andp_right; [|apply andp_right].
    + apply TT_prop_right. destruct H. apply (reachable_ind.si_reachable _ _ x) in H6.
      destruct H6. auto.
    + apply TT_prop_right. destruct H.
      destruct H.
      split; [| split].
      - simpl. rewrite H6; reflexivity.
      - simpl; intros ? [? ?] [? ?].
        apply vlabel_eq.
        rewrite H7.
        assert (~ (pg_lg (Graph_LGraph G)) |= x ~o~> v0
          satisfying (WeakMarkGraph.unmarked (Graph_LGraph G))); [| tauto].
        intro.
        apply reachable_by_is_reachable in H12.
        apply H9; auto.
      - simpl; intros ? [? ?] [? ?].
        match goal with | |- ?A = ?B => destruct A, B; auto end.
      (* rewrite H6; reflexivity. *)
(*
SearchAbout predicate_partialgraph (_ ~=~ _).
Locate si_stronger_partialgraph.
       reflexivity.
      unfold vertices_identical2.
      split; [apply Ensembles_ext.Intersection_proper |].
      1: rewrite Same_set_spec; intro; hnf; apply (proj1 H6).
      1: rewrite H6; reflexivity.
      rewrite vertices_identical_spec; intros.
      specialize (H7 x0).
      simpl in H7 |- *; unfold node in *.
      rewrite Intersection_spec in H8; destruct H8.
      f_equal; [f_equal |].
      - assert (~ reachable_by (pg_lg (Graph_LGraph G)) x (WeakMarkGraph.unmarked (Graph_LGraph G)) x0).
        1: {
          intro.
          apply reachable_by_is_reachable in H10; auto.
        }
        assert (true <> false) by congruence.
        destruct (vlabel (Graph_LGraph G) x0), (vlabel (Graph_LGraph G1) x0); try tauto.
      - apply (si_dst1 _ _ _ H6).
        apply (@left_valid _ _ _ _ _ _ (pg_lg (Graph_LGraph G)) (biGraph G)); auto.
      - apply (si_dst1 _ _ _ H6).
        apply (@right_valid _ _ _ _ _ _ (pg_lg (Graph_LGraph G)) (biGraph G)); auto.
*)
    + unfold ext. destruct H as [[? ?] ?]. specialize (H6 y). simpl in H6.
      destruct H7 as [? [? [? ?]]].
      LEM ((pg_lg (Graph_LGraph G)) |= x ~o~> y satisfying (WeakMarkGraph.unmarked (Graph_LGraph G))).
      - assert (vlabel (Graph_LGraph G1) y = true) by (symmetry; rewrite H6; right; auto).
        apply (exp_right true). normalize. split; [|split;[|split;[|split; [|split]]]]; auto.
        * specialize (H7 y); intuition.
        * specialize (H7 l); intuition.
        * specialize (H7 r); intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (y, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H10 (y, L)).
          specialize (H8 (y, L)). intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (y, R)) by
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
        * assert (evalid (pg_lg (Graph_LGraph G)) (y, L)) by
              (apply (@left_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst l. symmetry. specialize (H10 (y, L)).
          specialize (H8 (y, L)). intuition.
        * assert (evalid (pg_lg (Graph_LGraph G)) (y, R)) by
              (apply (@right_valid _ _ _ _ _ _ _ (biGraph G)); auto).
          subst r. symmetry. specialize (H10 (y, R)).
          specialize (H8 (y, R)). intuition.
  Qed.

  Lemma axiom_3 : forall l r x G, valid (imp (lookup G x true l r) (mark G x G)).
  Proof.
    intros. unfold valid, imp, lookup, mark. rewrite <- iter_sepcon.prop_impl_imp. normalize.
    destruct H as [? [? [? [? [? ?]]]]]. hnf. split; [|reflexivity].
    split; [|split]; [reflexivity | intros..]; [intuition|destruct H5; auto].
    apply reachable_by_head_prop in H5. simpl in H5. unfold Complement in H5. unfold In in H5.
    exfalso; auto.
  Qed.

  Lemma axiom_4 : forall G, valid (mark G null_node G).
  Proof.
    intros. unfold valid, mark, null_node. normalize. hnf. split; [|reflexivity].
    hnf. split; [|intros; split; intros]; [reflexivity | intuition |]. destruct H; auto.
    exfalso. apply reachable_by_head_valid in H.
    apply (@valid_not_null _ _ _ _ _ _ (maGraph G) _) in H; auto. reflexivity.
  Qed.

  Lemma lookup_graph_unfold: forall (G: A) x v l r,
      vlabel (Graph_LGraph G) x = v -> vvalid (pg_lg (Graph_LGraph G)) x -> vvalid (pg_lg (Graph_LGraph G)) l ->
      vvalid (pg_lg (Graph_LGraph G)) r -> dst (pg_lg (Graph_LGraph G)) (x, L) = l ->
      dst (pg_lg (Graph_LGraph G)) (x, R) = r -> (graph x G = ptto_node x v l r ⊗ graph l G ⊗ graph r G).
  Proof.
    intros. unfold graph. unfold ptto_node. apply bi_graph_unfold; auto.
    simpl. f_equal; [f_equal|]; auto.
  Qed.

  Lemma graph_graphs_eq_l:
    forall (G: A) v x l r, vlabel (Graph_LGraph G) x = v -> vvalid (pg_lg (Graph_LGraph G)) x ->
                           vvalid (pg_lg (Graph_LGraph G)) l -> vvalid (pg_lg (Graph_LGraph G)) r ->
                           dst (pg_lg (Graph_LGraph G)) (x, L) = l -> dst (pg_lg (Graph_LGraph G)) (x, R) = r ->
                           (ptto_node x v l r ⊗ (graph l G ⊗ graph r G)) =
                           graph l G ⊗ graphs (x :: l :: r :: nil) (Graph_LGraph G).
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
      assert (forall (g: A), graph l g = graphs (l :: nil) (Graph_LGraph g)) by (intros; simpl; rewrite ocon_emp; auto).
      rewrite (H13 G). rewrite (H13 G1). apply subgraph_update; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - rewrite !reachable_through_set_single'; auto.
  Qed.

  Lemma graph_graphs_eq_r:
    forall (G: A) v x l r, vlabel (Graph_LGraph G) x = v -> vvalid (pg_lg (Graph_LGraph G)) x ->
                           vvalid (pg_lg (Graph_LGraph G)) l -> vvalid (pg_lg (Graph_LGraph G)) r ->
                           dst (pg_lg (Graph_LGraph G)) (x, L) = l -> dst (pg_lg (Graph_LGraph G)) (x, R) = r ->
                           (ptto_node x v l r ⊗ (graph l G ⊗ graph r G)) =
                           graph r G ⊗ graphs (x :: l :: r :: nil) (Graph_LGraph G).
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
      assert (forall (g: A), graph r g = graphs (r :: nil) (Graph_LGraph g)) by (intros; simpl; rewrite ocon_emp; auto).
      rewrite (H13 G). rewrite (H13 G1). apply subgraph_update; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - intros. left. simpl in H14. destruct H14 as [? | [? | [? | [? | ?]]]]; [subst x0 ..|exfalso]; auto.
      - rewrite !reachable_through_set_single'; auto.
  Qed.

  Lemma lem_pttoupdate : forall v l r G x v1 G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. unfold valid, imp, and, star, mwand, union, subset_reach, eq_notreach, lookup, update.
    apply imp_andp_adjoint. normalize. apply precise_wand_ewand.
    + unfold ptto_node. apply log_normalize.mapsto_precise.
    + destruct H as [? [? [? [? [? ?]]]]]. rewrite <- ocon_assoc. rewrite <- (lookup_graph_unfold G x v l r); auto.
      rewrite <- ocon_assoc.
      assert (vgamma (LGraph_SGraph (Graph_LGraph G)) x = (v, l, r)). {
        simpl. f_equal; [f_equal |]; auto.
      } 
      pose proof (Graph_vgen_vgamma G x v v1 l r H5).
      rewrite <- (lookup_graph_unfold (Graph_vgen G x v1) x v1 l r);
        [| inversion H6 | ..|inversion H6|inversion H6]; auto.
      2: rewrite H8; auto.
      apply va_reachable_root_update_ramify; auto.
  Qed.

End GraphMark.
