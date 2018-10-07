Require Import RamifyCoq.sample_mark.env_dispose_bi.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.GraphBi_Mark.
Require Import RamifyCoq.data_structure.spatial_graph_dispose_bi.
Require Import RamifyCoq.data_structure.spatial_graph_unaligned_bi_VST.
Require Import RamifyCoq.floyd_ext.share.
Require RamifyCoq.graph.weak_mark_lemmas.
Import RamifyCoq.graph.weak_mark_lemmas.WeakMarkGraph.

Require Import VST.msl.wand_frame.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation vertices_at sh g P := (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ g P).
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST bool unit unit).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (graph sh x g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (mark x g g')
        LOCAL()
        SEP (graph sh x g').

Definition spanning_spec :=
  DECLARE _spanning
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x; fst (fst (vgamma g x)) = false)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (graph sh x g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (spanning_tree g x g')
        LOCAL()
        SEP (vertices_at sh (reachable g x) g').

Definition dispose_spec :=
  DECLARE _dispose
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (!!is_tree g x && graph sh x g)
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs := ltac:(with_library prog [mark_spec ; spanning_spec ; dispose_spec ; main_spec]).

Lemma graph_local_facts: forall sh x (g: Graph), vvalid g x -> @derives mpred Nveric (graph sh x g) (valid_pointer (pointer_val_val x)).
Proof.
  intros.
  eapply derives_trans; [apply (@va_reachable_root_stable_ramify pSGG_VST _ _ _ (sSGG_VST sh) g x (vgamma g x)); auto |].
  simpl vertex_at. unfold trinode. entailer!.
Qed.

Lemma graph_left_local_facts: forall sh x (g: Graph) d l r, vvalid g x -> vgamma g x = (d, l, r) -> graph sh x g |-- valid_pointer (pointer_val_val l).
Proof.
  intros.
  eapply derives_trans; [apply (@graph_ramify_aux1_left pSGG_VST (sSGG_VST sh) g x d l r); auto | ].
  assert (weak_valid g l) by (apply (gamma_left_weak_valid g x d l r); auto). destruct H1.
  - simpl in H1. subst l. simpl pointer_val_val. apply sepcon_valid_pointer1. entailer!.
  - apply sepcon_valid_pointer1. apply graph_local_facts; auto.
Qed.

Lemma graph_right_local_facts: forall sh x (g1 g2: Graph) l l' r,
    vvalid g1 x -> vgamma g1 x = (true, l, r) -> vvalid g2 x -> vgamma g2 x = (true, l', r) -> edge_spanning_tree g1 (x, L) g2 ->
    vertices_at sh (reachable g1 x) g2 |-- valid_pointer (pointer_val_val r).
Proof.
  intros.
  eapply derives_trans; [apply (@graph_ramify_aux1_right pSGG_VST (sSGG_VST sh) g1 g2 x l r); auto | ].
  assert (weak_valid g2 r) by (apply (gamma_right_weak_valid g2 x true l' r); auto). destruct H4.
  - simpl in H4. subst r. simpl pointer_val_val. apply sepcon_valid_pointer1. entailer!.
  - apply sepcon_valid_pointer1. apply graph_local_facts; auto.
Qed.
  
Lemma body_spanning: semax_body Vprog Gprog f_spanning spanning_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  assert (d = false) by (simpl in H1; auto).
  subst.
  assert (Hisptr: isptr (pointer_val_val x)). {
    destruct x. simpl. auto.
    apply (valid_not_null g) in H. exfalso; auto.
    reflexivity.
  }
  localize [data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
                    (pointer_val_val x)].
  forward. 1: entailer!; destruct l; simpl; auto.
  forward. 1: entailer!; destruct r; simpl; auto.
  forward.
  unlocalize [graph sh x (Graph_vgen g x true)].
  1: {
    apply (@root_update_ramify _ (sSGG_VST sh) g x _ (false, l, r) (true, l, r)); auto.
    eapply Graph_vgen_vgamma; eauto.
  }
  (* if (l) { *)
  symmetry in H1.
  pose proof Graph_vgen_true_mark1 g x _ _ H1 H.
  assert (H_GAMMA_g1: vgamma (Graph_vgen g x true) x = (true, l, r)) by
   (eapply Graph_vgen_vgamma; eauto).
  assert (vvalid (Graph_vgen g x true) x) by
      (destruct H2 as [[? _] _]; apply H2; auto).
  forget (Graph_vgen g x true) as g1.
  forward_if
    (EX g2: Graph,
     PROP  (edge_spanning_tree g1 (x, L) g2)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g2)).
  - apply denote_tc_test_eq_split. 2: entailer!. apply (graph_left_local_facts _ _ _ true l r); auto.
  - (* root_mark = l -> m; *)
    localize [data_at sh node_type (vgamma2cdata (vgamma g1 l)) (pointer_val_val l)].
    remember (vgamma g1 l) as dlr in |-*.
    destruct dlr as [[dd ll] rr]. 
    forward. simpl vgamma2cdata at 1.
    replace (if dd then 1 else 0) with (if node_pred_dec (marked g1) l then 1 else 0).
    2: {
      destruct (node_pred_dec (marked g1)); destruct dd; auto; symmetry in Heqdlr.
      apply vgamma_is_false in Heqdlr. simpl in a. unfold unmarked in Heqdlr. hnf in Heqdlr.
      unfold Ensembles.In in Heqdlr. simpl in Heqdlr. apply Heqdlr in a. exfalso; auto.
      apply vgamma_is_true in Heqdlr. exfalso; auto.
    }
    rewrite Heqdlr. clear dd ll rr Heqdlr.
    unlocalize [graph sh x g1].
    + destruct (vgamma g1 l) as [[dd ll] rr] eqn:? .
      assert (vvalid g1 l). {
        assert (weak_valid g1 l) by (eapply gamma_left_weak_valid; eauto).
        destruct H5; auto. hnf in H5. subst. exfalso; intuition.
      } unfold vgamma2cdata.
      apply (@va_reachable_internal_stable_ramify pSGG_VST _ _ _ (sSGG_VST sh) g1 x l (dd, ll, rr)); auto.
      apply (gamma_left_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 l).
      apply reachable_by_refl; auto.
    + (* if (root_mark == 0) { *)
      Opaque node_pred_dec.
      Opaque pSGG_VST.
      (* remember (if node_pred_dec (marked g1) l then 1 else 0). *)
      forward_if
        (EX g2: Graph,
         PROP  (edge_spanning_tree g1 (x, L) g2)
         LOCAL (temp _r (pointer_val_val r);
                temp _l (pointer_val_val l);
                temp _x (pointer_val_val x))
         SEP (vertices_at sh (reachable g1 x) g2)).
      * (* spanning(l); *)
        Transparent node_pred_dec.
        Transparent pSGG_VST.
        destruct (node_pred_dec (marked g1) l). 1: inversion H5.
        localize [graph sh l g1].
        assert (vvalid g1 l). {
          apply gamma_left_weak_valid in H1. 2: auto.
          destruct H2.
          rewrite (weak_valid_si _ _ _ H2) in H1.
          destruct H1. 2: auto.
          hnf in H1. subst l.
          simpl in H4. exfalso; auto.
        } assert (fst (fst (vgamma g1 l)) = false). {
          simpl in n.
          simpl. destruct (vlabel g1 l) eqn:? ; auto.
          symmetry in Heqb. apply n in Heqb. inversion Heqb.
        } forward_call (sh, g1, l).
        Intros g'.
        unlocalize [vertices_at sh (reachable g1 x) g'] using g' assuming H8.
        1: apply (@graph_ramify_aux1_left _ (sSGG_VST sh) g1 x true l r); auto.
        Exists g'. entailer!.
        assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; inversion H_GAMMA_g1; auto).
        unfold edge_spanning_tree. if_tac; subst l; [exfalso |]; auto.
      * (* x -> l = 0; *)
        destruct (node_pred_dec (marked g1) l). 2: exfalso; auto.
        localize [data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)].
        forward.
        unlocalize [vertices_at sh (reachable g1 x) (Graph_gen_left_null g1 x)].
        1: apply (@graph_gen_left_null_ramify _ (sSGG_VST sh) g1 x true l r); auto.
        Exists (Graph_gen_left_null g1 x).
        entailer!.
        apply (edge_spanning_tree_left_null g1 x true l r); auto.
  - forward. Exists g1. entailer!. 2: apply derives_refl. apply edge_spanning_tree_invalid.
    + apply (@left_valid _ _ _ _ _ _ g1 _ _) in H3; auto.
    + intro. apply (valid_not_null g1 l).
      * assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; inversion H_GAMMA_g1; auto). rewrite H9. apply H8.
      * hnf. destruct l. 1: inversion H4. auto.
  - (* if (r) { *)
    Intros g2.
    assert (vvalid g2 x) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x); auto).
    destruct (edge_spanning_tree_left_vgamma g1 g2 x l r H3 H_GAMMA_g1 H4) as [l' H_GAMMA_g2].
    forward_if
      (EX g3: Graph,
       PROP  (edge_spanning_tree g2 (x, R) g3)
       LOCAL (temp _r (pointer_val_val r);
              temp _l (pointer_val_val l);
              temp _x (pointer_val_val x))
       SEP (vertices_at sh (reachable g1 x) g3)).
    + apply denote_tc_test_eq_split. 2: entailer!. apply (graph_right_local_facts _ _ _ _ l l' r); auto.
    + (* root_mark = r -> m; *)
      localize [data_at sh node_type (vgamma2cdata (vgamma g2 r)) (pointer_val_val r)].
      remember (vgamma g2 r) as dlr in |-*. destruct dlr as [[dd ll] rr].
      forward. simpl vgamma2cdata at 1.
      replace (if dd then 1 else 0) with (if node_pred_dec (marked g2) r then 1 else 0).
      2: {
        destruct (node_pred_dec (marked g2)); destruct dd; auto; symmetry in Heqdlr.
        apply vgamma_is_false in Heqdlr. simpl in a. unfold unmarked in Heqdlr. hnf in Heqdlr.
        unfold Ensembles.In in Heqdlr. simpl in Heqdlr. apply Heqdlr in a. exfalso; auto.
        apply vgamma_is_true in Heqdlr. exfalso; auto.
      } rewrite Heqdlr. clear dd ll rr Heqdlr.
      unlocalize [vertices_at sh (reachable g1 x) g2].
      * destruct (vgamma g2 r) as [[dd ll] rr] eqn:? .
        assert (vvalid g1 r). {
          assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
          destruct H7; auto. hnf in H7; subst. exfalso; intuition.
        } unfold vgamma2cdata; apply (@vertices_at_ramif_1_stable _ _ _ _ _ _ _ (SGA_VST sh) _ _ r (dd, ll, rr)); auto.
        apply (gamma_right_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 r).
        apply reachable_by_refl; auto.
      * (* if (root_mark == 0) { *)
        Opaque node_pred_dec.
        Opaque pSGG_VST.
        forward_if
          (EX g3: Graph,
           PROP  (edge_spanning_tree g2 (x, R) g3)
           LOCAL (temp _r (pointer_val_val r);
                  temp _l (pointer_val_val l);
                  temp _x (pointer_val_val x))
           SEP (vertices_at sh (reachable g1 x) g3)).
        -- (* spanning(r); *)
          Transparent node_pred_dec.
          Transparent pSGG_VST.
          destruct (node_pred_dec (marked g2) r). 1: inversion H7.
          localize [graph sh r g2].
          assert (vvalid g1 r). {
            assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
            destruct H8; auto. hnf in H8; subst. exfalso; intuition.
          }
          assert (vvalid g2 r) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x); auto).
          assert (fst (fst (vgamma g2 r)) = false). {
            simpl in n |-* . destruct (vlabel g2 r) eqn:? ; auto.
            symmetry in Heqb. apply n in Heqb. exfalso; auto.
          }
          forward_call (sh, g2, r).
          Intros g3.
          unlocalize [vertices_at sh (reachable g1 x) g3] using g3 assuming H11.
          1: apply (@graph_ramify_aux1_right _ (sSGG_VST sh) g1 g2 x l r); auto.
          Exists g3. entailer!.
          assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; inversion H_GAMMA_g2; auto).
          unfold edge_spanning_tree. if_tac; subst r; [exfalso |]; auto.
        -- (* x -> r = 0; *)
          destruct (node_pred_dec (marked g2) r). 2: exfalso; auto.
          localize [data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l', pointer_val_val r)) (pointer_val_val x)].
          forward.
          unlocalize [vertices_at sh (reachable g1 x) (Graph_gen_right_null g2 x)].
          1: apply (@graph_gen_right_null_ramify _ (sSGG_VST sh) g1 g2 x true l' r); auto.
          Exists (Graph_gen_right_null g2 x).
          entailer!. apply (edge_spanning_tree_right_null g2 x true l' r); auto.
    + forward. Exists g2. entailer!. apply edge_spanning_tree_invalid.
      * apply (@right_valid _ _ _ _ _ _ g2 _ _) in H5; auto.
      * intro. apply (valid_not_null g2 r).
        -- assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; inversion H_GAMMA_g2; auto). rewrite H11. apply H10.
        -- hnf. destruct r. 1: inversion H6. auto.
    + (* return *)
      Intros g3. forward. Exists g3. entailer!.
      * apply (edge_spanning_tree_spanning_tree g g1 g2 g3 x l r); auto.
      * destruct H2. apply derives_refl'. apply vertices_at_Same_set. rewrite H2; reflexivity.
Qed. (* original: 5500 sec, VST 2.*: 8.91 secs *)
