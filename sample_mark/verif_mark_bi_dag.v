Require Import RamifyCoq.lib.Coqlib.
Require Export VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.DagBi_Mark.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_graph_bi_mark.
Require Import VST.msl.wand_frame.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation dag sh x g := (@reachable_dag_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST bool unit unit).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (dag sh x g)
  POST [ Tvoid ]
      EX g': Graph,
        PROP (mark x g g')
        LOCAL()
        SEP (dag sh x g').

Definition main_spec :=
 DECLARE _main
  WITH u : globals
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs := ltac:(with_library prog [mark_spec ; main_spec]).

Lemma dag_local_facts: forall sh x (g: Graph), weak_valid g x -> dag sh x g |-- valid_pointer (pointer_val_val x).
Proof.
  intros. destruct H.
  - simpl in H. subst x. entailer!.
  - destruct (vgamma g x) as [[d l] r] eqn:? . erewrite root_unfold; eauto. simpl vertex_at. entailer!.
Qed.

Lemma body_mark: semax_body Vprog Gprog f_mark mark_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.

  forward_if  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (dag sh x g)).
  - apply denote_tc_test_eq_split. 2: entailer!. apply dag_local_facts; auto.
  - (* return *) forward. Exists g. entailer!. destruct x. 1: simpl in H; inversion H. apply (mark_null_refl g).
  - (* skip *) forward. entailer!.
  - Intros. assert (vvalid g x) as gx_vvalid. {
      destruct H_weak_valid; [| auto].
      unfold is_null_SGBA in H0; simpl in H0; subst x.
      exfalso. apply H. auto.
    } assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i). {
      destruct x. 2: exfalso; apply H; reflexivity. split; simpl; auto.
      exists b, i. reflexivity.
    } destruct H0 as [? [b [i ?]]]. clear H0 H_weak_valid.
    erewrite root_unfold by eauto. Intros.
    change (vertex_at x (d, l, r)) with
        (@data_at CompSpecs sh node_type
                  (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).
    forward. (* root_mark = x -> m; *)
    eapply semax_pre with
        (PROP  ()
               LOCAL
               (temp _root_mark (Vint (Int.repr (if d then 1 else 0)));
                temp _x (pointer_val_val x))
               SEP  (dag sh x g)).
    1: erewrite root_unfold by eauto; simpl vertex_at; entailer!.
    forward_if  (* if (root_mark == 1) *)
      (PROP (d = false)
            LOCAL (temp _x (pointer_val_val x))
            SEP (dag sh x g)).
    + forward. (* return *) Exists g. entailer!.
      eapply (mark_vgamma_true_refl g); eauto.
      clear - H0; destruct d; [auto | inversion H0].
    + forward. (* skip; *) entailer!. clear - H0; destruct d; congruence.
    + erewrite root_unfold by eauto. Intros. subst d.
      change (vertex_at x (false, l, r)) with
          (@data_at CompSpecs sh node_type
                    (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).
      forward. (* l = x -> l; *) 1: entailer!; destruct l; simpl; auto.
      forward. (* r = x -> r; *) 1: entailer!; destruct r; simpl; auto.
      forward. (* x -> d = 1; *)
      pose proof Graph_vgen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
      apply semax_pre with
          (PROP  ()
                 LOCAL (temp _r (pointer_val_val r);
                        temp _l (pointer_val_val l);
                        temp _x (pointer_val_val x))
                 SEP (dag sh x (Graph_vgen g x true))).
      1: erewrite root_update_unfold by eauto; simpl vertex_at; entailer!.
      forget (Graph_vgen g x true) as g1.
      assert (weak_valid g1 l) by (eapply left_weak_valid; eauto).
      (* mark(l); *)
      localize [dag sh l g1].
      forward_call (sh, g1, l).
      Intros g2.
      unlocalize [dag sh x g2] using g2 assuming H3.
      1: subst; eapply (@dag_ramify_left _ (sSGG_VST sh) g); eauto.
      assert (weak_valid g2 r) by (eapply right_weak_valid; eauto).
      (* mark(r); *)
      localize [dag sh r g2].
      forward_call (sh, g2, r).
      Intros g3.
      unlocalize [dag sh x g3] using g3 assuming H5.
      1: subst; eapply (@dag_ramify_right _ (sSGG_VST sh) g); eauto.
      forward. (* ( return; ) *)
      Exists g3. entailer!.
      apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
Qed. (* Original: 114 seconds; VST 2.*: 2.739 secs *)
