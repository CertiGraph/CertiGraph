Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.copy.env_copy_bi.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.weak_mark_lemmas.
Require Import CertiGraph.graph.local_graph_copy.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.reachable_computable.
Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.Graph_Copy.
Require Import CertiGraph.msl_application.GraphBi.
Require Import CertiGraph.msl_application.GraphBi_Copy.
Require Import CertiGraph.copy.spatial_graph_bi_copy.
Require Import VST.msl.wand_frame.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

Hint Resolve concrete_valid_pointer_valid_pointer: valid_pointer.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion Graph'_LGraph: Graph' >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion Graph'_GeneralGraph: Graph' >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ (addr * LR) unit _ mpred (@SGP pSGG_VST addr (addr * LR) (sSGG_VST sh)) (SGA_VST sh) x g).
Notation holegraph sh x g := (@vertices_at _ _ _ _ _ mpred (@SGP pSGG_VST addr (addr * LR) (sSGG_VST sh)) (SGA_VST sh) (Ensembles.Intersection _ (@vvalid addr (addr * LR) _ _ g) (fun u => x <> u)) (LGraph_SGraph g)).
Notation Graph := (@Graph pSGG_VST (@addr pSGG_VST) (addr * LR) unit).
Notation vmap := (@LocalGraphCopy.vmap addr (addr * LR) addr (addr * LR) _ _ _ _ _ _ _ _ (@GMS _ _ _ CCS)).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh: wshare
  PRE [tint]
     PROP ()
     PARAMS (Vint (Int.repr 16))
     GLOBALS ()
     SEP ()
  POST [ tptr tvoid ]
     EX v: addr,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (data_at Ews node_type (pointer_val_val null,
                                 (pointer_val_val null, pointer_val_val null))
                  (pointer_val_val v);
          concrete_valid_pointer v).

Definition copy_spec :=
 DECLARE _copy
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [tptr (Tstruct _Node noattr)]
          PROP  (weak_valid g x)
          PARAMS (pointer_val_val x)
          GLOBALS ()
          SEP   (graph sh x g)
  POST [ (tptr (Tstruct _Node noattr)) ]
        EX xgg: pointer_val * Graph * Graph',
        let x' := fst (fst xgg) in
        let g1 := snd (fst xgg) in
        let g1' := snd xgg in
        PROP (copy (x: @addr pSGG_VST) g g1 g1';
             x = null /\ x' = null \/ x' = vmap g1 x)
        LOCAL (temp ret_temp (pointer_val_val x'))
        SEP   (graph sh x g1; graph Ews x' g1').

Definition main_spec :=
 DECLARE _main
  WITH u : globals
  PRE  [] main_pre prog tt u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := ltac:(with_library prog [copy_spec; mallocN_spec; main_spec]).

Transparent pSGG_VST sSGG_VST.

Lemma graph_local_facts: forall sh x (g: Graph), weak_valid g x -> graph sh x g |-- valid_pointer (pointer_val_val x).
Proof.
  intros. destruct H.
  - simpl in H. subst x. entailer!.
  - eapply derives_trans.
    + apply (@va_reachable_root_stable_ramify pSGG_VST _ _ _ (sSGG_VST sh) g x (vgamma g x)); auto.
    + simpl.
      entailer!.
Qed.

Opaque pSGG_VST sSGG_VST.

Lemma body_copy: semax_body Vprog Gprog f_copy copy_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.
  forward_if  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (graph sh x g)).
  - apply denote_tc_test_eq_split. 2: entailer!. apply graph_local_facts; auto.
  - assert (x = NullPointer) by (destruct x; simpl in H; inversion H; auto). subst x.
    forward.
    Exists ((NullPointer, g), empty_Graph').
    simpl. entailer!.
    + apply (copy_null_refl g).
    + rewrite va_reachable_invalid; auto. apply derives_refl. (* TODO why?*)
  - forward. entailer!.
  - Intros.
    assert (vvalid g x) as gx_vvalid. {
      destruct H_weak_valid; [| auto]. simpl in H0.
      subst; exfalso; apply H; auto.
    } assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i). {
      destruct x. 2: exfalso; apply H; reflexivity. split; simpl; auto.
      exists b, i. reflexivity.
    } destruct H0 as [? [b [i ?]]]. clear H0 H_weak_valid.
    localize [data_at sh node_type (pointer_val_val d, (pointer_val_val l, pointer_val_val r)) (pointer_val_val x); concrete_valid_pointer d].
    forward. (* x0 = x -> m; *) 1: entailer!; destruct d; simpl; auto.
    unlocalize [graph sh x g]. 1: apply (@root_stable_ramify _ (sSGG_VST sh) g x _ H_GAMMA_g); auto.
    forward_if  (* if (x0 != 0) *)
      (PROP (d = null)
       LOCAL (temp _x (pointer_val_val x))
       SEP (graph sh x g)).
    { apply denote_tc_test_eq_split. 2: entailer!.
      eapply derives_trans; [apply (@root_stable_ramify _ (sSGG_VST sh) g (ValidPointer b i) _ H_GAMMA_g); auto |].
      apply sepcon_valid_pointer1. Transparent sSGG_VST. simpl vertex_at. unfold_data_at (data_at _ _ _ _).
      entailer!.
    }
  1: { (* if-then branch *)
    forward. (* return x0; *)
    apply (exp_right (d, g, empty_Graph')).
    simpl.
    entailer!; auto.
    1: split.
    + eapply (copy_vgamma_not_null_refl g); eauto.
      clear - H0.
      destruct d; [change null with (NullPointer) | simpl in H0; change nullval with (Vint Int.zero) in H0]; try congruence.
    + right.
      inversion H_GAMMA_g; auto.
    + rewrite (va_reachable_invalid _ d); auto.
      cancel.
  }
  1: { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    clear - H0. destruct d; inversion H0. auto.
  }

  Intros.
  subst d.
  forward_call sh. (* x0 = (struct Node * ) mallocN (sizeof (struct Node)); *)

  Intros x0.
  assert_PROP (x0 <> null) as x0_not_null. { entailer!. }

  localize
  [data_at sh node_type (pointer_val_val null, (pointer_val_val l, pointer_val_val r)) (pointer_val_val x);
   concrete_valid_pointer x0].
  (* localize *)

  forward.
  (* l = x -> l; *)
  {
    entailer!.
    rewrite value_fits_eq in H4; simpl in H4.
    destruct H4 as [_ [? _]].
    rewrite value_fits_eq in H4; simpl in H4.
    unfold tc_val' in H4.
    simpl in H4.
    destruct l; simpl; auto.
  }

  forward.
  (* r = x -> r; *)
  {
    entailer!.
    rewrite value_fits_eq in H5; simpl in H5.
    destruct H5 as [_ [? _]].
    rewrite value_fits_eq in H5; simpl in H5.
    unfold tc_val' in H5.
    simpl in H5.
    destruct r; simpl; auto.
  }

  forward.
  (* x -> m = x0; *)

  unlocalize
  [data_at Ews node_type
           (pointer_val_val null, (pointer_val_val null, pointer_val_val null))
           (pointer_val_val x0);
   holegraph Ews x0 (initial_copied_Graph x x0 g);
   graph sh x (Graph_vgen g x x0)].
  {
    cancel.
    rewrite sepcon_assoc.
    match goal with
    | |- _ |-- _ * (_ -* (_ * (?P * _))) =>
      replace P with emp; [| symmetry; apply (@root_update_ramify1 _ (sSGG_VST Ews) g x x0 x0 (null, l, r) (x0, l, r)); auto]
    end.
    match goal with
    | |- ?A * _ |-- _ =>
      replace A with (A * concrete_valid_pointer null) by (rewrite concrete_valid_pointer_null, sepcon_emp; auto)
    end.
    match goal with
    | |- _ |-- ?A * _ =>
      replace A with (A * concrete_valid_pointer null) by (rewrite concrete_valid_pointer_null, sepcon_emp; auto)
    end.
    apply (@root_update_ramify2 _ (sSGG_VST sh)  g x x0 x0 (null, l, r) (x0, l, r)); auto.
    eapply Graph_vgen_vgamma; eauto.
  }
  (* unlocalize *)
  destruct (not_null_copy1 g x x0 _ _ H_GAMMA_g gx_vvalid x0_not_null) as [H_vopy1 [H_x0 BiMaFin_g1']].
  forget (Graph_vgen g x x0) as g1.
  forget (initial_copied_Graph x x0 g) as g1'.

  forward.
  (* x0 -> m = 0; *)

  assert_PROP (weak_valid g1 l).
  1: apply prop_right; eapply left_weak_valid; eauto.

  match goal with
  | |- context [SEPx (?A :: _)] =>
      replace A with (A * concrete_valid_pointer null) by (rewrite concrete_valid_pointer_null, sepcon_emp; auto)
  end; Intros.

  localize [graph sh l g1].
  (* localize *)

  forward_call (sh, g1, l).
  Intros ret; destruct ret as [[l0 g2] g2''].
  rename H2 into H_copy, H3 into H_l0.
  cbv [fst snd] in H_copy, H_l0 |- *.
  (* l0 = copy(l); *)

  unlocalize
    [data_at Ews node_type (Vint (Int.repr 0), (pointer_val_val null, pointer_val_val null)) (pointer_val_val x0) * concrete_valid_pointer null;
         holegraph Ews x0 g1';
         graph sh x g2;
         graph Ews l0 g2'']
  using (g2'', g2, l0)
  assuming (H_copy, H_l0).
  {
    rewrite allp_uncurry'.
    rewrite allp_uncurry'.
    rewrite <- sepcon_assoc.
    match goal with
    | |- ?F1 * (?F2 * _) |-- _ * allp (fun _ => _ --> (_ * ?F3 _ _ -* _)) =>
           apply (@graph_ramify_left _ (sSGG_VST sh) g g1 g1' x l r F1 F2 F3)
    end; eauto.
  }
  (* unlocalize *)

  Intros. gather_SEP (data_at _ _ _ _) (concrete_valid_pointer _) (vertices_at _ _)
                     (reachable_vertices_at _ g2'').
  replace_SEP 0
      (EX g2': LGraph,
       !! (extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') /\
           is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e nil) g2') &&
          (data_at Ews node_type
            (pointer_val_val null, (pointer_val_val null, pointer_val_val null)) (pointer_val_val x0) * concrete_valid_pointer null *
           holegraph Ews x0 g2')).
  {
    entailer.
    apply (@extend_copy_left _ (sSGG_VST Ews) g g1 g2 g1' g2'' (ValidPointer b i) l r (vmap g1 (ValidPointer b i)) l0 (null, null, null)); auto.
  }
  clear g2'' H_copy BiMaFin_g1'.
  Intros g2'. rename H2 into H_copy_left, H3 into BiMaFin_g2'.

  forward. (* x0 -> l = l0; *)

  pose proof (@va_labeledgraph_add_edge_left _ (sSGG_VST Ews) g g1 g2 g1' g2' x l r x0 l0) as HH.
  Opaque vvalid graph_gen.labeledgraph_add_edge. simpl vertices_at in HH |- *. Transparent vvalid graph_gen.labeledgraph_add_edge. rewrite HH by auto; clear HH.

  pose proof (@va_labeledgraph_egen_left _ (sSGG_VST sh) g2 x x0) as HH.
  Opaque Graph_LGraph.
  simpl reachable_vertices_at in HH |- *. rewrite HH; clear HH.
  Transparent Graph_LGraph.

  destruct (labeledgraph_add_edge_ecopy1_left g g1 g2 g1' g2' x l r x0 l0 gx_vvalid H_GAMMA_g H_vopy1 H_copy_left H_x0 H_l0 BiMaFin_g2' x0_not_null) as [H_ecopy1_left [BiMaFin_g3' [H_x0L Hl0_dst]]].
  clear BiMaFin_g2'.
  forget (Graph_egen g2 (x: addr, L) (x0: addr, L)) as g3.
  forget (graph_gen.labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L)) as g3'.

  assert_PROP (weak_valid g3 r).
  { apply prop_right. eapply right_weak_valid; eauto. }
  localize [graph sh r g3].
  (* localize *)

  forward_call (sh, g3, r).
  Intros ret; destruct ret as [[r0 g4] g4''].
  rename H3 into H_copy, H4 into H_r0.
  cbv [fst snd] in H_copy, H_r0 |- *.
  (* r0 = copy(r); *)

  unlocalize
    [data_at Ews node_type
          (Vint (Int.repr 0), (pointer_val_val l0, pointer_val_val null))
          (pointer_val_val x0) * concrete_valid_pointer null;
         holegraph Ews x0 g3';
         graph sh x g4; graph Ews r0 g4'']
  using (g4'', g4, r0)
  assuming (H_copy, H_r0).
  {
    rewrite allp_uncurry'.
    rewrite allp_uncurry'.
    rewrite <- sepcon_assoc.
    match goal with
    | |- ?F1 * (?F2 * _) |-- _ * allp (fun _ => _ --> (_ * ?F3 _ _ -* _)) =>
           apply (@graph_ramify_right _ (sSGG_VST sh) g g1 g2 g3 g1' g2' g3' x l r F1 F2 F3)
    end; eauto.
  }
  (* Unlocalize *)
  Intros. gather_SEP (data_at _ _ _ _) (concrete_valid_pointer _) (vertices_at _ _)
                     (reachable_vertices_at _ g4'').
  replace_SEP 0
      (EX g4': LGraph,
       !! (extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') /\
           is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g4') &&
          (data_at Ews node_type
            (pointer_val_val null, (pointer_val_val l0, pointer_val_val null)) (pointer_val_val x0) * concrete_valid_pointer null *
           holegraph Ews x0 g4')).
  {
    clear Hl0_dst.
    entailer.
    apply (@extend_copy_right _ (sSGG_VST Ews) g g1 g2 g3 g4 g1' g2' g3' g4''(ValidPointer b i) l r (vmap g1 (ValidPointer b i)) r0 (null, l0, null)); auto.
  }
  Opaque extended_copy.
  rewrite extract_exists_in_SEP. (* should be able to use tactic directly *)
  Transparent extended_copy.
  clear g4'' H_copy BiMaFin_g3'.
  Intros g4'. rename H3 into H_copy_right, H4 into BiMaFin_g4'.

  forward. (* x0 -> r = r0; *)

  pose proof @va_labeledgraph_add_edge_right _ (sSGG_VST Ews) g g1 g2 g3 g4 g1' g2' g3' g4' x l r x0 r0 as HH.
  Opaque vvalid graph_gen.labeledgraph_add_edge. simpl vertices_at in HH |- *. Transparent vvalid graph_gen.labeledgraph_add_edge. rewrite HH by auto; clear HH.

  pose proof @va_labeledgraph_egen_right _ (sSGG_VST sh) g4 x x0 as HH.
  Opaque Graph_LGraph.
  simpl reachable_vertices_at in HH |- *. rewrite HH; clear HH.
  Transparent Graph_LGraph.

  destruct (labeledgraph_add_edge_ecopy1_right g g1 g2 g3 g4 g1' g2' g3' g4' x l r x0 r0 gx_vvalid H_GAMMA_g H_vopy1 H_copy_left H_ecopy1_left H_copy_right H_x0 H_x0L H_r0 BiMaFin_g4' x0_not_null) as [H_ecopy1_right [BiMaFin_g5' [H_x0R Hr0_dst]]].
  clear BiMaFin_g4'.
  forget (Graph_egen g4 (x: addr, R) (x0: addr, R)) as g5.
  forget (graph_gen.labeledgraph_add_edge g4' (x0, R) x0 r0 (null, L)) as g5'.

  gather_SEP (data_at _ _ _ _) (concrete_valid_pointer _) (vertices_at _ _).
  replace_SEP 0 (EX gg5': Graph', !! (@copy _ _ _ _ CCS x g g5 gg5' /\ x0 = vmap g5 x) && graph Ews x0 gg5').
  {
    entailer.
    eapply (@copy_final pSGG_VST (sSGG_VST Ews) g g1 g2 g3 g4 g5 g1' g2' g3' g4' g5'); [| | | | | | | | eassumption ..]; eauto.
  }

  forward. (* return x0; *)
  rewrite H9.
  apply (exp_right (vlabel g5 (ValidPointer b i), g5, gg5')); entailer!; auto. cancel.
  apply derives_refl.
Time Qed. (* Takes 40 seconds. *)
