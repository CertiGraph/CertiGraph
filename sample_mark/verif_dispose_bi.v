Require Import VST.floyd.proofauto.
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

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Coercion SGraph_PGraph: SGraph >-> PGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Identity Coercion PGraph_PreGraph: PGraph >-> PreGraph.

Notation vertices_at sh g P := (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ g P).
Notation graph sh x g := (@graph _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST bool unit).
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
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mark_spec :: spanning_spec :: dispose_spec :: main_spec::nil.

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
    rewrite is_null_def. auto.
  }
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
                     (pointer_val_val x))).
  
  (* begin l = x -> l; *)
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  (* end l = x -> l; *)

  (* begin r = x -> r; *)
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  (* end r = x -> r; *)

  (* begin x -> m = 1; *)
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs sh node_type
                   (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))).
  (* end x -> m = 1; *)
  
  unlocalize (PROP ()
              LOCAL  (temp _r (pointer_val_val r); temp _l (pointer_val_val l); temp _x (pointer_val_val x))
              SEP  (graph sh x (Graph_gen g x true))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    rewrite Graph_gen_spatial_spec by eauto.
    pose proof (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ x (false, l, r) (true, l, r)).
    simpl in H2; auto.
  } Unfocus.

  (* if (l) { *)
  apply -> ram_seq_assoc.
  symmetry in H1.
  pose proof Graph_gen_true_mark1 g x _ _ H1 H.
  assert (H_GAMMA_g1: vgamma (Graph_gen g x true) x = (true, l, r)) by
   (rewrite (proj1 (proj2 (Graph_gen_spatial_spec g x _ true _ _ H1))) by assumption;
    apply spacialgraph_gen_vgamma).
  assert (vvalid (Graph_gen g x true) x) by (destruct H2 as [[? _] _]; apply H2; auto).
  forget (Graph_gen g x true) as g1.
  unfold semax_ram.
  
  forward_if_tac
    (EX g2: Graph,
     PROP  (edge_spanning_tree g1 (x, L) g2)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g2)); [admit | | gather_current_goal_with_evar ..].

  (* root_mark = l -> m; *)
  localize
    (PROP  ()
     LOCAL (temp _l (pointer_val_val l))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g1 l)) (pointer_val_val l))).
  remember (vgamma g1 l) as dlr in |-*.
  destruct dlr as [[dd ll] rr].
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  replace (if dd then 1 else 0) with (if node_pred_dec (marked g1) l then 1 else 0).
  Focus 2. {
    destruct (node_pred_dec (marked g1)); destruct dd; auto; symmetry in Heqdlr.
    apply vgamma_is_false in Heqdlr. simpl in a. unfold unmarked in Heqdlr. hnf in Heqdlr.
    unfold Ensembles.In in Heqdlr. simpl in Heqdlr. apply Heqdlr in a. exfalso; auto.
    apply vgamma_is_true in Heqdlr. exfalso; auto.
  } Unfocus.
  rewrite Heqdlr. simpl temp at 1.
  assert ((Vint (Int.repr (if (@vlabel pointer_val (prod pointer_val LR) PointerVal_EqDec
           PointerValLR_EqDec bool unit (@Graph_LGraph pSGG_VST bool unit g1)
           l) then 1 else 0))) =
          (Vint (Int.repr (if node_pred_dec (marked g1) l then 1 else 0)))). {
    simpl. f_equal. f_equal.
    change (vlabel (lg_gg g1) l) with (vlabel g1 l).
    simpl.
    destruct (@vlabel pointer_val (prod pointer_val LR) PointerVal_EqDec
           PointerValLR_EqDec bool unit (@Graph_LGraph pSGG_VST bool unit g1)
           l); auto.
  }
  rewrite H5. clear H5.
  unlocalize
    (PROP  ()
     LOCAL (temp _root_mark (Vint (Int.repr (if node_pred_dec (marked g1) l then 1 else 0)));
            temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP  (graph sh x g1)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    destruct (vgamma g1 l) as [[dd ll] rr] eqn:? .
    entailer!.
    rewrite (update_self g1 l (dd, ll, rr)) at 2 by auto.
    assert (vvalid g1 l). {
      assert (weak_valid g1 l) by (eapply gamma_left_weak_valid; eauto).
      destruct H5; auto. rewrite is_null_def in H5. subst. exfalso; intuition.
    }
    apply (@vertices_at_ramify1 _ _ _ _ _ _ _ (SGA_VST sh) g1 (reachable g1 x) l (dd, ll, rr) (dd, ll, rr)); auto.
    apply (gamma_left_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 l).
    apply reachable_by_refl; auto.
  } Unfocus.

  (* if (root_mark == 0) { *)

  unfold semax_ram.
  apply semax_seq_skip.
  Opaque node_pred_dec.
  Opaque pSGG_VST.
  (* remember (if node_pred_dec (marked g1) l then 1 else 0). *)
  forward_if_tac
    (EX g2: Graph,
     PROP  (edge_spanning_tree g1 (x, L) g2)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g2)).

  (* spanning(l); *)

  Transparent node_pred_dec.
  Transparent pSGG_VST.
  destruct (node_pred_dec (marked g1) l). inversion H5.
  localize
    (PROP ()
     LOCAL (temp _l (pointer_val_val l))
     SEP (graph sh l g1)).
  assert (vvalid g1 l). {
    apply gamma_left_weak_valid in H1. 2: auto.
    destruct H2.
    rewrite (weak_valid_si _ _ _ H2) in H1.
    destruct H1. 2: auto.
    rewrite is_null_def in H1. subst l.
    simpl in H3. exfalso; auto.
  }
  assert (fst (fst (vgamma g1 l)) = false). {
    simpl in n.
    simpl. destruct (vlabel g1 l) eqn:? .
    + symmetry in Heqb. apply n in Heqb. inversion Heqb.
    + auto.
  }
  eapply semax_ram_seq';
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g1, l)
  | semax_ram_after_call; intros g';
    repeat (apply ram_extract_PROP; intro) ].
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  unlocalize
    (PROP (edge_spanning_tree g1 (x, L) g')
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g'))
    using [H8]%RamAssu
    binding [g']%RamBind.
  Grab Existential Variables.
  Focus 2. {
    assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; inversion H_GAMMA_g1; auto).
    unfold edge_spanning_tree.
    if_tac; subst l; [exfalso |]; auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward. entailer.
    apply (exp_right g').
    entailer.
  } Unfocus.
  Focus 1. {
    simplify_ramif.
    apply (@graph_ramify_aux1_left _ (sSGG_VST sh) _ g1 x true l r); auto.
  } Unfocus.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  destruct (node_pred_dec (marked g1) l). 2: exfalso; auto.

  (* x -> l = 0; *)

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))
                   (pointer_val_val x))).
  eapply semax_ram_seq';
    [ repeat apply eexists_add_stats_cons; constructor
    | store_tac 
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs sh node_type []
           (Vint (Int.repr 1), (Vint (Int.repr 0), pointer_val_val r))) with
         (@data_at CompSpecs sh node_type
                   (Vint (Int.repr 1), (Vint (Int.repr 0), pointer_val_val r))).
  unlocalize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) (Graph_gen_left_null g1 x))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@graph_gen_left_null_ramify _ (sSGG_VST sh) g1 x true l r); auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward.
    entailer.
    apply (exp_right (Graph_gen_left_null g1 x)).
    entailer!.
    apply (edge_spanning_tree_left_null g1 x true l r); auto.
    apply derives_refl.
  } Unfocus.
  Focus 1. {
    forward.
    Intro x0.
    apply (exp_right x0).
    entailer!.
  } Unfocus.
  Focus 2. {
    forward.
    entailer.
    apply (exp_right g1).
    entailer!; auto.
    apply edge_spanning_tree_invalid.
    + apply (@left_valid _ _ _ _ g1 _ _ (biGraph g1)) in H3; auto.
    + intro. apply (valid_not_null g1 l).
      - assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; inversion H_GAMMA_g1; auto).
        rewrite H9. apply H8.
      - rewrite is_null_def. apply (destruct_pointer_val_NP). left; auto.
  } Unfocus.

  (* if (r) { *)

  Intro g2.
  normalize.

  assert (vvalid g2 x) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r x); auto).
  destruct (edge_spanning_tree_left_vgamma g1 g2 x l r H3 H_GAMMA_g1 H4) as [l' H_GAMMA_g2].

  forward_if_tac
    (EX g3: Graph,
     PROP  (edge_spanning_tree g2 (x, R) g3)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g3)); [admit | | gather_current_goal_with_evar ..].

  (* root_mark = r -> m; *)

  localize
    (PROP  ()
     LOCAL  (temp _r (pointer_val_val r))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g2 r)) (pointer_val_val r))).
  remember (vgamma g2 r) as dlr in |-*.
  destruct dlr as [[dd ll] rr].
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  replace (if dd then 1 else 0) with (if node_pred_dec (marked g2) r then 1 else 0).
  Focus 2. {
    destruct (node_pred_dec (marked g2)); destruct dd; auto; symmetry in Heqdlr.
    apply vgamma_is_false in Heqdlr. simpl in a. unfold unmarked in Heqdlr. hnf in Heqdlr.
    unfold Ensembles.In in Heqdlr. simpl in Heqdlr. apply Heqdlr in a. exfalso; auto.
    apply vgamma_is_true in Heqdlr. exfalso; auto.
  } Unfocus.
  rewrite Heqdlr. simpl temp at 1.
  assert ((Vint (Int.repr (if (@vlabel pointer_val (prod pointer_val LR) PointerVal_EqDec
           PointerValLR_EqDec bool unit (@Graph_LGraph pSGG_VST bool unit g2)
           r) then 1 else 0)))
          = (Vint (Int.repr (if node_pred_dec (marked g2) r then 1 else 0)))). {
    simpl. do 2 f_equal.
    destruct (@vlabel pointer_val (prod pointer_val LR) PointerVal_EqDec
           PointerValLR_EqDec bool unit (@Graph_LGraph pSGG_VST bool unit g2)
           r); auto.
  } rewrite H7. clear H7.
  unlocalize
    (PROP  ()
     LOCAL (temp _root_mark (Vint (Int.repr (if node_pred_dec (marked g2) r then 1 else 0)));
            temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP  (vertices_at sh (reachable g1 x) g2)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    destruct (vgamma g2 r) as [[dd ll] rr] eqn:? .
    pose proof (update_self g2 r (dd, ll, rr) Heqp).
    
    assert (vertices_at sh (reachable g1 x) g2 = vertices_at sh (reachable g1 x) (spatialgraph_vgen g2 r (dd, ll, rr))). {
      apply vertices_at_vi_eq; auto.
      apply (edge_spanning_tree_left_reachable_vvalid g1 g2 x true l r); auto.
    }
    simpl in H8. rewrite H8 at 2.
    assert (vvalid g1 r). {
      assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
      destruct H9; auto. rewrite is_null_def in H9. subst. exfalso; intuition.
    }
    apply (@vertices_at_ramify1 _ _ _ _ _ _ _ (SGA_VST sh) g2 (reachable g1 x) r (dd, ll, rr) (dd, ll, rr)); auto.
    rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r r); auto.
    apply (gamma_right_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 r).
    apply reachable_by_refl; auto.
  } Unfocus.

  (* if (root_mark == 0) { *)

  unfold semax_ram.
  apply semax_seq_skip.
  Opaque node_pred_dec.
  Opaque pSGG_VST.

  forward_if_tac
    (EX g3: Graph,
     PROP  (edge_spanning_tree g2 (x, R) g3)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g3)).

  (* spanning(r); *)

  Transparent node_pred_dec.
  Transparent pSGG_VST.
  destruct (node_pred_dec (marked g2) r). inversion H7.
  localize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r))
     SEP (graph sh r g2)).
  assert (vvalid g1 r). {
      assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
      destruct H8; auto. rewrite is_null_def in H8. subst. exfalso; intuition.
  }
  assert (vvalid g2 r) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r r); auto).
  assert (fst (fst (vgamma g2 r)) = false). {
    simpl in n |-* . destruct (vlabel g2 r) eqn:? .
    + symmetry in Heqb. apply n in Heqb. exfalso; auto.
    + auto.
  }
  eapply semax_ram_seq';
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g2, r)
  | semax_ram_after_call; intros g3;
    repeat (apply ram_extract_PROP; intro) ].
  
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  unlocalize
    (PROP (edge_spanning_tree g2 (x, R) g3)
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) g3))
    using [H11]%RamAssu
    binding [g3]%RamBind.
  Grab Existential Variables.
  Focus 2. {
    assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; inversion H_GAMMA_g2; auto).
    unfold edge_spanning_tree.
    if_tac; subst r; [exfalso |]; auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram.
    forward.
    entailer.
    apply (exp_right g3).
    entailer.
  } Unfocus.
  Focus 1. {
    simplify_ramif.
    apply (@graph_ramify_aux1_right _ (sSGG_VST sh) _ g1 g2 x l r); auto.
  } Unfocus.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  destruct (node_pred_dec (marked g2) r). 2: exfalso; auto.

  (* x -> r = 0; *)
  
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l', pointer_val_val r))
                     (pointer_val_val x))).
  eapply semax_ram_seq';
    [ repeat apply eexists_add_stats_cons; constructor
    | store_tac 
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l', Vint (Int.repr 0)))) with
         (@data_at CompSpecs sh node_type
                   (Vint (Int.repr 1), (pointer_val_val l', Vint (Int.repr 0)))).
  unlocalize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (vertices_at sh (reachable g1 x) (Graph_gen_right_null g2 x))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@graph_gen_right_null_ramify _ (sSGG_VST sh) g1 g2 x true l' r); auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward.
    entailer.
    apply (exp_right (Graph_gen_right_null g2 x)).
    entailer!.
    apply (edge_spanning_tree_right_null g2 x true l' r); auto.
    apply derives_refl.
  } Unfocus.
  Focus 1. {
    forward.
    Intro x0.
    apply (exp_right x0).
    entailer!.
  } Unfocus.
  Focus 2. {
    forward.
    entailer.
    apply (exp_right g2).
    entailer!.
    apply edge_spanning_tree_invalid.
    + apply (@right_valid _ _ _ _ g2 _ _ (biGraph g2)) in H5; auto.
    + intro. apply (valid_not_null g2 r).
      - assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; inversion H_GAMMA_g2; auto).
        rewrite H11. apply H10.
      - rewrite is_null_def. apply (destruct_pointer_val_NP). left; auto.
  } Unfocus.

  (* return *)
  Intro g3.
  normalize.
  forward.
  apply (exp_right g3).
  entailer!.
  Focus 2. {
    destruct H2.
    rewrite (vertices_at_P_Q_eq g3 (reachable g1 x) (reachable g x)).
    + apply derives_refl.
    + intro v. unfold Ensembles.In; intros.
      rewrite <- (edge_spanning_tree_right_vvalid g2 g3 x true l' r v); auto.
      apply (edge_spanning_tree_left_reachable_vvalid g1 g2 x true l r H3 H_GAMMA_g1 H4 v); auto.
    + unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In . (* 1 min 22 sec *)
      split; intro v; rewrite H2; tauto. (* 1 min 20 sec *)
  } Unfocus.
  apply (edge_spanning_tree_spanning_tree g g1 g2 g3 x l r); auto. (* 1 min 27 sec *)
Time Qed. (* 9305 sec *)
