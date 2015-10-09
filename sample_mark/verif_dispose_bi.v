Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_dispose_bi.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.WeakMarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_mark_bi.
Require Import RamifyCoq.data_structure.spatial_graph_dispose_bi.
Require Import RamifyCoq.data_structure.spatial_graph_bi.
Require Import RamifyCoq.data_structure.spatial_graph_unaligned_bi_VST.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Notation vertices_at sh g P := (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST (sSGG_VST sh)) _ g P).
Notation graph sh x g := (@graph _ _ _ _ _ _ (@SGP pSGG_VST (sSGG_VST sh)) _ x g).
Existing Instances MGS biGraph maGraph finGraph RGF.
  
Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! mark g x g' && graph sh x g')).

Definition spanning_spec :=
  DECLARE _spanning
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; vvalid (pg_gg g) x; fst (fst (vgamma g x)) = false)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! spanning_tree g x g' && vertices_at sh (reachable g x) g')).

Definition dispose_spec :=
  DECLARE _dispose
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(!!is_tree g x && graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`emp).

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
    SEP   (`(data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
                     (pointer_val_val x)))).
  
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
              SEP  (`(graph sh x (Graph_gen g x true)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite Graph_gen_spatial_spec by eauto.
    pose proof (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ x (false, l, r) (true, l, r)).
    simpl in H3; auto.
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
    (PROP  ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX g2: Graph, !! edge_spanning_tree g1 (x, L) g2 && vertices_at sh (reachable g1 x) g2))); [admit | | gather_current_goal_with_evar ..].

  (* root_mark = l -> m; *)
  localize
    (PROP  ()
     LOCAL  (temp _l (pointer_val_val l))
     SEP  (`(data_at sh node_type (vgamma2cdata (vgamma g1 l)) (pointer_val_val l)))).
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
  rewrite Heqdlr.
  unlocalize
    (PROP  ()
     LOCAL (temp _root_mark (Vint (Int.repr (if node_pred_dec (marked g1) l then 1 else 0)));
            temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP  (`(graph sh x g1))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite <- H5.
    do 2 f_equal.
    destruct (@vlabel pointer_val (pointer_val * LR) PointerVal_EqDec
         PointerValLR_EqDec bool unit
         (fun
            (g0 : @PreGraph pointer_val (pointer_val * LR) PointerVal_EqDec
                    PointerValLR_EqDec) (_ : pointer_val -> bool)
            (_ : pointer_val * LR -> unit) => @BiMaFin pSGG_VST g0) g1 l); auto.
  } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    (* Opaque trinode. *)
    Opaque gamma.
    destruct (vgamma g1 l) as [[dd ll] rr] eqn:? .
    entailer!.
    rewrite (update_self g1 l (dd, ll, rr)) at 2 by auto.
    assert (vvalid g1 l). {
      assert (weak_valid g1 l) by (eapply gamma_left_weak_valid; eauto).
      destruct H8; auto. rewrite is_null_def in H8. subst. exfalso; intuition.
    }
    apply (@vertices_at_ramify _ _ _ _ _ _ _ (SGA_VST sh) g1 (reachable g1 x) l (dd, ll, rr) (dd, ll, rr)); auto.
    apply (gamma_left_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 l).
    apply reachable_by_reflexive; auto.
    Transparent gamma.
  } Unfocus.

  (* if (root_mark == 0) { *)

  unfold semax_ram.
  apply semax_seq_skip.
  Opaque node_pred_dec.
  Opaque pSGG_VST.
  (* remember (if node_pred_dec (marked g1) l then 1 else 0). *)
  forward_if_tac
    (PROP  ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX g2: Graph, !! edge_spanning_tree g1 (x, L) g2 && vertices_at sh (reachable g1 x) g2))).

  (* spanning(l); *)

  Transparent node_pred_dec.
  Transparent pSGG_VST.
  destruct (node_pred_dec (marked g1) l). inversion H5.
  localize
    (PROP ()
     LOCAL (temp _l (pointer_val_val l))
     SEP (`(graph sh l g1))).
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
  | forward_call (sh, g1, l); apply derives_refl
  | abbreviate_semax_ram].
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  unlocalize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX  g' : Graph, !!edge_spanning_tree g1 (x, L) g' && vertices_at sh (reachable g1 x) g'))
    ).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; unfold gamma in H_GAMMA_g1; inversion H_GAMMA_g1; auto).
    assert (forall (gg : Graph), spanning_tree g1 l gg -> edge_spanning_tree g1 (x, L) gg). {
      intros; unfold edge_spanning_tree.
      destruct (node_pred_dec (marked g1) (dst g1 (x, L))); subst l; [exfalso |]; auto.
    }
    apply (@graph_ramify_aux1_left _ (sSGG_VST sh) g1 x true l r); auto.
  } Unfocus.
  unfold semax_ram.
  forward.
  entailer.
  apply (exp_right g').
  entailer.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  destruct (node_pred_dec (marked g1) l). 2: exfalso; auto.

  (* x -> l = 0; *)

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))
                     (pointer_val_val x)))).
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
     SEP (`(vertices_at sh (reachable g1 x) (Graph_gen_left_null g1 x)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    apply (@graph_gen_left_null_ramify _ (sSGG_VST sh) g1 x true l r); auto.
  } Unfocus.
  unfold semax_ram. forward.
  entailer.
  apply (exp_right (Graph_gen_left_null g1 x)).
  entailer!.
  apply (edge_spanning_tree_left_null g1 x true l r); auto.
  forward.
  entailer.
  apply (exp_right g2).
  entailer!.
  Focus 2. {
    forward.
    entailer.
    apply (exp_right g1).
    entailer!.
    apply edge_spanning_tree_invalid.
    intro. apply (valid_not_null g1 l).
    + assert (l = dst g1 (x, L)) by (simpl in H_GAMMA_g1; unfold gamma in H_GAMMA_g1; inversion H_GAMMA_g1; auto).
      rewrite H6. apply H5.
    + rewrite is_null_def. apply (destruct_pointer_val_NP). left; auto.
  } Unfocus.

  (* if (r) { *)

  normalize.
  intro g2.
  normalize.

  assert (vvalid g2 x) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r x); auto).
  destruct (edge_spanning_tree_left_vgamma g1 g2 x l r H3 H_GAMMA_g1 H4) as [l' H_GAMMA_g2].

  forward_if_tac
    (PROP  ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX g3: Graph, !! edge_spanning_tree g2 (x, R) g3 && vertices_at sh (reachable g1 x) g3))); [admit | | gather_current_goal_with_evar ..].

  (* root_mark = r -> m; *)

  localize
    (PROP  ()
     LOCAL  (temp _r (pointer_val_val r))
     SEP  (`(data_at sh node_type (vgamma2cdata (vgamma g2 r)) (pointer_val_val r)))).
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
  rewrite Heqdlr.

  unlocalize
    (PROP  ()
     LOCAL (temp _root_mark (Vint (Int.repr (if node_pred_dec (marked g2) r then 1 else 0)));
            temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP  (`(vertices_at sh (reachable g1 x) g2))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite <- H7.
    do 2 f_equal.
    destruct (@vlabel pointer_val (pointer_val * LR) PointerVal_EqDec
         PointerValLR_EqDec bool unit
         (fun
            (g0 : @PreGraph pointer_val (pointer_val * LR) PointerVal_EqDec
                    PointerValLR_EqDec) (_ : pointer_val -> bool)
            (_ : pointer_val * LR -> unit) => @BiMaFin pSGG_VST g0) g2 r); auto.
  } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    Opaque gamma.
    destruct (vgamma g2 r) as [[dd ll] rr] eqn:? .
    entailer!.
    pose proof (update_self g2 r (dd, ll, rr) Heqp).
    
    assert (vertices_at sh (reachable g1 x) g2 = vertices_at sh (reachable g1 x) (spatialgraph_vgen g2 r (dd, ll, rr))). {
      apply vertices_at_vi_eq; auto.
      apply (edge_spanning_tree_left_reachable_vvalid g1 g2 x true l r); auto.
    }
    simpl in H11. rewrite H11 at 2.
    assert (vvalid g1 r). {
      assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
      destruct H12; auto. rewrite is_null_def in H12. subst. exfalso; intuition.
    }
    apply (@vertices_at_ramify _ _ _ _ _ _ _ (SGA_VST sh) g2 (reachable g1 x) r (dd, ll, rr) (dd, ll, rr)); auto.
    rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r r); auto.
    apply (gamma_right_reachable_included g1 _ _ _ _ H3 H_GAMMA_g1 r).
    apply reachable_by_reflexive; auto.
    Transparent gamma.
  } Unfocus.

  (* if (root_mark == 0) { *)

  unfold semax_ram.
  apply semax_seq_skip.
  Opaque node_pred_dec.
  Opaque pSGG_VST.

  forward_if_tac
    (PROP  ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX g3: Graph, !! edge_spanning_tree g2 (x, R) g3 && vertices_at sh (reachable g1 x) g3))).

  (* spanning(r); *)

  Transparent node_pred_dec.
  Transparent pSGG_VST.
  destruct (node_pred_dec (marked g2) r). inversion H7.
  localize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r))
     SEP (`(graph sh r g2))).
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
  | forward_call (sh, g2, r); apply derives_refl
  | abbreviate_semax_ram].
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  unlocalize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX  g3 : Graph, !!edge_spanning_tree g2 (x, R) g3 && vertices_at sh (reachable g1 x) g3))
    ).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; unfold gamma in H_GAMMA_g2; inversion H_GAMMA_g2; auto).
    assert (forall (gg: Graph), spanning_tree g2 r gg -> edge_spanning_tree g2 (x, R) gg). {
      intros; unfold edge_spanning_tree.
      destruct (node_pred_dec (marked g2) (dst g2 (x, R))); subst r; [exfalso |]; auto.
    }
    assert (vvalid g1 r). {
      assert (weak_valid g1 r) by (eapply gamma_right_weak_valid; eauto).
      destruct H14; auto. rewrite is_null_def in H14. rewrite H14 in H6. exfalso; intuition.
    }
    assert (vvalid g2 r) by (rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r r); auto).
    apply (@graph_ramify_aux1_right _ (sSGG_VST sh) g1 g2 x l r); auto.
  } Unfocus.
  unfold semax_ram.
  forward.
  entailer.
  apply (exp_right g3).
  entailer.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  gather_current_goal_with_evar.
  destruct (node_pred_dec (marked g2) r). 2: exfalso; auto.

  (* x -> r = 0; *)
  
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l', pointer_val_val r))
                     (pointer_val_val x)))).
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
     SEP (`(vertices_at sh (reachable g1 x) (Graph_gen_right_null g2 x)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    apply (@graph_gen_right_null_ramify _ (sSGG_VST sh) g1 g2 x true l' r); auto.
  } Unfocus.
  unfold semax_ram. forward.
  entailer.
  apply (exp_right (Graph_gen_right_null g2 x)).
  entailer!.
  apply (edge_spanning_tree_right_null g2 x true l' r); auto.
  forward.
  entailer.
  apply (exp_right g3).
  entailer!.
  Focus 2. {
    forward.
    entailer.
    apply (exp_right g2).
    entailer!.
    apply edge_spanning_tree_invalid.
    intro. apply (valid_not_null g2 r).
    + assert (r = dst g2 (x, R)) by (simpl in H_GAMMA_g2; unfold gamma in H_GAMMA_g2; inversion H_GAMMA_g2; auto).
      rewrite H8. apply H7.
    + rewrite is_null_def. apply (destruct_pointer_val_NP). left; auto.
  } Unfocus.

  (* return *)

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
    + intro v. rewrite H2. tauto.
  } Unfocus.
  
Abort.
