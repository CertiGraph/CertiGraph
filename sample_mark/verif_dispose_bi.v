Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_dispose_bi.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_mark_bi.
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
        SEP (`(EX g': Graph, !! spanning_tree g x g' && vertices_at sh g' (reachable g x))).

Definition dispose_spec :=
  DECLARE _dispose
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(!!tree g x && graph sh x g))
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
    apply (valid_not_null g) in H0. exfalso; auto.
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
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro l_old; autorewrite with subst; clear l_old.
  (* end l = x -> l; *)

  (* begin r = x -> r; *)
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro r_old; autorewrite with subst; clear r_old.
  (* end r = x -> r; *)

  (* begin x -> m = 1; *)
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_store_tac
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs CS_legal sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs CS_legal sh node_type
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
    simpl in H4; auto.
  } Unfocus.

  (* if (l) { *)
  apply -> ram_seq_assoc.
  symmetry in H2.
  pose proof Graph_gen_true_mark1 g x _ _ H2 H0.
  assert (H_GAMMA_g1: vgamma (Graph_gen g x true) x = (true, l, r)) by
   (rewrite (proj1 (proj2 (Graph_gen_spatial_spec g x _ true _ _ H2))) by assumption;
    apply spacialgraph_gen_vgamma).
  forget (Graph_gen g x true) as g1.
  unfold semax_ram.
  
  forward_if_tac
    (PROP  ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(EX g2: Graph, !! spanning_tree g1 l g2 && graph sh x g2))); [| gather_current_goal_with_evar ..].

  (* root_mark = l -> m; *)
  localize
    (PROP  ()
     LOCAL  (temp _l (pointer_val_val l))
     SEP  (`(data_at sh node_type (vgamma2cdata (vgamma g1 l)) (pointer_val_val l)))).
  remember (vgamma g1 l) as dlr in |-*.
  destruct dlr as [[dd ll] rr].
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro root_mark_old; autorewrite with subst; clear root_mark_old.
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
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    Opaque trinode.
    Opaque gamma.
    entailer!.
    rewrite (update_self g1 x (true, l, r)) at 2 by auto.
    pose proof (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g1 _ x (true, l, r) (true, l, r)).

    admit.
  } Unfocus.

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
     SEP (`(EX g2: Graph, !! spanning_tree g1 l g2 && graph sh x g2))).
  Transparent node_pred_dec.
  Transparent pSGG_VST.
  destruct (node_pred_dec (marked g1) l). inversion H5.
  localize
    (PROP ()
     LOCAL (temp _l (pointer_val_val l))
     SEP (`(graph sh l g1))).
  assert (vvalid g1 l). {
    apply gamma_left_weak_valid in H2. 2: auto.
    destruct H3.
    rewrite (weak_valid_si _ _ _ H3) in H2.
    destruct H2. 2: auto.
    rewrite is_null_def in H2. subst l.
    simpl in H4. exfalso; auto.
  }
  assert (fst (fst (vgamma g1 l)) = false). {
    simpl in n.
    simpl. destruct (vlabel g1 l) eqn:? .
    + symmetry in Heqb. apply n in Heqb. inversion Heqb.
    + auto.
  }
  eapply semax_ram_seq';
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call' (sh, g1, l); apply derives_refl
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
     SEP (`(EX  g' : Graph, !!spanning_tree g1 l g' && graph sh x g'))
    ).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite !exp_emp.
    (*     graph_ramify_aux1 *)
    (*       RamifyCoq.data_structure.general_spatial_graph.graph_ramify_aux1 *)
    admit.
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
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))
                     (pointer_val_val x)))).
  eapply semax_ram_seq';
    [ repeat apply eexists_add_stats_cons; constructor
    | new_store_tac 
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs CS_legal sh node_type []
           (Vint (Int.repr 1), (Vint (Int.repr 0), pointer_val_val r))) with
         (@data_at CompSpecs CS_legal sh node_type
                   (Vint (Int.repr 1), (Vint (Int.repr 0), pointer_val_val r))).
  unlocalize
    (PROP ()
     LOCAL (temp _r (pointer_val_val r);
            temp _l (pointer_val_val l);
            temp _x (pointer_val_val x))
     SEP (`(graph sh x (Graph_gen_left_null g1 x)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    admit.
  } Unfocus.
  unfold semax_ram. forward.
  entailer.
  apply (exp_right (Graph_gen_left_null g1 x)).
  entailer!.
  admit.
  forward.
  entailer.
  apply (exp_right g2).
  entailer!.
  Focus 2. {
    forward.
    entailer.
    apply (exp_right g1).
    entailer!.
    admit.
  } Unfocus.
Abort.
