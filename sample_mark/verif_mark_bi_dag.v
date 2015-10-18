Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_bi.
Require Import RamifyCoq.data_structure.spatial_graph_mark_bi.
Require Import RamifyCoq.data_structure.spatial_graph_aligned_bi_VST.

Local Open Scope logic.

Notation graph sh x g := (@graph _ _ _ _ _ _ (@SGP pSGG_VST (sSGG_VST sh)) _ x g).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid g x; localDag g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! (mark g x g' /\ localDag g' x) && graph sh x g')).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_hd, tptr (Tstruct _Node noattr))::(_n, (Tstruct _Node noattr))::nil.

Definition Gprog : funspecs := mark_spec :: main_spec::nil.

Ltac revert_exp_left_tac x :=
  match goal with
  | |- ?P |-- _ =>
      let P0 := fresh "P" in
      set (P0 := P);
      pattern x in P0;
      subst P0;
      apply (revert_exists_left x); try clear x
  end.

Lemma body_mark: semax_body Vprog Gprog f_mark mark_spec.
Proof.
  start_function.
  change pointer_val with addr in *.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_Dag.
  rename H1 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.

  forward_if_tac  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (`(graph sh x g))).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return *)
    pose proof mark_invalid_refl g NullPointer.
    spec H0;
    [pose proof valid_not_null g NullPointer; rewrite is_null_def in H1; intro; apply H1; auto; congruence |].
    apply (exp_right g); entailer!.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
  } Unfocus.
  normalize.
  assert (vvalid g x) as gx_vvalid.
  Focus 1. {
    destruct H_weak_valid; [| auto].
    rewrite is_null_def in H0; subst x.
    exfalso.
    apply H. auto.
  } Unfocus.
  destruct_pointer_val x. clear H0 H_weak_valid.
  assert (gl_weak_valid: weak_valid g l) by (eapply gamma_left_weak_valid; eauto).
  assert (gr_weak_valid: weak_valid g r) by (eapply gamma_right_weak_valid; eauto).

  rewrite dag_graph_unfold with (S := l :: r :: nil); [| auto | auto | eapply gamma_step_list; eauto].
  rewrite H_GAMMA_g.
  change (vertex_at x (d, l, r)) with
    (@data_at CompSpecs sh node_type
       (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).
  normalize.
  forward. (* root_mark = x -> m; *)

  eapply semax_pre with 
    (PROP  ()
     LOCAL 
      (temp _root_mark (Vint (Int.repr (if d then 1 else 0)));
      temp _x (pointer_val_val x))
     SEP  (`(graph sh x g))).
  Focus 1. {
    rewrite dag_graph_unfold with (S := l :: r :: nil); [| auto | auto | eapply gamma_step_list; eauto].
    rewrite H_GAMMA_g.
    entailer!.
  } Unfocus.

  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (`(graph sh x g))).
  Focus 1. { (* if-then branch *)
    forward. (* return *)
    apply (exp_right g).
    assert (mark g (ValidPointer b i) g).
    Focus 1. {
      apply mark_marked_root_refl.
      simpl.
      inversion H_GAMMA_g.
      destruct d; [auto | inversion H0].
    } Unfocus.
    entailer!.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    destruct d; congruence.
  } Unfocus.

  normalize.

  rewrite dag_graph_unfold with (S := l :: r :: nil); [| auto | auto | eapply gamma_step_list; eauto].
  rewrite H_GAMMA_g.
  change (vertex_at x (false, l, r)) with
    (@data_at CompSpecs sh node_type
       (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).
  normalize.

  forward. (* l = x -> l; *)
  forward. (* r = x -> r; *)
  forward. (* x -> d = 1; *)

  pose proof Graph_gen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
  assert (H_GAMMA_g1: vgamma (Graph_gen g x true) x = (true, l, r)) by
   (rewrite (proj1 (proj2 (Graph_gen_spatial_spec g x _ true _ _ H_GAMMA_g))) by assumption;
    apply spacialgraph_gen_vgamma).

  apply semax_pre with
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(graph sh x (Graph_gen g x true)))).
  Focus 1. {
    rewrite dag_graph_unfold with (S := l :: r :: nil); [| auto | auto | eapply gamma_step_list; eauto].
    rewrite H_GAMMA_g1.
    change (@field_at CompSpecs sh node_type []
             (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
           (@data_at CompSpecs sh node_type
             (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))).
    rewrite dag_graph_gen_step_list with (x0 := x) (d := (true, l, r));
      [| auto | auto | eapply (gamma_step_list g); eauto].
    pose proof Graph_gen_spatial_spec g x false true l r H_GAMMA_g.
    pose proof @graphs_vi_eq _ _ _ _ _ _ SGP (@SGA _ (sSGG_VST sh)) (Graph_gen g x true) (spatialgraph_vgen g x (true, l, r)) (l :: r :: nil) H2.

    rewrite <- H3.
    forget (Graph_gen g x true) as g1.
    entailer!.
    apply derives_refl.
  } Unfocus.

  assert (H_Dag_g1_x: localDag (Graph_gen g x true) x) by auto.
  forget (Graph_gen g x true) as g1.
  assert (g1x_valid: vvalid g1 x) by (apply (proj1 (proj1 H0)); auto).
  assert (g1l_weak_valid: weak_valid g1 l) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).
  assert (g1r_weak_valid: weak_valid g1 r) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).
  assert (H_Dag_g1_l: localDag g1 l).
  Focus 1. {
    apply local_dag_step with x; auto; [apply maGraph |].
    assert (step_list g1 x (l :: r :: nil)).
    eapply (gamma_step_list g1); eauto.
    rewrite <- (H2 l).
    simpl; tauto.
  } Unfocus.

  localize
   (PROP  ()
    LOCAL (temp _l (pointer_val_val l))
    SEP   (`(graph sh l g1))).
  (* localize *)
  
  rewrite <- ram_seq_assoc.
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call (sh, g1, l); apply derives_refl
  | abbreviate_semax_ram].

  apply semax_ram_pre with
   (PROP  ()
    LOCAL  (tc_environ Delta; temp _l (pointer_val_val l))
    SEP 
    (`(EX  g' : Graph, !!(mark g1 l g') && graph sh l g'))).
  entailer!.
  apply exp_left; intro g'; apply (exp_right g'); entailer!.

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`((EX g2: Graph, !! mark g1 l g2 && graph sh x g2)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer.
    rewrite !exp_emp.
    eapply (@graph_ramify_aux1_left _ (sSGG_VST sh) g1); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  normalize; intros g2; normalize.
  assert (H_GAMMA_g2: vgamma g2 x = (true, l, r)).
  Focus 1. {
    
    eapply gamma_true_mark; eauto.
    apply weak_valid_vvalid_dec; auto.
    destruct H2 as [[? _] _]. rewrite <- H2; auto.
  } Unfocus.
  assert (g2x_valid: vvalid g2 x) by (apply (proj1 (proj1 H2)); auto).
  assert (g2r_weak_valid: weak_valid g2 r) by (apply (weak_valid_si g1 g2 _ (proj1 H2)); auto).

  assert (H_Dag_g2_x: localDag g2 x) by (destruct H2 as [? _]; rewrite <- H2; auto).
  assert (H_Dag_g2_r: localDag g2 r).
  Focus 1. {
    apply local_dag_step with x; auto; [apply maGraph |].
    assert (step_list g2 x (l :: r :: nil)).
    eapply (gamma_step_list g2); eauto.
    rewrite <- (H3 r).
    simpl; tauto.
  } Unfocus.

  localize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r))
    SEP   (`(graph sh r g2))).
  (* localize *)
  
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call (sh, g2, r); apply derives_refl
  | abbreviate_semax_ram].
  (* mark(r); *)

  apply semax_ram_pre with
   (PROP  ()
    LOCAL  (tc_environ Delta; temp _r (pointer_val_val r))
    SEP 
    (`(EX  g' : Graph, !!mark g2 r g' && graph sh r g'))).
  entailer!.
  apply exp_left; intro g'; apply (exp_right g'); entailer!.

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(EX g3: Graph, !!mark g2 r g3 && graph sh x g3))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    eapply (@graph_ramify_aux1_right _ (sSGG_VST sh)  g2); eauto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  forward. (* ( return; ) *)
  apply (exp_right g3); entailer!. split.
  + apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
  + destruct H1 as [? _].
    rewrite <- H1.
    auto.
Time Qed. (* Takes 4557 minuts. *)
