Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_unionfind.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.GList.
Require Import RamifyCoq.msl_application.GList_UnionFind.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_graph_glist.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Local Coercion UGraph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation vertices_at sh P g:= (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ P g).
Notation whole_graph sh g := (vertices_at sh (vvalid g) g).
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST).
Notation uf_under_bound g := (uf_under_bound id g).
Existing Instances maGraph finGraph liGraph RGF.

Definition vlabel_in_bound (g: Graph) := forall x, vvalid g x -> Z.of_nat (vlabel g x) <= Int.max_signed.

Lemma rank_unchanged_in_bound: forall (g g': Graph), uf_equiv g g' -> rank_unchanged g g' -> vlabel_in_bound g -> vlabel_in_bound g'.
Proof. unfold uf_equiv, rank_unchanged, vlabel_in_bound. intros. destruct H as [? _]. pose proof H2. rewrite <- H in H2. rewrite <- H0; auto. Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh: wshare, n:Z
  PRE [ 67%positive OF tint]
     PROP (0 <= n <= Int.max_signed)
     LOCAL (temp 67%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: addr,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (data_at sh node_type (pointer_val_val null, (Vint (Int.repr 0)))
              (pointer_val_val v)).

Definition find_spec :=
 DECLARE _find
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x /\ uf_under_bound g)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (whole_graph sh g)
  POST [ tptr (Tstruct _Node noattr) ]
        EX g': Graph, EX rt : pointer_val,
        PROP (uf_equiv g g' /\ uf_root g' x rt /\ uf_under_bound g' /\ rank_unchanged g g')
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (whole_graph sh g').

Definition unionS_spec :=
 DECLARE _unionS
  WITH sh: wshare, g: Graph, x: pointer_val, y: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr)), _y OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x /\ vvalid g y /\ uf_under_bound g /\ vlabel_in_bound g)
          LOCAL (temp _x (pointer_val_val x); temp _y (pointer_val_val y))
          SEP   (whole_graph sh g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g' /\ uf_under_bound g')
        LOCAL()
        SEP (whole_graph sh g').

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH sh: wshare, g: Graph
    PRE []
      PROP (uf_under_bound g)
      LOCAL ()
      SEP (whole_graph sh g)
    POST [tptr (Tstruct _Node noattr)]
      EX g': Graph, EX rt: pointer_val,
      PROP (~ vvalid g rt /\ vvalid g' rt /\ is_partial_graph g g' /\ uf_under_bound g')
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (whole_graph sh g').

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mallocN_spec :: makeSet_spec :: find_spec :: unionS_spec ::nil.

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function.
  forward_call (sh, 8).
  - compute. split; intros; inversion H0.
  - Intros x.
    assert_PROP (x <> null) as x_not_null by (entailer !; destruct H1 as [? _]; apply H1).
    assert_PROP (~ vvalid g x) by (entailer; apply (@vertices_at_sepcon_unique_1x _ _ _ _ SGBA_VST _ _ (SGA_VST sh) (SGAvs_VST sh) g x (vvalid g) (O, null))).
    forward. forward. forward.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr 0), pointer_val_val x)) with (@data_at CompSpecs sh node_type (Vint (Int.repr 0), pointer_val_val x)).
    apply (exp_right (make_set_Graph O tt tt x g x_not_null H0)). entailer. apply (exp_right x). entailer !.
    + split; [|split]; simpl; [right | apply is_partial_make_set_pregraph | apply uf_under_bound_make_set_graph]; auto.
    + assert (Coqlib.Prop_join (vvalid g) (eq x) (vvalid (make_set_Graph 0%nat tt tt x g x_not_null H0))). {
        simpl; hnf; split; intros; [unfold graph_gen.addValidFunc | subst a]; intuition.
      } assert (vgamma (make_set_Graph O tt tt x g x_not_null H0) x = (O, x)). {
        unfold vgamma, UnionFindGraph.vgamma. simpl. f_equal.
        - destruct (SGBA_VE x x); [| hnf in c; unfold Equivalence.equiv in c; exfalso]; auto.
        - unfold graph_gen.updateEdgeFunc. destruct (EquivDec.equiv_dec (x, tt) (x, tt)). 2: compute in c; exfalso; auto. destruct (SGBA_VE null null); auto.
          hnf in c. unfold Equivalence.equiv in c. exfalso; auto.
      } rewrite <- (vertices_at_sepcon_1x (make_set_Graph 0%nat tt tt x g x_not_null H0) x (vvalid g) _ (O, x)); auto. apply sepcon_derives. 1: entailer !.
      assert (vertices_at sh (vvalid g) g = vertices_at sh (vvalid g) (make_set_Graph O tt tt x g x_not_null H0)). {
        apply vertices_at_vertices_identical. simpl. hnf. intros. destruct a as [y ?]. unfold Morphisms_ext.app_sig. simpl.
        unfold UnionFindGraph.vgamma. simpl. unfold graph_gen.updateEdgeFunc. f_equal.
        - destruct (SGBA_VE y x); [hnf in e; subst y; exfalso |]; auto.
        - destruct (EquivDec.equiv_dec (x, tt) (y, tt)); auto. hnf in e. inversion e. subst y. exfalso; auto.
      } rewrite <- H6. entailer.
Qed.

Lemma false_Cne_eq: forall x y, typed_false tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + symmetry in Heqb1. apply binop_lemmas2.int_eq_true in Heqb1. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma true_Cne_neq: forall x y, typed_true tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + simpl in H. inversion H.
    + subst b0. apply int_eq_false_e in Heqb1. intro. inversion H0. auto.
  - intro. inversion H0. auto.
Qed.

Lemma ADMIT: forall P: Prop, P.
Admitted.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function.
  destruct H. remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa].
  (* p = x -> parent; *)
  localize
    (PROP  ()
     LOCAL (temp _x (pointer_val_val x))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x))).
  rewrite <- H1. simpl vgamma2cdata.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _p (pointer_val_val pa); temp _x (pointer_val_val x))
     SEP  (whole_graph sh g)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite <- H1. simpl.
    apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  } Unfocus.
  unfold semax_ram.
  (* if (p != x) { *)
  forward_if_tac
    (EX g': Graph, EX rt : pointer_val,
     PROP (uf_equiv g g' /\ uf_root g' x rt /\ uf_under_bound g' /\ rank_unchanged g g')
     LOCAL (temp _p (pointer_val_val rt); temp _x (pointer_val_val x))
     SEP (whole_graph sh g'));
    [apply ADMIT | | gather_current_goal_with_evar ..].
  (* p0 = find(p); *)
  forward_call (sh, g, pa). 1: symmetry in H1; apply valid_parent in H1; auto.
  Intros vret. destruct vret as [g' root]. simpl fst in *. simpl snd in *. forward. symmetry in H1.
  pose proof (true_Cne_neq _ _ H2).
  assert (weak_valid g' root) by (right; destruct H4; apply reachable_foot_valid in H4; auto).
  assert (vvalid g' x) by (destruct H3 as [? _]; rewrite <- H3; apply H).
  assert (~ reachable g' root x) by (apply (uf_equiv_not_reachable g g' x r pa root); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g' x root H8 H9 H10)) (Graph_gen_redirect_parent g' x root H8 H9 H10) =
          vertices_at sh (vvalid g') (Graph_gen_redirect_parent g' x root H8 H9 H10)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
  remember (vgamma g' x) as rpa eqn:?H. destruct rpa as [r' pa']. symmetry in H12.
  localize
   (PROP  ()
    LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr (Z.of_nat r')), pointer_val_val pa')
                   (pointer_val_val x))).
    eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
    assert (force_val (sem_cast_neutral (pointer_val_val root)) = pointer_val_val root) by (destruct root; simpl; auto). rewrite H13. clear H13.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat r')), pointer_val_val root) (pointer_val_val x)) with
        (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat r')), pointer_val_val root) (pointer_val_val x)).
  unlocalize
   (PROP ()
    LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
    SEP (whole_graph sh (Graph_gen_redirect_parent g' x root H8 H9 H10))).
  Grab Existential Variables.
  Focus 3. { Intros g' rt. forward. apply (exp_right g'). entailer !. apply (exp_right rt). entailer !. } Unfocus.
  Focus 3. {
    forward. apply (exp_right g). apply (exp_right x). entailer ! . apply false_Cne_eq in H2. subst pa. split; [|split; [split |]]; auto.
    - apply (uf_equiv_refl _  (liGraph g)).
    - apply uf_root_vgamma with (n := r); auto.
    - repeat intro; auto.
  } Unfocus.
  Focus 2. {
    simplify_ramif. rewrite H11. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H4.
    apply reachable_foot_valid in H4. intro. subst root. apply (valid_not_null g' null H4). simpl. auto.
  } Unfocus.
  rewrite H11. unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g' x root H8 H9 H10)). apply (exp_right root). rewrite H11. entailer !.
  assert (uf_root g' x root). {
    rewrite <- (uf_equiv_root_the_same g g' x root); auto. apply (uf_root_edge _ (liGraph g) _ pa); [| apply (vgamma_not_dst g x r pa) | rewrite (uf_equiv_root_the_same g g')]; auto.
  } split; [|split].
  - apply (graph_gen_redirect_parent_equiv g g' x r pa); auto.
  - simpl. apply (uf_root_gen_dst_same g' (liGraph g') x x root); auto. apply reachable_refl; auto.
  - apply uf_under_bound_redirect_parent; auto.
Qed. (* 56.251 secs *)

(* Print Assumptions body_find. *)

Lemma true_Ceq_eq: forall x y, typed_true tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + symmetry in Heqb1. apply binop_lemmas2.int_eq_true in Heqb1. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma false_Ceq_neq: forall x y, typed_false tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Int.eq i i0) eqn:? .
    + simpl in H. inversion H.
    + subst b0. apply int_eq_false_e in Heqb1. intro. inversion H0. auto.
  - intro. inversion H0. auto.
Qed.

Lemma body_unionS: semax_body Vprog Gprog f_unionS unionS_spec.
Proof.
  start_function.
  destruct H as [? [? [? ?]]]. forward_call (sh, g, x). Intros vret. destruct vret as [g1 x_root]. simpl fst in *. simpl snd in *. apply rank_unchanged_in_bound in H6; auto.
  assert (vvalid g1 y) by (destruct H3 as [? _]; rewrite <- H3; apply H0).
  forward_call (sh, g1, y). Intros vret. destruct vret as [g2 y_root]. simpl fst in *. simpl snd in *. apply rank_unchanged_in_bound in H11; auto.
  forward_if_tac
    (PROP (x_root <> y_root)
     LOCAL (temp _yRoot (pointer_val_val y_root); temp _xRoot (pointer_val_val x_root);
     temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (vertices_at sh (vvalid g2) g2)). 1: apply ADMIT.
  Focus 1. { forward. apply (exp_right g2). entailer !; auto. apply true_Ceq_eq in H12. subst y_root. apply (the_same_root_union g g1 g2 x y x_root); auto. } Unfocus.
  Focus 1. { forward. apply false_Ceq_neq in H12. entailer. } Unfocus.

  (* xRank = xRoot -> rank; *)
  Intros. remember (vgamma g2 x_root) as rpa eqn:?H. destruct rpa as [rankXRoot paXRoot]. symmetry in H13.
  localize
    (PROP  ()
     LOCAL (temp _xRoot (pointer_val_val x_root))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H13. simpl vgamma2cdata. apply -> ram_seq_assoc.
  eapply semax_ram_seq;
  [subst RamFrame RamFrame0; unfold abbreviate;
   repeat apply eexists_add_stats_cons; constructor
  | load_tac
  | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
            temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP  (whole_graph sh g2)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H13. simpl. apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) x_root (rankXRoot, paXRoot)); auto.
    destruct H8 as [? _]. rewrite <- H8. destruct H4. apply reachable_foot_valid in H4. apply H4.
  } Unfocus.

  (* yRank = yRoot -> rank; *)
  remember (vgamma g2 y_root) as rpa eqn:?H. destruct rpa as [rankYRoot paYRoot]. symmetry in H14.
  localize
    (PROP  ()
     LOCAL (temp _yRoot (pointer_val_val y_root))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H14. simpl vgamma2cdata. apply -> ram_seq_assoc.
  eapply semax_ram_seq;
  [subst RamFrame RamFrame0; unfold abbreviate;
   repeat apply eexists_add_stats_cons; constructor
  | load_tac
  | abbreviate_semax_ram].
  unlocalize
    (PROP  ()
     LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot))); temp _xRoot (pointer_val_val x_root);
            temp _yRoot (pointer_val_val y_root); temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP  (whole_graph sh g2)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H14. simpl. apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) y_root (rankYRoot, paYRoot)); auto.
    destruct H9. apply reachable_foot_valid in H9. apply H9.
  } Unfocus.
  assert (vvalid g2 x_root) by (destruct H8 as [? _]; rewrite <- H8; destruct H4; apply reachable_foot_valid in H4; apply H4). clear H1 H2 H5 H6.
  assert (Int.signed (Int.repr (Z.of_nat rankXRoot)) = Z.of_nat (vlabel g2 x_root)). {
    simpl vgamma in H13. inversion H13. apply Int.signed_repr. split.
    - pose proof Int.min_signed_neg. pose proof (Zle_0_nat rankXRoot). intuition.
    - specialize (H11 x_root H15). auto.
  } assert (Int.signed (Int.repr (Z.of_nat rankYRoot)) = Z.of_nat (vlabel g2 y_root)). {
    simpl vgamma in H14. inversion H14. apply Int.signed_repr. split.
    - pose proof Int.min_signed_neg. pose proof (Zle_0_nat rankYRoot). intuition.
    - destruct H9 as [? _]. apply reachable_foot_valid in H2. specialize (H11 y_root H2). auto.
  } clear H11.
  unfold semax_ram.
  forward_if_tac
    (EX g': Graph,
     PROP (uf_union g x y g' /\ uf_under_bound g')
          LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                 temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                 temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (whole_graph sh g')).
  Focus 3. { Intros g'. forward. apply (exp_right g'). entailer. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.
  assert (weak_valid g2 y_root) by (right; destruct H9; apply reachable_foot_valid in H6; apply H6).
  assert (~ reachable g2 y_root x_root) by (intro; destruct H9; specialize (H16 _ H11); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 x_root y_root H6 H15 H11)) (Graph_gen_redirect_parent g2 x_root y_root H6 H15 H11) =
          vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 x_root y_root H6 H15 H11)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }

  (* xRoot -> parent = yRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H13. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val y_root)) = pointer_val_val y_root) by (destruct y_root; simpl; auto). rewrite H17. clear H17.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankXRoot)), pointer_val_val y_root) (pointer_val_val x_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankXRoot)), pointer_val_val y_root) (pointer_val_val x_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 x_root y_root H6 H15 H11))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H13. simpl vgamma2cdata. rewrite H16. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H9.
    apply reachable_foot_valid in H9. intro. subst y_root. apply (valid_not_null g2 null H9). simpl. auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g2 x_root y_root H6 H15 H11)). entailer !. split.
    - apply (diff_root_union_1 g g1 g2 x y x_root y_root); auto.
    - rewrite H1 in *. rewrite H2 in *. rewrite <- Nat2Z.inj_lt in H5. destruct H9. apply uf_under_bound_redirect_parent_lt; auto.
  } Unfocus.
  assert (weak_valid g2 x_root) by (right; destruct H8; rewrite <- H6; destruct H4; apply reachable_foot_valid in H4; auto).
  assert (vvalid g2 y_root) by (destruct H9; apply reachable_foot_valid in H9; apply H9).
  assert (~ reachable g2 x_root y_root) by (intro; rewrite (uf_equiv_root_the_same g1 g2) in H4; auto; destruct H4; specialize (H17 _ H16); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16)) (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16) =
          vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
  forward_if_tac
    (EX g': Graph,
     PROP (uf_union g x y g' /\ uf_under_bound g')
          LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                 temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                 temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (whole_graph sh g')).
  Focus 3. { unfold POSTCONDITION. unfold abbreviate. rewrite overridePost_overridePost. intros. apply andp_left2. auto. } Unfocus.
  Focus 2. { gather_current_goal_with_evar. } Unfocus.

  (* yRoot -> parent = xRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H14. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val x_root)) = pointer_val_val x_root) by (destruct x_root; simpl; auto). rewrite H19. clear H19.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H14. simpl vgamma2cdata. rewrite H17. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H4.
    apply reachable_foot_valid in H4. intro. subst x_root. apply (valid_not_null g1 null H4). simpl. auto.
  } Unfocus.
  Focus 1. {
    unfold semax_ram. forward. apply (exp_right (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16)). entailer !. split.
    - apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto.
    - rewrite H1 in *. rewrite H2 in *. rewrite <- Nat2Z.inj_lt in H18. apply uf_under_bound_redirect_parent_lt; auto.
      rewrite (uf_equiv_root_the_same g1 g2) in H4; auto. destruct H4. auto.
  } Unfocus.

  (* yRoot -> parent = xRoot; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root))).
  rewrite H14. simpl vgamma2cdata.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  assert (force_val (sem_cast_neutral (pointer_val_val x_root)) = pointer_val_val x_root) by (destruct x_root; simpl; auto). rewrite H19. clear H19.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat rankYRoot)), pointer_val_val x_root) (pointer_val_val y_root)).
  unlocalize
   (PROP ()
         LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
                temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
                temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite H14. simpl vgamma2cdata. rewrite H17. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H4.
    apply reachable_foot_valid in H4. intro. subst x_root. apply (valid_not_null g1 null H4). simpl. auto.
  } Unfocus. clear H17.
  remember (Graph_gen_redirect_parent g2 y_root x_root H6 H11 H16) as g3.
  assert (uf_union g x y g3) by (rewrite Heqg3; simpl; apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto).

  (* xRoot -> rank = xRank + 1; *)
  localize
   (PROP  ()
    LOCAL (temp _xRoot (pointer_val_val x_root); temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))))
    SEP   (data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root))).
  rewrite H13. simpl vgamma2cdata.
  eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  rewrite add_repr. replace (Z.of_nat rankXRoot + 1) with (Z.of_nat (rankXRoot + 1)). 2: rewrite Nat2Z.inj_add; simpl; auto.
  change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat (rankXRoot + 1))), pointer_val_val paXRoot) (pointer_val_val x_root)) with
      (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat (rankXRoot + 1))), pointer_val_val paXRoot) (pointer_val_val x_root)).
  unlocalize
   (PROP ()
    LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
           temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
           temp _x (pointer_val_val x); temp _y (pointer_val_val y))
    SEP (whole_graph sh (Graph_vgen g3 x_root (rankXRoot + 1)%nat))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    assert (vertices_at sh (vvalid (Graph_vgen g3 x_root (rankXRoot + 1)%nat)) (Graph_vgen g3 x_root (rankXRoot + 1)%nat) =
            vertices_at sh (vvalid g3) (Graph_vgen g3 x_root (rankXRoot + 1)%nat)). {
      apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition.
    } rewrite H19. clear H19. rewrite H13. simpl vgamma2cdata. apply (@graph_vgen_ramify _ (sSGG_VST sh)).
    - rewrite Heqg3. simpl. destruct H8 as [? _]. rewrite <- H8. destruct H4; apply reachable_foot_valid in H4; apply H4.
    - apply (graph_gen_redirect_parent_vgamma _ _ _ rankXRoot paXRoot) in Heqg3; auto. intros. inversion H19; auto.
  } Unfocus.
  unfold semax_ram. forward. apply (exp_right (Graph_vgen g3 x_root (rankXRoot + 1)%nat)). entailer !.
  rewrite H1 in *; rewrite H2 in *. assert (Z.of_nat (vlabel g2 x_root) = Z.of_nat (vlabel g2 y_root)) by (clear -H5 H18; intuition). apply Nat2Z.inj in H23.
  simpl in H13. inversion H13. clear H26. apply uf_under_bound_redirect_parent_eq; auto. rewrite (uf_equiv_root_the_same g1 g2) in H4; auto. destruct H4. auto.
Qed. (* 192.772 secs *)
