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
Existing Instances maGraph finGraph liGraph RGF.

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
          PROP  (vvalid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (whole_graph sh g)
  POST [ tptr (Tstruct _Node noattr) ]
        EX g': Graph, EX rt : pointer_val,
        PROP (uf_equiv g g' /\ uf_root g' x rt)
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (whole_graph sh g').

Definition unionS_spec :=
 DECLARE _unionS
  WITH sh: wshare, g: Graph, x: pointer_val, y: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr)), _y OF (tptr (Tstruct _Node noattr))]
          PROP  (vvalid g x /\ vvalid g y)
          LOCAL (temp _x (pointer_val_val x); temp _y (pointer_val_val y))
          SEP   (whole_graph sh g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL()
        SEP (whole_graph sh g').

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH sh: wshare, g: Graph
    PRE []
      PROP ()
      LOCAL ()
      SEP (whole_graph sh g)
    POST [tptr (Tstruct _Node noattr)]
      EX g': Graph, EX rt: pointer_val,
      PROP (~ vvalid g rt /\ vvalid g' rt /\ is_partial_graph g g')
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (whole_graph sh g').

Definition Gprog : funspecs := ltac:(with_library prog [mallocN_spec; makeSet_spec; find_spec; unionS_spec]).

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function.
  forward_call (sh, 8).
  - compute. split; intros; inversion H.
  - Intros x.
    assert_PROP (x <> null) as x_not_null by (entailer !; destruct H0 as [? _]; apply H0).
    assert_PROP (~ vvalid g x) by (entailer; apply (@vertices_at_sepcon_unique_1x _ _ _ _ SGBA_VST _ _ (SGA_VST sh) (SGAvs_VST sh) g x (vvalid g) (O, null))).
    forward. forward. forward.
    Exists (make_set_Graph O tt tt x g x_not_null H). Exists x. entailer!.
    + split; simpl; [right | apply is_partial_make_set_pregraph]; auto.
    + assert (Coqlib.Prop_join (vvalid g) (eq x) (vvalid (make_set_Graph 0%nat tt tt x g x_not_null H))). {
        simpl; hnf; split; intros; [unfold graph_gen.addValidFunc | subst a]; intuition.
      } assert (vgamma (make_set_Graph O tt tt x g x_not_null H) x = (O, x)). {
        unfold vgamma, UnionFindGraph.vgamma. simpl. f_equal.
        - destruct (SGBA_VE x x); [| hnf in c; unfold Equivalence.equiv in c; exfalso]; auto.
        - unfold graph_gen.updateEdgeFunc. destruct (EquivDec.equiv_dec (x, tt) (x, tt)). 2: compute in c; exfalso; auto. destruct (SGBA_VE null null); auto.
          hnf in c. unfold Equivalence.equiv in c. exfalso; auto.
      } rewrite <- (vertices_at_sepcon_1x (make_set_Graph 0%nat tt tt x g x_not_null H) x (vvalid g) _ (O, x)); auto. apply sepcon_derives. 1: apply derives_refl.
      assert (vertices_at sh (vvalid g) g = vertices_at sh (vvalid g) (make_set_Graph O tt tt x g x_not_null H)). {
        apply vertices_at_vertices_identical. simpl. hnf. intros. destruct a as [y ?]. unfold Morphisms_ext.app_sig. simpl.
        unfold UnionFindGraph.vgamma. simpl. unfold graph_gen.updateEdgeFunc. f_equal.
        - destruct (SGBA_VE y x); [hnf in e; subst y; exfalso |]; auto.
        - destruct (EquivDec.equiv_dec (x, tt) (y, tt)); auto. hnf in e. inversion e. subst y. exfalso; auto.
      } rewrite <- H5. apply derives_refl.
Qed.

Lemma false_Cne_eq: forall x y, typed_false tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .    
    + pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma true_Cne_neq: forall x y, typed_true tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .    
    + simpl in H. inversion H.
    + subst b0. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. intro; apply H0. inversion H1. reflexivity.
  - intro. inversion H0. auto.
Qed.

Lemma graph_local_facts: forall sh x (g: Graph), vvalid g x -> whole_graph sh g |-- valid_pointer (pointer_val_val x).
Proof.
  intros. eapply derives_trans; [apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (vgamma g x)); auto |].
  simpl vertex_at at 1. unfold binode. entailer!.
Qed.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function.
  remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa].
  (* p = x -> parent; *)
  localize [data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x)]. rewrite <- H0. simpl vgamma2cdata.
  forward. 1: entailer!; destruct pa; simpl; auto.
  unlocalize [whole_graph sh g].
  1: rewrite <- H0; simpl vgamma2cdata; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  assert (H_PARENT_Valid: vvalid g pa) by (eapply valid_parent; eauto).
  (* if (p != x) { *)
  forward_if
    (EX g': Graph, EX rt : pointer_val,
     PROP (uf_equiv g g' /\ uf_root g' x rt)
     LOCAL (temp _p (pointer_val_val rt); temp _x (pointer_val_val x))
     SEP (whole_graph sh g')).
  - apply denote_tc_test_eq_split; apply graph_local_facts; auto.
  - (* p0 = find(p); *)
    forward_call (sh, g, pa). Intros vret. destruct vret as [g' root]. simpl fst in *. simpl snd in *. Opaque pointer_val_val. forward. Transparent pointer_val_val.
    pose proof (true_Cne_neq _ _ H1).
    assert (weak_valid g' root) by (right; destruct H3; apply reachable_foot_valid in H3; auto).
    assert (vvalid g' x) by (destruct H2 as [? _]; rewrite <- H2; apply H).
    assert (~ reachable g' root x) by (apply (uf_equiv_not_reachable g g' x r pa root); auto).
    assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g' x root H5 H6 H7)) (Graph_gen_redirect_parent g' x root H5 H6 H7) =
            vertices_at sh (vvalid g') (Graph_gen_redirect_parent g' x root H5 H6 H7)). {
      apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
    remember (vgamma g' x) as rpa eqn:?H. destruct rpa as [r' pa']. symmetry in H9.
    localize [data_at sh node_type (Vint (Int.repr (Z.of_nat r')), pointer_val_val pa') (pointer_val_val x)].
    forward. unlocalize [whole_graph sh (Graph_gen_redirect_parent g' x root H5 H6 H7)].
    + rewrite H8. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H3.
      apply reachable_foot_valid in H3. intro. subst root. apply (valid_not_null g' null H3). simpl. auto.
    + Exists (Graph_gen_redirect_parent g' x root H5 H6 H7) root. rewrite H8. entailer!. split.
      * apply (graph_gen_redirect_parent_equiv g g' x r pa); auto.
      * simpl. apply (uf_root_gen_dst_same g' (liGraph g') x x root); auto. 2: apply reachable_refl; auto.
        rewrite <- (uf_equiv_root_the_same g g' x root); auto.
        apply (uf_root_edge _ (liGraph g) _ pa); [| apply (vgamma_not_dst g x r pa) | rewrite (uf_equiv_root_the_same g g')]; auto.
  - forward. Exists g x. entailer!. apply false_Cne_eq in H1. subst pa. split; [|split]; auto.
    + apply (uf_equiv_refl _  (liGraph g)).
    + apply uf_root_vgamma with (n := r); auto.
  - Intros g' rt. forward. Exists g' rt. entailer!.
Qed.

(* Print Assumptions body_find. *)

Lemma true_Ceq_eq: forall x y, typed_true tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .
    + pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. subst. reflexivity.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma false_Ceq_neq: forall x y, typed_false tint (force_val (sem_cmp_pp Ceq (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .
    + simpl in H. inversion H.
    + pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. intro. apply H0. inversion H1. reflexivity.
  - intro. apply n. inversion H0; reflexivity.
Qed.

Lemma body_unionS: semax_body Vprog Gprog f_unionS unionS_spec.
Proof.
  start_function.
  destruct H.
  forward_call (sh, g, x). Intros vret. destruct vret as [g1 x_root]. simpl fst in *. simpl snd in *.
  assert (vvalid g1 y) by (destruct H1 as [? _]; rewrite <- H1; apply H0).
  forward_call (sh, g1, y). Intros vret. destruct vret as [g2 y_root]. simpl fst in *. simpl snd in *.
  assert (H_VALID_XROOT: vvalid g2 x_root) by (destruct H4 as [? _]; rewrite <- H4; destruct H2; apply reachable_foot_valid in H2; apply H2).
  assert (H_VALID_YROOT: vvalid g2 y_root) by (destruct H5; apply reachable_foot_valid in H5; apply H5).
  assert (H_XROOT_NOT_NULL: x_root <> null) by (intro; subst x_root; apply (valid_not_null g2 null H_VALID_XROOT); simpl; auto).
  assert (H_YROOT_NOT_NULL: y_root <> null) by (intro; subst y_root; apply (valid_not_null g2 null H_VALID_YROOT); simpl; auto).
  forward_if_tac
    (PROP (x_root <> y_root)
     LOCAL (temp _yRoot (pointer_val_val y_root); temp _xRoot (pointer_val_val x_root);
     temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (vertices_at sh (vvalid g2) g2)).
  - apply denote_tc_test_eq_split; apply graph_local_facts; auto.
  - forward. Exists g2. entailer !. apply true_Ceq_eq in H6. subst y_root. apply (the_same_root_union g g1 g2 x y x_root); auto.
  - forward. apply false_Ceq_neq in H6. entailer!.
  - Intros. (* xRank = xRoot -> rank; *)
    remember (vgamma g2 x_root) as rpa eqn:?H. destruct rpa as [rankXRoot paXRoot]. symmetry in H7.
    localize [data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root)].
    rewrite H7. simpl vgamma2cdata. forward.
    unlocalize [whole_graph sh g2].
    1: rewrite H7; simpl; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) x_root (rankXRoot, paXRoot)); auto.
    (* yRank = yRoot -> rank; *)
    remember (vgamma g2 y_root) as rpa eqn:?H. destruct rpa as [rankYRoot paYRoot]. symmetry in H8.
    localize [data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root)].
    rewrite H8. simpl vgamma2cdata. forward.
    unlocalize [whole_graph sh g2].
    1: rewrite H8; simpl; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g2 (vvalid g2) y_root (rankYRoot, paYRoot)); auto.
    forward_if
      (EX g': Graph,
       PROP (uf_union g x y g')
       LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
              temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
              temp _x (pointer_val_val x); temp _y (pointer_val_val y))
       SEP (whole_graph sh g')).
    + assert (weak_valid g2 y_root) by (right; auto). rename H_VALID_XROOT into H11.
      assert (~ reachable g2 y_root x_root) by (intro; destruct H5; specialize (H13 _ H12); auto).
      assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)) (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12) =
          vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)). {
        apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
      (* xRoot -> parent = yRoot; *)
      localize [data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root)].
      rewrite H7. simpl vgamma2cdata. forward. unlocalize [whole_graph sh (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12)].
      1: rewrite H7; simpl vgamma2cdata; rewrite H13; apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto.
      Exists (Graph_gen_redirect_parent g2 x_root y_root H10 H11 H12). rewrite H13. entailer!. apply (diff_root_union_1 g g1 g2 x y x_root y_root); auto.
    + assert (weak_valid g2 x_root) by (right; auto). rename H_VALID_YROOT into H11.
      assert (~ reachable g2 x_root y_root) by (intro; rewrite (uf_equiv_root_the_same g1 g2) in H2; auto; destruct H2; specialize (H13 _ H12); auto).
      assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)) (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12) =
              vertices_at sh (vvalid g2) (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)). {
        apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
      forward_if
      (EX g': Graph,
       PROP (uf_union g x y g')
       LOCAL (temp _xRank (Vint (Int.repr (Z.of_nat rankXRoot))); temp _yRank (Vint (Int.repr (Z.of_nat rankYRoot)));
              temp _xRoot (pointer_val_val x_root); temp _yRoot (pointer_val_val y_root);
              temp _x (pointer_val_val x); temp _y (pointer_val_val y))
       SEP (whole_graph sh g')).
      * (* yRoot -> parent = xRoot; *)
        localize [data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root)].
        rewrite H8. simpl vgamma2cdata. forward. unlocalize [whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)].
        1: rewrite H8; simpl vgamma2cdata; rewrite H13; apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto.
        Exists (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12). rewrite H13. entailer!. apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto.
      * (* yRoot -> parent = xRoot; *)
        localize [data_at sh node_type (vgamma2cdata (vgamma g2 y_root)) (pointer_val_val y_root)].
        rewrite H8. simpl vgamma2cdata. forward. unlocalize [whole_graph sh (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)].
        1: rewrite H8; simpl vgamma2cdata; rewrite H13; apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto.
        set (g3 := (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12)).
        assert (uf_union g x y g3) by (subst g3; simpl; apply (diff_root_union_2 g g1 g2 x y x_root y_root); auto).
        (* xRoot -> rank = xRank + 1; *)
        localize [data_at sh node_type (vgamma2cdata (vgamma g2 x_root)) (pointer_val_val x_root)].
        rewrite H7. simpl vgamma2cdata. forward.
        rewrite add_repr. replace (Z.of_nat rankXRoot + 1) with (Z.of_nat (rankXRoot + 1)) by (rewrite Nat2Z.inj_add; simpl; auto).
        unlocalize [whole_graph sh (Graph_vgen g3 x_root (rankXRoot + 1)%nat)].
        -- assert (vertices_at sh (vvalid (Graph_vgen g3 x_root (rankXRoot + 1)%nat)) (Graph_vgen g3 x_root (rankXRoot + 1)%nat) =
                   vertices_at sh (vvalid g3) (Graph_vgen g3 x_root (rankXRoot + 1)%nat)). {
             apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition.
           } rewrite H16. clear H16. rewrite H7. simpl vgamma2cdata. apply (@graph_vgen_ramify _ (sSGG_VST sh)).
           ++ subst g3. simpl. auto.
           ++ subst g3. remember (Graph_gen_redirect_parent g2 y_root x_root H10 H11 H12) as g3.
              apply (graph_gen_redirect_parent_vgamma _ _ _ rankXRoot paXRoot) in Heqg3; auto. intros. inversion H16; auto.
        -- Exists (Graph_vgen g3 x_root (rankXRoot + 1)%nat). entailer!.
    + Intros g3. forward. Exists g3. entailer!.
Qed. (* 4.207 secs *)
