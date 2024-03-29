Require Import CertiGraph.unionfind.env_unionfind_iter.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.reachable_computable.
Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.UnionFindGraph.
Require Import CertiGraph.msl_application.GList.
Require Import CertiGraph.msl_application.GList_UnionFind.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.unionfind.spatial_graph_uf_iter.

Local Coercion UFGraph_LGraph: UFGraph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation vertices_at sh P g:= (@vertices_at _ _ _ _ _ mpred (@SGP pSGG_VST nat unit (sSGG_VST sh)) (SGA_VST sh) P g).
Notation whole_graph sh g := (vertices_at sh (vvalid g) g).
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ x g).
Notation UFGraph := (@UFGraph pSGG_VST).
#[local] Existing Instances maGraph finGraph liGraph RGF.

Definition find_spec :=
 DECLARE _find
  WITH sh: wshare, g: UFGraph, x: pointer_val
  PRE [tptr (Tstruct _Node noattr)]
          PROP  (vvalid g x)
          PARAMS (pointer_val_val x)
          GLOBALS ()
          SEP   (whole_graph sh g)
  POST [ tptr (Tstruct _Node noattr) ]
        EX g': UFGraph, EX rt : pointer_val,
        PROP (uf_equiv g g'; uf_root g' x rt)
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (whole_graph sh g').

Definition Gprog : funspecs := ltac:(with_library prog [find_spec]).

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

Lemma graph_local_facts: forall sh x (g: UFGraph), vvalid g x -> whole_graph sh g |-- valid_pointer (pointer_val_val x).
Proof.
  intros. eapply derives_trans; [apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (vgamma g x)); auto |].
  simpl vertex_at at 1. unfold binode. entailer!.
Qed.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function.
  remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa]. symmetry in H0.
  (* tmp = x *)
  Opaque pointer_val_val. forward. Transparent pointer_val_val.
  (* p = x -> parent; *)
  localize [data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x)].
  rewrite H0. simpl vgamma2cdata. forward. 1: entailer!; destruct pa; simpl; auto.
  unlocalize [whole_graph sh g].
  1: rewrite H0; simpl; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  forward_while (EX p: pointer_val, EX ppa: pointer_val,
                 PROP (reachable g x p /\ vgamma g p = (vlabel g p, ppa))
                 LOCAL (temp _p (pointer_val_val ppa); temp _tmp (pointer_val_val p); temp _x (pointer_val_val x))
                 SEP (vertices_at sh (vvalid g) g)).
  - Exists x pa. entailer!. split; [apply reachable_refl | f_equal; simpl in H0; inversion H0]; auto.
  - entailer!. destruct H1. apply reachable_foot_valid in H1. pose proof (valid_parent _ _ _ _ H1 H5). apply denote_tc_test_eq_split; apply graph_local_facts; auto.
  - destruct H1. 
    Opaque pointer_val_val. forward. Transparent pointer_val_val. remember (vgamma g ppa) as rpa eqn:?H. destruct rpa as [mr mgpa]. symmetry in H3.
    assert (H_VALID_PPA: vvalid g ppa) by (apply (valid_parent _ p (vlabel g p)); [apply reachable_foot_valid in H1 |]; auto).
    localize [data_at sh node_type (vgamma2cdata (vgamma g ppa)) (pointer_val_val ppa)].
    rewrite H3. simpl vgamma2cdata. forward. 1: entailer!; destruct mgpa; simpl; auto.
    unlocalize [whole_graph sh g].
    1: rewrite H3; simpl; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) ppa (mr, mgpa)); auto.
    Exists (ppa, mgpa). simpl fst. simpl snd. assert (mr = vlabel g ppa) by (simpl in H3; inversion H3; auto). rewrite <- H4. entailer !.
    apply reachable_edge with p; auto. apply (vgamma_not_edge g p (vlabel g p)); auto. apply reachable_foot_valid in H1; auto.
    intro. subst. apply HRE; trivial.
  - destruct H1.
    rename HRE into Htemp.
    assert (HRE: p = ppa). {
      destruct p; destruct ppa; inversion Htemp; trivial.
    }
    subst ppa. assert (uf_root g x p) by (split; intros; auto; apply (parent_loop g p (vlabel g p) y); auto).
    forward_while (EX g': UFGraph, EX tmp: pointer_val, EX xv: pointer_val,
                   PROP (uf_equiv g g' /\ uf_root g' xv p)
                   LOCAL (temp _p (pointer_val_val p); temp _tmp (pointer_val_val tmp); temp _x (pointer_val_val xv))
                   SEP (whole_graph sh g')).
    + Exists g p x. entailer!. apply (uf_equiv_refl _  (liGraph g)).
    + entailer!. apply denote_tc_test_eq_split; apply graph_local_facts.
      * destruct H4 as [_ [? _]]. apply reachable_head_valid in H4; assumption.
      * destruct H4 as [[? _] _]. rewrite <- H4. apply reachable_foot_valid in H1; assumption.
    + destruct H4 as [? ?].
      rename HRE into Htemp'.
      assert (HRE: xv <> p). {
        intro; subst; apply Htemp'; trivial.
      }
      remember (vgamma g' xv) as rpa eqn:?H. destruct rpa as [xr xpa]. symmetry in H6.
      assert (H_VALID_XV: vvalid g' xv) by (destruct H5 as [? _]; apply reachable_head_valid in H5; auto).
      localize [data_at sh node_type (vgamma2cdata (vgamma g' xv)) (pointer_val_val xv)].
      rewrite H6. simpl vgamma2cdata. forward. 1: entailer!; destruct xpa; simpl; auto.
      unlocalize [whole_graph sh g'].
      1: rewrite H6; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g' (vvalid g') xv (xr, xpa)); auto.
      assert (weak_valid g' p) by (right; destruct H4; rewrite <- H4; apply reachable_foot_valid in H1; auto).
      assert (vvalid g' xv) by (destruct H5; apply reachable_head_valid in H5; auto).
      assert (~ reachable g' p xv) by (intro; destruct H5 as [_ ?]; specialize (H5 _ H9); auto).
      assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g' xv p H7 H8 H9)) (Graph_gen_redirect_parent g' xv p H7 H8 H9) =
              vertices_at sh (vvalid g') (Graph_gen_redirect_parent g' xv p H7 H8 H9)). {
        apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
      assert (H_P_NOT_NULL: p <> null) by (apply reachable_foot_valid in H1; intro; subst p; apply (valid_not_null g null H1); simpl; auto).
      localize [data_at sh node_type (Vint (Int.repr (Z.of_nat xr)), pointer_val_val xpa) (pointer_val_val xv)].
      forward. unlocalize [whole_graph sh (Graph_gen_redirect_parent g' xv p H7 H8 H9)].
      1: rewrite H10; apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto.
      Opaque pointer_val_val. forward. Transparent pointer_val_val.
      Exists (((Graph_gen_redirect_parent g' xv p H7 H8 H9), xpa), xpa). simpl fst. simpl snd. rewrite H10. entailer !. split.
      * apply (graph_gen_redirect_parent_equiv' g g' xv p); auto.
      * apply (uf_root_gen_dst_preserve g' (liGraph g')); auto.
        -- apply (vgamma_not_reachable _ _ xr); auto. pose proof (uf_root_not_eq_root_vgamma g' _ _ _ _ H6 H5 HRE). auto.
        -- apply (vgamma_uf_root g' xv xr xpa p); auto.
    + destruct H4. forward. Exists g' p. entailer!. rewrite <- (uf_equiv_root_the_same g g' x p); auto.
Qed.
