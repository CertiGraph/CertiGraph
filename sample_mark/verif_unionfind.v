Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_unionfind.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.GraphAsList.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GList.
Require Import RamifyCoq.msl_application.GList_UnionFind.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_graph_glist.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation vertices_at sh P g:= (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ P g).
Notation whole_graph sh g := (vertices_at sh (vvalid g) g).
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST nat unit unit).
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
        PROP (findS g x g' /\ uf_root g' x rt)
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

(*
Definition makeSet_spec :=
  DECLARE _makeSet
  WITH g : Graph, l : list pointer_val, sh: wshare
    PRE []
      PROP (uf_graph g)
      LOCAL ()
      SEP (graphs sh g l)
    POST [tptr (Tstruct _Node noattr)]
      EX g': Graph, EX rt: pointer_val,
      PROP (uf_graph g' /\ new_singleton g g' rt)
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (graphs sh g' [rt :: l]).
 *)

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH sh: wshare
    PRE []
      PROP ()
      LOCAL ()
      SEP ()
    POST [tptr (Tstruct _Node noattr)]
      EX g: Graph, EX rt: pointer_val,
      PROP (uf_graph g)
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (graph sh rt g).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mallocN_spec :: makeSet_spec :: find_spec :: unionS_spec ::nil.

Lemma ADMIT: forall P: Prop, P.
Admitted.

Lemma body_makeSet: semax_body Vprog Gprog f_makeSet makeSet_spec.
Proof.
  start_function.
  forward_call (sh, 8).
  - compute. split; intros; inversion H.
  - Intros x. 
    assert_PROP (x <> null) as x_not_null by
          (entailer !; destruct H0 as [? _]; apply H0).
    forward. forward. forward.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr 0), pointer_val_val x)) with
    (@data_at CompSpecs sh node_type (Vint (Int.repr 0), pointer_val_val x)).
    apply (exp_right (single_Graph x x_not_null O tt tt)). entailer.
    apply (exp_right x). entailer !.
    + simpl. apply single_uf_is_uf. auto.
    + unfold reachable_vertices_at. simpl. unfold vertices_at. unfold iter_sepcon.pred_sepcon.
      apply (exp_right (x:: nil)). entailer !.
      * simpl. split.
        -- intros. rewrite reachabel_single_uf. intuition. auto.
        -- constructor. intuition. constructor.
      * simpl. unfold graph_vcell. unfold vgamma. simpl. unfold graph_gen.updateEdgeFunc.
        assert ((if EquivDec.equiv_dec (x, tt) (x, tt) then null else x) = null) by (destruct (EquivDec.equiv_dec (x, tt) (x, tt)); [|compute in c; exfalso]; auto).
        rewrite H2. assert ((if SGBA_VE null null then x else null) = x). {
          Transparent pSGG_VST. compute. Opaque pSGG_VST. destruct (PV_eq_dec NullPointer NullPointer); [|exfalso]; auto.
        } rewrite H3. entailer !.
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

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function.
  remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa].
  localize
    (PROP  ()
     LOCAL (temp _x (pointer_val_val x))
     SEP  (data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x))).
  rewrite <- H0. simpl vgamma2cdata.
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
    simplify_ramif. rewrite <- H0. simpl.
    apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  } Unfocus.
  unfold semax_ram.
  forward_if_tac
    (EX g': Graph, EX rt : pointer_val,
     PROP (findS g x g' /\ uf_root g' x rt)
     LOCAL (temp _p (pointer_val_val rt); temp _x (pointer_val_val x))
     SEP (whole_graph sh g'));
    [apply ADMIT | | gather_current_goal_with_evar ..].
  forward_call (sh, g, pa). 1: symmetry in H0; apply valid_parent in H0; auto.
  Intros vret. destruct vret as [g' root]. simpl in *. forward.
  pose proof (true_Cne_neq _ _ H1).
  assert (weak_valid g' root) by (right; destruct H3; apply reachable_foot_valid in H3; auto).
  assert (vvalid g' x) by (destruct H2 as [_ [[? _] _]]; rewrite <- H2; apply H).
  assert ((vgamma g' x) = (r, pa)) by (apply (findS_preserves_vgamma g); auto).
  assert (~ reachable g' root x) by (destruct H3; apply (vgamma_not_reachable' _ _ r pa); auto).
  assert (vertices_at sh (vvalid (Graph_gen_redirect_parent g' x root H5 H6 H8)) (Graph_gen_redirect_parent g' x root H5 H6 H8) =
          vertices_at sh (vvalid g') (Graph_gen_redirect_parent g' x root H5 H6 H8)). {
    apply vertices_at_Same_set. unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In. simpl. intuition. }
  localize
   (PROP  ()
    LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr (Z.of_nat r)), pointer_val_val pa)
                   (pointer_val_val x))).
    eapply semax_ram_seq';
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac 
    | abbreviate_semax_ram].
    assert (force_val (sem_cast_neutral (pointer_val_val root)) = pointer_val_val root) by (destruct root; simpl; auto). rewrite H10. clear H10.
    change (@field_at CompSpecs sh node_type [] (Vint (Int.repr (Z.of_nat r)), pointer_val_val root) (pointer_val_val x)) with
        (@data_at CompSpecs sh node_type (Vint (Int.repr (Z.of_nat r)), pointer_val_val root) (pointer_val_val x)).
    unlocalize
      (PROP ()
       LOCAL (temp _p (pointer_val_val root); temp _x (pointer_val_val x))
       SEP (whole_graph sh (Graph_gen_redirect_parent g' x root H5 H6 H8))).
    Grab Existential Variables.
    Focus 3. { Intros g' rt. forward. apply (exp_right g'). entailer !. apply (exp_right rt). entailer !. } Unfocus.
    Focus 3. {
      forward. apply (exp_right g). apply (exp_right x). entailer ! . apply false_Cne_eq in H1. subst pa. split; split; [|split| |]; auto.
      - reflexivity.
      - apply (uf_equiv_refl _  (liGraph g)).
      - repeat intro; auto.
      - apply uf_root_vgamma with (n := r); auto.
    } Unfocus.
    Focus 2. {
      simplify_ramif. rewrite H9. apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); auto. destruct H3.
      apply reachable_foot_valid in H3. intro. subst root. apply (valid_not_null g' null H3). simpl. auto.
    } Unfocus.
    rewrite H9. unfold semax_ram. forward.
    change (fun a : environ => (EX x0 : Graph, (EX x1 : pointer_val, (PROP (findS g x x0 /\ uf_root x0 x x1) LOCAL (temp _p (pointer_val_val x1); temp _x (pointer_val_val x))
                                                                           SEP (vertices_at sh (vvalid x0) x0)) a))%logic) with
        (EX x0 : Graph, (EX x1 : pointer_val, (PROP (findS g x x0 /\ uf_root x0 x x1) LOCAL (temp _p (pointer_val_val x1); temp _x (pointer_val_val x)) SEP
                                                    (vertices_at sh (vvalid x0) x0)))). apply (exp_right (Graph_gen_redirect_parent g' x root H5 H6 H8)).
    apply (exp_right root). rewrite H9. entailer !. split.
  - apply (graph_gen_redirect_parent_findS g g' x r pa root H5 H6 H8); auto.
  - simpl. apply (uf_root_gen_dst g' (liGraph g') x x root); auto.
    + apply (uf_root_edge _ (liGraph g') _ pa); auto. apply vgamma_not_dst with r; auto.
    + apply reachable_refl; auto.
Qed. (* 47.715 secs *)

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
  destruct H.
  forward_call (sh, g, x). Intros vret. destruct vret as [g1 x_root]. simpl fst in *. simpl snd in *.
  assert (vvalid g1 y) by (destruct H1 as [_ [[? _] _]]; rewrite <- H1; apply H0).
  forward_call (sh, g1, y). Intros vret. destruct vret as [g2 y_root]. simpl fst in *. simpl snd in *.
  forward_if_tac
    (PROP ( )
     LOCAL (temp _yRoot (pointer_val_val y_root); temp _xRoot (pointer_val_val x_root);
     temp _x (pointer_val_val x); temp _y (pointer_val_val y))
     SEP (vertices_at sh (vvalid g2) g2)). 1: apply ADMIT.
  Focus 1. {
    forward. apply (exp_right g2). entailer !; auto. apply true_Ceq_eq in H6. subst y_root.
Abort.
