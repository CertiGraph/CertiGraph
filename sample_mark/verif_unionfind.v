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

Notation vertices_at sh g P := (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ g P).
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
          SEP   (graph sh x g)
  POST [ tptr (Tstruct _Node noattr) ]
        EX g': Graph, EX rt : pointer_val,
        PROP (uf_equiv g g' /\ uf_root g' x rt)
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (graph sh x g').

Definition unionS_spec :=
 DECLARE _unionS
  WITH sh: wshare, g: Graph, x: pointer_val, y: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr)), _y OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x /\ weak_valid g y)
          LOCAL (temp _x (pointer_val_val x); temp _y (pointer_val_val y))
          SEP   (graph sh x g * graph sh y g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (uf_union g x y g')
        LOCAL()
        SEP (graph sh x g').

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
    + simpl. apply single_uf_is_uf.
    + unfold reachable_vertices_at. simpl. unfold vertices_at. unfold iter_sepcon.pred_sepcon.
      apply (exp_right (x:: nil)). entailer !.
      * simpl. split.
        -- intros. rewrite reachabel_single_uf. intuition.
        -- constructor. intuition. constructor.
      * simpl. unfold graph_vcell. unfold vgamma. simpl. unfold graph_gen.updateEdgeFunc.
        destruct (EquivDec.equiv_dec (x, tt) (x, tt)); entailer !.
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
     SEP  (graph sh x g)).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif. rewrite <- H0. simpl.
    apply (@va_reachable_root_stable_ramify _ _ _ _ SGBA_VST _ _ _ _ _ _ (SGA_VST sh) g x (r, pa)); auto.
  } Unfocus.
  unfold semax_ram.
  forward_if_tac
    (EX g': Graph, EX rt : pointer_val,
     PROP (uf_equiv g g' /\ uf_root g' x rt)
     LOCAL (temp _p (pointer_val_val rt))
     SEP (graph sh x g')); [apply ADMIT | | gather_current_goal_with_evar ..].
  localize
    (PROP (vvalid g pa)
     LOCAL (temp _p (pointer_val_val pa))
     SEP (graph sh pa g)).
  1: symmetry in H0; apply valid_parent in H0; auto.
  eapply semax_ram_seq;
    [subst RamFrame RamFrame0; unfold abbreviate;
        repeat apply eexists_add_stats_cons; constructor
    | semax_ram_call_body (sh, g, pa)
    | semax_ram_after_call; intros [g' x']; simpl fst; simpl snd;
      apply ram_extract_PROP; intros]. destruct H3.
    unlocalize
      (PROP ()
       LOCAL (temp _p0 (pointer_val_val x'); temp _p (pointer_val_val pa))
       SEP (graph sh pa g'))
    using [H3; H4]%RamAssu
    binding [g'; x']%RamBind.
  Grab Existential Variables.
  Focus 3. {
    Intros g' rt. forward. apply (exp_right g'). entailer !.
    apply (exp_right rt). entailer !.
  } Unfocus.
  Focus 3. {
    forward. apply (exp_right g). apply (exp_right x). entailer !.
    assert (pa = x). {
      hnf in H1. destruct pa, x; inversion H1; auto. simpl in H1. clear H5.
      unfold sem_cmp_pp in H1. simpl in H1. destruct (eq_block b b0).
      - destruct (Int.eq i i0) eqn:? .
        + symmetry in Heqb1. apply binop_lemmas2.int_eq_true in Heqb1. subst; auto.
        + simpl in H1. inversion H1.
      - simpl in H1. inversion H1.
    } subst pa. split; [|split]; auto.
    - apply (uf_equiv_refl _  (liGraph g)).
    - hnf.
  }
    
    
  
Qed.


