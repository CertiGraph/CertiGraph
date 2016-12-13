Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_unionfind.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.GraphAsList.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GList.
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
Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST nat unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST nat unit).
Existing Instances maGraph finGraph liGraph RGF.

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
        LOCAL(temp ret_temp (pointer_val_val rt))
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

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := find_spec :: unionS_spec ::nil.

Lemma ADMIT: forall P: Prop, P.
Admitted.

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
    apply (@va_reachable_root_stable_ramify _ _ _ _ SGBA_VST _ _ _ _ _ (SGA_VST sh) g x (r, pa)); auto.
  } Unfocus.
  unfold semax_ram.
  forward_if_tac
    (EX g': Graph, EX rt : pointer_val,
     PROP (uf_equiv g g' /\ uf_root g' x rt)
     LOCAL(temp ret_temp (pointer_val_val rt))
     SEP (graph sh x g')); [apply ADMIT | | gather_current_goal_with_evar ..].
  localize
    (PROP (vvalid g pa)
     LOCAL (temp _p (pointer_val_val pa))
     SEP (graph sh pa g)).
    1: admit.
    apply -> ram_seq_assoc.
    eapply semax_ram_seq'.
    + subst RamFrame RamFrame0; unfold abbreviate;
        repeat apply eexists_add_stats_cons; constructor.
    + semax_ram_call_body (sh, g, pa).
  
Qed.


