Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Export VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.DagBi_Mark.
Require Import RamifyCoq.data_structure.spatial_graph_aligned_bi_VST.

Local Open Scope logic.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Coercion SGraph_PGraph: SGraph >-> PGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Identity Coercion PGraph_PreGraph: PGraph >-> PreGraph.

Notation dag sh x g := (@dag _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST bool unit).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (dag sh x g)
  POST [ Tvoid ]
      EX g': Graph,
        PROP (mark x g g')
        LOCAL()
        SEP (dag sh x g').

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
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.

  forward_if_tac  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (dag sh x g)).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return *)
    apply (exp_right g); entailer!; auto.
    apply (mark_null_refl g).
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

  erewrite dag_unfold by eauto.
  normalize.
  rewrite H_GAMMA_g.
  change (vertex_at x (d, l, r)) with
    (@data_at CompSpecs sh node_type
       (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).

  forward. (* root_mark = x -> m; *)

  eapply semax_pre with 
    (PROP  ()
     LOCAL 
      (temp _root_mark (Vint (Int.repr (if d then 1 else 0)));
      temp _x (pointer_val_val x))
     SEP  (dag sh x g)).
  Focus 1. {
    erewrite dag_unfold by eauto.
    rewrite H_GAMMA_g.
    entailer!.
  } Unfocus.
  
  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (dag sh x g)).
  Focus 1. { (* if-then branch *)
    forward. (* return *)
    apply (exp_right g).
    entailer!; auto.
    eapply (mark_vgamma_true_refl g); eauto.
    clear - H0; destruct d; [auto | inversion H0].
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    clear - H0; destruct d; congruence.
  } Unfocus.

  erewrite dag_unfold by eauto.
  rewrite H_GAMMA_g.
  normalize.
  change (vertex_at x (false, l, r)) with
    (@data_at CompSpecs sh node_type
       (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)).

  forward. (* l = x -> l; *)
  forward. (* r = x -> r; *)
  forward. (* x -> d = 1; *)

  pose proof Graph_gen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
  apply semax_pre with
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (dag sh x (Graph_gen g x true))).
  Focus 1. {
    pose proof Graph_gen_spatial_spec g x false true l r H_GAMMA_g.
    rewrite H2.
    erewrite dag_vgen by eauto.
    entailer!.
  } Unfocus.

  forget (Graph_gen g x true) as g1.

  localize
   (PROP  (weak_valid g1 l)
    LOCAL (temp _l (pointer_val_val l))
    SEP   (dag sh l g1)).
  1: eapply left_weak_valid; eauto.  
  (* localize *)

  rewrite <- ram_seq_assoc.
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g1, l) 
  | semax_ram_after_call; intros g2;
    repeat (apply ram_extract_PROP; intro)].

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (dag sh x g2))
  using [H3]%RamAssu
  binding [g2]%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    subst.
    eapply (@dag_ramify_left _ (sSGG_VST sh) _ g); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  localize
   (PROP  (weak_valid g2 r)
    LOCAL (temp _r (pointer_val_val r))
    SEP   (dag sh r g2)).
  1: eapply right_weak_valid; eauto.  
  (* localize *)
  
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g2, r) 
  | semax_ram_after_call; intros g3;
    repeat (apply ram_extract_PROP; intro) ].
  (* mark(r); *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (dag sh x g3))
  using [H5]%RamAssu
  binding [g3]%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    subst.
    eapply (@dag_ramify_right _ (sSGG_VST sh) _ g); eauto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  forward. (* ( return; ) *)
  apply (exp_right g3); entailer!; auto.
  apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
Time Qed. (* Takes 3 hours. *)

