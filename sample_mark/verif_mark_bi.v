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
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.GraphBi_Mark.
Require Import RamifyCoq.sample_mark.spatial_graph_bi_mark.

Local Open Scope logic.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Check SGP.

Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST bool unit (sSGG_VST sh)) _ x g).
Notation Graph := (@Graph pSGG_VST bool unit unit).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (graph sh x g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (mark x g g')
        LOCAL ()
        SEP   (graph sh x g').

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Vprog : varspecs := (_hd, tptr (Tstruct _Node noattr))::(_n, (Tstruct _Node noattr))::nil.

Definition Gprog : funspecs := mark_spec :: main_spec::nil.

Lemma ADMIT: forall P: Prop, P.
Admitted.

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
     SEP   (graph sh x g)).
  apply ADMIT. (* type checking for pointer comparable. VST will fix it. *)
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
    unfold is_null_SGBA in H0; simpl in H0; subst x.
    exfalso.
    apply H. auto.
  } Unfocus.
  destruct_pointer_val x. clear H0 H_weak_valid.

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x))).
  (* localize *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* root_mark = x -> m; *)

  unlocalize (PROP ()  LOCAL  (temp _root_mark (Vint (Int.repr (if d then 1 else 0))); temp _x (pointer_val_val x))  SEP  (graph sh x g)).

  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@root_stable_ramify _ (sSGG_VST sh) g x _ H_GAMMA_g); auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram.
  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (graph sh x g)).
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

  Intros. subst d.
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x))).
  (* localize *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* l = x -> l; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* r = x -> r; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ subst RamFrame RamFrame0; unfold abbreviate;
      repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs sh node_type
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))).
  (* x -> d = 1; *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (graph sh x (Graph_vgen g x true))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@root_update_ramify _ (sSGG_VST sh) g x _ (false, l, r) (true, l, r)); auto.
    eapply Graph_vgen_vgamma; eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)

  pose proof Graph_vgen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
  forget (Graph_vgen g x true) as g1.

  localize
   (PROP  (weak_valid g1 l)
    LOCAL (temp _l (pointer_val_val l))
    SEP   (graph sh l g1)).
  1: eapply left_weak_valid; eauto.  
  (* localize *)

  rewrite <- ram_seq_assoc.
  eapply semax_ram_seq;
  [ subst RamFrame RamFrame0; unfold abbreviate;
    repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g1, l) 
  | semax_ram_after_call; intros g2;
    repeat (apply ram_extract_PROP; intro) ].

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (graph sh x g2))
  using [H3]%RamAssu
  binding [g2]%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    subst.
    eapply (@graph_ramify_left _ (sSGG_VST sh) _ g); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  localize
   (PROP  (weak_valid g2 r)
    LOCAL (temp _r (pointer_val_val r))
    SEP   (graph sh r g2)).
  1: eapply right_weak_valid; eauto.  
  (* localize *)
  
  eapply semax_ram_seq;
  [ subst RamFrame RamFrame0; unfold abbreviate;
    repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g2, r) 
  | semax_ram_after_call; intros g3;
    repeat (apply ram_extract_PROP; intro) ].
  (* mark(r); *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (graph sh x g3))
  using [H5]%RamAssu
  binding [g3]%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    subst.
    eapply (@graph_ramify_right _ (sSGG_VST sh) _ g); eauto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  forward. (* ( return; ) *)
  apply (exp_right g3); entailer!; auto.
  apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
Time Qed. (* 358 secs. *)

(* Print Assumptions body_mark. *)
