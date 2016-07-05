Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Export VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_copy_bi.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.local_graph_copy.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.Graph_Copy.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.GraphBi_Copy.
Require Import RamifyCoq.sample_mark.spatial_graph_bi_copy.

Local Open Scope logic.

Hint Rewrite eval_cast_neutral_is_pointer_or_null using auto : norm. (* TODO: should not need this *)

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation graph sh x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ _ (@SGP pSGG_VST addr (addr * LR) (sSGG_VST sh)) _ x g).
Notation holegraph sh x g := (@vertices_at _ _ _ _ _ _ (@SGP pSGG_VST addr (addr * LR) (sSGG_VST sh)) _ (Ensembles.Intersection _ (@vvalid addr (addr * LR) _ _ g) (fun u => x <> u)) (LGraph_SGraph g)).
Notation Graph := (@Graph pSGG_VST (@addr pSGG_VST) (addr * LR)).
Notation vmap := (@LocalGraphCopy.vmap addr (addr * LR) addr (addr * LR) _ _ _ _ _ _ (@GMS _ _ CCS)).
Existing Instances MGS biGraph maGraph finGraph RGF.

(*
Definition natural_alignment := 8.

Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs) /\
                           Int.unsigned ofs + n < Int.modulus
  | _ => False
  end.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned) 
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: val,
     PROP (malloc_compatible n v) 
     LOCAL (temp ret_temp v) 
     SEP (memory_block Tsh n v).
*)

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh: wshare
  PRE [ 1%positive OF tint]
     PROP () 
     LOCAL (temp 1%positive (Vint (Int.repr 16)))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: addr,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val v)) 
     SEP (data_at sh node_type (pointer_val_val null, (pointer_val_val null, pointer_val_val null))
              (pointer_val_val v)).

Definition copy_spec :=
 DECLARE _copy
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (graph sh x g)
  POST [ (tptr (Tstruct _Node noattr)) ]
        EX xgg: pointer_val * Graph * Graph,
        let x' := fst (fst xgg) in
        let g1 := snd (fst xgg) in
        let g1' := snd xgg in
        PROP (copy (x: addr) g g1 g1'; x = null /\ x' = null \/ x' = vmap g1 x)
        LOCAL (temp ret_temp (pointer_val_val x'))
        SEP   (graph sh x g1; graph sh x' g1').

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_x, tptr (Tstruct _Node noattr))::(_y, tptr (Tstruct _Node noattr))::(_n, (Tstruct _Node noattr))::nil.

Definition Gprog : funspecs := copy_spec :: mallocN_spec :: main_spec::nil.

Lemma body_mark: semax_body Vprog Gprog f_copy copy_spec.
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
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return 0; *)
    apply (exp_right ((NullPointer, g), empty_Graph)).
    simpl.
    entailer!; auto.
    + apply (copy_null_refl g).
    + rewrite va_reachable_invalid; auto.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
  } Unfocus.
  normalize.
  assert (vvalid g x) as gx_vvalid.
  Focus 1. {
    destruct H_weak_valid; [| auto].
    simpl in H0.
    subst; exfalso; apply H. auto.
  } Unfocus.
  destruct_pointer_val x. clear H0 H_weak_valid.

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (data_at sh node_type (pointer_val_val d, (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x))).
  (* localize *)

  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* x0 = x -> m; *)

  unlocalize (PROP ()  LOCAL  (temp _x0 (pointer_val_val d); temp _x (pointer_val_val x))  SEP  (graph sh x g)).

  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@root_stable_ramify _ (sSGG_VST sh) g x _ H_GAMMA_g); auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram.
  forward_if_tac  (* if (x0 != 0) *)
    (PROP   (d = null)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (graph sh x g)).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    forward. (* return x0; *)
    apply (exp_right (d, g, empty_Graph)).
    simpl.
    entailer!; auto.
    split.
    + eapply (copy_vgamma_not_null_refl g); eauto.
      clear - H0.
      destruct d; [change null with (NullPointer) | simpl in H0; change nullval with (Vint Int.zero) in H0]; try congruence.
    + right.
      inversion H_GAMMA_g; auto.
    + rewrite va_reachable_invalid; auto.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    clear - H0. destruct d; inversion H0. auto.
  } Unfocus.

  Intros.
  subst d.
  forward_call sh. (* x0 = (struct Node * ) mallocN (sizeof (struct Node)); *)

  Intros x0.
  assert_PROP (x0 <> null) as x0_not_null. entailer!. destruct H3 as [? _]. apply H1.

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x); temp _x0 (pointer_val_val x0))
    SEP   (data_at sh node_type (pointer_val_val null, (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x))).
  (* localize *)

  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* l = x -> l; *)

  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac
    | abbreviate_semax_ram].
  (* r = x -> r; *)

  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | store_tac
    | abbreviate_semax_ram].

  autorewrite with norm. (* TODO: should not need this *)
  change (@field_at CompSpecs sh node_type []
           (pointer_val_val x0, (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs sh node_type
           (pointer_val_val x0, (pointer_val_val l, pointer_val_val r))).

  (* x -> m = x0; *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x);
           temp _x0 (pointer_val_val x0))
    SEP (data_at sh node_type
           (pointer_val_val null, (pointer_val_val null, pointer_val_val null))
           (pointer_val_val x0);
         holegraph sh x0 (initial_copied_Graph x x0 g);
         graph sh x (Graph_vgen g x x0))).
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    apply (@root_update_ramify _ (sSGG_VST sh) g x x0 _ (null, l, r) (x0, l, r)); auto.
    eapply Graph_vgen_vgamma; eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)

  destruct (not_null_copy1 g x x0 _ _ H_GAMMA_g gx_vvalid x0_not_null) as [H_vopy1 [H_x0 BiMaFin_g1']].
  forget (Graph_vgen g x x0) as g1.
  forget (initial_copied_Graph x x0 g) as g1'.

  forward. (* x0 -> m = 0; *)

  localize
   (PROP  (weak_valid g1 l)
    LOCAL (temp _l (pointer_val_val l))
    SEP   (graph sh l g1)).
  1: eapply left_weak_valid; eauto.  
  (* localize *)

  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g1, l)
  | semax_ram_after_call; intros [[l0 g2] g2''];
    repeat (apply ram_extract_PROP; intro) ].

  (* l0 = copy(l); *)

  rename H2 into H_copy, H3 into H_l0.
  cbv [fst snd] in H_copy, H_l0 |- *.
  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _l0 (pointer_val_val l0);
           temp _x (pointer_val_val x);
           temp _x0 (pointer_val_val x0))
    SEP (data_at sh node_type (Vint (Int.repr 0), (pointer_val_val null, pointer_val_val null)) (pointer_val_val x0);
         holegraph sh x0 g1';
         graph sh x g2;
         graph sh l0 g2''))
  using [H_copy; H_l0]%RamAssu
  binding [l0; g2; g2'']%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    eapply (@graph_ramify_left _ (sSGG_VST sh) RamUnit g); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  gather_SEP 0 1 3.
  replace_SEP 0
      (EX g2': LGraph,
       !! (extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') /\
           is_guarded_BiMaFin (fun v => x0 <> v) (fun e => ~ In e nil) g2') &&
          (data_at sh node_type
            (pointer_val_val null, (pointer_val_val null, pointer_val_val null)) (pointer_val_val x0) *
           holegraph sh x0 g2')).
  Focus 1. {
    entailer.
    apply (@extend_copy_left _ (sSGG_VST sh) g g1 g2 g1' g2'' (ValidPointer b i) l r (vmap g1 (ValidPointer b i)) l0 (null, null, null)); auto.
  } Unfocus.
  Opaque extended_copy.
  rewrite extract_exists_in_SEP. (* should be able to use tactic directly *)
  Transparent extended_copy.
  clear g2'' H_copy BiMaFin_g1'.
  Intros g2'. rename H2 into H_copy_left, H3 into BiMaFin_g2'.

  forward. (* x0 -> l = l0; *)
  autorewrite with norm. (* TODO: should not need this *)

  rewrite (va_labeledgraph_add_edge_left g g1 g2 g1' g2' x l r x0 l0) by auto.
  rewrite (va_labeledgraph_egen_left g2 x x0).
  destruct (labeledgraph_add_edge_ecopy1_left g g1 g2 g1' g2' x l r x0 l0 gx_vvalid H_GAMMA_g H_vopy1 H_copy_left H_x0 H_l0 BiMaFin_g2' x0_not_null) as [H_ecopy1_left [BiMaFin_g3' H_x0L]].
  clear BiMaFin_g2'.
  forget (Graph_egen g2 (x: addr, L) (x0: addr, L)) as g3.
  forget (graph_gen.labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L)) as g3'.

  normalize.
  localize
   (PROP  (weak_valid g3 r)
    LOCAL (temp _r (pointer_val_val r))
    SEP   (graph sh r g3)).
  1: eapply right_weak_valid; eauto.  
  (* localize *)

  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | semax_ram_call_body (sh, g3, r)
  | semax_ram_after_call; intros [[r0 g4] g4''];
    repeat (apply ram_extract_PROP; intro) ].
  (* r0 = copy(r); *)

  rename H3 into H_copy, H4 into H_r0.
  cbv [fst snd] in H_copy, H_r0 |- *.
  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _r0 (pointer_val_val r0);
           temp _x (pointer_val_val x);
           temp _x0 (pointer_val_val x0))
    SEP (data_at sh node_type
          (Vint (Int.repr 0), (pointer_val_val l0, pointer_val_val null))
          (pointer_val_val x0);
         holegraph sh x0 g3';
         graph sh x g4; graph sh r0 g4''))
  using [H_copy; H_r0]%RamAssu
  binding [r0; g4; g4'']%RamBind.
  Grab Existential Variables.
  Focus 2. {
    simplify_ramif.
    eapply (@graph_ramify_right _ (sSGG_VST sh) RamUnit g); eauto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram. (* should not need this *)
  gather_SEP 0 1 3.
  replace_SEP 0
      (EX g4': LGraph,
       !! (extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') /\
           is_guarded_BiMaFin (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g4') &&
          (data_at sh node_type
            (pointer_val_val null, (pointer_val_val l0, pointer_val_val null)) (pointer_val_val x0) *
           holegraph sh x0 g4')).
  Focus 1. {
    entailer.
    apply (@extend_copy_right _ (sSGG_VST sh) g g1 g2 g3 g4 g1' g2' g3' g4''(ValidPointer b i) l r (vmap g1 (ValidPointer b i)) r0 (null, l0, null)); auto.
  } Unfocus.
  Opaque extended_copy.
  rewrite extract_exists_in_SEP. (* should be able to use tactic directly *)
  Transparent extended_copy.
  clear g4'' H_copy BiMaFin_g3'.
  Intros g4'. rename H3 into H_copy_right, H4 into BiMaFin_g4'.

  forward. (* x0 -> r = r0; *)
  autorewrite with norm. (* TODO: should not need this *)

  rewrite (va_labeledgraph_add_edge_right g g1 g2 g3 g4 g1' g2' g3' g4' x l r x0 r0) by auto.
  rewrite (va_labeledgraph_egen_right g4 x x0).
  destruct (labeledgraph_add_edge_ecopy1_right g g1 g2 g3 g4 g1' g2' g3' g4' x l r x0 r0 gx_vvalid H_GAMMA_g H_vopy1 H_copy_left H_ecopy1_left H_copy_right H_x0 H_x0L H_r0 BiMaFin_g4' x0_not_null) as [H_ecopy1_right [BiMaFin_g5' H_x0R]].
  clear BiMaFin_g4'.
  forget (Graph_egen g4 (x: addr, R) (x0: addr, R)) as g5.
  forget (graph_gen.labeledgraph_add_edge g4' (x0, R) x0 r0 (null, L)) as g5'.

  gather_SEP 0 1.
  replace_SEP 0 (EX gg5': Graph, !! (@copy _ _ _ CCS x g g5 gg5' /\ x0 = vmap g5 x) && graph sh x0 gg5').
  Focus 1. {
    entailer!.
    eapply (@copy_final pSGG_VST (sSGG_VST sh) g g1 g2 g3 g4 g5 g1' g2' g3' g4' g5'); [| | | | | | | | eassumption ..]; eauto.
  } Unfocus.

  forward. (* return x0; *)
  rewrite H7.
  apply (exp_right (vlabel g5 (ValidPointer b i), g5, gg5')); entailer!; auto. cancel.
  apply derives_refl.
Time Qed. (* Takes 9575 seconds. *)
