Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.GraphBi_Mark.
Require Import RamifyCoq.data_structure.spatial_graph_aligned_bi_VST.

Local Open Scope logic.

Notation graph sh x g := (@graph _ _ _ _ _ _ (@SGP pSGG_VST (sSGG_VST sh)) _ x g).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        EX g': @Graph pSGG_VST,
        PROP (mark x g g')
        LOCAL ()
        SEP   (`(graph sh x g')).

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
     SEP   (`(graph sh x g))).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return *)
    apply (exp_right g); entailer!.
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
(*
  assert (gl_weak_valid: weak_valid g l) by (eapply gamma_left_weak_valid; eauto).
  assert (gr_weak_valid: weak_valid g r) by (eapply gamma_right_weak_valid; eauto).
*)
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  (* root_mark = x -> m; *)

  unlocalize (PROP ()  LOCAL  (temp _root_mark (Vint (Int.repr (if d then 1 else 0))); temp _x (pointer_val_val x))  SEP  (`(graph sh x g))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!. rewrite (update_self g (ValidPointer b i) (d, l, r)) at 2 by auto.
    apply (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ (ValidPointer b i) (d, l, r) (d, l, r)); auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram.
  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (`(graph sh x g))).
  Focus 1. { (* if-then branch *)
    forward. (* return *)
    apply (exp_right g).
    entailer!.
    eapply (mark_vgamma_true_refl g); eauto.
    destruct d; [auto | inversion H0].
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    destruct d; congruence.
  } Unfocus.

  normalize.
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  (* l = x -> l; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | load_tac 
    | abbreviate_semax_ram].
  (* r = x -> r; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
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
    SEP (`(graph sh x (Graph_gen g x true)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite Graph_gen_spatial_spec by eauto.
    rewrite <- data_at_offset_zero.
    apply (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ x (false, l, r) (true, l, r)); auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)

  pose proof Graph_gen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
  forget (Graph_gen g x true) as g1.
(*
  assert (g1x_valid: vvalid g1 x) by (apply (proj1 (proj1 H0)); auto).
  assert (g1l_weak_valid: weak_valid g1 l) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).
  assert (g1r_weak_valid: weak_valid g1 r) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).
*)
  localize
   (PROP  (weak_valid g1 l)
    LOCAL (temp _l (pointer_val_val l))
    SEP   (`(graph sh l g1))).
  (* localize *)
  
  rewrite <- ram_seq_assoc.
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | normalize; forward_call (sh, g1, l) g2; apply derives_refl
  | abbreviate_semax_ram].

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`((EX g2: Graph, !! mark l g1 g2 && graph sh x g2)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer.
    rewrite !exp_emp.
    apply andp_right; [apply prop_right |].
    + eapply left_weak_valid; eauto.
    + eapply (@graph_ramify_aux1_left _ (sSGG_VST sh) g1); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  normalize; intros g2; normalize.
  assert (g2x_valid: vvalid g2 x) by (apply (proj1 (proj1 H2)); auto).
  assert (g2r_weak_valid: weak_valid g2 r) by (apply (weak_valid_si g1 g2 _ (proj1 H2)); auto).

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
    eapply (@graph_ramify_aux1_right _ (sSGG_VST sh) g2); eauto.
    eapply gamma_true_mark; eauto.
    apply weak_valid_vvalid_dec; auto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  forward. (* ( return; ) *)
  apply (exp_right g3); entailer!.
  apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
  eapply gamma_true_mark; eauto.
  apply weak_valid_vvalid_dec; auto.
Time Qed. (* Takes 3 hours. *)
