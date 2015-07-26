Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.sample_mark.env_mark.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_mark.
Require Import RamifyCoq.data_structure.spatial_graph_VST.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.
Notation graph sh x g := (@graph _ _ _ _ _ _ (SGP_VST sh) x g).
Existing Instances MGS biGraph maGraph finGraph.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        EX g': Graph, 
        PROP (mark g x g')
        LOCAL()
        SEP (`(graph sh x g')).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_hd, tptr (Tstruct _Node noattr))::(_n, (Tstruct _Node noattr))::nil.

Definition Gprog : funspecs := mark_spec :: main_spec::nil.

Lemma destruct_pointer_val_VP: forall x,
  pointer_val_val x <> nullval \/
  isptr (pointer_val_val x) ->
  isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  split; simpl; auto.
  exists b, i; auto.
Qed.

Lemma destruct_pointer_val_NP: forall x,
  pointer_val_val x = nullval \/
  ~ isptr (pointer_val_val x) ->
  x = NullPointer.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  inversion H; try tauto.
  inversion H0.
Qed.

Ltac destruct_pointer_val x :=
  first [
    let H := fresh "H" in
    assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i) by (apply (destruct_pointer_val_VP x); tauto);
    destruct H as [?H [?b [?i ?H]]]
  | assert (x = NullPointer) by (apply (destruct_pointer_val_NP x); tauto)].

Ltac ram_simplify_Delta :=
  match goal with
  | |- semax_ram ?D _ _ _ _ => simplify_Delta_at D
  | _ => idtac
  end.

Ltac clear_RamFrame_abbr :=
  repeat match goal with
             | H := @abbreviate (list SingleFrame) _ |- _ => 
                        unfold H, abbreviate; clear H 
             | H := _: @SingleFrame' _ _ _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.
  
Ltac abbreviate_RamFrame_rec F RamFrame :=
  match F with
  | nil => idtac
  | RAM_FRAME.Build_SingleFrame ?l ?g ?s ?f :: ?F_tail =>
      abbreviate_RamFrame_rec F_tail RamFrame;
      let RamFrame0 := fresh "RamFrame" in
      set (RamFrame0 := f) in RamFrame;
      try change @RAM_FRAME.SingleFrame' with @SingleFrame' in RamFrame0
  end.

Ltac abbreviate_RamFrame :=
  clear_RamFrame_abbr;
  match goal with
  | |- semax_ram _ ?F _ _ _ =>
         let RamFrame := fresh "RamFrame" in
         set (RamFrame := @abbreviate (list SingleFrame) F);
         replace F with RamFrame by reflexivity;
         abbreviate_RamFrame_rec F RamFrame
  end.

Ltac abbreviate_semax_ram :=
  match goal with
  | |- semax_ram _ _ _ _ _ =>
         ram_simplify_Delta; unfold_abbrev';
         match goal with |- semax_ram ?D _ _ ?C ?P => 
            abbreviate D : tycontext as Delta;
            abbreviate P : ret_assert as POSTCONDITION ;
            match C with
            | Ssequence ?C1 ?C2 =>
               (* use the next 3 lines instead of "abbreviate"
                  in case C1 contains an instance of C2 *)
                let MC := fresh "MORE_COMMANDS" in
                pose (MC := @abbreviate _ C2);
                change C with (Ssequence C1 MC);
                match C1 with
                | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                | _ => idtac
                end
            | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
            | _ => idtac
            end
        end
  end;
  abbreviate_RamFrame;
  clear_abbrevs;
  simpl typeof.

Ltac solve_split_by_closed :=
  repeat first
    [ apply split_by_closed_nil
    | apply split_by_closed_cons_closed; solve [repeat constructor; auto with closed]
    | apply split_by_closed_cons_unclosed].

Ltac localize P :=
  match goal with
  | |- semax ?Delta ?Pre ?c ?Post =>
         change (semax Delta Pre c Post) with (semax_ram Delta nil Pre c Post);
         abbreviate_RamFrame
  | |- semax_ram ?Delta _ ?Pre ?c ?Post => idtac
  end;
  match goal with
  | RamFrame := @abbreviate (list SingleFrame) ?F |-
    semax_ram ?Delta _ ?Pre ?c ?Post =>
         apply semax_ram_localize with P; eexists;
         abbreviate_RamFrame
  end.

Ltac unlocalize Pre' :=
  match goal with
  | RamFrame := @abbreviate _ (RAM_FRAME.Build_SingleFrame ?l ?g ?s _ :: ?F) |-
    semax_ram ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c ?Ret =>
    clear_RamFrame_abbr;
    match Pre' with
    | PROPx ?P' (LOCALx ?Q' (SEPx ?R')) =>
        eapply (fun Q1' Q2' => semax_ram_unlocalize_PROP_LOCAL_SEP Delta l g s F P Q R c Ret P' Q' Q1' Q2' R'); gather_current_goal_with_evar
    end
  end.

Lemma pointer_val_val_is_pointer_or_null: forall x,
  is_pointer_or_null (pointer_val_val x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Hint Resolve pointer_val_val_is_pointer_or_null.
(*
Ltac rewrite_vi_graph g1 g2 H :=
  let HH := fresh "H" in
  assert (g1 -=- g2) as HH; [eapply H |
    match goal with
    | |- appcontext [graph ?sh ?x g1] =>
           change (graph sh x g1) with (@spatial_graph2.graph (SGA_VST sh) x g1);
           erewrite (fun x => @reachable_vi_eq (SGA_VST _) g1 g2 x HH);
           change (@spatial_graph2.graph (SGA_VST sh) x g2) with (graph sh x g2)
    end].
*)
Lemma body_mark: semax_body Vprog Gprog f_mark mark_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H1 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H0 into H_weak_valid.

  forward_if_tac  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (`(graph sh x g))).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return *)
    pose proof mark_invalid_refl g NullPointer.
    spec H1;
    [pose proof valid_not_null g NullPointer; rewrite is_null_def in H2; intro; apply H2; auto; congruence |].
    apply (exp_right g); entailer!.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
  } Unfocus.
  normalize.
  assert (vvalid g x) as gx_vvalid.
  Focus 1. {
    destruct H_weak_valid; [| auto].
    rewrite is_null_def in H1; subst x.
    exfalso.
    apply H0. auto.
  } Unfocus.
  destruct_pointer_val x. clear H1 H_weak_valid.
  assert (gl_weak_valid: weak_valid g l) by (eapply gamma_left_weak_valid; eauto).
  assert (gr_weak_valid: weak_valid g r) by (eapply gamma_right_weak_valid; eauto).

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro root_mark_old; autorewrite with subst; clear root_mark_old.
  (* root_mark = x -> m; *)

  unlocalize (PROP ()  LOCAL  (temp _root_mark (Vint (Int.repr (if d then 1 else 0))); temp _x (pointer_val_val x))  SEP  (`(graph sh x g))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. { entailer!. apply (@graph_ramify_aux0 (SGA_VST sh) g x d l r); auto. } Unfocus.
  (* unlocalize *)

  unfold semax_ram.
  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (`(graph sh x g))).
  Focus 1. { (* if-then branch *)
    forward. (* return *)
    rewrite_vi_graph g g' @mark_marked_root; [| eauto |].
    + clear - H1 H_GAMMA_g.
      unfold gamma in H_GAMMA_g.
      destruct d; [| inversion H1].
      destruct (node_pred_dec (marked g) (ValidPointer b i)); [| inversion H_GAMMA_g].
      auto.
    + auto.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    destruct d; congruence.
  } Unfocus.

  normalize.
  subst d.
  destruct (@mark1_exists (SGA_VST sh) g x gx_vvalid) as [g1 ?H].
  assert (g1x_valid: vvalid g1 x) by (apply (proj1 (proj1 H1)); auto).
  assert (g1l_weak_valid: weak_valid g1 l) by (apply (weak_valid_si g g1 _ (proj1 H1)); auto).
  assert (g1r_weak_valid: weak_valid g1 r) by (apply (weak_valid_si g g1 _ (proj1 H1)); auto).
  assert (H_GAMMA_g1: gamma g1 x = (true, l, r)) by (apply gamma_marks with g; auto).

  destruct (mark_exists' g1 l g1l_weak_valid) as [g2 ?H].
  assert (g2x_valid: vvalid g2 x) by (apply (proj1 (proj1 H4)); auto).
  assert (g2r_weak_valid: weak_valid g2 r) by (apply (weak_valid_si g1 g2 _ (proj1 H4)); auto).
  
  destruct (mark_exists' g2 r g2r_weak_valid) as [g3 ?H].

  assert (g3 -=- g').
  Focus 1. {
    apply mark1_mark_list_vi with g x (l :: r :: nil) g1.
    + intros.
      destruct (Coqlib.t_eq_dec r x0); [| destruct (Coqlib.t_eq_dec l x0)]; [| | simpl in H6; exfalso; tauto]; subst x0.
      - intro; apply reachable_by_decidable; simpl; auto with GraphLib.
      - intro; apply reachable_by_decidable; simpl; auto with GraphLib.
    + intros.
      destruct (Coqlib.t_eq_dec r x0); [| destruct (Coqlib.t_eq_dec l x0)]; [| | simpl in H6; exfalso; tauto]; subst x0; unfold Decidable; auto with GraphLib.
    + intro; apply reachable_by_decidable; simpl; auto with GraphLib.
    + auto.
    + unfold gamma in H_GAMMA_g.
      destruct (node_pred_dec (marked g) x); try solve [inversion H_GAMMA_g].
      rewrite unmarked_spec; auto.
    + unfold gamma in H_GAMMA_g; inversion H_GAMMA_g; subst.
      unfold step_list.
      intros; simpl.
      rewrite biEdge_only2; [| auto | reflexivity].
      rewrite !(eq_sym_iff n').
      tauto.
    + auto.
    + apply mark_list_cons with g2; auto.
      apply mark_list_cons with g3; auto.
      constructor.
    + auto.
  } Unfocus.

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro l_old; autorewrite with subst; clear l_old.
  (* l = x -> l; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro r_old; autorewrite with subst; clear r_old.
  (* r = x -> r; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_store_tac
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs CS_legal sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs CS_legal sh node_type
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))).
  (* x -> d = 1; *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(graph sh x g1))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    change (@data_at CompSpecs CS_legal sh node_type
            (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
            (pointer_val_val x)) with 
           (@spatial_graph2.trinode (SGA_VST sh) x (false, l, r)).
    change (@data_at CompSpecs CS_legal sh node_type
            (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))
            (pointer_val_val x)) with 
           (@spatial_graph2.trinode (SGA_VST sh) x (true, l, r)).
    rewrite <- H_GAMMA_g, <- H_GAMMA_g1.
    apply (@graph_ramify_aux1 (SGA_VST sh) g g1).
    auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)

  localize
   (PROP  ()
    LOCAL (temp _l (pointer_val_val l))
    SEP   (`(graph sh l g1))).
  (* localize *)
  
  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call' (sh, g1, g2, l); apply derives_refl
  | abbreviate_semax_ram].
  (* mark(l); *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(graph sh x g2))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    apply (@graph_ramify_aux2 (SGA_VST sh) g1 g2); auto.
    eapply gamma_left_reachable_included; eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  localize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r))
    SEP   (`(graph sh r g2))).
  (* localize *)
  
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call' (sh, g2, g3, r); apply derives_refl
  | abbreviate_semax_ram].
  (* mark(r); *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(graph sh x g3))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    apply (@graph_ramify_aux2 (SGA_VST sh) g2 g3); auto.
    rewrite <- !(Extensionality_Ensembles _ _ _ (reachable_ind.si_reachable _ _ _ (proj1 H4))).
    simpl.
    eapply (gamma_right_reachable_included g1 _ _ _ _ g1x_valid H_GAMMA_g1); eauto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  rewrite_vi_graph g3 g' H6.
  forward. (* ( return; ) *)
Time Qed. (* Takes 30 minuts. *)
