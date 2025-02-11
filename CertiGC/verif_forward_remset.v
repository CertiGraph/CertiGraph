Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import Coq.Program.Basics.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import VST.msl.wand_frame.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.

#[local] Open Scope logic.

Lemma body_forward_remset: semax_body Vprog Gprog f_forward_remset forward_remset_spec.
Proof.
  start_function.
  rename H into Hghc. rename H0 into Hoc. rename H1 into Hfrc. rename H2 into Hrpc.
  rename H3 into Hftneq. destruct Hfrc as [Hese [Hghgf [Hghgt [Hcc Hndd]]]].
  assert (Hgsc: generation_space_compatible g (from, nth_gen g from, nth_space h from)) by
    (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrf [Hshf Hsizef]].
  assert (Hgsc: generation_space_compatible g (to, nth_gen g to, nth_space h to)) by
    (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrt [Hsht Hsizet]].
  assert (Hptrf: isptr (space_start (nth_space h from))) by
    (rewrite <- Haddrf; apply start_isptr).
  assert (Hptrt: isptr (space_start (nth_space h to))) by
    (rewrite <- Haddrt; apply start_isptr).
  freeze [0; 1; 2; 4; 5] FR.
  assert (HS: forall gen, graph_has_gen g gen -> Z.of_nat gen < MAX_SPACES). {
    intros. eapply gen_range; eassumption. }
  assert (HMf: Z.of_nat from < MAX_SPACES) by (apply HS; assumption).
  assert (HMt: Z.of_nat to < MAX_SPACES) by (apply HS; assumption). clear HS.
  localize [space_struct_rep sh hp h from; space_struct_rep sh hp h to].
  unfold space_struct_rep, space_quad.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  gather_SEP (data_at sh space_type _ (space_address hp from))
    (data_at sh space_type _ (space_address hp to)).
  replace_SEP 0 (space_struct_rep sh hp h from * space_struct_rep sh hp h to) by
    (unfold space_struct_rep; entailer !!).
  unlocalize [heap_rep sh h hp]. 1: apply heap_rep_ramif_stable; assumption. clear HMf HMt.
  forward_if True.
  - entailer !!. rewrite !sameblock_offset_val by assumption. simpl. tauto.
  - forward. entailer !!.
  - change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
      with int_or_ptr_type in H.
    remember (space_start (nth_space h from)) as from_start.
    remember (space_start (nth_space h to)) as to_start.
    destruct from_start; inversion Hptrf. destruct to_start; inversion Hptrt.
    unfold sem_sub_pp in H. simpl in H. unfold eq_block. rewrite !peq_true in H.
    simpl in H. rewrite !(Ptrofs.add_commut i), !(Ptrofs.add_commut i0),
      !Ptrofs.sub_shifted, !ptrofs_sub_repr, !ptrofs_divs_repr in H. 3, 5: rep_lia.
    2: apply remset_space_signed_range. 2: apply rest_space_signed_range.
    rewrite <- !Z.mul_sub_distr_l, !(Z.mul_comm WORD_SIZE), !Z.quot_mul,
      !ptrofs_to_int64_repr in H; [| reflexivity | reflexivity | lia..].
    apply typed_false_of_bool in H. rewrite negb_false_iff in H. apply lt64_repr in H.
    2: apply rest_space_repable_signed. 2: apply remset_space_repable_signed.
    exfalso. unfold enough_space_enhanced in Hese. fold (rest_gen_size h to) in H.
    fold (remset_gen_size h from) in H. pose proof unmarked_gen_size_nonneg g from. lia.
  - Intros. thaw FR.
    forward_loop (EX n: Z, EX g': LGraph, EX h': heap, EX rh': remset_heap, EX rmst': remset,
                  PROP ((g', h', rh', rmst') = fold_left (forward_remset_item from to)
                        (sublist 0 n (nth from rh [])) (g, h, rh, rmst))
                  LOCAL (temp _q
                           (offset_val (WORD_SIZE * available_space (nth_space h' from))
                              (space_start (nth_space h' from)));
                         temp _from_rem_limit
                           (offset_val (WORD_SIZE * total_space (nth_space h' from))
                              (space_start (nth_space h' from)));
                         temp _from_limit
                           (offset_val (WORD_SIZE * available_space (nth_space h' from))
                              (space_start (nth_space h' from)));
                         temp _from_start (space_start (nth_space h from));
                         temp _from (space_address hp from);
                         temp _to (space_address hp to);
                         temp _next (heap_next_address hp to))
                  SEP (heap_rep sh h' hp; all_string_constants rsh gv; outlier_rep outlier;
                       graph_rep g'; heap_remset_rep g' h' rh'; remset_rep sh g' rmst')).
    + Exists 0 g h rh rmst. simpl fold_left. entailer !.
    + Intros n g' h' rh' rmst'. forward_if.
      * apply denote_tc_test_eq_split. unfold heap_remset_rep.

Abort.
