Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import Stdlib.Program.Basics.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import VST.msl.wand_frame.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.forward_lemmas.

#[local] Opaque Int64.repr.
#[local] Opaque lgraph_copy_v.

#[local] Open Scope logic.

Lemma body_forward_intr:
  forall (Espec : OracleKind)
    (rsh sh : share)
    (gv : globals)
    (g : LGraph)
    (h : part_heap)
    (hp : val)
    (outlier : outlier_t)
    (from to : nat)
    (depth : Z)
    (intr : interior_t)
    (SHr : readable_share rsh)
    (SHw : writable_share sh)
    (Hghc : graph_heap_compatible g h)
    (Hoc : outlier_compatible g outlier)
    (Hfpc : forward_p_compatible (FwdPntIntr intr) outlier g from)
    (Hfc : forward_condition g h from to)
    (Hdep : 0 <= depth <= Int.max_signed)
    (Hft : from <> to),
    semax (func_tycontext f_forward Vprog Gprog [])
      (PROP ( )
         LOCAL (temp _from_start (gen_start g from);
                temp _from_limit (limit_address g h from);
                temp _next (heap_next_address hp to); temp _p (interior_address intr g);
                temp _depth (Vint (Int.repr depth)))
         SEP (all_string_constants rsh gv; outlier_rep outlier;
              graph_rep g; heap_rep sh h hp)) (fn_body f_forward)
      (normal_ret_assert
         ((EX (g' : LGraph) (h' : part_heap),
            PROP ((g', h') =
                    forward_graph_and_heap from to (Z.to_nat depth)
                      (forward_p2forward_t (FwdPntIntr intr) g) g h)
              RETURN ( ) SEP (all_string_constants rsh gv; outlier_rep outlier;
                              forward_p_rep sh (upd_fwd from to g (FwdPntIntr intr)) None g';
                              graph_rep g'; heap_rep sh h' hp))%argsassert *
            stackframe_of f_forward)).
Proof.
  intros. simpl fn_body. abbreviate_semax. destruct Hfc as [Hesto [Hfrom [Hto [Hcp Hnodg]]]].
  destruct intr as [v n]. simpl in Hfpc.
  unfold limit_address, heap_next_address, interior_address.
  destruct Hfpc as [Hhv [Hn [Hrm [SCAN Hvnf]]]]. freeze [0; 1; 3] FR.
  localize [vertex_rep (nth_sh g (vgeneration v)) g v].
  unfold vertex_rep, vertex_at. Intros.
  assert_PROP (offset_val (WORD_SIZE * n) (vertex_address g v) =
                 field_address (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
                   [ArraySubsc n] (vertex_address g v)) as Hofse. {
    entailer !. unfold field_address. rewrite if_true; [simpl; f_equal|]. clear -H5 Hn.
    rewrite <- fields_eq_length in Hn. unfold field_compatible in *; simpl in *. easy. }
  assert (Hsv: readable_share (nth_sh g (vgeneration v))) by
    apply writable_readable, generation_share_writable.
  assert (Hipi: is_pointer_or_integer (Znth n (make_fields_vals g v))). {
    pose proof mfv_all_is_ptr_or_int g v Hcp Hnodg Hhv as Ha. rewrite Forall_forall in Ha.
    apply Ha, Znth_In. rewrite fields_eq_length. assumption. } forward.
  gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
  replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v) by
    (unfold vertex_rep, vertex_at; entailer !!).
  unlocalize [graph_rep g]. 1: apply graph_vertex_ramif_stable; assumption. thaw FR.
  gather_SEP (graph_rep _) (outlier_rep _).
  sep_apply (intr_valid_int_or_ptr g outlier from v n). 1: red; easy. Intros.
  rename H into Hvintr. remember (Znth n (make_fields_vals g v)) as vn.
  unfold make_fields_vals in Heqvn.
  rewrite Hrm, Znth_map in Heqvn; [|rewrite make_fields_eq_length; assumption].
  forward_call vn.
  remember (graph_rep g * heap_unused_rep h * outlier_rep outlier) as P.
  remember (gen_start g from) as fp. remember (nth_sh g from) as fsh.
  remember (available_size h from) as gn. remember (WORD_SIZE * gn)%Z as fn.
  assert (Pweak: P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
    apply weak_derives_strong. subst. sep_apply (graph_and_heap_rest_data_at_ g h from).
    unfold generation_data_at_. rewrite data_at__memory_block, sizeof_tarray_int_or_ptr;
      [Intros; cancel | unfold available_size].
    destruct (available_space_tight_range (nth_space h from)). assumption. } subst vn.
  destruct (Znth n (make_fields g v)) as [z | gc | e] eqn:?; unfold field2val.
  (* Unboxed z | Outlier | Edge *)
  - (* Unboxed z *)
    unfold odd_Z2val. rewrite if_true by auto. forward_if. 1: exfalso; contradiction.
    forward. Exists g h. entailer !!. simpl. rewrite Heqf. simpl.
    rewrite fwd_graph_heap_unfold. reflexivity.
  - (* Outlier *)
    destruct gc as [b i]. unfold GC_Pointer2val. forward_if. 2: discriminate.
    forward_call (Vptr b i). unfold heap_rep; Intros.
    gather_SEP (graph_rep _) (heap_unused_rep _) (outlier_rep _). rewrite <- HeqP.
    replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
      (entailer; assumption). Intros.
    assert (HGC: In (GCPtr b i) outlier) by (eapply in_gcptr_outlier; eauto).
    assert (Hweakp: P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
      subst; cancel; apply andp_right; [|cancel].
      assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS. apply derives_weak.
      sep_apply (outlier_rep_valid_pointer outlier (GCPtr b i) HGC).
      simpl GC_Pointer2val. cancel. }
    replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
      (entailer; assumption). Intros. clear Hweakp.
    forward_call (fsh, fp, fn, (Vptr b i), P).
    Intros vret. destruct vret as [Hyes | Hno]. (* is_from? *)
    + (* yes *)
      rewrite HeqP. Intros.
      gather_SEP (graph_rep g) (heap_unused_rep _) (outlier_rep _).
      change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in Hyes.
      rewrite Heqfp, Heqfn, Heqgn in Hyes.
      sep_apply (graph_heap_outlier_FF g h outlier from (GCPtr b i)).
      assert_PROP False by entailer !. contradiction.
    + (* no *)
      forward_if. 1: contradiction. rewrite HeqP. Intros. forward. Exists g h.
      simpl forward_p2forward_t. rewrite Heqf. simpl field2forward.
      rewrite fwd_graph_heap_unfold. unfold heap_rep. entailer !!.
  - (* Edge *)
    assert (Hein: In e (get_edges g v)) by
      (rewrite get_edges_In_iff, <- Heqf; apply Znth_In; now rewrite make_fields_eq_length).
    assert (Hhe: graph_has_e g e). {
      pose proof get_edges_fst g v e Hein as Hfst. split; rewrite Hfst; assumption. }
    simpl field2val in *. remember (dst g e) as v'.
    assert (Hhv': graph_has_v g v') by (subst v'; red in Hnodg; eapply Hnodg; eassumption).
    pose proof graph_has_v_addr_isptr _ _ Hhv' as Hisptr.
    destruct (vertex_address g v') eqn: Heqav'; try contradiction.
    forward_if. 2: discriminate. clear H H'. forward_call (Vptr b i).
    unfold heap_rep; Intros. gather_SEP (graph_rep _) (heap_unused_rep _) (outlier_rep _).
    rewrite <- HeqP. rewrite <- Heqav' in *.
    replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
      (entailer; assumption). clear Pweak. Intros.
    assert (P |-- (weak_derives P (valid_pointer (vertex_address g v') * TT) && emp) * P)
      as Pweak. { apply weak_derives_strong. subst P.
                  sep_apply (graph_rep_valid_pointer g v'). cancel. }
    replace_SEP 1 (weak_derives P (valid_pointer (vertex_address g v') * TT) && emp * P)
      by entailer!!. clear Pweak. Intros.
    forward_call (fsh, fp, fn, (vertex_address g v'), P).
    (* is_from *)
    Intros vret. rewrite HeqP.
    sep_apply (graph_and_heap_rest_v_in_range_iff g h from v'). Intros. rename H into Hviff.
    rewrite <- Heqfp, <- Heqgn, <- Heqfn in Hviff. destruct vret as [Hvv | Hvv].
    + (* yes, is_from *)
      rewrite Hviff in Hvv. clear Hviff. forward_if. 2: discriminate. clear H H'.
      freeze [1; 2; 3; 4] FR.
      localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
      unfold vertex_rep, vertex_at. Intros. rewrite Hvv.
      assert (readable_share (nth_sh g from)) by
        (unfold nth_sh; apply writable_readable, generation_share_writable).
      sep_apply (data_at_minus1_address(nth_sh g from) (Z2val (make_header g v')) (
                     vertex_address g v')). Intros.
      forward. clear H0.
      gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v')) g v') by
        (unfold vertex_rep, vertex_at; entailer !!).
      unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ Hhv').
      pose proof make_header_int_rep_mark_iff g v' as Hiff. simpl in Hiff.
      forward_if.
      * (* yes, already forwarded *)
        rewrite Hiff in H0. clear Hiff. rename H0 into Hrm'.
        localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
        rewrite Hvv. unfold vertex_rep, vertex_at. Intros.
        unfold make_fields_vals at 2. rewrite Hrm'.
        assert (Hrg: 0 <= 0 < Zlength (make_fields_vals g v')). {
          split. 1: lia. rewrite fields_eq_length.
          apply (proj1 (raw_fields_range (vlabel g v'))). }
        assert (Hipic: is_pointer_or_integer
                         (vertex_address g (copied_vertex (vlabel g v')))). {
          apply isptr_is_pointer_or_integer. unfold vertex_address.
          rewrite isptr_offset_val. apply graph_has_gen_start_isptr, Hcp; assumption. }
        forward. rewrite Znth_0_cons.
        gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v')) g v'). {
          unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
          rewrite Hrm'. entailer !!. }
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ Hhv').
        localize [vertex_rep (nth_sh g (vgeneration v)) g v].
        unfold vertex_rep, vertex_at. Intros.
        assert (writable_share (nth_sh g (vgeneration v))) by
          (unfold nth_sh; apply generation_share_writable).
        forward. sep_apply field_at_data_at_cancel.
        gather_SEP (data_at _ _ _ _ ) (data_at _ _ _ _).
        remember (copied_vertex (vlabel g v')) as cv.
        remember (labeledgraph_gen_dst g e cv) as g'.
        replace_SEP 0 (vertex_rep (nth_sh g' (vgeneration v)) g' v).
        1: { unfold vertex_rep, vertex_at. replace (nth_sh g' (vgeneration v)) with
            (nth_sh g (vgeneration v)) by (subst g'; reflexivity).
             replace (Zlength (make_fields_vals g' v)) with (Zlength (make_fields_vals g v))
               by (subst g'; repeat rewrite fields_eq_length; apply lgd_raw_fld_length_eq).
             rewrite (lgd_mfv_change_in_one_spot g v e cv n);
               [|rewrite make_fields_eq_length| | ]; try assumption. entailer !!. }
        subst g' cv.
        unlocalize [graph_rep (labeledgraph_gen_dst g e
                                 (copied_vertex (vlabel g v')))].
        1: apply (graph_vertex_lgd_ramif g v e (copied_vertex (vlabel g v')) n);
        try (rewrite make_fields_eq_length); assumption.
        Exists (labeledgraph_gen_dst g e (copied_vertex (vlabel g (dst g e)))) h.
        simpl forward_p2forward_t. rewrite Heqf. simpl field2forward. simpl forward_p_rep.
        rewrite fwd_graph_heap_unfold. subst v'. rewrite if_true by assumption.
        rewrite Hrm'. thaw FR. unfold heap_rep. entailer !!.
      * (* not yet forwarded *)
        forward. thaw FR. freeze [0; 1; 2; 3] FR. rename H0 into Hrm'.
        rewrite Hiff in Hrm'. clear Hiff. apply not_true_is_false in Hrm'.
        rewrite make_header_Wosize by assumption.
        pose proof gen_range _ _ _ Hghc Hto as Htrange. unfold heap_struct_rep.
        destruct (gt_gs_compatible _ _ Hghc _ Hto) as [Has [Hgen Hpre]].
        rewrite nth_space_Znth in *. remember (Znth (Z.of_nat to) (spaces h)) as sp_to.
        assert (Hss: isptr (space_start sp_to)) by (rewrite <- Has; apply start_isptr).
        remember (map space_quad (spaces h)) as l.
        assert (Hst: @Znth (val * (val * (val* val))) (Vundef, (Vundef, (Vundef, Vundef)))
                       (Z.of_nat to) l = space_quad sp_to). {
          subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_lia). reflexivity. }
        forward; rewrite Hst; unfold space_quad. 1: entailer !!.
        forward. simpl sem_binary_operation'. rewrite sapi_ptr_val; [| assumption | rep_lia].
        Opaque Znth. forward. Transparent Znth. rewrite sapil_ptr_val by easy.
        rewrite Hst. unfold space_quad. rewrite <- Z.add_assoc.
        replace (1 + Zlength (raw_fields (vlabel g v'))) with (vertex_size g v') by
          (unfold vertex_size; lia). thaw FR. freeze [0; 2; 3; 4] FR.
        assert (Hi : 0 <= Z.of_nat to < Zlength (spaces h)) by (rewrite spaces_size; rep_lia).
        assert (Hh: has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v')) by
          (subst from; apply estc_has_space; assumption).
        assert (Hnn: space_start (Znth (Z.of_nat to) (spaces h)) <> nullval). {
          rewrite <- Heqsp_to. destruct (space_start sp_to); [contradiction..|].
          discriminate. }
        rewrite (heap_unused_rep_cut h (Z.of_nat to) (vertex_size g v') Hi Hh Hnn).
        rewrite <- Heqsp_to. thaw FR. simpl fst. simpl snd.
        gather_SEP (data_at _ _ _ _) (heap_unused_rep _).
        replace_SEP 0 (heap_rep sh (cut_heap h (Z.of_nat to) (vertex_size g v')) hp). {
          entailer !!. unfold heap_rep, heap_struct_rep.
          apply sepcon_derives; [ | apply derives_refl].
          apply derives_refl'; f_equal. unfold_cut_heap. simpl. unfold_cut_space.
          unfold space_quad at 2. rewrite <- upd_Znth_map. f_equal. }
        sep_apply (graph_vertex_ramif_stable _ _ Hhv'). Intros.
        freeze [1; 2; 3] FR. rewrite Hvv. remember (nth_sh g from) as shv.
        assert (Hws: writable_share (space_sh sp_to)) by
          (rewrite <- Hgen; apply generation_share_writable).
        remember (space_sh sp_to) as sht. rewrite (data_at__tarray_value _ _ 1).
        2: unfold vertex_size; rep_lia. Intros.
        remember (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to)) as sp_ad.
        rewrite (data_at__int_or_ptr_integer sht sp_ad).
        assert_PROP
          (force_val (sem_add_ptr_int
                        (if Archi.ptr64 then tulong else tuint) Signed
                        (offset_val (WORD_SIZE * (used_space sp_to + 1)) (space_start sp_to))
                        (eval_unop Oneg tint (Vint (Int.repr 1)))) =
             field_address (if Archi.ptr64 then tulong else tuint) [] sp_ad) as Hforce. {
          subst sp_ad. entailer !. unfold field_address. simpl. rewrite neg_repr.
          rewrite sem_add_pi_ptr_special; auto. 2: rep_lia. rewrite if_true by assumption.
          simpl. rewrite !offset_offset_val. f_equal. unfold WORD_SIZE. lia. }
        forward. sep_apply (field_at_data_at_cancel
                              sht (if Archi.ptr64 then tulong else tuint)
                              (Z2val (make_header g v')) sp_ad). clear Hforce.
        subst sp_ad. rewrite offset_offset_val.
        replace (vertex_size g v' - 1) with (Zlength (raw_fields (vlabel g v')))
          by (unfold vertex_size; lia).
        replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
          (WORD_SIZE * (used_space sp_to + 1))%Z by rep_lia.
        remember (offset_val (WORD_SIZE * (used_space sp_to + 1)) (space_start sp_to)) as nv.
        thaw FR. freeze [0; 1; 2; 3; 5] FR. rename i into j.
        remember (Zlength (raw_fields (vlabel g v'))) as n'.
        assert (Hnv: isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
        remember (field_address heap_type _ _) as n_addr.
        forward_for_simple_bound
          n'
            (EX i: Z,
                PROP ( )
                  LOCAL (temp _newv nv;
                         temp _sz (if Archi.ptr64 then Vlong (Int64.repr n')
                                   else Vint (Int.repr n'));
                         temp _hd (Z2val (make_header g v'));
                         temp _v (vertex_address g v');
                         temp _from_start fp;
                         temp _from_limit (offset_val fn fp);
                         temp _next n_addr;
                         temp _p (offset_val (WORD_SIZE * n) (vertex_address g v));
                         temp _depth (Vint (Int.repr depth)))
                  SEP (vertex_rep shv g v';
                       data_at sht (tarray int_or_ptr_type i)
                         (sublist 0 i (make_fields_vals g v')) nv;
                       data_at_ sht (tarray int_or_ptr_type (n' - i))
                         (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
        -- pose proof raw_fields_range2 (vlabel g v') as Hrr. simpl in Hrr.
           now rewrite <- Heqn' in Hrr.
        -- rewrite sublist_nil. rewrite Z.sub_0_r, Z.mul_0_r.
           rewrite isptr_offset_val_zero by assumption.
           rewrite data_at_zero_array_eq; [entailer!! | easy..].
        -- unfold vertex_rep, vertex_at. Intros.
           rewrite fields_eq_length, <- Heqn'. forward.
           ++ entailer !!. pose proof mfv_all_is_ptr_or_int _ _ Hcp Hnodg Hhv' as Hf.
              rewrite Forall_forall in Hf. apply Hf, Znth_In. now rewrite fields_eq_length.
           ++ rewrite (data_at__tarray_value _ _ 1) by lia. Intros.
              rewrite data_at__singleton_array_eq.
              assert_PROP
                (field_compatible int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv)) as Hfc
                  by (sep_apply (data_at__local_facts sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer !).
              assert_PROP
                ((if Archi.ptr64 then
                    force_val (sem_add_ptr_long int_or_ptr_type nv (Vlong (Int64.repr i)))
                  else force_val (sem_add_ptr_int int_or_ptr_type
                                    Signed nv (Vint (Int.repr i)))) =
                   field_address int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv)) as Hf. {
                unfold field_address. rewrite if_true by assumption. clear. entailer!. }
              simpl in Hf. gather_SEP (data_at shv _ _ _) (data_at _ (_ n') _ _).
              replace_SEP 0 (vertex_rep shv g v') by
                (unfold vertex_rep, vertex_at; rewrite fields_eq_length; entailer!!).
              forward. rewrite offset_offset_val.
              replace (n' - i - 1) with (n' - (i + 1)) by lia.
              replace (WORD_SIZE * i + WORD_SIZE * 1) with
                (WORD_SIZE * (i + 1))%Z by rep_lia.
              gather_SEP (data_at _ _ _ nv) (field_at _ _ _ _ _).
              rewrite data_at_mfs_eq; [entailer!! | assumption | subst n'; assumption].
        -- thaw FR. rewrite Hvv, <- Heqshv.
           gather_SEP (vertex_rep _ _ _) (_ -* _).
           replace_SEP 0 (graph_rep g) by (entailer !!; apply wand_frame_elim).
           rewrite sublist_same by (rewrite ?fields_eq_length; lia).
           replace_SEP 2 emp. { replace (n' - n') with 0 by lia. clear. entailer !!.
                                apply data_at__value_0_size. }
           assert (Hnveq: nv = vertex_address g (new_copied_v g to)). {
             subst nv. unfold vertex_address, new_copied_v. simpl. f_equal.
             - unfold vertex_offset. simpl. rewrite Hpre. reflexivity.
             - unfold gen_start. rewrite if_true by assumption. rewrite Has. reflexivity. }
           gather_SEP (data_at sht _ _ nv) (emp) (data_at sht _ _ _).
           replace_SEP 0 (vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
                            (make_header g v') (make_fields_vals g v')). {
             normalize. rewrite <- Hgen.
             change (generation_sh (nth_gen g to)) with (nth_sh g to).
             rewrite <- fields_eq_length in Heqn'.
             replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
               with (offset_val (- WORD_SIZE) nv) by
               (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
             rewrite <- Hnveq. unfold vertex_at; entailer !!. }
           gather_SEP (vertex_at _ _ _ _) (graph_rep _).
           rewrite (copied_v_derives_new_g g v' to) by assumption.
           freeze [1; 2; 3] FR. remember (lgraph_add_copied_v g v' to) as g'.
           assert (Hvsame: vertex_address g' v' = vertex_address g v') by
             (subst g'; apply lacv_vertex_address_old; assumption).
           assert (Hcvsame: vertex_address g' (new_copied_v g to) =
                              vertex_address g (new_copied_v g to)) by
             (subst g'; apply lacv_vertex_address_new; assumption).
           rewrite <- Hvsame. rewrite <- Hcvsame in Hnveq.
           assert (Hws': writable_share (nth_sh g' (vgeneration v'))) by
             (unfold nth_sh; apply generation_share_writable).
           assert (Hgcv': graph_has_v g' (new_copied_v g to)) by
             (subst g'; apply lacv_graph_has_v_new; assumption).
           sep_apply (graph_rep_valid_int_or_ptr _ _ Hgcv'). Intros. rename H0 into Hvg'.
           rewrite <- Hnveq in Hvg'. assert (Hgv': graph_has_v g' v') by
             (subst g'; apply lacv_graph_has_v_old; assumption).
           remember (nth_sh g' (vgeneration v')) as sh'.
           sep_apply (graph_vertex_lmc_ramif g' v' (new_copied_v g to) Hgv').
           rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
           unfold vertex_rep, vertex_at. Intros.
           sep_apply (data_at_minus1_address
                        sh' (Z2val (make_header g' v')) (vertex_address g' v')).
           Intros. forward. clear H0.
           sep_apply (field_at_data_at_cancel
                        sh' (if Archi.ptr64 then tulong else tuint) (Z2val 0)
                        (offset_val (- WORD_SIZE) (vertex_address g' v'))).
           forward_call nv. remember (make_fields_vals g' v') as l'.
           assert (Hl': 0 < Zlength l'). { subst l'. rewrite fields_eq_length.
                                           apply (proj1 (raw_fields_range (vlabel g' v'))). }
           rewrite data_at_tarray_value_split_1 by assumption. Intros.
           assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                     (vertex_address g' v') (Vint (Int.repr 0))) =
                          field_address int_or_ptr_type [] (vertex_address g' v')) as Hf. {
             clear. entailer!. unfold field_address. rewrite if_true by assumption.
             simpl. rewrite isptr_offset_val_zero; [reflexivity | now destruct H7]. }
           forward. clear Hf.
           sep_apply (field_at_data_at_cancel sh' int_or_ptr_type nv (vertex_address g' v')).
           gather_SEP (data_at sh' (if Archi.ptr64 then tulong else tuint) _ _)
             (data_at sh' int_or_ptr_type _ _) (data_at _ _ _ _).
           rewrite Hnveq. subst l'. rewrite <- lmc_vertex_rep_eq. thaw FR1.
           gather_SEP (vertex_rep _ _ _) (_ -* _). remember (new_copied_v g to) as ncv.
           sep_apply
             (wand_frame_elim
                (vertex_rep sh' (lgraph_mark_copied g' v' ncv) v')
                (graph_rep (lgraph_mark_copied g' v' ncv))).
           rewrite <- (lmc_vertex_address g' v' ncv) in *.
           rewrite (lmc_graph_has_v g' v' ncv) in Hgcv'.
           rewrite <- (lmc_nth_sh g' v' ncv) in Heqsh'. subst g'.
           replace (lgraph_mark_copied (lgraph_add_copied_v g v' to) v' ncv)
             with (lgraph_copy_v g v' to) in * by (now subst ncv).
           remember (lgraph_copy_v g v' to) as g'.
           forward_call nv. rewrite <- Hnveq in *.
           rewrite lacv_vertex_address; [|apply graph_has_v_in_closure|]; [|assumption..].
           rewrite <- Hvsame.
           assert (Hvsame': vertex_address g' v = vertex_address g v). {
             subst g'. apply lcv_vertex_address; [|apply graph_has_v_in_closure]; easy. }
           rewrite <- Hvsame' in *. rewrite (lcv_mfv_Zlen_eq g v v' to Hto Hhv) in Hofse.
           rewrite <- Heqg' in Hofse. remember (nth_sh g' (vgeneration v)) as shh.
           remember (make_fields_vals g' v) as mfv.
           remember (labeledgraph_gen_dst g' e ncv) as gg.
           assert (Hng'v: 0 <= n < Zlength (make_fields_vals g' v)) by
             (subst g'; rewrite fields_eq_length, <- lcv_raw_fields; assumption).
           assert (Heqf': Znth n (make_fields g' v) = FieldEdge e) by
             (subst g'; unfold make_fields in *; rewrite <- lcv_raw_fields; assumption).
           assert (Hn': 0 <= n < Zlength (make_fields g' v)) by
             (rewrite make_fields_eq_length; rewrite fields_eq_length in Hng'v; assumption).
           assert (Hv': graph_has_v g' v) by
             (subst g'; apply lcv_graph_has_v_old; assumption).
           assert (Hvnv': v <> v') by (intro; subst v; clear -Hvv Hvnf; contradiction).
           assert (Hrmg'v: raw_mark (vlabel g' v) = false) by
             (subst g'; rewrite <- lcv_raw_mark; assumption).
           assert (Hwshh: writable_share shh) by
             (rewrite Heqshh; unfold nth_sh; apply generation_share_writable).
           localize [vertex_rep (nth_sh g' (vgeneration v)) g' v].
           unfold vertex_rep, vertex_at. Intros. rewrite Heqmfv in *; rewrite <- Heqshh.
           forward.
           rewrite Hnveq.
           sep_apply (field_at_data_at_cancel
                        shh
                        (tarray int_or_ptr_type (Zlength (make_fields_vals g' v)))
                        (upd_Znth n (make_fields_vals g' v) (vertex_address g' ncv))
                        (vertex_address g' v)).
           gather_SEP (data_at shh _ _ _) (data_at shh _ _ _).
           replace_SEP 0 (vertex_rep (nth_sh gg (vgeneration v)) gg v).
           1: { unfold vertex_rep, vertex_at.
                replace (nth_sh gg (vgeneration v)) with shh by (subst shh gg; reflexivity).
                replace (Zlength (make_fields_vals gg v)) with
                  (Zlength (make_fields_vals g' v)) by
                  (subst gg; repeat rewrite fields_eq_length; apply lgd_raw_fld_length_eq).
                rewrite (lgd_mfv_change_in_one_spot g' v e ncv n); try assumption.
                entailer!!. } subst gg ncv.
           unlocalize [graph_rep (labeledgraph_gen_dst g' e (new_copied_v g to))].
           1: apply (graph_vertex_lgd_ramif g' v e (new_copied_v g to) n); assumption.
           remember (new_copied_v g to) as ncv.
           remember (labeledgraph_gen_dst g' e ncv) as gg. thaw FR.
           remember (cut_heap h (Z.of_nat to) (vertex_size g v')) as h'.
           unfold heap_rep. Intros.
           gather_SEP (heap_struct_rep _ _ _) (heap_unused_rep _).
           replace_SEP 0 (heap_rep sh h' hp) by
             (unfold heap_rep; simpl heap_head; entailer!).
           rewrite Hnveq in Hcvsame.
           assert (H': (gg, h') = forward_graph_and_heap from to 0 (ForwardEdge e) g h). {
             simpl. rewrite <- Heqv'. rewrite if_true by assumption.
             rewrite Hrm'. subst gg h' g' ncv. reflexivity. }
           forward_if.
           ++ rename H0 into Hdepg. forward_if.
              ** pose proof raw_tag_lt_noscan _ _ Hrm' H0 as SCAN'. clear H0.
                 replace fp with (gen_start gg from) by
                   (subst fp gg g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (gen_start gg from)) with
                   (limit_address gg h' from) by
                  (unfold limit_address; subst fn gn h'; now rewrite cti_available_size).
                 replace n_addr with (heap_next_address hp to) by
                   (subst n_addr; reflexivity).
                 assert (Hfc': forward_condition gg h' from to). {
                   eapply forward_graph_and_heap_fc; try eassumption; red; easy. }
                 assert (Hghc': graph_heap_compatible gg h'). {
                   eapply forward_graph_and_heap_ghc; try eassumption; red; easy. }
                 assert (Ho': outlier_compatible gg outlier). {
                   subst gg g'. apply lcv_outlier_compatible; assumption. }
                forward_for_simple_bound
                  n'
                    (EX i: Z, EX g3: LGraph, EX h3: part_heap,
                            PROP ((g3, h3) = forward_gh_loop forward_graph_and_heap
                                               from to (Z.to_nat (depth - 1))
                                               (sublist 0 i (vertex_pos_pairs gg ncv))
                                               (gg, h'))
                              LOCAL (temp _newv nv;
                                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n')
                                               else Vint (Int.repr n'));
                                     temp _from_start (gen_start g3 from);
                                     temp _from_limit (limit_address g3 h3 from);
                                     temp _next (heap_next_address hp to);
                                     temp _depth (Vint (Int.repr depth)))
                              SEP (all_string_constants rsh gv;
                                   outlier_rep outlier;
                                   graph_rep g3;
                                   heap_rep sh h3 hp))%assert.
                --- pose proof raw_fields_range2 (vlabel g v') as Hl. simpl in Hl.
                    now rewrite <- Heqn' in Hl.
                --- Exists gg h'. autorewrite with sublist. simpl forward_gh_loop.
                    entailer !!.
                --- change (Tpointer tvoid {| attr_volatile := false;
                                             attr_alignas := Some 3%N |})
                      with (int_or_ptr_type). Intros.  rename H1 into Hfwdlp.
                    pose proof fl_fwd_gh_loop from to (Z.to_nat (depth - 1))
                      (sublist 0 i (vertex_pos_pairs gg ncv)) (gg,h') as Hfl.
                    rewrite <- Hfwdlp in Hfl. simpl fst in Hfl. rename H0 into Hirange.
                    assert (Hghg: graph_has_gen gg to) by
                      (rewrite Heqgg, lgd_graph_has_gen; subst g';
                       rewrite <- lcv_graph_has_gen; assumption).
                    assert (Hghv: graph_has_v gg ncv) by
                      (subst gg; rewrite <- lgd_graph_has_v; subst ncv;
                       rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                    forward_call (rsh, sh, gv, g3, h3, hp, outlier, from, to, depth - 1,
                                   FwdPntIntr (InteriorVertexPos ncv i), @None val).
                    +++ apply prop_right. simpl. rewrite sub_repr.
                        do 4 f_equal. rewrite Hnveq.
                        first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                        *** simpl. f_equal.
                            rewrite <- (lgd_vertex_address_eq g' e ncv), <- Heqgg.
                            subst ncv. apply (fl_vertex_address _ _ _ _ _ _ Hghg Hfl).
                            apply graph_has_v_in_closure; assumption.
                        *** rewrite <- Hnveq. assumption.
                    +++ entailer !!.
                    +++ split; [|split; [|split]].
                        *** destruct Hfc' as [? [? [? [? ?]]]].
                            eapply forward_gh_loop_ghc. 9: apply Hfwdlp. all: eauto.
                            apply Forall_sublist, vertex_pos_pairs_in_range.
                        *** destruct Hfc' as [? [? [? [? ?]]]].
                            eapply fl_outlier_compatible. 7: apply Hfl.
                            all: try eassumption.
                            apply Forall_sublist, vertex_pos_pairs_in_range.
                        *** simpl. subst ncv.
                            split; [|split; [|split; [|split]]].
                            ---- eapply fl_graph_has_v with (g := gg); eassumption.
                            ---- erewrite <- fl_raw_fields; eauto. subst n' gg g' from.
                                  simpl. rewrite lcv_vlabel_new; assumption.
                            ---- erewrite <- fl_raw_mark; try eassumption. subst gg g' from.
                                 simpl. rewrite lcv_vlabel_new; assumption.
                            ---- erewrite <- fl_raw_tag; try eassumption. subst gg g' from.
                                 simpl. rewrite lcv_vlabel_new; assumption.
                            ---- apply not_eq_sym. assumption.
                        *** eapply forward_gh_loop_fc. 5: apply Hfwdlp. all: eauto.
                            apply Forall_sublist, vertex_pos_pairs_in_range.
                    +++ Intros vret. destruct vret as [g4 h4]. rename H0 into Hgh4.
                        simpl fst in *. simpl snd in *. Exists g4 h4. simpl in Hgh4.
                        simpl upd_fwd. simpl forward_p_rep.
                        remember (field2forward (Znth i (make_fields g3 ncv))) as newi.
                        pose proof (fr_forward_graph_and_heap_eq from to
                          (Z.to_nat (depth - 1)) newi g3 h3 g4 h4 Hgh4) as Hfr3.
                        assert (Hgs: gen_start g3 from = gen_start g4 from). {
                          eapply fr_gen_start; [| eassumption ].
                          erewrite <- fl_graph_has_gen; eauto. } rewrite Hgs.
                        pose proof (heaprel_forward_graph_and_heap_eq from to
                          (Z.to_nat (depth - 1)) newi g3 h3 g4 h4 Hgh4) as Hhr.
                        assert (Hla: limit_address g3 h3 from = limit_address g4 h4 from). {
                          unfold limit_address. f_equal. 2: assumption. f_equal.
                          rewrite (heap_relation_available_size _ _ _ Hhr). reflexivity. }
                        rewrite Hla. entailer !!. eapply forward_gh_loop_add_tail_vpp; eauto.
                        simpl. Transparent lgraph_copy_v. rewrite lcv_vlabel_new; assumption.
                --- Intros g3 h3. rename H0 into Hfwdlp.
                    rewrite sublist_same in Hfwdlp; auto.
                    2: { subst n' gg g' from ncv. rewrite vpp_Zlength,
                        <- lgd_raw_fld_length_eq, lcv_vlabel_new; auto. }
                    simpl forward_p2forward_t. rewrite Heqf. simpl field2forward.
                    Exists g3 h3. simpl forward_p_rep. entailer !!.
                 replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                   (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia). simpl.
                 rewrite if_true by reflexivity. rewrite Hrm', if_true; assumption.
              ** pose proof raw_tag_ge_noscan _ _ Hrm' H0 as SCAN'. clear H0.
                 forward. Exists gg h'. simpl forward_p2forward_t. rewrite Heqf.
                 simpl field2forward. simpl forward_p_rep. entailer !!.
                 replace (Z.to_nat depth) with (S (Z.to_nat (depth-1))) by
                   (clear - Hdepg; lia). simpl. rewrite if_true by reflexivity.
                 rewrite Hrm'. rewrite if_false; [reflexivity | assumption].
           ++ forward. Exists gg h'. assert (depth = 0) by lia. subst depth. clear H0.
              simpl forward_p2forward_t. rewrite Heqf. simpl field2forward.
              simpl forward_p_rep. entailer !!.
    + forward_if. 1: contradiction. rewrite Hviff in Hvv.
      forward. Exists g h. entailer !!.
      * simpl. rewrite Heqf. simpl. rewrite fwd_graph_heap_unfold, if_false; easy.
      * unfold heap_rep. entailer !!.
Qed.
