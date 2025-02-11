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
Require Import CertiGraph.CertiGC.forward_lemmas.

Local Opaque Int64.repr.

Local Open Scope logic.

Lemma body_forward_extr:
  forall (Espec : OracleKind)
    (rsh sh : share)
    (gv : globals)
    (g : LGraph)
    (h : heap)
    (hp : val)
    (outlier : outlier_t)
    (from to : nat)
    (depth : Z)
    (extr : exterior_t)
    (v : val)
    (SHr : readable_share rsh)
    (SHw : writable_share sh)
    (Hghc : graph_heap_compatible g h)
    (Hoc : outlier_compatible g outlier)
    (Hfpc : forward_p_compatible (FwdPntExtr extr) outlier g from)
    (Hfc : forward_condition g h from to)
    (Hdep : 0 <= depth <= Int.max_signed)
    (Hft : from <> to),
  semax (func_tycontext f_forward Vprog Gprog [])
    (PROP ( )
     LOCAL (temp _from_start (gen_start g from); temp _from_limit (limit_address g h from);
     temp _next (heap_next_address hp to); temp _p v; temp _depth (Vint (Int.repr depth)))
     SEP (all_string_constants rsh gv; outlier_rep outlier;
     data_at sh int_or_ptr_type (exterior2val g extr) v; graph_rep g;
     heap_rep sh h hp)) (fn_body f_forward)
    (normal_ret_assert
       ((EX (g' : LGraph) (h' : heap),
         PROP ((g', h') =
               forward_graph_and_heap from to (Z.to_nat depth)
                 (forward_p2forward_t (FwdPntExtr extr) g) g h)
         RETURN ( ) SEP (all_string_constants rsh gv; outlier_rep outlier;
                    forward_p_rep sh (upd_fwd from to g (FwdPntExtr extr)) (Some v) g';
                    graph_rep g'; heap_rep sh h' hp))%argsassert *
        stackframe_of f_forward)).
Proof.
  intros. simpl fn_body. abbreviate_semax. unfold limit_address.
  destruct Hfc as [Hesto [Hfrom [Hto [Hcp Hnodg]]]]. red in Hfpc.
  assert (Hipi: is_pointer_or_integer (exterior2val g extr)). {
    destruct extr as [? | ? | ?]; simpl; auto.
    - destruct g0. simpl. exact I.
    - apply isptr_is_pointer_or_integer, graph_has_v_addr_isptr, Hfpc. }
  forward.
  assert_PROP (valid_int_or_ptr (exterior2val g extr)) as Hvextr. {
    gather_SEP (graph_rep _) (outlier_rep _).
    sep_apply (extr_valid_int_or_ptr _ _ _ Hfpc). entailer!!. }
  forward_call (exterior2val g extr).
  remember (graph_rep g * heap_unused_rep h * outlier_rep outlier)
    as P. pose proof graph_and_heap_rest_data_at_ _ _ _ Hfrom Hghc as Hgenat.
  unfold generation_data_at_ in Hgenat. remember (gen_start g from) as fp.
  remember (nth_sh g from) as fsh. remember (available_size h from) as gn.
  remember (WORD_SIZE * gn)%Z as fn.
  assert (Pweak: P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
    apply weak_derives_strong. subst. sep_apply Hgenat.
    rewrite data_at__memory_block.
    rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold available_size].
    destruct (available_space_tight_range (nth_space h from)). assumption. }
  destruct extr as [z | gp | ev]; simpl exterior2val.
  - unfold odd_Z2val. forward_if. 1: contradiction.
    forward. Exists g h. simpl forward_p2forward_t.
    rewrite fwd_graph_heap_unfold. entailer !!.
  - unfold GC_Pointer2val. destruct gp. forward_if.
    2: apply Int.one_not_zero in H; contradiction.
    forward_call (Vptr b i).
    unfold heap_rep; Intros.
    gather_SEP (graph_rep _) (heap_unused_rep _) (outlier_rep _). rewrite <- HeqP.
    replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
      (entailer; assumption). Intros. simpl exterior2val in *. simpl in Hfpc.
    assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) as Hweakp. {
      subst. cancel. apply andp_right. 2: cancel.
      assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS. apply derives_weak.
      sep_apply (outlier_rep_valid_pointer _ _ Hfpc).
      simpl GC_Pointer2val. cancel. }
    replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
      (entailer; assumption). Intros.
    forward_call (fsh, fp, fn, (Vptr b i), P). Intros vret. destruct vret as [Hv | Hv].
    + rewrite HeqP. Intros.
      gather_SEP (graph_rep g) (heap_unused_rep _) (outlier_rep _).
      change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in Hv.
      rewrite Heqfp, Heqfn, Heqgn in Hv.
      sep_apply (graph_heap_outlier_FF g h outlier from (GCPtr b i)).
      assert_PROP False by entailer !. contradiction.
    + forward_if. 1: contradiction. forward. Exists g h. simpl forward_p2forward_t.
      rewrite fwd_graph_heap_unfold. unfold heap_rep. entailer !!.
  - simpl in Hfpc. pose proof graph_has_v_addr_isptr _ _ Hfpc as Hisptr.
    destruct (vertex_address g ev) eqn:Heqev ; try contradiction.
    forward_if. 2: apply Int.one_not_zero in H; contradiction. clear H H'.
    simpl in Hipi, Hvextr. forward_call (Vptr b i).
    rewrite <- Heqev in *. unfold heap_rep; Intros.
    gather_SEP (graph_rep _) (heap_unused_rep _) (outlier_rep _). rewrite <- HeqP.
    replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
      (entailer; assumption). Intros.
    assert (P |-- (weak_derives P (valid_pointer (vertex_address g ev) * TT) && emp)
            * P) as Pweakv. { apply weak_derives_strong. subst.
      sep_apply (graph_rep_valid_pointer _ _ Hfpc). cancel. }
    replace_SEP 1 (weak_derives P (valid_pointer (vertex_address g ev) * TT) && emp * P)
      by (entailer; assumption). Intros.
    forward_call (fsh, fp, fn, (vertex_address g ev), P). Intros vv. rewrite HeqP.
    sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ Hghc Hfrom Hfpc). Intros.
    rename H into Hviff. rewrite <- Heqfp, <- Heqgn, <- Heqfn in Hviff.
    destruct vv as [Hvv | Hvv].
    + rewrite Hviff in Hvv. clear Hviff. forward_if.
      2: apply Int.one_not_zero in H; contradiction. clear H H'. freeze [1; 2; 3; 4; 5] FR.
      localize [vertex_rep (nth_sh g (vgeneration ev)) g ev].
      unfold vertex_rep, vertex_at. Intros. rewrite Hvv.
      assert (readable_share (nth_sh g from)) by
        (unfold nth_sh; apply writable_readable, generation_share_writable).
      sep_apply (data_at_minus1_address (nth_sh g from) (Z2val (make_header g ev))
                   (vertex_address g ev)). Intros.
      forward. clear H0.
      gather_SEP (data_at _ (if Archi.ptr64 then tulong else tuint) _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (nth_sh g (vgeneration ev)) g ev) by
        (unfold vertex_rep, vertex_at; entailer !!).
      unlocalize [graph_rep g]. 1: now apply (graph_vertex_ramif_stable _ _ Hfpc).
      forward_if.
      * try apply Int64.same_if_eq in H0.
        pose proof make_header_int_rep_mark_iff g ev as Hiff. simpl in Hiff.
        rewrite Hiff in H0. clear Hiff. rename H0 into Hrm.
        localize [vertex_rep (nth_sh g (vgeneration ev)) g ev].
        rewrite Hvv. unfold vertex_rep, vertex_at. Intros.
        unfold make_fields_vals at 2. rewrite Hrm.
        assert (Hrg: 0 <= 0 < Zlength (make_fields_vals g ev)). {
          split. 1: lia. rewrite fields_eq_length.
          apply (proj1 (raw_fields_range (vlabel g ev))). }
        assert (Hipic: is_pointer_or_integer
                         (vertex_address g (copied_vertex (vlabel g ev)))). {
          apply isptr_is_pointer_or_integer. unfold vertex_address.
          rewrite isptr_offset_val. apply graph_has_gen_start_isptr, Hcp; assumption. }
        forward. rewrite Znth_0_cons.
        gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration ev)) g ev). {
          unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
          rewrite Hrm. entailer !!. }
        unlocalize [graph_rep g]. 1: now apply (graph_vertex_ramif_stable _ _ Hfpc). thaw FR.
        forward. simpl forward_p2forward_t. Exists g h.
        rewrite fwd_graph_heap_unfold, Hvv, Hrm. rewrite if_true by reflexivity.
        entailer !!. simpl upd_fwd. rewrite if_true by reflexivity.
        rewrite Hrm. simpl forward_p_rep. unfold heap_rep. cancel.
      * forward. thaw FR. freeze [0; 1; 2; 3; 4] FR.
        try apply Int64_eq_false in H0. rename H0 into Hrm.
        pose proof make_header_int_rep_mark_iff g ev as Hiff. simpl in Hiff.
        rewrite Hiff in Hrm. clear Hiff. apply not_true_is_false in Hrm.
        rewrite make_header_Wosize by assumption.
        pose proof gen_range _ _ _ Hghc Hto as Htrange. unfold heap_struct_rep.
        destruct (gt_gs_compatible _ _ Hghc _ Hto) as [Has [Hgen Hpre]].
        rewrite nth_space_Znth in *.
        remember (Znth (Z.of_nat to) (spaces h)) as sp_to.
        assert (Hss: isptr (space_start sp_to)) by (rewrite <- Has; apply start_isptr).
        remember (map space_quad (spaces h)) as l.
        assert (Hst: @Znth (val * (val * (val*val))) (Vundef, (Vundef, (Vundef,Vundef)))
                  (Z.of_nat to) l = space_quad sp_to). {
          subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_lia). reflexivity. }
        unfold heap_next_address.
        forward; rewrite Hst; unfold space_quad. 1: entailer !!.
        forward. simpl sem_binary_operation'.
        rewrite sapi_ptr_val; [|assumption | rep_lia].
        Opaque Znth. forward. Transparent Znth.
        rewrite sapil_ptr_val by assumption. rewrite Hst. unfold space_quad.
        rewrite <- Z.add_assoc.
        replace (1 + Zlength (raw_fields (vlabel g ev))) with (vertex_size g ev) by
          (unfold vertex_size; lia). thaw FR. freeze [0; 2; 3; 4; 5] FR.
        assert (Hi : 0 <= Z.of_nat to < Zlength (spaces h)) by (rewrite spaces_size; rep_lia).
        assert (Hh: has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g ev)) by
          (subst from; apply estc_has_space; assumption).
        assert (Hn: space_start (Znth (Z.of_nat to) (spaces h)) <> nullval). {
          rewrite <- Heqsp_to. destruct (space_start sp_to); try contradiction.
          discriminate. }
        rewrite (heap_unused_rep_cut h (Z.of_nat to) (vertex_size g ev) Hi Hh Hn).
        rewrite <- Heqsp_to. thaw FR. simpl snd. simpl fst.
        gather_SEP (data_at _ heap_type _ _) (heap_unused_rep _).
        replace_SEP 0 (heap_rep sh (cut_heap h (Z.of_nat to) (vertex_size g ev)) hp). {
          entailer !!. unfold heap_rep, heap_struct_rep.
          apply sepcon_derives; [ | apply derives_refl]. unfold_cut_heap. simpl spaces.
          apply derives_refl'; f_equal. unfold_cut_space.
          unfold space_quad at 2. rewrite <- upd_Znth_map. f_equal. }
        sep_apply (graph_vertex_ramif_stable _ _ Hfpc). Intros.
        freeze [1; 2; 3; 4; 5] FR. rewrite Hvv. remember (nth_sh g from) as shv.
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
          subst sp_ad. entailer !. simpl. rewrite neg_repr.
          rewrite sem_add_pi_ptr_special; auto. 2: rep_lia. simpl in *.
          unfold field_address. rewrite if_true by assumption.
          simpl. rewrite !offset_offset_val. f_equal. unfold WORD_SIZE. lia. }
        forward. sep_apply (field_at_data_at_cancel
                              sht (if Archi.ptr64 then tulong else tuint)
                              (Z2val (make_header g ev)) sp_ad). clear Hforce.
        subst sp_ad. rewrite offset_offset_val.
        replace (vertex_size g ev - 1) with (Zlength (raw_fields (vlabel g ev)))
          by (unfold vertex_size; lia).
        replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
          (WORD_SIZE * (used_space sp_to + 1))%Z by rep_lia.
        remember (offset_val (WORD_SIZE * (used_space sp_to + 1)) (space_start sp_to)) as nv.
        thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j.
        remember (Zlength (raw_fields (vlabel g ev))) as n.
        assert (Hnv: isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
        remember (field_address heap_type _ _) as n_addr.
        forward_for_simple_bound
          n
            (EX i: Z,
             PROP ( )
             LOCAL (temp _newv nv;
                    temp _sz (if Archi.ptr64 then Vlong (Int64.repr n)
                              else Vint (Int.repr n));
                    temp _hd (Z2val (make_header g ev));
                    temp _v (vertex_address g ev);
                    temp _from_start fp;
                    temp _from_limit (offset_val fn fp);
                    temp _next n_addr;
                    temp _p v;
                    temp _depth (Vint (Int.repr depth)))
             SEP (vertex_rep shv g ev;
                  data_at sht (tarray int_or_ptr_type i)
                    (sublist 0 i (make_fields_vals g ev)) nv;
                  data_at_ sht (tarray int_or_ptr_type (n - i))
                    (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
        -- pose proof raw_fields_range2 (vlabel g ev) as Hrr. simpl in Hrr.
           now rewrite <- Heqn in Hrr.
        -- rewrite sublist_nil. replace (n - 0) with n by lia.
           replace (WORD_SIZE * 0)%Z with 0 by lia.
           rewrite isptr_offset_val_zero by assumption.
           rewrite data_at_zero_array_eq;
             [|reflexivity | assumption | reflexivity]. entailer !!.
        -- unfold vertex_rep, vertex_at. rename H0 into Hir. Intros.
           rewrite fields_eq_length, <- Heqn. forward.
           ++ entailer !. pose proof mfv_all_is_ptr_or_int _ _ Hcp Hnodg Hfpc as Hf.
              rewrite Forall_forall in Hf. apply Hf, Znth_In. now rewrite fields_eq_length.
           ++ rewrite (data_at__tarray_value _ _ 1) by lia. Intros.
              rewrite data_at__singleton_array_eq.
              assert_PROP (field_compatible int_or_ptr_type []
                             (offset_val (WORD_SIZE * i) nv)) as Hfc by
                (sep_apply (data_at__local_facts
                              sht int_or_ptr_type
                              (offset_val (WORD_SIZE * i) nv)); entailer !).
              assert_PROP
                ((if Archi.ptr64 then
                    force_val (sem_add_ptr_long int_or_ptr_type nv (Vlong (Int64.repr i)))
                  else force_val (sem_add_ptr_int int_or_ptr_type
                                    Signed nv (Vint (Int.repr i)))) =
                   field_address int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv)) as Hf. {
                unfold field_address. rewrite if_true by assumption. clear. entailer!. }
              simpl in Hf.
              gather_SEP (data_at _ _ _ (offset_val _ _))
                (data_at _ _ _ (vertex_address g _)).
              replace_SEP 0 (vertex_rep shv g ev) by
                (unfold vertex_rep, vertex_at; rewrite fields_eq_length; entailer!!).
              forward. rewrite offset_offset_val.
              replace (n - i - 1) with (n - (i + 1)) by lia.
              replace (WORD_SIZE * i + WORD_SIZE * 1) with (WORD_SIZE * (i + 1))%Z by lia.
              gather_SEP (data_at sht _ _ nv) (field_at _ _ _ _ _).
              rewrite data_at_mfs_eq; [| assumption | subst n; assumption]. entailer !!.
        -- thaw FR. rewrite Hvv, <- Heqshv. gather_SEP (vertex_rep _ _ _) (_ -* _).
           replace_SEP 0 (graph_rep g) by (entailer !!; apply wand_frame_elim).
           rewrite sublist_same by (rewrite ?fields_eq_length; lia).
           replace_SEP 2 emp. { replace (n - n) with 0 by lia. clear. entailer !.
                                apply data_at__value_0_size. }
           assert (Hnveq: nv = vertex_address g (new_copied_v g to)). {
             subst nv. unfold vertex_address, new_copied_v. simpl. f_equal.
             - unfold vertex_offset. simpl. rewrite Hpre. reflexivity.
             - unfold gen_start. rewrite if_true by assumption. rewrite Has. reflexivity. }
           gather_SEP (data_at _ _ _ nv) (emp) (data_at sht _ _ _).
           replace_SEP
             0 (vertex_at (nth_sh g to)
                  (vertex_address g (new_copied_v g to))
                  (make_header g ev) (make_fields_vals g ev)). {
             normalize. rewrite <- Hgen.
             change (generation_sh (nth_gen g to)) with (nth_sh g to).
             rewrite <- fields_eq_length in Heqn.
             replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
               with (offset_val (- WORD_SIZE) nv) by
               (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
             rewrite <- Hnveq. unfold vertex_at; entailer!!. } clear Heqnv.
           gather_SEP (vertex_at _ _ _ _) (graph_rep _).
           rewrite (copied_v_derives_new_g g ev to) by assumption.
           freeze [1; 2; 3; 4] FR. remember (lgraph_add_copied_v g ev to) as g'.
           assert (Hvasame: vertex_address g' ev = vertex_address g ev) by
             (subst g'; apply lacv_vertex_address_old; assumption).
           assert (Hcvsame: vertex_address g' (new_copied_v g to) =
                              vertex_address g (new_copied_v g to)) by
             (subst g'; apply lacv_vertex_address_new; assumption).
           rewrite <- Hvasame. rewrite <- Hcvsame in Hnveq.
           assert (Hws': writable_share (nth_sh g' (vgeneration ev))) by
             (unfold nth_sh; apply generation_share_writable).
           assert (Hgcv': graph_has_v g' (new_copied_v g to)) by
             (subst g'; apply lacv_graph_has_v_new; assumption).
           sep_apply (graph_rep_valid_int_or_ptr _ _ Hgcv'). Intros. rename H0 into Hvg'.
           rewrite <- Hnveq in Hvg'. assert (Hgv': graph_has_v g' ev) by
             (subst g'; apply lacv_graph_has_v_old; assumption).
           remember (nth_sh g' (vgeneration ev)) as sh'.
           sep_apply (graph_vertex_lmc_ramif g' ev (new_copied_v g to) Hgv').
           rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
           unfold vertex_rep, vertex_at. Intros.
           sep_apply (data_at_minus1_address
                        sh' (Z2val (make_header g' ev)) (vertex_address g' ev)).
           Intros. forward. clear H0. try rewrite Int.signed_repr by rep_lia.
           sep_apply (field_at_data_at_cancel
                        sh' (if Archi.ptr64 then tulong else tuint)
                        (if Archi.ptr64 then (Vlong (Int64.repr 0)) else (Vint (Int.repr 0)))
                        (offset_val (- WORD_SIZE) (vertex_address g' ev))).
           forward_call nv. remember (make_fields_vals g' ev) as l'.
           assert (Hl': 0 < Zlength l'). { subst l'. rewrite fields_eq_length.
                                      apply (proj1 (raw_fields_range (vlabel g' ev))). }
           rewrite data_at_tarray_value_split_1 by assumption. Intros.
           assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                     (vertex_address g' ev) (Vint (Int.repr 0))) =
                          field_address int_or_ptr_type [] (vertex_address g' ev)) as Hf. {
             clear. entailer!. unfold field_address. rewrite if_true by assumption.
             simpl. rewrite isptr_offset_val_zero; [reflexivity | now destruct H7]. }
           forward. clear Hf.
           sep_apply (field_at_data_at_cancel sh' int_or_ptr_type nv (vertex_address g' ev)).
           gather_SEP
             (data_at _ (if Archi.ptr64 then tulong else tuint) _ _)
               (data_at _ int_or_ptr_type nv _) (data_at _ _ _ _).
           rewrite Hnveq. subst l'. rewrite <- lmc_vertex_rep_eq. thaw FR1.
           gather_SEP (vertex_rep _ _ _) (_ -* _).
           sep_apply
             (wand_frame_elim
                (vertex_rep sh' (lgraph_mark_copied g' ev (new_copied_v g to)) ev)
                (graph_rep (lgraph_mark_copied g' ev (new_copied_v g to)))).
           rewrite <- (lmc_vertex_address g' ev (new_copied_v g to)) in *. subst g'.
           change (lgraph_mark_copied (lgraph_add_copied_v g ev to) ev (new_copied_v g to))
             with (lgraph_copy_v g ev to) in *.
           remember (lgraph_copy_v g ev to) as g'. rewrite <- Hnveq in *. thaw FR.
           forward_call nv. remember (cut_heap h (Z.of_nat to) (vertex_size g ev)) as h'.
           forward. drop_LOCAL 10%nat. do 2 drop_LOCAL 0%nat. rewrite Hnveq in Hcvsame.
           assert (H': (g', h') = forward_graph_and_heap from to 0 (ForwardVertex ev) g h). {
             simpl. rewrite if_true by assumption. rewrite Hrm. subst g' h'. reflexivity. }
           forward_if.
           2: { forward. Exists g' h'. assert (depth = 0) by lia. subst depth.
                simpl forward_p2forward_t. entailer !!. simpl upd_fwd.
                rewrite if_true by reflexivity. rewrite Hrm. simpl. entailer !!. }
           rename H0 into Hdepg. forward_if.
           ++ pose proof raw_tag_lt_noscan _ _ Hrm H0 as SCAN'. clear H0.
              replace fp with (gen_start g' from) by
                (subst fp g'; apply lcv_gen_start; assumption).
              replace (offset_val fn (gen_start g' from)) with (limit_address g' h' from) by
                (unfold limit_address; subst fn gn h'; now rewrite cti_available_size).
              assert (Hfc': forward_condition g' h' from to). {
                eapply forward_graph_and_heap_fc; try eassumption; red; easy. }
              assert (Hghc': graph_heap_compatible g' h'). {
                eapply forward_graph_and_heap_ghc; try eassumption; red; easy. }
              assert (Ho': outlier_compatible g' outlier). {
                subst g'. apply lcv_outlier_compatible; assumption. }
              forward_for_simple_bound
                n
                  (EX i: Z, EX g3: LGraph, EX h3: heap,
                          PROP ((g3, h3) = forward_gh_loop forward_graph_and_heap
                                             from to (Z.to_nat (depth - 1))
                                             (sublist 0 i (vertex_pos_pairs g'
                                                             (new_copied_v g to)))
                                             (g', h'))
                    LOCAL (temp _newv nv;
                           temp _sz (if Archi.ptr64 then
                                       Vlong (Int64.repr n) else Vint (Int.repr n));
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 h3 from);
                           temp _next (heap_next_address hp to);
                           temp _depth (Vint (Int.repr depth)))
                    SEP (all_string_constants rsh gv;
                         outlier_rep outlier;
                         data_at sh int_or_ptr_type
                           (vertex_address g3 (new_copied_v g to)) v;
                         graph_rep g3;
                         heap_rep sh h3 hp))%assert.
              ** pose proof raw_fields_range2 (vlabel g ev) as Hl. simpl in Hl.
                 now rewrite <- Heqn in Hl.
              ** Exists g' h'. autorewrite with sublist.
                 simpl forward_gh_loop. entailer !!.
              ** change (Tpointer tvoid {| attr_volatile := false;
                                          attr_alignas := Some 3%N |})
                   with (int_or_ptr_type). Intros. rename H0 into Hirange.
                 rename H1 into Hfwdlp.
                 pose proof fl_fwd_gh_loop from to (Z.to_nat (depth - 1))
                   (sublist 0 i (vertex_pos_pairs g' (new_copied_v g to))) (g',h') as Hfl.
                 rewrite <- Hfwdlp in Hfl. simpl fst in Hfl.
                 assert (Hghg: graph_has_gen g' to) by
                   (rewrite Heqg', <- lcv_graph_has_gen; assumption).
                 assert (Hghv: graph_has_v g' (new_copied_v g to)) by
                   (rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                 forward_call (rsh, sh, gv, g3, h3, hp, outlier, from, to, depth - 1,
                                FwdPntIntr (InteriorVertexPos (new_copied_v g to) i),
                                @None val).
                 --- apply prop_right. simpl. rewrite sub_repr, Hnveq.
                     do 4 f_equal. destruct Hfc' as [? [? [? [? ?]]]].
                     first [rewrite sem_add_pi_ptr_special' |
                             rewrite sem_add_pl_ptr_special']; auto.
                     +++ simpl. f_equal. erewrite fl_vertex_address; eauto.
                         subst g'. apply graph_has_v_in_closure. assumption.
                     +++ rewrite <- Hnveq. assumption.
                 --- entailer !!.
                 --- split; [|split; [|split]].
                     +++ destruct Hfc' as [? [? [? [? ?]]]].
                         eapply forward_gh_loop_ghc. 9: apply Hfwdlp. all: eauto.
                         apply Forall_sublist, vertex_pos_pairs_in_range.
                     +++ destruct Hfc' as [? [? [? [? ?]]]].
                         eapply fl_outlier_compatible. 7: apply Hfl.
                         all: try eassumption.
                         apply Forall_sublist, vertex_pos_pairs_in_range.
                     +++ simpl. split; [|split; [|split; [|split]]].
                         *** eapply fl_graph_has_v with (g := g'); eassumption.
                         *** erewrite <- fl_raw_fields; eauto. subst n g' from.
                             rewrite lcv_vlabel_new; assumption.
                         *** erewrite <- fl_raw_mark; try eassumption. subst g' from.
                             rewrite lcv_vlabel_new; assumption.
                         *** erewrite <- fl_raw_tag; try eassumption. subst g' from.
                             rewrite lcv_vlabel_new; assumption.
                         *** apply not_eq_sym. assumption.
                     +++ eapply forward_gh_loop_fc. 5: apply Hfwdlp. all: eauto.
                         apply Forall_sublist, vertex_pos_pairs_in_range.
                 --- Intros vret. destruct vret as [g4 h4]. rename H0 into Hgh4.
                     simpl fst in *. simpl snd in *. Exists g4 h4. simpl in Hgh4.
                     simpl upd_fwd. simpl forward_p_rep.
                     remember (field2forward
                                 (Znth i (make_fields g3 (new_copied_v g to)))) as newi.
                     pose proof fr_forward_graph_and_heap from to (Z.to_nat (depth - 1))
                       newi g3 h3 as Hfr3. rewrite <- Hgh4 in Hfr3. simpl fst in Hfr3.
                     assert (Hgs: gen_start g3 from = gen_start g4 from). {
                       eapply fr_gen_start; try eassumption.
                       erewrite <- fl_graph_has_gen; eassumption. } rewrite Hgs.
                     pose proof heaprel_forward_graph_and_heap from to
                       (Z.to_nat (depth - 1)) newi g3 h3 as Hhr.
                     rewrite <- Hgh4 in Hhr. simpl snd in Hhr.
                     assert (Hla: limit_address g3 h3 from = limit_address g4 h4 from). {
                       unfold limit_address. f_equal. 2: assumption. f_equal.
                       destruct Hhr as [Hgsize _]. rewrite Hgsize. reflexivity. }
                     assert (Hvd: vertex_address g3 (new_copied_v g to) =
                                    vertex_address g4 (new_copied_v g to)). {
                       eapply fr_vertex_address; try eassumption.
                       - erewrite <- fl_graph_has_gen; eassumption.
                       - apply graph_has_v_in_closure.
                         eapply fl_graph_has_v; eassumption. } rewrite Hla, Hvd.
                     entailer !!. eapply forward_gh_loop_add_tail_vpp; eauto.
                     rewrite lcv_vlabel_new; assumption.
              ** Intros g3 h3. rename H0 into Hgh3. rewrite sublist_same in Hgh3; auto.
                 2: { subst n g' from. rewrite vpp_Zlength, lcv_vlabel_new; auto. }
                 simpl forward_p2forward_t. Exists g3 h3. simpl upd_fwd.
                 rewrite if_true by assumption. rewrite Hrm.
                 simpl forward_p_rep. entailer !!.
                 replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                   (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia). simpl.
                 rewrite if_true by reflexivity. rewrite Hrm, if_true; assumption.
           ++ pose proof raw_tag_ge_noscan _ _ Hrm H0 as SCAN'. clear H0.
              forward. Exists g' h'. simpl upd_fwd. rewrite if_true by assumption.
              rewrite Hrm. simpl forward_p_rep. entailer !!.
              replace (Z.to_nat depth) with (S (Z.to_nat (depth-1))) by (clear - Hdepg; lia).
              simpl. rewrite if_true by reflexivity. rewrite Hrm.
              rewrite if_false by assumption. reflexivity.
    + forward_if. 1: contradiction. rewrite Hviff in Hvv. forward.
        Exists g h. entailer !!; simpl.
        * rewrite fwd_graph_heap_unfold. rewrite if_false; easy.
        * unfold heap_rep. rewrite if_false by assumption. simpl exterior2val. entailer !!.
Qed.
