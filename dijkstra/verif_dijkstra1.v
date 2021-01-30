Require Import CertiGraph.graph.SpaceAdjMatGraph1.
Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_math_proof.
Require Import CertiGraph.dijkstra.dijkstra_spec1.

Local Open Scope Z_scope.

Section DijkstraProof.
  
  (* The invariants have been dragged out of the 
     proof for readability and reuse
   *)

  Context {size: Z}.
  Context {inf: Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.

  Lemma Permutation_cons_In: forall {A} (l1 l2: list A) a,
      Permutation l1 (a :: l2) ->
      In a l1.
  Proof.
    intros.
    pose proof (in_eq a l2).
    apply Permutation_sym in H.
    apply (Permutation_in _ H); trivial.
  Qed.

  Lemma update_pri_by_key_unaffected:
  forall l key newpri,
    map heap_item_key (update_pri_by_key l key newpri) = map heap_item_key l.
  Proof.
    intros. induction l.
    - trivial.
    - simpl. rewrite IHl. f_equal.
      unfold update_pri_by_key, update_pri_if_key, heap_item_key.
      destruct (Z.eq_dec key (fst (fst a))); simpl fst; trivial.
  Qed.
  
  Lemma Int_signed_strip:
    forall a b, Int.signed a = Int.signed b -> a = b.
  Proof.
    intros.
    pose proof (Int.signed_eq a b). unfold zeq in H0.
    destruct (Z.eq_dec (Int.signed a) (Int.signed b)).
    simpl in H0. apply int_eq_e; trivial.
    exfalso. apply n. trivial.
  Qed.
  (* why was that so awful? *)

  Lemma body_getCell: semax_body Vprog (@Gprog size inf) f_getCell (@getCell_spec size inf).
  Proof.
    start_function.
    rewrite (SpaceAdjMatGraph_unfold _ id _ _ addresses u); trivial.
    assert (Zlength (map Int.repr (Znth u (@graph_to_mat size g id))) = size). {
      unfold graph_to_mat, vert_to_list.
      rewrite Znth_map; repeat rewrite Zlength_map.
      all: rewrite nat_inc_list_Zlength; lia.
    }
    assert (0 <= i < Zlength (map Int.repr (Znth u (@graph_to_mat size g id)))) by lia.
    assert (0 <= i < Zlength (Znth u (@graph_to_mat size g id))). {
      rewrite Zlength_map in H1. lia.
    }
    Intros.
    freeze FR := (iter_sepcon _ _) (iter_sepcon _ _).
    unfold list_rep.
    forward. forward. forward. thaw FR.
    rewrite (SpaceAdjMatGraph_unfold _ id _ _ addresses u); trivial.
    cancel.
  Qed.

  Definition keys_dist_linked_correctly i keys dist h :=
    forall k,
      Znth i keys = k ->
      find_item_by_key (heap_items h) k =
      [(k, Znth i dist, Int.repr i)] \/
      ~ In k (proj_keys h).
  
  Definition dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr keys_ptr temp_item arr addresses :=
    EX i : Z,
    EX h : heap,
    EX keys: list key_type,
    EX dist_and_prev : list int,
    PROP (heap_capacity h = size;
         heap_size h = i;
         (* Permutation keys (proj_keys h); *)
         forall j,
           0 <= j < i ->
           keys_dist_linked_correctly j keys dist_and_prev h;
         dist_and_prev = list_repeat (Z.to_nat i) (Int.repr inf);
         Zlength keys = i;
         forall j,
           0 <= j < i ->
           In (Znth j keys) (proj_keys h);

         forall item,
           In item (heap_items h) ->
           0 <= Int.signed (snd item) < size;

         forall item,
           In item (heap_items h) ->
           heap_item_priority item = Int.repr inf)

    LOCAL (temp _dist (pointer_val_val dist_ptr);
          temp _prev (pointer_val_val prev_ptr);
          temp _src (Vint (Int.repr src));
          temp _pq priq_ptr;
          temp _graph (pointer_val_val arr);
          temp _size (Vint (Int.repr size));
          temp _keys (pointer_val_val keys_ptr);
          temp _inf (Vint (Int.repr inf));
          temp _temp_item (pointer_val_val temp_item))
    SEP (valid_pq priq_ptr h;
         hitem_ (pointer_val_val temp_item);
        data_at Tsh
                (tarray tint size)
                (map Vint (map Int.repr keys) ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val keys_ptr);
        data_at Tsh
                (tarray tint size)
                (map Vint dist_and_prev ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val prev_ptr);
        data_at Tsh
                (tarray tint size)
                (map Vint dist_and_prev ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val dist_ptr);
        @SpaceAdjMatGraph size CompSpecs sh id
                          g (pointer_val_val arr) addresses;
        free_tok (pointer_val_val keys_ptr) (size * sizeof tint);
        free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr))).

  Definition src_picked_first h src (popped: list V) :=
    0 < Zlength (heap_items h) ->
    popped = [] ->
    forall min_item,
      In min_item (heap_items h) ->
      Forall (cmp_rel min_item) (heap_items h) ->
      src = Int.signed (snd min_item).
  
  Definition in_heap_or_popped (popped: list V) (h: heap) :=
    forall i_item,
      (In (Int.signed (snd i_item)) popped -> ~ In i_item (heap_items h)).

  Definition dijk_forloop_inv (g: @DijkGG size inf) sh src keys
             dist_ptr prev_ptr keys_ptr priq_ptr graph_ptr temp_item addresses :=
    EX prev : list V,
    EX dist : list Z,
    EX popped : list V,
    EX h : heap,
    PROP (
        dijkstra_correct g src popped prev dist;
      
      Znth src dist = 0;
      Znth src prev = src;

      popped <> [] -> In src popped;
      heap_capacity h = size;
      (* Permutation keys (proj_keys h); *)
      
      forall i,
        vvalid g i ->
        keys_dist_linked_correctly i keys (map Int.repr dist) h;

      src_picked_first h src popped;

      in_heap_or_popped popped h;      

      (* TODO:
         commenting out the two below for now, but I'll have to see
         if I need some new versions of these in the proofs later on *)

      (* A fact about the relationship b/w
         the priq and popped arrays *)
      (*
      forall v,
        vvalid g v ->
        In v popped <-> Znth v priq = Z.add inf 1;
       *)
      
      (* A fact about the relationship b/w 
         dist and priq arrays *)
      (*
      forall dst, vvalid g dst ->
                  ~ In dst popped ->
                  Znth dst priq = Znth dst dist;
       *)
      
      (* Information about the ranges of the three arrays *)
      @inrange_prev size inf prev;
      @inrange_dist inf dist;

      forall i,
        vvalid g i ->
        ~ In i popped ->
        In (Znth i keys) (proj_keys h);

      forall item,
        In item (heap_items h) ->
        0 <= Int.signed (snd item) < size)
         
         LOCAL (temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _keys (pointer_val_val keys_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf));
               temp _temp_item (pointer_val_val temp_item))
         SEP (valid_pq priq_ptr h;
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr prev))
                     (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr keys))
                     (pointer_val_val keys_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             hitem_ (pointer_val_val temp_item);
             free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr));
             free_tok (pointer_val_val keys_ptr) (size * sizeof tint)).
  
  Definition dijk_forloop_break_inv (g: @DijkGG size inf) sh
             src keys dist_ptr prev_ptr keys_ptr priq_ptr
             graph_ptr temp_item addresses :=
    EX prev: list V,
    EX dist: list Z,
    EX popped: list V,
    EX h : heap,
    PROP (

        (* This fact comes from breaking while *)
        heap_size h = 0;
         
      (* And the correctness condition is established *)
      dijkstra_correct g src popped prev dist)
         LOCAL (temp _pq priq_ptr;
               temp _temp_item (pointer_val_val temp_item);
               temp _keys (pointer_val_val keys_ptr))
         SEP (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             valid_pq priq_ptr h;
             data_at Tsh (tarray tint (heap_capacity h)) (map Vint (map Int.repr keys))
                     (pointer_val_val keys_ptr);
             data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) / sizeof tint))
                      (pointer_val_val temp_item);
             free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr));
             free_tok (pointer_val_val keys_ptr) (heap_capacity h * sizeof tint)).
  
  Definition dijk_inner_forloop_inv (g: @DijkGG size inf) sh
             src u ti min_item keys
             dist_ptr prev_ptr priq_ptr keys_ptr h graph_ptr addresses :=
    EX i : Z,
    EX prev' : list V,
    EX dist' : list Z,
    EX popped' : list V,
    EX h' : heap,

    PROP (
        (* inv_popped is not affected *)
        forall dst,
          vvalid g dst ->
          inv_popped g src popped' prev' dist' dst;
      
      (* inv_unpopped is restored for those vertices
         that the for loop has scanned and repaired *)
      forall dst,
        0 <= dst < i ->
        inv_unpopped g src popped' prev' dist' dst;
      
      (* a weaker version of inv_popped is
         true for those vertices that the
         for loop has not yet scanned *)
      forall dst,
        i <= dst < size ->
        inv_unpopped_weak g src popped' prev' dist' dst u;
      
      (* similarly for inv_unseen,
         the invariant has been
         restored until i:
         u has been taken into account *)
      forall dst,
        0 <= dst < i ->
        inv_unseen g src popped' prev' dist' dst;
      
      (* and a weaker version of inv_unseen is
         true for those vertices that the
         for loop has not yet scanned *)
      forall dst,
        i <= dst < size ->
        inv_unseen_weak g src popped' prev' dist' dst u;
      
      (* further, some useful facts about src... *)
      Znth src dist' = 0;
      Znth src prev' = src;
      popped' <> [] -> In src popped';

      src_picked_first h' src popped';
           
      (* a useful fact about u *)
      In u popped';

      (*
      (* A fact about the relationship b/w 
         priq and popped arrays *)
      forall v,
        vvalid g v ->
        In v popped' <-> Znth v priq' = Z.add inf 1;
      
      (* A fact about the relationship b/w 
         dist and priq arrays *)
      forall dst,
        vvalid g dst ->
        ~ In dst popped' ->
        Znth dst priq' = Znth dst dist';
       *)
      
      (* the lengths of the threee arrays *)
      Zlength dist' = size;
      Zlength prev' = size;
      heap_capacity h' = size;
                                                           
      (* and ranges of the three arrays *)
      @inrange_prev size inf prev';
      (* @inrange_priq inf priq'; *)
      @inrange_dist inf dist';

      forall i,
        vvalid g i ->
        ~ In i popped' ->
        In (Znth i keys) (proj_keys h');

      in_heap_or_popped popped' h';

      forall item,
        In item (heap_items h') ->
        0 <= Int.signed (snd item) < size)
         
         LOCAL (temp _u (Vint (Int.repr u));
               temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _keys keys_ptr;
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf));
               temp _temp_item (pointer_val_val ti))
         
         SEP (valid_pq priq_ptr h';
             data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev'))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist'))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id 
                               g (pointer_val_val graph_ptr) addresses;
             hitem min_item (pointer_val_val ti);
             data_at Tsh (tarray tint (heap_capacity h)) (map Vint (map Int.repr keys))
                     keys_ptr;
             free_tok (pointer_val_val ti) 12;
             free_tok keys_ptr (heap_capacity h * 4)).
  
  (* DIJKSTRA PROOF BEGINS *)

  Lemma body_dijkstra: semax_body Vprog (@Gprog size inf) f_dijkstra (@dijkstra_spec size inf).
  Proof.
    start_function.
    rename H1 into Hsz'.
    pose proof (size_further_restricted g).
    pose proof (inf_bounds g).
    rename H1 into Hsz.
    rename H2 into Hinf.
    assert (Hmaxranges: Int.max_signed <= Int.max_unsigned) by now compute.
    forward_call ((sizeof(Tstruct _structItem noattr))).
    Intros ti. rename H1 into H_mc_ti.
    forward_call (size * sizeof(tint)).
    1: simpl; lia.
    Intro keys_pv.
    remember (pointer_val_val keys_pv) as pre_keys.
    forward_call (size).
    1: split; rep_lia.
    Intros temp.
    destruct temp as [priq_ptr h]; simpl fst in *; simpl snd in *.
    rename H1 into H_mc_keys.
    rename H2 into H_h_sz.
    rename H3 into H_h_cap.

    forward_for_simple_bound
      size
      (dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr keys_pv ti graph_ptr addresses).
    - Exists h (@nil key_type) (@nil int).
      entailer!.
      1: { unfold heap_size in H_h_sz.
           apply Zlength_nil_inv in H_h_sz.
           rewrite H_h_sz in *.
           split; inversion 1.
      }
               
      remember (heap_capacity h) as size.
      rewrite app_nil_l, data_at__tarray.
      replace (size * sizeof tint / sizeof tint) with size.
      2: rewrite Z.div_mul; trivial; simpl; lia.
      entailer!. 
      apply (weaken_prehitem_ (pointer_val_val ti)).
      trivial.
      
    - rename keys into keys0.
      forward. forward.
      forward_call (priq_ptr, h0, inf, Int.repr i).
      1: lia.
      rename H7 into Hc.
      rename H8 into Hg.
      rename H9 into Hn.
      Intro temp'. destruct temp' as [h' key].
      forward.
      repeat rewrite upd_Znth_list_repeat; try lia.
      simpl fst in *. simpl snd in *.
      (* A number of tweaks to the keys array in SEP... *)
      rewrite upd_Znth_app2.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *.
           rewrite Zlength_list_repeat; lia.
      }
      replace (i - Zlength (map Vint (map Int.repr keys0))) with 0.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *. lia.
      }
      replace (Z.to_nat (size - i)) with (Z.to_nat 1 + Z.to_nat (size - (i + 1)))%nat.
      2: lia. 
      rewrite <- (list_repeat_app _ (Z.to_nat 1) (Z.to_nat (size - (i + 1)))).
      simpl list_repeat at 1.
      rewrite upd_Znth_app1.
      2: { rewrite binary_heap_Zmodel.Zlength_one. lia. }
      replace (upd_Znth 0 [Vundef] (Vint (Int.repr key))) with [(Vint (Int.repr key))].
      2: { rewrite upd_Znth0. reflexivity. }
      (* and done *)
      
      Exists h' (keys0 ++ [key]) (dist_and_prev ++ [Int.repr inf]).
      entailer!;
              remember (heap_capacity h) as size;
        remember (heap_size h0) as i;
        symmetry in Heqsize; rename Heqsize into H_h_cap;
          symmetry in Heqi; rename Heqi into H3;
            clear H9 H10 H11 H12 H13 H14 H15 H16 H17
              H18 H19 H20 PNpriq_ptr.
      + split3; [| |split3; [| |split3]].
        * rewrite <- H3. unfold heap_size.
          pose proof (Permutation_Zlength _ _ H8).
          rewrite Zlength_cons, <- Z.add_1_r in H5.
          symmetry. trivial.
        * red. intros.
          rewrite <- (list_repeat1 (Int.repr inf)).
          rewrite list_repeat_app, <- Z2Nat.inj_add by lia.
          rewrite Znth_list_repeat_inrange by lia.
          destruct (Z.eq_dec i j).
          -- subst j. left.
             admit. 
          (* H7: Permutation ((k, Int.repr inf, Int.repr i) :: heap_items h0) (heap_items h') *)

          -- assert (0 <= j < i) by lia.
             clear H5 n.
             rewrite Znth_app1 in H9 by lia.
             red in H4.
             specialize (H4 _ H10 _ H9). 
             rewrite Znth_list_repeat_inrange in H4 by lia.
             admit.
        * rewrite <- list_repeat1, list_repeat_app,
          Z2Nat.inj_add. trivial. lia. lia.
        * rewrite Zlength_app, binary_heap_Zmodel.Zlength_one.
          lia.
        * intros. destruct (Z.eq_dec i j).
          -- subst j; clear H5.
             rewrite Znth_app2 by lia.
             replace (i - Zlength keys0) with 0 by lia.
             rewrite Znth_0_cons.
             apply (Permutation_map heap_item_key), Permutation_sym in H8.
             unfold proj_keys.
             apply (Permutation_cons_In _ _ _ H8).
          -- assert (0 <= j < i) by lia. clear H5 n.
             rewrite Znth_app1 by lia.
             apply (Permutation_map heap_item_key) in H8.
             rewrite map_cons in H8.
             unfold proj_keys in Hc |- *.
             apply (Permutation_in _ H8).
             simpl. right. apply Hc; trivial.
        * intros.
          apply Permutation_sym in H8.
          apply (Permutation_in _ H8) in H5.
          simpl in H5. destruct H5.
          -- subst item. simpl snd.
             rewrite Int.signed_repr; rep_lia.
          -- apply Hg; trivial.
        * intros.
          apply Permutation_sym in H8.
          apply (Permutation_in _ H8) in H5.
          simpl in H5. destruct H5.
          -- subst item. unfold heap_item_priority; trivial.
          -- apply Hn; trivial.
          
      + repeat rewrite map_app; rewrite app_assoc; cancel.
        rewrite list_repeat1, upd_Znth_app2,
        Zlength_map, Zlength_list_repeat, Z.sub_diag,
        upd_Znth_app1, upd_Znth0, <- app_assoc.
        cancel.
        rewrite binary_heap_Zmodel.Zlength_one. lia.
        lia.
        rewrite Zlength_map, Zlength_app,
        binary_heap_Zmodel.Zlength_one,
        Zlength_list_repeat, Zlength_list_repeat. lia.
        lia. lia.
    - (* At this point we are done with the
       first for loop. The arrays are all set to inf. *)
      Intros ha keys dist_and_prev.
      (* the keys array will not change *)
      (* pre_keys are no longer needed *)
      clear Heqpre_keys H_mc_keys pre_keys.
      remember (pointer_val_val keys_pv) as keys_ptr.
      rename H6 into Hc.
      rename H7 into Hj.
      rename H8 into Hn.

      rewrite Z.sub_diag, list_repeat_0, app_nil_r, app_nil_r.
      assert (Htemp: 0 <= src < Zlength keys) by lia.
      forward. forward. forward.
      clear Htemp.
      forward_call (priq_ptr, ha, Znth src keys, Int.repr 0).
      Intros hb.
      rename H6 into H_ha_hb_rel.
      assert (H_hb_cap: heap_capacity hb = size) by lia.
      clear H7.
      (* Special values for src have been inserted *)
      
      (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
       *)
      
      forward_loop
      (dijk_forloop_inv g sh src keys dist_ptr prev_ptr keys_pv priq_ptr graph_ptr ti addresses)
      break: (dijk_forloop_break_inv g sh src keys dist_ptr prev_ptr keys_pv priq_ptr graph_ptr ti addresses).
      + unfold dijk_forloop_inv.
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) src).
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
        Exists (@nil V) hb.
        repeat rewrite <- upd_Znth_map; entailer!.

        clear H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
              H18 PNpriq_ptr PNkeys_ptr.
        
        remember (heap_capacity h) as size.
        assert (Htemp: Zlength (list_repeat (Z.to_nat size) inf) = size). {
          rewrite Zlength_list_repeat; ulia.
        }
        
        split3; [| |split3; [| |split3; [| |split3; [| |split]]]].
        * apply (dijkstra_correct_nothing_popped g src); trivial.
        * rewrite upd_Znth_same; ulia. 
        * rewrite upd_Znth_same; ulia.
        * red. intros.
          destruct (Z.eq_dec i src).
          -- subst i.
             rewrite upd_Znth_same.
             admit.
             rewrite Zlength_map, Zlength_list_repeat; lia.
          -- rewrite upd_Znth_diff; trivial.
             2,3: rewrite Zlength_map, Zlength_list_repeat; try lia.
             rewrite map_list_repeat, Znth_list_repeat_inrange.
             2,3: apply (vvalid_meaning g); trivial.
             admit.
        * red. intros.
          (* ha is all infs (see Hn)
             and hb is ha with src tweaked to 0 (see H_ha_hb_rel)
             and 0 < inf, 
             so this is true.
             Aquinas?
           *)
          admit.
        * red. intros. inversion H4.
        * red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
        * red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
        * intros.
          apply (Permutation_map heap_item_key) in H_ha_hb_rel.
          rewrite update_pri_by_key_unaffected in H_ha_hb_rel.
          apply Permutation_sym in H_ha_hb_rel.
          unfold proj_keys in Hc |- *.
          apply (Permutation_in _ H_ha_hb_rel), Hc, (vvalid_meaning g); trivial.          
        * intros.
          apply (Permutation_in _ H_ha_hb_rel) in H4.
          unfold update_pri_by_key in H4.
          apply list_in_map_inv in H4.
          destruct H4 as [orig [? ?]].
          unfold update_pri_if_key in H4.
          destruct (Z.eq_dec (Znth src keys) (heap_item_key orig)).
          -- subst item. simpl snd. unfold heap_item_payload.
             apply Hj; trivial.
          -- subst orig. apply Hj; trivial.
        * repeat rewrite map_list_repeat; cancel.

      + (* Now the body of the while loop begins. *)
        unfold dijk_forloop_inv.
        rename H1 into H_ha_cap.
        rename H2 into H_ha_size.
        rename H3 into H_keys_ha.
        subst dist_and_prev.
        rename H5 into H_keys_sz.

        Intros prev dist popped hc.
        (* may need a link between hc and hb? *)

        rename H11 into Hd.
        rename H12 into Hk.
                
        assert_PROP (Zlength prev = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (Zlength dist = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (NoDup (heap_items hc)). {
          sep_apply valid_pq_NoDup. entailer!.
        }

        rename H5 into H_hc_cap.
        rename H13 into H13'.
        forward_call (priq_ptr, hc).
        forward_if. (* checking if it's time to break *)
        * (* No, don't break. *)

          assert_PROP (0 <= heap_size hc <= Int.max_unsigned). {
            unfold valid_pq.
            Intros arr junk lookup l_contents.
            entailer!. 
            unfold heap_size. 
            pose proof (Zlength_nonneg junk). 
            split; [apply Zlength_nonneg|]. 
            apply Z.le_trans with (m := heap_capacity hc).
            1: rewrite <- H15, Zlength_app; lia.
            lia.
          }
          rewrite Int.unsigned_repr in H5 by trivial.
          freeze FR := (data_at _ _ _ _)
                         (data_at _ _ _ _)
                         (data_at _ _ _ _)
                         (free_tok _ _)
                         (free_tok _ _)
                         (SpaceAdjMatGraph _ _ _ _ _).      
          forward_call (priq_ptr,
                        hc,
                        pointer_val_val ti). 
          1: lia.

          (* hd is skipped because it is "head" *)
          Intros temp. destruct temp as [he min_item]. 
          simpl fst in *. simpl snd in *.

          thaw FR.
          unfold hitem.
          forward.
          replace (data_at Tsh t_item (heap_item_rep min_item) (pointer_val_val ti)) with (hitem min_item (pointer_val_val ti)).
          2: unfold hitem; trivial.
          simpl.
          remember (Int.signed (snd min_item)) as u.
          
          
          (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

          (* We prove a few useful facts about u: *)
          assert (H_u_valid: vvalid g u). {
            apply (vvalid_meaning g); trivial.
            subst u.
            apply Hk, (Permutation_cons_In _ _ _ H15).
          }
          
          assert (0 <= u < size). {
            apply (vvalid_meaning g) in H_u_valid; trivial.
          } 

          assert (Ha: In min_item (heap_items hc)). {
            apply Permutation_cons_In with (l2 := heap_items he); trivial.
          }
          assert (~ (In u popped)). {
            intro. apply (H8 min_item); trivial.
            subst u. trivial.
          }
                    
          assert (Htemp: 0 <= u < Zlength dist) by lia.
          pose proof (Znth_dist_cases _ _ Htemp H10).
          clear Htemp.
          
          (* This is the priq array with which
           we will enter the for loop.
           The dist and prev arrays are the same.
           Naturally, going in with this new priq
           and the old dist and prev means that
           dijkstra_correct is currently broken.
           The for loop will repair this and restore
           dijkstra_correct.
           *)


          forward_for_simple_bound
            size
            (dijk_inner_forloop_inv
            g sh src u ti min_item keys
               dist_ptr prev_ptr priq_ptr keys_ptr he graph_ptr addresses).
          -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
            (* We must prove the for loop's invariants for i = 0 *)
            Exists prev.
            Exists dist.
            Exists (u :: popped).
            Exists he.

            entailer!.
            2: {
              replace (heap_capacity h) with (heap_capacity he) by lia.
              cancel. 
            }
            remember (Int.signed (snd min_item)) as u.
            remember (heap_capacity h) as size. 
            symmetry in Heqsize.
            clear H20 H21 H22 H23 H24 H25 H26 H27 H28
                  H29 H30 H31 H32 H33 PNpriq_ptr.

            assert (Hl: popped = [] -> src = u). {
              intros. subst u.
              apply H7; trivial.
              (* min_item beat everyone in he
                 hc is min_item + everyone in he
                 min_item can beat everyone in he
                 and it can beat itself.
                 Aquinas?
               *)
              admit.
            }

            split3; [| | split3; [| |split3; [| |split3;
                    [| |split]]]]; trivial.
            ++ (* if popped = [], then 
                prove inv_popped for [u].
                if popped <> [], then we're set
                *)
               destruct popped eqn:?.
               2: {
                 (* TODO update the lemma *)
                 (* apply (inv_popped_add_u _ _ _ _ _ _ priq); try ulia. *)
                 (* apply H_popped_src_1; inversion 1. *)
                 admit.
               }
               replace u with src in * by now apply Hl.  
               intros. intro.
               simpl in H21; destruct H21; [|lia].
               subst dst; clear H20.
               destruct H19; [left | right].
               ** exfalso. rewrite H19 in H2. ulia.
               ** exists (src, []). split3.
                  --- split3; [| |split3]; trivial.
                      +++ split; trivial.
                      +++ rewrite path_cost.path_cost_zero; ulia.
                      +++ apply Forall_forall.
                          inversion 1.
                  --- unfold path_in_popped.
                      intros. 
                      inversion H20.
                      +++ simpl in H21. 
                          subst step. simpl; left; trivial.
                      +++ destruct H21 as [? [? _]].
                          inversion H21.
                  --- red. intros. rewrite path_cost.path_cost_zero; try ulia.
                      apply path_cost_pos; trivial.
  
            ++ intros.
               apply (vvalid_meaning g) in H20.
               apply inv_unpopped_weak_add_unpopped; trivial.

            ++ intros.
               apply (vvalid_meaning g) in H20.
               apply (inv_unseen_weak_add_unpopped g prev _ _ src); trivial.

            ++ intros. clear H20.
               destruct popped eqn:?.
               2: right; apply H4; inversion 1.
               simpl. left. symmetry. apply Hl; trivial.
               
            ++ red. intros. inversion H21.

            ++ apply in_eq.

            ++ intros. rewrite not_in_cons in H21; destruct H21.
               specialize (Hd _ H20 H22).
               unfold proj_keys in Hd |- *.
               pose proof (Permutation_map heap_item_key H15).
               apply (Permutation_in _ H23) in Hd. 
               simpl in Hd. destruct Hd as [Hd | ?]; trivial.
               exfalso. apply H21.
               (* u's key is the same as i's key.
                  u = i
                  Aquinas?
                *)
               admit.

            ++ red in H8 |- *. intros.
               specialize (H8 i_item). intro.
               replace i_item with min_item in *.
               2: {
                 assert (In i_item (heap_items hc)). {
                   apply (in_cons min_item) in H21.
                   apply Permutation_sym in H15.
                   apply (Permutation_in _ H15); trivial.
                 }
                 simpl in H20. destruct H20.
                 2: exfalso; apply H8; trivial.
                 rewrite H20 in Hequ.
                 apply Int_signed_strip in Hequ.
                 assert (NoDup (map snd (heap_items hc))) by admit.
                 
(* Aquinas, could you get me through? I sorta started... 
                    
apply (in_map snd) in H22.
apply In_nth_error in H22.
destruct H22 as [i_index ?].

apply (in_map snd) in Ha.
apply In_nth_error in Ha.
destruct Ha as [min_index ?].

 *)
(* if yes, I'll go back and get you the admitted assertion about NoDup *)

                 admit.
               }
               destruct (In_Permutation_cons _ _ H21) as [he' ?].
               pose proof (Perm_Perm_cons_Perm H15 H22).
               apply (NoDup_Perm_False H13' H23).
               
            ++ intros.
               apply (in_cons min_item) in H20.
               apply Permutation_sym in H15.
               apply (Permutation_in _ H15) in H20.
               apply Hk; trivial.

            ++ subst u.
               rewrite Int.repr_signed. trivial.

          -- (* We now begin with the for loop's body *)
            freeze FR := (data_at _ _ _ _) (data_at _ _ _ _)  (data_at _ _ _ _).
            assert (1 = 1) by trivial.
            Intros.
            
            rename H22 into H_inv_popped.
            rename H23 into H_inv_unpopped.
            rename H24 into H_inv_unpopped_weak.
            rename H25 into H_inv_unseen.
            rename H26 into H_inv_unseen_weak.
            rename H34 into H_h'_cap.
            rename H35 into H34.
            rename H36 into H35.
            rename H37 into He.
            rename H38 into Hf.
            rename H39 into Hl.

            forward_call (sh, g, graph_ptr, addresses, u, i).            
            remember (Znth i (Znth u (@graph_to_mat size g id))) as cost.

            assert (H_i_valid: vvalid g i). {
              apply (vvalid_meaning g); trivial.
            }

            rewrite <- elabel_Znth_graph_to_mat in Heqcost; try ulia.

            forward_if.
            ++ rename H22 into Htemp.
               assert (0 <= cost <= Int.max_signed / size). {
                 pose proof (edge_representable g (u, i)).
                 rewrite Heqcost in *.
                 apply (valid_edge_bounds g).
                 rewrite (evalid_meaning g). split; trivial.
                 rewrite Int.signed_repr in Htemp; trivial.
               }
               clear Htemp.
               assert (H_ui_valid: evalid g (u,i)). {
                 apply evalid_dijk with (cost0 := cost);
                   trivial.
               }
               
               assert (0 <= Znth u dist' <= inf). {
                 assert (0 <= u < Zlength dist') by lia.
                 apply (sublist.Forall_Znth _ _ _ H23) in H35.
                 assumption.
               }
               assert (0 <= Znth i dist' <= inf). {
                 assert (0 <= i < Zlength dist') by lia.
                 apply (sublist.Forall_Znth _ _ _ H24) in H35.
                 assumption.
               }
               assert (0 <= Znth u dist' + cost <= Int.max_signed). {
                 (* IMPORTANT:
                  the key point where 
                  we were forced to lower
                  inf's upper bound
                  *)
                 pose proof (inf_further_restricted g).
                 lia.
               }
               thaw FR.
               forward. forward. forward_if.

               ** rename H26 into H_improvement.
                  (* We know that we are definitely
                   going to make edits in the arrays:
                   we have found a better path to i, via u *)
                  rename H23 into Htemp.
                  assert (H23: 0 <= Znth u dist' < inf) by lia.
                  clear Htemp.

                  assert (H_i_not_popped: ~ In i (popped')). { 
                    apply (not_in_popped g src u i cost prev' dist'); trivial.
                  }
                  assert (Htemp : 0 <= i < Zlength dist') by lia.
                  pose proof (Znth_dist_cases i dist' Htemp H35).
                  clear Htemp.
                  rename H26 into icases.
                  (* rewrite <- H_priq_dist_link in icases; trivial. *)
                  (* hrmm this is gonna 
                     be a problem.
                     I need to be able to say that 
                     each item IN the PQ
                     is there at cost = or < inf
                   *) 

                  assert (0 <= i < Zlength keys) by lia.
                  forward. forward. forward. forward.
                  forward; rewrite upd_Znth_same; trivial.
                  1: entailer!.
                  1,3: repeat rewrite Zlength_map; lia.
                  forward_call (priq_ptr, h', Znth i keys, Int.repr (Znth u dist' + cost)).
                  
(* Now we must show that the for loop's invariant
   holds if we take another step,
   ie when i increments
                
   We will provide the arrays as they stand now:
   with the i'th cell updated in all three arrays,
   to log a new improved path via u 
 *)
                  Intros hf.
                  Exists (upd_Znth i prev' u).
                  Exists (upd_Znth i dist' (Znth u dist' + cost)).
                  Exists popped'.
                  Exists hf.
                  repeat rewrite <- upd_Znth_map.
                  entailer!.

                  clear H38 H39 H40 H41 H42 H43 H44 H45 H46
                        H47 H48 H49 H50
                        PNkeys_ptr PNpriq_ptr.

                  remember (Int.signed (snd min_item)) as u.
                  remember (heap_capacity h) as size.

                  remember (Znth u dist' + elabel g (u, i)) as newcost.
                  fold V in *. simpl id in *.
                  rewrite <- Heqnewcost in *.

                  assert (u <> i) by (intro; subst; lia).
                  
                  split3; [| | split3;
                               [| | split3;
                                    [| | split3;
                                         [| |split3;
                          [| |split3; [| |split3]]]]]];
                  intros.
                  (* 14 goals *)
                  --- apply inv_popped_newcost; ulia.
                  --- admit.
                      (* TODO update this lemma *)
                      (* apply inv_unpopped_newcost with (priq0 := priq'); ulia.  *)
                  --- now apply inv_unpopped_weak_newcost.
                  --- apply inv_unseen_newcost; ulia.
                  --- apply inv_unseen_weak_newcost; ulia. 
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- red. intros.
                      rewrite H40 in H31.
                      inversion H31.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- apply Forall_upd_Znth;  ulia.
                  --- apply Forall_upd_Znth;  ulia.
                  --- specialize (He _ H39 H40).
                      unfold proj_keys in He |- *.
                      apply (Permutation_map heap_item_key) in H36.
                      rewrite update_pri_by_key_unaffected in H36.
                      apply Permutation_sym in H36.
                      apply (Permutation_in _ H36); trivial.
                  --- red in Hf |- *.
                      intros some_item ?. intro. 
                      pose proof (Permutation_in _ H36 H40).
                      unfold update_pri_by_key in H41.
                      apply list_in_map_inv in H41.
                      destruct H41 as [x [? ?]].
                      unfold update_pri_if_key in H41.
                      destruct (Z.eq_dec (Znth i keys) (heap_item_key x)).
                      +++ rewrite e in *.
                          rewrite H41 in H39.
                          simpl in H39. unfold heap_item_payload in H39.
                          apply (Hf x); trivial.
                      +++ apply (Hf _ H39). subst x; trivial.
                  --- apply (Permutation_in _ H36) in H39.
                      unfold update_pri_by_key in H39.
                      apply list_in_map_inv in H39.
                      destruct H39 as [orig [? ?]].
                      unfold update_pri_if_key in H39.
                      destruct (Z.eq_dec (Znth i keys) (heap_item_key orig)).
                      +++ subst item. unfold heap_item_payload. simpl.
                          apply Hl; trivial.
                      +++ subst orig. apply Hl; trivial. 
                        
               ** (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                 rename H26 into H_non_improvement.
                 forward. 
                 (* The old arrays are just fine. *)
                 Exists prev' dist' popped' h'.
                 entailer!.
                 remember (Int.signed (snd min_item)) as u.
                 remember (heap_capacity h) as size.
                 
                 clear H26 H36 H37 H38 H39 H40 H41 H42 H43 H44
                       H45 H46 H47 PNkeys_ptr PNpriq_ptr.
                 
                 assert (elabel g (u, i) < inf). {
                   apply Z.le_lt_trans with (m := Int.max_signed / size);
                     trivial.
                   apply H22.
                   apply (inf_further_restricted g).
                 }
                 split3; [| |split].
                 --- intros. apply inv_unpopped_new_dst
                               with (u0 := u) (i0 := i); trivial.
                 --- intros. destruct (Z.eq_dec dst i).
                     +++ subst dst. lia.
                     +++ apply H_inv_unpopped_weak; lia.
                 --- intros. destruct (Z.eq_dec dst i).
                     2: apply H_inv_unseen; lia.

                     unfold inv_unseen; intros.
                     subst dst.

                     assert (i <= i < size) by lia.
                     destruct (Z.eq_dec m u).
                     2: now apply (H_inv_unseen_weak _ H42) with (m:=m).
                     subst m.
                     rename p2m into p2u.
                     rewrite H38 in H_non_improvement.
                     assert (0 <= u < size) by lia.
                     rewrite path_cost_glue_one_step.
                     destruct H41 as [_ [_ [_ [? _]]]].
                     simpl id in *. ulia.
                 --- intros.
                     assert (i <= dst < size) by lia.
                     apply H_inv_unseen_weak; trivial.
            ++  (* i was not a neighbor of u.
                 We must prove the for loop's invariant holds *)
              forward.
              Exists prev' dist' popped' h'.
              thaw FR.
              entailer!.
              remember (Int.signed (snd min_item)) as u.
              remember (heap_capacity h) as size.
              
              clear H23 H24 H25 H26 H36 H37 H38 H39 H40 H41
                    H42 H43 H44 PNkeys_ptr PNpriq_ptr.

              rewrite Int.signed_repr in H22.
              2: apply edge_representable.
              split3; [| |split]; intros.
              ** destruct (Z.eq_dec dst i).
                 --- subst dst. 
(* Will need to use the second half of the 
   for loop's invariant.          
   Whatever path worked for i then will 
   continue to work for i now:
   i cannot be improved by going via u 
 *)
                     unfold inv_unpopped; intros.
                     assert (i <= i < size) by lia.
                     destruct (H_inv_unpopped_weak i H26 H24 H25).
                     1: left; trivial.
                     destruct H36 as [? [[? [? [? [? [? ?]]]]]?]].
                     remember (Znth i prev') as mom.

                     assert (Znth mom dist' < inf). {
                       pose proof (edge_cost_pos g (mom, i)).
                       ulia.
                     }
                     
                     right. split3; [| |split3; [| |split3]]; trivial.
                     
                     intros.
                     destruct (@Znth_dist_cases inf mom' dist')
                       as [e | e]; trivial.
                     1: apply (vvalid_meaning g) in H45; ulia.
                     1: { rewrite e.
                          pose proof (edge_cost_pos g (mom', i)).
                          ulia.
                     }
                     
                     destruct (zlt (Znth mom' dist' +
                                    elabel g (mom', i)) inf).
                     2: ulia.
                     
                     destruct (Z.eq_dec mom' u).
                     1: { subst mom'.
                          assert (0 <= Znth u dist'). {
                            apply (sublist.Forall_Znth _ _ u) in H35.
                            simpl in H35. apply H35.
                            lia.
                          }
                          simpl id in *. ulia.
                     }
                     apply H43; trivial.
                 --- apply H_inv_unpopped; lia.
              ** destruct (Z.eq_dec dst i);
                   [| apply H_inv_unpopped_weak]; lia. 
              ** destruct (Z.eq_dec dst i).
                 2: apply H_inv_unseen; lia.
                 subst dst.
                 assert (i <= i < size) by lia.
                 unfold inv_unseen; intros.
                 destruct (Z.eq_dec m u).
                 2: now apply (H_inv_unseen_weak _ H24)
                   with (m:=m).
                 
                 subst m.
                 assert (0 <= Znth u dist'). {
                   apply (sublist.Forall_Znth _ _ u) in H35.
                   apply H35.
                   ulia.
                 }
                 rewrite path_cost_glue_one_step.
                 destruct H38 as [? _].
                 pose proof (path_cost_pos _ _ H38).
                 simpl id in *. ulia.
              ** apply H_inv_unseen_weak; lia.
          -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
            Intros prev' dist' popped' h'.
            replace (heap_capacity he) with size by lia.
            unfold dijk_forloop_inv.
            Exists prev' dist' popped' h'.
            entailer!.
            2: unfold hitem_, hitem; apply data_at_data_at_.
            
            remember (Int.signed (snd min_item)) as u.
            split.
            ++ unfold dijkstra_correct.
               split3; [auto | apply H21 | apply H23];
                 try rewrite <- (vvalid_meaning g); trivial.
            ++ red. intros.
               admit.
           
        * (* After breaking from the while loop,
           prove break's postcondition *)
          forward.
          unfold dijk_forloop_break_inv.
          Exists prev dist popped hc.
          assert (heap_capacity hc = heap_capacity h) by lia.
          assert_PROP (0 <= heap_size hc <= Int.max_unsigned). {
            unfold valid_pq.
            Intros arr junk lookup l_contents.
            entailer!. 
            unfold heap_size. 
            pose proof (Zlength_nonneg junk). 
            split; [apply Zlength_nonneg|]. 
            apply Z.le_trans with (m := heap_capacity hc).
            1: rewrite <- H16, Zlength_app; lia.
            lia.
          }
          rewrite H13. entailer!.
          clear -H5 H14.
          rewrite Int.unsigned_repr in H5 by trivial.
          unfold heap_size in *.
          pose proof (Zlength_nonneg (heap_items hc)).
          lia.
          admit.
          (* HELP is this the coercion you proved? *)
      + (* from the break's postcon, prove the overall postcon *)
        unfold dijk_forloop_break_inv.
        Intros prev dist popped hc.
        freeze FR := (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (SpaceAdjMatGraph _ _ _ _ _).

        forward_call (priq_ptr, hc).
        forward_call (Tsh, keys_pv, size, keys).
        entailer!. admit. (* has to do with freeing ti *)
        (* thaw FR. *)
        forward.
        Exists prev dist popped. entailer!.
        intros. destruct (H7 _ H10) as [? _]; trivial.
        admit.
        Unshelve. admit.
  Admitted. 

End DijkstraProof.
