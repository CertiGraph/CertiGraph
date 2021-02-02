Require Import CertiGraph.graph.SpaceAdjMatGraph1.
Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_math_proof.
Require Import CertiGraph.dijkstra.dijkstra_spec1.

Local Open Scope Z_scope.

Set Nested Proofs Allowed.

Section DijkstraProof.
  
  (* The invariants have been dragged out of the 
     proof for readability and reuse
   *)

  Context {size: Z}.
  Context {inf: Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.
  
  Lemma Permutation_cons_In: forall {A} (l1 l2: list A) a,
      Permutation l1 (a :: l2) -> In a l1.
  Proof.
    intros.
    pose proof (in_eq a l2).
    apply Permutation_sym in H.
    apply (Permutation_in _ H); trivial.
  Qed.

  Lemma update_pri_by_key_keys_unaffected:
  forall l key newpri,
    map heap_item_key (update_pri_by_key l key newpri) = map heap_item_key l.
  Proof.
    intros. induction l; trivial.
    simpl. rewrite IHl. f_equal.
    unfold update_pri_by_key, update_pri_if_key, heap_item_key.
    destruct (Z.eq_dec key (fst (fst a))); simpl fst; trivial.
  Qed.
  
  Lemma update_pri_by_key_payloads_unaffected:
  forall l key newpri,
    map heap_item_payload (update_pri_by_key l key newpri) = map heap_item_payload l.
  Proof.
    intros. induction l; trivial.
    simpl. rewrite IHl. f_equal.
    unfold update_pri_by_key, update_pri_if_key, heap_item_payload, heap_item_key.
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

  Lemma In_update_pri_by_key: forall i L k np,
      In i (update_pri_by_key L k np) ->
      (In i L /\ heap_item_key i <> k) \/
      (exists oi, In oi L /\ 
                  heap_item_key i = k /\ 
                  heap_item_payload i = heap_item_payload oi /\ 
                  heap_item_key i = heap_item_key oi /\
                  heap_item_priority i = np).
  Proof.
    intros.
    unfold update_pri_by_key in H.
    rewrite in_map_iff in H. destruct H as [oi [? ?]].
    revert H. unfold update_pri_if_key. case Z.eq_dec; intros.
    2: left; subst; auto.
    right. exists oi. split; trivial. subst i.
    unfold heap_item_key, heap_item_payload, heap_item_priority in *.
    simpl. tauto.
  Qed.


  Lemma body_getCell: semax_body Vprog (@Gprog size inf) f_getCell
                                 (@getCell_spec size inf).
  Proof.
    start_function.
    rewrite (SpaceAdjMatGraph_unfold _ id _ _ addresses u); trivial.
    assert (Zlength (map Int.repr (Znth u (@graph_to_mat size g id))) = size). {
      unfold graph_to_mat, vert_to_list.
      rewrite Znth_map; repeat rewrite Zlength_map.
      all: rewrite nat_inc_list_Zlength; lia.
    }
    assert (0 <= i < Zlength (map Int.repr
                                  (Znth u (@graph_to_mat size g id)))) by lia.
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
  
  Definition dijk_setup_loop_inv g sh src dist_ptr
             prev_ptr priq_ptr keys_ptr temp_ptr arr addresses :=
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

         Permutation (map heap_item_payload (heap_items h))
                     (map Int.repr (nat_inc_list (Z.to_nat i)));
         
         Forall (fun item =>
                   heap_item_priority item = Int.repr inf)
                (heap_items h);
         
         NoDup (map heap_item_payload (heap_items h));

         forall j,
           0 <= j < i ->
           In (Znth j keys, Int.repr inf, Int.repr j)
              (heap_items h);

         forall some_item,
           In some_item (heap_items h) ->
           Znth (Int.signed (heap_item_payload some_item)) keys =
           heap_item_key some_item;

         forall j,
           0 <= j < i ->
           exists j_item,
	     In j_item (heap_items h) /\
	     j = Int.signed (heap_item_payload j_item);

         NoDup keys;
         
         (Permutation
            keys
            (map heap_item_key (heap_items h))))
         
    LOCAL (temp _dist (pointer_val_val dist_ptr);
          temp _prev (pointer_val_val prev_ptr);
          temp _src (Vint (Int.repr src));
          temp _pq priq_ptr;
          temp _graph (pointer_val_val arr);
          temp _size (Vint (Int.repr size));
          temp _keys (pointer_val_val keys_ptr);
          temp _inf (Vint (Int.repr inf));
          temp _temp (pointer_val_val temp_ptr))
    SEP (valid_pq priq_ptr h;
         hitem_ (pointer_val_val temp_ptr);
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
        free_tok (pointer_val_val temp_ptr) (sizeof (Tstruct _structItem noattr))).

  Definition src_picked_first h src (popped: list V) :=
    0 < Zlength (heap_items h) ->
    popped = [] ->
    forall min_item,
      In min_item (heap_items h) ->
      Forall (cmp_rel min_item) (heap_items h) ->
      src = Int.signed (heap_item_payload min_item).
  
  Definition in_heap_or_popped (popped: list V) (h: heap) :=
    forall i_item,
      (In (Int.signed (heap_item_payload i_item)) popped -> ~ In i_item (heap_items h)).

  Definition dijk_forloop_inv (g: @DijkGG size inf) sh src keys
             dist_ptr prev_ptr keys_ptr priq_ptr graph_ptr temp_ptr addresses :=
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

      Forall (fun item =>
                0 <= Int.signed (heap_item_payload item) < size)
             (heap_items h);
      
      NoDup (map heap_item_payload (heap_items h));

      forall some_item,
        In some_item (heap_items h) ->
        Znth (Int.signed (heap_item_payload some_item)) keys =
        heap_item_key some_item;

      forall i,
        vvalid g i ->
        ~ In i popped ->
        exists i_item,
          In i_item (heap_items h) /\
          i = Int.signed (heap_item_payload i_item))
         
         LOCAL (temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _keys (pointer_val_val keys_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf));
               temp _temp (pointer_val_val temp_ptr))
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
             hitem_ (pointer_val_val temp_ptr);
             free_tok (pointer_val_val temp_ptr)
                      (sizeof (Tstruct _structItem noattr));
             free_tok (pointer_val_val keys_ptr) (size * sizeof tint)).
  
  Definition dijk_forloop_break_inv (g: @DijkGG size inf) sh
             src keys dist_ptr prev_ptr keys_ptr priq_ptr
             graph_ptr temp_ptr addresses :=
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
               temp _temp (pointer_val_val temp_ptr);
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
             data_at Tsh (tarray tint (heap_capacity h))
                     (map Vint (map Int.repr keys))
                     (pointer_val_val keys_ptr);
             data_at_ Tsh (tarray tint
                                  (sizeof (Tstruct _structItem noattr) / sizeof tint))
                      (pointer_val_val temp_ptr);
             free_tok (pointer_val_val temp_ptr)
                      (sizeof (Tstruct _structItem noattr));
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

      Forall (fun item =>
                0 <= Int.signed (heap_item_payload item) < size)
             (heap_items h');

      forall i,
        vvalid g i ->
        keys_dist_linked_correctly i keys (map Int.repr dist') h';

      NoDup (map heap_item_payload (heap_items h'));

      forall some_item : heap_item,
        In some_item (heap_items h') ->
        Znth (Int.signed (heap_item_payload some_item)) keys =
        heap_item_key some_item;
      
      forall i,
        vvalid g i ->
        ~ In i popped' ->
        exists i_item,
          In i_item (heap_items h') /\
          i = Int.signed (heap_item_payload i_item))
         
         LOCAL (temp _u (Vint (Int.repr u));
               temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _keys keys_ptr;
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf));
               temp _temp (pointer_val_val ti))
         
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
             data_at Tsh (tarray tint (heap_capacity h))
                     (map Vint (map Int.repr keys))
                     keys_ptr;
             free_tok (pointer_val_val ti) 12;
             free_tok keys_ptr (heap_capacity h * 4)).
  
  (* DIJKSTRA PROOF BEGINS *)

  Lemma body_dijkstra: semax_body Vprog (@Gprog size inf)
                                  f_dijkstra (@dijkstra_spec size inf).
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
      (dijk_setup_loop_inv g sh src dist_ptr
                           prev_ptr priq_ptr keys_pv ti graph_ptr addresses).
    - Exists h (@nil key_type) (@nil int).
      entailer!.
      1: { unfold heap_size in H_h_sz.
           apply Zlength_nil_inv in H_h_sz.
           rewrite H_h_sz in *.
           split3; [| |split3; [| |split]]; trivial; try apply Forall_nil.
           1,3: apply NoDup_nil.
           inversion 1.
      }
               
      remember (heap_capacity h) as size.
      rewrite app_nil_l, data_at__tarray.
      replace (size * sizeof tint / sizeof tint) with size.
      2: rewrite Z.div_mul; trivial; simpl; lia.
      entailer!. 
      apply (malloc_hitem (pointer_val_val ti)).
      trivial.
      
    - rename keys into keys0.
      forward. forward.
      forward_call (priq_ptr, h0, inf, Int.repr i).
      1: lia.
      rename H7 into Hc.
      rename H8 into Hg.
      rename H9 into Hn.
      rename H10 into Hp.
      rename H11 into Ht.
      rename H12 into Hx.
      rename H13 into Hb'.
      rename H14 into H_NoDup_keys.
      rename H15 into H_keys_perm.
             
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
      replace (upd_Znth 0 [Vundef] (Vint (Int.repr key))) with
          [(Vint (Int.repr key))].
      2: { rewrite upd_Znth0. reflexivity. }
      (* and done *)
      
      Exists h' (keys0 ++ [key]) (dist_and_prev ++ [Int.repr inf]).

      assert_PROP (NoDup (map heap_item_key (heap_items h'))). {
        sep_apply valid_heap_NoDup_keys. entailer!.
      }
      rename H9 into Hc'.
            
      entailer!;
              remember (heap_capacity h) as size;
        remember (heap_size h0) as i;
        symmetry in Heqsize; rename Heqsize into H_h_cap;
          symmetry in Heqi; rename Heqi into H3;
            clear H9 H10 H11 H12 H13 H14 H15 H16 H17
              H18 H19 H20 PNpriq_ptr.
      + split3; [| |split3;
                    [| |split3; [| |split3; [| |split3; [| |split3]]]]].
        * rewrite <- H3. unfold heap_size.
          pose proof (Permutation_Zlength _ _ H8).
          rewrite Zlength_cons, <- Z.add_1_r in H5.
          symmetry. trivial.
        * intros.
          destruct (Z.eq_dec i j).
          -- subst j; clear H5.
             red. intros.
             rewrite Znth_app2;
               rewrite Zlength_list_repeat; try lia.
             replace (i - i) with 0 by lia.
             rewrite Znth_0_cons.
             rewrite Znth_app2 in H5 by lia.
             replace (i - Zlength keys0) with 0 in H5 by lia.
             rewrite Znth_0_cons in H5. subst k.
             symmetry in H8.
             apply Permutation_cons_In in H8.
             left.
             clear -H8 Hc'.
             apply in_split in H8. destruct H8 as [L1 [L2 ?]].
             rewrite H in *. clear H h'.
             unfold find_item_by_key. rewrite filter_app. simpl.
             case Z.eq_dec; simpl. 2: destruct 1; trivial. intros _.
             rewrite map_app in Hc'. simpl in Hc'. apply NoDup_remove_2 in Hc'.
             apply not_In_app in Hc'. destruct Hc'.
             rewrite filter_empty, filter_empty; try reflexivity;
               intros; case Z.eq_dec; simpl; auto; intro; exfalso; 
                 [apply H0 | apply H]; rewrite <- e;
                   unfold heap_item_key at 1; simpl; apply in_map; trivial.
          -- assert (0 <= j < i) by lia.
             clear H5 n.
             red in H4 |- *.
             intros.
             rewrite Znth_app1 in H5 by lia.
             specialize (H4 _ H9 _ H5).
             destruct H4.
             ++ left. rewrite Znth_app1.
                2: rewrite Zlength_list_repeat; lia.
                clear -H4 H8 Hc'.
                apply Permutation_find_item_by_key with (k := k) in H8.
                change (?x :: ?y) with ([x] ++ y) in H8.
                rewrite find_item_by_key_app, H4 in H8.
                revert H8. unfold find_item_by_key at 1. simpl.
                case Z.eq_dec; simpl; intros.
                2: { apply Permutation_length_1_inv in H8. trivial. }
                exfalso. unfold heap_item_key in e. simpl in e. subst k.
                symmetry in H8.
                apply Permutation_map with (f := heap_item_key) in H8.
                unfold heap_item_key at 2 in H8.
                simpl in H8. remember (heap_items h'). clear -Hc' H8.
                apply Permutation_two_eq in H8.
                unfold find_item_by_key in H8.
                generalize (NoDup_filter _ (Z.eq_dec key) _ Hc'); intro.
                rewrite <- (filter_map_comm _ _ _
                                            (fun y :
                                                   key_type => Z.eq_dec key y)) in H8.
                change Z with key_type in *.
                rewrite H8 in H.
                inversion H. apply H2. left. trivial.
                intros [[? ?] ?]. unfold heap_item_key. simpl.
                case Z.eq_dec; case Z.eq_dec; auto. intros. destruct n. auto.
             ++ unfold find_item_by_key.
                specialize (Hc _ H9). rewrite H5 in Hc. exfalso.
                apply H4; trivial.
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
        *
          (* rewrite Forall_forall. intros item ?. *)
          apply (Permutation_map heap_item_payload), Permutation_sym in H8.
          apply (Permutation_trans H8). simpl.
          pose proof (nat_inc_list_plus_1_Permutation i).
          apply (Permutation_map Int.repr), Permutation_sym in H5.
          simpl in H5.
          apply (perm_skip (Int.repr i)) in Hg.
          apply (Permutation_trans Hg); trivial. lia.
        * rewrite Forall_forall. intros item ?.
          apply Permutation_sym in H8.
          apply (Permutation_in _ H8) in H5.
          simpl in H5. destruct H5.
          -- subst item. unfold heap_item_priority. trivial.
          -- rewrite Forall_forall in Hn.
             specialize (Hn _ H5). trivial.
        * apply (Permutation_map heap_item_payload) in H8.
          apply (Permutation_NoDup H8).
          simpl.
          apply NoDup_cons; trivial.
          intro.
          apply (Permutation_in _ Hg) in H5.
          apply list_in_map_inv in H5.
          destruct H5 as [? [? ?]].
          apply nat_inc_list_in_iff in H9. destruct H9.
          inversion H5.
          repeat rewrite Int.Z_mod_modulus_eq, Z.mod_small in H12;
            try ulia.
        * intros.
          apply (Permutation_in _ H8). simpl.
          destruct (Z.eq_dec i j).
          -- subst j. clear H5. left.
             rewrite Znth_app2 by lia.
             replace (i - Zlength keys0) with 0 by lia.
             rewrite Znth_0_cons. trivial. 
          -- assert (0 <= j < i) by lia.
             clear H5. right.
             rewrite Znth_app1 by lia. apply Ht; trivial.
        * intros.
          symmetry in H8.
          apply (Permutation_in _ H8) in H5.
          simpl in H5. destruct H5.
          -- subst some_item. simpl.
             rewrite Int.signed_repr by ulia.
             rewrite Znth_app2 by lia.
             replace (i - Zlength keys0) with 0 by lia.
             rewrite Znth_0_cons.
             unfold heap_item_key. trivial.
          -- rewrite Znth_app1. apply Hx; trivial.
             replace (Zlength keys0) with i by lia.
             eapply in_map in H5.
             eapply Permutation_in in H5. 2: apply Hg.
             apply In_Znth_iff in H5.
             destruct H5 as [loc [? ?]].
             rewrite Zlength_map in H5.
             rewrite Znth_map in H9; auto.
             rewrite nat_inc_list_i in H9.
             1,2: rewrite nat_inc_list_Zlength in H5; trivial.
             rewrite <- H9.
             rewrite Z2Nat.id in H5. 2: lia.
             rewrite Int.signed_repr by ulia. lia.
        * intros. destruct (Z.eq_dec i j).
          -- subst j. clear H5.
             exists (key, Int.repr inf, Int.repr i).
             split; [|simpl; rewrite Int.signed_repr; ulia].
             apply (Permutation_in _ H8). simpl.
             left; trivial.
          -- assert (0 <= j < i) by lia.
             specialize (Hb' _ H9).
             destruct Hb' as [? [? ?]].
             exists x. split; trivial.
             apply (Permutation_in _ H8). right; trivial.
        * pose proof (Permutation_cons_append keys0 key).
          apply (Permutation_NoDup H5). clear H5.
          apply NoDup_cons; trivial.
          apply (Permutation_map heap_item_key) in H8.
          symmetry in H8.
          apply (Permutation_NoDup H8) in Hc'.
          simpl in Hc'.
          apply NoDup_cons_2 in Hc'.
          unfold heap_item_key in Hc' at 1. simpl in Hc'.
          intro.
          apply (Permutation_in _ H_keys_perm) in H5. contradiction.
        * pose proof (Permutation_cons_append keys0 key).
          symmetry in H5.
          apply (Permutation_trans H5).
          apply (Permutation_map heap_item_key) in H8.
          simpl in H8. 
          apply Permutation_trans with
              (l' :=
                 (heap_item_key (key, Int.repr inf, Int.repr i)
                                :: map heap_item_key (heap_items h0)));
            trivial.
          unfold heap_item_key at 1. simpl.
          apply perm_skip. trivial.
          
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
      rename H9 into Hq.
      rename H10 into Hu.
      rename H11 into Hy.
      rename H12 into Hc'.
      rename H13 into H_NoDup_keys.
      clear H14.

      assert_PROP (NoDup (map heap_item_key (heap_items ha))). {
        sep_apply valid_heap_NoDup_keys. entailer!.
      }
      rename H6 into Hr.
     
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
        (dijk_forloop_inv g sh src keys
                          dist_ptr prev_ptr keys_pv priq_ptr
                          graph_ptr ti addresses)
        break: (dijk_forloop_break_inv
                  g sh src keys dist_ptr prev_ptr
                  keys_pv priq_ptr graph_ptr ti addresses).
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
        
        split3; [| |split3; [| |split3; [| |split3;
                                            [| |split3; [| |split3]]]]].
        * apply (dijkstra_correct_nothing_popped g src); trivial.
        * rewrite upd_Znth_same; ulia. 
        * rewrite upd_Znth_same; ulia.
        * red in H3 |- *. intros.
          left.
          apply (vvalid_meaning g) in H4.
          specialize (H3 _ H4 _ H6).
          destruct (Z.eq_dec i src).
          -- subst i.
             rewrite upd_Znth_same.
             2: rewrite Zlength_map, Zlength_list_repeat; lia.
             specialize (Hu _ H4). rewrite H6 in Hu.
             destruct H3. 2: { destruct H3. unfold proj_keys.
               change k with (heap_item_key (k, Int.repr inf, Int.repr src)).
               apply in_map. trivial. }
             rewrite Znth_list_repeat_inrange in H3; trivial.
             apply Permutation_find_item_by_key with (k := k) in H_ha_hb_rel.
             rewrite H6 in H_ha_hb_rel.
             rewrite find_item_by_key_update_pri_by_key with 
               (op := Int.repr inf) (v := Int.repr src) in H_ha_hb_rel; trivial.
             symmetry in H_ha_hb_rel. apply Permutation_length_1_inv in H_ha_hb_rel.
             trivial.
          -- rewrite upd_Znth_diff; trivial.
             2,3: rewrite Zlength_map, Zlength_list_repeat; try lia.
             rewrite map_list_repeat, Znth_list_repeat_inrange by lia.
             rewrite Znth_list_repeat_inrange in H3 by lia.
             destruct H3. 2: { destruct H3. rewrite <- H6. apply Hc. trivial. }
             assert (Znth src keys <> k). {
               intro. clear -H H4 H6 n H_NoDup_keys H7 H5.
               pose proof (NoDup_nth keys Inhabitant_Z).
               rewrite H0 in H_NoDup_keys. clear H0.
               rewrite <- H7 in H6.
               do 2 rewrite <- nth_Znth in H6. 2-4: lia.
               rewrite Zlength_correct in H5.
               apply H_NoDup_keys in H6; lia.
             }
             apply Permutation_find_item_by_key with (k := k) in H_ha_hb_rel.
             rewrite find_item_by_key_update_pri_by_key' in H_ha_hb_rel; auto.
             rewrite H3 in H_ha_hb_rel. symmetry in H_ha_hb_rel.
             apply Permutation_length_1_inv in H_ha_hb_rel. trivial.
        * red. intros.
          generalize H_ha_hb_rel; intro Hx.
          apply (Permutation_in min_item) in H_ha_hb_rel; trivial.
          apply In_update_pri_by_key in H_ha_hb_rel.
          assert (Hxxx: In (Znth src keys, Int.repr inf, Int.repr src)
                           (heap_items ha)). {
            apply Hu; trivial.
          }
          destruct H_ha_hb_rel as [[? ?] | ?].
          -- rewrite Forall_forall in H8.
             specialize (H8 (Znth src keys, Int.zero, Int.repr src)).
             spec H8. symmetry in Hx.
             apply (Permutation_in (Znth src keys, Int.zero, Int.repr src)) in
                 Hx; auto.
             unfold update_pri_by_key.
             rewrite in_map_iff.
             exists (Znth src keys, Int.repr inf, Int.repr src).
             unfold update_pri_if_key, heap_item_key. simpl.
             case Z.eq_dec. 2: intro Hxx; contradiction. intros _.
             split. trivial. trivial.
             clear -H9 H8 Hn Hinf.
             unfold cmp_rel, cmp, heap_item_priority in *. simpl in H8.
             rewrite Forall_forall in Hn.
             rewrite (Hn _ H9) in H8.
             remember (Int.lt Int.zero (Int.repr inf)). destruct b. discriminate.
             symmetry in Heqb.
             apply lt_false_inv in Heqb.
             unfold Int.zero in Heqb.
             rewrite Int.signed_repr in Heqb.
             rewrite Int.signed_repr in Heqb.
             1-3: rep_lia.
          -- destruct H9 as [oi [? [? [? [? ?]]]]].
             destruct min_item as [[m1 m2] m3].
             unfold heap_item_key, heap_item_payload, heap_item_priority in *.
             simpl in *.
             subst m2 m3.
             destruct oi as [[o1 o2] o3]. simpl in *. subst o1. subst m1.
             rewrite Forall_forall in Hn.
             generalize (Hn _ H9); intro. simpl in H10. subst o2.
             rename Hr into H10.
             replace (fun hi : heap_item => fst (fst hi)) with
                 heap_item_key in H10.
             2: unfold heap_item_key; trivial.
             clear -H10 Hxxx H9 Hsz H. rename H into Hsz'.
             apply in_split in H9. destruct H9 as [L1 [L2 ?]].
             rewrite H in *. apply in_app_or in Hxxx.
             rewrite map_app in H10. simpl in H10.
             apply NoDup_remove_2 in H10.
             unfold heap_item_key in H10 at 1. simpl in H10.
             destruct Hxxx. destruct H10.
             apply in_or_app. left.
             apply (in_map heap_item_key) in H0.
             apply H0.
             destruct H0. inversion H0. rewrite Int.signed_repr; auto. rep_lia.
             destruct H10.
             apply in_or_app. right.
             apply (in_map heap_item_key) in H0.
             apply H0.
        * red. intros. inversion H4.
        * red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
        * red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
        * intros.
          apply (Permutation_map heap_item_key) in H_ha_hb_rel.
          rewrite update_pri_by_key_keys_unaffected in H_ha_hb_rel.
          apply Permutation_sym in H_ha_hb_rel.
          unfold proj_keys in Hc |- *.
          apply (Permutation_in _ H_ha_hb_rel), Hc, (vvalid_meaning g); trivial.      
        * rewrite Forall_forall. intros.
          apply (Permutation_in _ H_ha_hb_rel) in H4.
          unfold update_pri_by_key in H4.
          apply list_in_map_inv in H4.
          destruct H4 as [orig [? ?]].
          unfold update_pri_if_key in H4.
          destruct (Z.eq_dec (Znth src keys) (heap_item_key orig)).
          -- subst x. simpl.
             apply (in_map heap_item_payload), (Permutation_in _ Hj) in H6.
             apply list_in_map_inv in H6.
             destruct H6 as [? [? ?]].
             apply nat_inc_list_in_iff in H6.
             rewrite Z2Nat.id in H6 by lia.
             rewrite H4, Int.signed_repr; ulia.
          -- subst x.
             apply (in_map heap_item_payload), (Permutation_in _ Hj) in H6.
             apply list_in_map_inv in H6.
             destruct H6 as [? [? ?]].
             apply nat_inc_list_in_iff in H6.
             rewrite Z2Nat.id in H6 by lia.
             rewrite H4, Int.signed_repr; ulia.
        * apply (Permutation_map heap_item_payload), Permutation_sym in H_ha_hb_rel.
          rewrite update_pri_by_key_payloads_unaffected in H_ha_hb_rel.
          apply (Permutation_NoDup H_ha_hb_rel); trivial.
        * intros.
          apply (Permutation_in _ H_ha_hb_rel) in H4.
          apply In_update_pri_by_key in H4.
          destruct H4 as [[? ?] | ?].
          1: apply Hy; trivial.
          destruct H4 as [? [? [? [? [? ?]]]]].
          specialize (Hy _ H4).
          rewrite H7, H8; trivial.          
        * intros i ? _.
          apply (vvalid_meaning g) in H4.
          specialize (Hc' _ H4).
          destruct Hc' as [? [? ?]].
          exists (update_pri_if_key
                    (Znth src keys)
                    (Int.repr 0)
                    x).
          split.
          -- symmetry in H_ha_hb_rel.
             apply (Permutation_in _ H_ha_hb_rel).
             unfold update_pri_by_key.
             apply in_map; trivial.
          -- unfold update_pri_if_key.
             destruct (Z.eq_dec (Znth src keys)
                                (heap_item_key x)); trivial.
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
        rename H13 into Hs.
        rename H14 into Ht.
        rename H15 into Hz.
                
        assert_PROP (Zlength prev = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (Zlength dist = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (NoDup (heap_items hc)). {
          sep_apply valid_pq_NoDup. entailer!.
        }
        assert_PROP (NoDup (map heap_item_key (heap_items hc))). {
          sep_apply valid_heap_NoDup_keys. entailer!.
        }
        rename H14 into Hd'.


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
            1: rewrite <- H16, Zlength_app; lia.
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
          replace (data_at Tsh t_item (heap_item_rep min_item)
                           (pointer_val_val ti)) with
              (hitem min_item (pointer_val_val ti)).
          2: unfold hitem; trivial.
          simpl.
          remember (Int.signed (snd min_item)) as u.
          
          
          (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

          (* We prove a few useful facts about u: *)
          assert (H_u_valid: vvalid g u). {
            apply (vvalid_meaning g); trivial.
            subst u.
            rewrite Forall_forall in Hk.
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
              apply Forall_forall.
              intros.
              rewrite Forall_forall in H16.
              specialize (H16 x).
              apply (Permutation_in x) in H15; trivial.
              destruct H15. subst x. reflexivity. auto.
            }

            split3; [| | split3; [| |split3; [| |split3;
                                                 [| |split3; [| |split3;
                    [| |split]]]]]]; trivial.
            ++ (* if popped = [], then 
                prove inv_popped for [u].
                if popped <> [], then we're set
                *)
               destruct popped eqn:?.
               2: {
                 intros.
                 replace (heap_capacity h) with size in *.
                 apply inv_popped_add_u'; try ulia.
                 1: apply H4; inversion 1.
                 rewrite <- Heql in *.
                 intros.
                 
                 specialize (Hz _ H21 H22).
                 destruct Hz as [i_item [? ?]].
                 
                 assert (cmp_rel min_item i_item). {
                   clear -H23 Ha H15 H16.
                   eapply Permutation_in in Ha.
                   eapply Permutation_in in H23. 2,3: apply H15.
                   destruct H23. subst. reflexivity.
                   rewrite Forall_forall in H16. auto.
                 }
                 unfold cmp_rel, cmp in H25. revert H25.
                 case_eq (Int.lt (heap_item_priority i_item)
                                 (heap_item_priority min_item)).
                 discriminate. intros ? _.
                 apply lt_false_inv in H25.
                 red in H6.
                 replace (Int.signed (heap_item_priority i_item)) with
                     (Znth i dist) in H25.
                 replace (Int.signed (heap_item_priority min_item)) with
                     (Znth u dist) in H25.
                 lia.

                 - specialize (Ht _ Ha).
                   unfold heap_item_payload in Ht.
                   rewrite <- Hequ in Ht.
                   specialize (H6 _ H_u_valid _ Ht).
                   destruct H6.
                   2: { exfalso. apply H6. unfold proj_keys.
                        apply in_map; trivial.
                   }
                   rewrite find_item_by_key_finds_item in H6; trivial.
                   inversion H6.
                   unfold heap_item_priority. simpl.
                   rewrite Znth_map, Int.signed_repr; ulia.
                   
                 - specialize (Ht _ H23).
                   unfold heap_item_payload in Ht.
                   unfold heap_item_payload in H24.
                   rewrite <- H24 in Ht.
                   specialize (H6 _ H21 _ Ht).
                   destruct H6.
                   2: { exfalso. apply H6. unfold proj_keys.
                        apply in_map; trivial.
                   }
                   rewrite find_item_by_key_finds_item in H6; trivial.
                   inversion H6.
                   unfold heap_item_priority. simpl.
                   apply (vvalid_meaning g) in H21.
                   rewrite Znth_map, Int.signed_repr; try ulia.
                   red in H10. rewrite Forall_forall in H10.
                   assert (In (Znth i dist) dist). {
                     apply Znth_In. lia.
                   }
                   specialize (H10 _ H26).
                   ulia.
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
               simpl in Hd.

               destruct Hd as [Hd | ?]; trivial.
               exfalso. apply H21.
               clear -H22 Hz H8 Hd Hequ Ha H6 H20 H_u_valid Ht.
               assert (exists i_item,
                          In i_item (heap_items hc) /\
                          i = Int.signed (snd i_item)). {
                 apply Hz; trivial.
               }
               clear H8 H22.
               destruct H as [i_item [Hb ?]].
               
               generalize (H6 _ H20 _ eq_refl); intro.
               destruct H0. 2: {
                 destruct H0. rewrite <- Hd.
                 unfold proj_keys. apply in_map. trivial.
               }
               generalize (H6 _ H_u_valid (heap_item_key min_item)); intro.
               destruct H1. subst u; apply Ht; trivial.
               2: { destruct H1. apply in_map. trivial. }
               rewrite Hd in H1 at 1. rewrite H0 in H1. inversion H1.
               apply (vvalid_meaning g) in H20.
               apply (vvalid_meaning g) in H_u_valid.
               repeat rewrite Int.Z_mod_modulus_eq, Z.mod_small in H5; ulia.

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
                 rename Hs into H23.
                 destruct min_item as [[mi1 mi2] mi3].
                 destruct i_item as [[i1 i2] i3].
                 simpl in Hequ. subst i3.
                 clear -Ha H22 H23.
                 apply in_split in Ha. destruct Ha as [l1 [l2 ?]].
                 rewrite H in H23.
                 rewrite map_app in H23. simpl in H23.
                 apply NoDup_remove in H23. destruct H23.
                 rewrite H in H22.
                 apply in_app_or in H22.
                 destruct H22. exfalso. apply H1. apply in_or_app. left.
                 apply in_map_iff. exists (i1, i2, mi3). auto.
                 destruct H2. trivial.
                 exfalso. apply H1. apply in_or_app. right.
                 apply in_map_iff. exists (i1, i2, mi3). auto. 
               }
               destruct (In_Permutation_cons _ _ H21) as [he' ?].
               pose proof (Perm_Perm_cons_Perm H15 H22).
               apply (NoDup_Perm_False H13' H23).
               
            ++ rewrite Forall_forall. intros.
               apply (in_cons min_item) in H20.
               apply Permutation_sym in H15.
               apply (Permutation_in _ H15) in H20.
               rewrite Forall_forall in Hk. apply Hk; trivial.
            ++ red in H6 |- *. intros.
               specialize (H6 _ H20 _ H21).
               destruct H6.
               ** (* i used to be in hc, but some minimum has been tossed
                     from hc. the question becomes whether i was that min.
                   *)
                 apply (vvalid_meaning g) in H20.
                 apply (vvalid_meaning g) in H_u_valid.                   
                 clear -H6 H15 H20 H21 Hequ Hd' Ht Ha H_keys_sz
                           H_u_valid H_NoDup_keys.
                 destruct (Z.eq_dec i u).
                 --- subst i. right. intro.
                     apply (Permutation_map heap_item_key) in H15.
                     apply (Permutation_NoDup H15) in Hd'.
                     simpl in Hd'.
                     apply NoDup_cons_2 in Hd'. apply Hd'.
                     unfold proj_keys in H.
                     replace k with (heap_item_key min_item) in H; trivial.
                     specialize (Ht _ Ha).
                     rewrite <- Ht, <- H21, Hequ. f_equal.
                     
                 --- left. unfold find_item_by_key in *.
                     apply (Permutation_filter _ _ _
                              (fun item : heap_item =>
                                 Z.eq_dec (heap_item_key item) k))
                       in H15.
                     rewrite H6 in H15.
                     apply Permutation_length_1_inv in H15.
                     simpl in H15.
                     destruct (Z.eq_dec (heap_item_key min_item) k).
                     +++ simpl in H15. exfalso.
                         specialize (Ht _ Ha).
                         rewrite <- Ht, <- H21 in e.
                         unfold heap_item_payload in e. rewrite <- Hequ in e.
                         apply n.
                         do 2 rewrite <- nth_Znth in e; try lia.
                         pose proof (NoDup_nth keys Inhabitant_Z).
                         rewrite H in H_NoDup_keys.
                         specialize (H_NoDup_keys (Z.to_nat u) (Z.to_nat i)).
                         spec H_NoDup_keys. rewrite <- ZtoNat_Zlength; lia.
                         spec H_NoDup_keys. rewrite <- ZtoNat_Zlength; lia.
                         ulia.
                     +++ simpl in H15; trivial.
                     
               ** right. intro. apply H6.
                  unfold proj_keys in *.
                  apply (Permutation_map heap_item_key) in H15.
                  rewrite map_cons in H15.
                  apply (in_cons (heap_item_key min_item)) in H22.
                  apply Permutation_sym in H15.
                  apply (Permutation_in _ H15) in H22; trivial.
            ++ clear -Hs H15.
               assert (In min_item (heap_items hc)) by
                   (eapply Permutation_cons_In; eauto).
               apply in_split in H. destruct H as [L1 [L2 ?]].
               rewrite H in H15.
               symmetry in H15. apply Permutation_cons_app_inv in H15.
               apply (Permutation_map heap_item_payload) in H15.
               symmetry in H15.
               eapply Permutation_NoDup. apply H15. rewrite H in Hs.
               rewrite map_app in Hs. simpl in Hs.
               eapply NoDup_remove_1 in Hs. rewrite map_app. apply Hs.
            ++ intros.
               symmetry in H15.
               apply (in_cons min_item),
               (Permutation_in _ H15) in H20.
               apply Ht; trivial.
            ++ intros. apply not_in_cons in H21.
               destruct H21.
               specialize (Hz _ H20 H22).
               destruct Hz as [? [? ?]].
               exists x; split; trivial.
               rewrite Hequ, H24 in H21.
               unfold heap_item_payload in H21.
               assert (x <> min_item). {
                 intro. subst x. apply H21. trivial.
               }
               clear H21.
               apply (Permutation_in _ H15) in H23.
               simpl in H23. destruct H23; trivial.
               exfalso; apply H25; symmetry; trivial.
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
            rename H40 into Ho.
            rename H41 into Hv.
            rename H42 into Hw.
            rename H43 into Ha'.

            forward_call (sh, g, graph_ptr, addresses, u, i).            
            remember (Znth i (Znth u (@graph_to_mat size g id))) as cost.

            assert (H_i_valid: vvalid g i). {
              apply (vvalid_meaning g); trivial.
            }

            rewrite <- elabel_Znth_graph_to_mat in Heqcost; try ulia.

            forward_if.
            ++ rename H22 into Htemp.
               assert (0 <= cost <= Int.max_signed / size - 1). {
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
                  forward_call (priq_ptr, h',
                                Znth i keys, Int.repr (Znth u dist' + cost)).
                  
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
                          [| |split3; [| |split3; [| |split3; [| |split3]]]]]]]];
                  intros.
                  (* 19 goals *)
                  --- apply inv_popped_newcost; ulia.
                  --- apply inv_unpopped_newcost'; ulia.
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
                      rewrite update_pri_by_key_keys_unaffected in H36.
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
                  --- rewrite Forall_forall. intros.
                      apply (Permutation_in _ H36) in H39.
                      unfold update_pri_by_key in H39.
                      apply list_in_map_inv in H39.
                      destruct H39 as [orig [? ?]].
                      unfold update_pri_if_key in H39.
                      destruct (Z.eq_dec (Znth i keys) (heap_item_key orig)).
                      +++ subst x. unfold heap_item_payload. simpl.
                          rewrite Forall_forall in Hl. apply Hl; trivial.
                      +++ subst orig. rewrite Forall_forall in Hl.
                          apply Hl; trivial.
                  --- red in Ho |- *.
                      intros.
                      specialize (Ho _ H39 _ H40).
                      destruct Ho.
                      +++ left.
                          apply (vvalid_meaning g) in H39.
                          destruct (Z.eq_dec i0 i).
                          *** subst i0.
                              rewrite upd_Znth_same.
                              2: rewrite Zlength_map; lia.
                              apply Permutation_find_item_by_key with (k := k) in H36.
                              rewrite H40 in H36.
                              rewrite (find_item_by_key_update_pri_by_key
                                         _ _ (Int.repr (Znth i dist'))
                                         (Int.repr i) _) in H36.
                              symmetry in H36.
                              apply Permutation_length_1_inv in H36; trivial.
                              rewrite Znth_map in H41; ulia.
                              
                          *** rewrite upd_Znth_diff; trivial.
                              2,3: rewrite Zlength_map; try lia.
                              assert (Znth i keys <> k). {
                                intro.
                                pose proof (NoDup_nth keys Inhabitant_Z).
                                rewrite H43 in H_NoDup_keys. clear H43.
                                rewrite <- H42 in H40.
                                do 2 rewrite <- nth_Znth in H40. 2-4: lia.
                                rewrite Zlength_correct in H_keys_sz.
                                apply H_NoDup_keys in H40; lia.
                              }
                              apply Permutation_find_item_by_key with (k := k) in H36.
                              rewrite find_item_by_key_update_pri_by_key' in H36; auto.
                              rewrite H41 in H36. symmetry in H36.
                              apply Permutation_length_1_inv in H36. trivial.
                      +++ right. intro. apply H41.
                          unfold proj_keys in *.
                          apply (Permutation_map heap_item_key) in H36.
                          rewrite update_pri_by_key_keys_unaffected in H36.
                          apply (Permutation_in _ H36) in H42; trivial.
                  --- apply (Permutation_map heap_item_payload) in H36.
                      rewrite update_pri_by_key_payloads_unaffected in H36.
                      symmetry in H36.
                      apply (Permutation_NoDup H36); trivial.
                  --- apply (Permutation_in _ H36) in H39.
                      apply In_update_pri_by_key in H39.
                      destruct H39 as [[? ?] | ?].
                      1: apply Hw; trivial.
                      destruct H39 as [? [? [? [? [? ?]]]]].
                      specialize (Hw _ H39).
                      rewrite H41, H42; trivial.
                  --- specialize (Ha' _ H39 H40).
                      destruct Ha' as [? [? ?]].
                      exists (update_pri_if_key
                                (Znth i keys)
                                (Int.repr newcost)
                                x).
                      split.
                      +++ symmetry in H36.
                          apply (Permutation_in _ H36).
                          unfold update_pri_by_key.
                          apply in_map; trivial.
                      +++ unfold update_pri_if_key.
                          destruct (Z.eq_dec (Znth i keys)
                                             (heap_item_key x)); trivial.
                      
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
                   apply Z.le_lt_trans with (m := Int.max_signed / size - 1);
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
                                                     
            unfold dijkstra_correct.
            split3; [auto | apply H21 | apply H23];
              try rewrite <- (vvalid_meaning g); trivial.
            
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
            1: rewrite <- H17, Zlength_app; lia.
            lia.
          }
          rewrite H13. entailer!.
          clear -H5 H14.
          rewrite Int.unsigned_repr in H5 by trivial.
          unfold heap_size in *.
          pose proof (Zlength_nonneg (heap_items hc)).
          lia.
          apply free_hitem.
      + (* from the break's postcon, prove the overall postcon *)
        unfold dijk_forloop_break_inv.
        Intros prev dist popped hc.
        freeze FR := (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (SpaceAdjMatGraph _ _ _ _ _)
                       (valid_pq _ _)
                       (free_tok (pointer_val_val keys_pv) _).
        forward_call (pointer_val_val ti,
                      (sizeof (Tstruct _structItem noattr) / sizeof tint)).
        1: {
          replace (sizeof tint *
                   (sizeof (Tstruct _structItem noattr) / sizeof tint)) with
              (sizeof (Tstruct _structItem noattr)) by ulia.
            
          entailer!.
        }
        thaw FR.
        forward_call (priq_ptr, hc).
        freeze FR := (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (SpaceAdjMatGraph _ _ _ _ _).
        forward_call (pointer_val_val keys_pv, heap_capacity hc).
        1: rewrite Z.mul_comm; entailer!.
        forward. thaw FR.
        Exists prev dist popped. entailer!.
        intros. destruct (H7 _ H15) as [? _]; trivial.
  Time Qed.

  (* Print Assumptions body_dijkstra. *)


End DijkstraProof.
