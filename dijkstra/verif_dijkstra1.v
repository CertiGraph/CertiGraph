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

  
  Definition dijk_setup_loop_inv g sh src dist prev v_pq keys_ptr v_temp arr addresses :=
    EX i : Z,
    EX h : heap,
    EX keys: list key_type,
    PROP (Permutation keys (nat_inc_list (Z.to_nat i)))
    LOCAL (temp _dist (pointer_val_val dist);
          temp _prev (pointer_val_val prev);
          temp _src (Vint (Int.repr src));
          temp _pq v_pq;
          temp _graph (pointer_val_val arr);
          temp _size (Vint (Int.repr size));
          temp _keys (pointer_val_val keys_ptr);
          temp _inf (Vint (Int.repr inf)))
    SEP (valid_pq v_pq h;
        data_at_ Tsh (Tstruct _structItem noattr) v_temp;
        data_at Tsh
                (tarray tint size)
                (map Vint (map Int.repr keys) ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val keys_ptr);
        free_tok (pointer_val_val keys_ptr) (heap_capacity h * sizeof tint);
        data_at Tsh
                (tarray tint size)
                ((list_repeat (Z.to_nat i)
                              (Vint (Int.repr inf)))
                   ++ (list_repeat (Z.to_nat (size-i))
                                   Vundef)) (pointer_val_val prev);
        data_at Tsh
                (tarray tint size)
                ((list_repeat (Z.to_nat i) (Vint (Int.repr inf)))
                   ++ (list_repeat (Z.to_nat (size-i))
                                   Vundef)) (pointer_val_val dist);
        @SpaceAdjMatGraph size CompSpecs sh id
                          g (pointer_val_val arr) addresses).
  
  Definition dijk_forloop_inv (g: @DijkGG size inf) sh src
             dist_ptr prev_ptr priq_ptr graph_ptr addresses :=
    EX prev : list V,
    EX priq : list Z,
    EX dist : list Z,
    EX popped : list V,
    PROP (
        (* The overall correctness condition *)
        dijkstra_correct g src popped prev dist;
      
      (* Some special facts about src *)
      Znth src dist = 0;
      Znth src prev = src;
      popped <> [] -> In src popped;
      popped = [] -> src = find priq (fold_right Z.min (hd 0 priq) priq) 0;
      
      (* A fact about the relationship b/w
         the priq and popped arrays *)
      forall v,
        vvalid g v ->
        In v popped <-> Znth v priq = Z.add inf 1;
      
      (* A fact about the relationship b/w 
         dist and priq arrays *)
      forall dst, vvalid g dst ->
                  ~ In dst popped ->
                  Znth dst priq = Znth dst dist;
      
      (* Information about the ranges of the three arrays *)
      @inrange_prev size inf prev;
      @inrange_dist inf dist;
      @inrange_priq inf priq)
         
         LOCAL (temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq (pointer_val_val priq_ptr);
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf)))
         SEP (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr priq))
                       (pointer_val_val priq_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             free_tok (pointer_val_val priq_ptr) (sizeof tint * size)).
  
  Definition dijk_forloop_break_inv (g: @DijkGG size inf) sh
                                    src dist_ptr prev_ptr priq_ptr
                                    graph_ptr addresses :=
    EX prev: list V,
    EX priq: list Z,
    EX dist: list Z,
    EX popped: list V,
    PROP (
        (* This fact comes from breaking while *)
        Forall (fun x => x >= inf) priq;
      (* And the correctness condition is established *)
      dijkstra_correct g src popped prev dist)
         LOCAL (temp _pq (pointer_val_val priq_ptr))
         SEP (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev))
                      (pointer_val_val prev_ptr);
             (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr priq))
                        (pointer_val_val priq_ptr));
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             free_tok (pointer_val_val priq_ptr) (sizeof tint * size)).
  
  Definition dijk_inner_forloop_inv (g: @DijkGG size inf) sh
             src (priq dist prev : list Z)
             dist_ptr prev_ptr priq_ptr graph_ptr addresses :=
    EX i : Z,
    EX prev' : list V,
    EX priq' : list Z,
    EX dist' : list Z,
    EX popped' : list V,
    let u :=
        find priq (fold_right Z.min (hd 0 priq) priq) 0 in
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
      popped' = [] -> src = find priq' (fold_right Z.min
                                                   (hd 0 priq') priq') 0;
      
      (* a useful fact about u *)
      In u popped';
      
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
      
      (* the lengths of the threee arrays *)
      Zlength priq' = size;
      Zlength dist' = size;
      Zlength prev' = size;
                                                           
      (* and ranges of the three arrays *)
      @inrange_prev size inf prev';
      @inrange_priq inf priq';
      @inrange_dist inf dist')
         
         LOCAL (temp _u (Vint (Int.repr u));
               temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq (pointer_val_val priq_ptr);
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf)))
         
         SEP (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev'))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr priq'))
                     (pointer_val_val priq_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist'))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id 
                               g (pointer_val_val graph_ptr) addresses;
             free_tok (pointer_val_val priq_ptr) (sizeof tint * size)).
  


  
  (* DIJKSTRA PROOF BEGINS *)

  Lemma body_dijkstra: semax_body Vprog (@Gprog size inf) f_dijkstra (@dijkstra_spec size inf).
  Proof.
    start_function.
    pose proof (size_further_restricted g).
    pose proof (inf_bounds g).
    rename H1 into Hsz.
    rename H2 into Hinf.
    assert (Int.max_signed <= Int.max_unsigned) by now compute.
    forward_call (size * sizeof(tint)).
    1: simpl; lia.
    Intro keys_pv.
    remember (pointer_val_val keys_pv) as keys.
    forward_call (size).
    1: admit. (* add to precon? *)
    Intros temp.
    destruct temp as [priq_ptr h].
    simpl fst in *; simpl snd in *.
    forward_for_simple_bound
      size
      (dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr keys_pv v_temp_item graph_ptr addresses).
    - rewrite list_repeat_0, app_nil_l, Z.sub_0_r, data_at__tarray.
      replace (size * sizeof tint / sizeof tint) with size.
      2: { rewrite Z.div_mul; trivial; simpl; lia. }
      rewrite  <- Heqkeys.
      Exists h. Exists (@nil key_type).
      entailer!.
    - forward. forward.
      forward_call (priq_ptr, h0, inf, Int.repr i).
      1: { admit. }
      Intro temp'. destruct temp' as [h' key].
      forward.
      repeat rewrite upd_Znth_list_repeat; try lia.
      simpl fst in *. simpl snd in *.
      assert (Zlength keys0 = i). {
        unfold key_type in *.
        rewrite (Permutation_Zlength _ _ H5).
        rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
      }
      rewrite upd_Znth_app2.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *.
           rewrite H8.
           rewrite Zlength_list_repeat; lia.
      }
      replace (i - Zlength (map Vint (map Int.repr keys0))) with 0.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *. lia.
      }
      replace (Z.to_nat (size - i)) with (Z.to_nat 1 + Z.to_nat (size - (i + 1)))%nat.
      2: { admit. }
      rewrite <- (list_repeat_app _ (Z.to_nat 1) (Z.to_nat (size - (i + 1)))).
      simpl list_repeat at 1.
      rewrite upd_Znth_app1.
      2: { rewrite binary_heap_Zmodel.Zlength_one. lia. }
      replace (upd_Znth 0 [Vundef] (Vint (Int.repr key))) with [(Vint (Int.repr key))].
      2: { rewrite upd_Znth0. reflexivity. }
      Exists h'.
      Exists (keys0 ++ [key]).
      rewrite H6.
      entailer!.
      +
        (* this is interesting, and it may need to come 
           from PQ?
         *)
        admit.
      + rewrite map_app, map_app, app_assoc. cancel. 
    - (* At this point we are done with the
       first for loop. The arrays are all set to inf. *)
      replace (size - size) with 0 by lia;
        rewrite list_repeat_0, <- (app_nil_end).
      Intros h' keys'.
      assert (Zlength keys' = size). {
        unfold key_type in *.
        rewrite (Permutation_Zlength _ _ H4).
        rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
      }
      forward. forward.
      do 2 rewrite <- map_list_repeat.
      forward.
      1: { entailer!.
           apply Forall_Znth with (i := src) in H3.
           2: lia.
           rewrite <- app_nil_end.
           repeat rewrite Znth_map.
           apply I.
           2: rewrite Zlength_map.
           all: unfold key_type in *; rewrite H5; auto.
      }
      rewrite <- app_nil_end.
      repeat rewrite Znth_map.
      3: rewrite Zlength_map.
      2,3: unfold key_type in *; lia.
      forward_call (priq_ptr, h', Znth src keys', Int.repr 0).
      (* Special values for src have been inserted *)
      
      (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
       *)

      (* HERE *)
      
      forward_loop
      (dijk_forloop_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr addresses)
      break: (dijk_forloop_break_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr addresses).
      + unfold dijk_forloop_inv.
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) src).
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
        Exists (@nil V).
        repeat rewrite <- upd_Znth_map; entailer!;
          clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
        assert (Zlength (list_repeat (Z.to_nat size) inf) = size). {
          rewrite Zlength_list_repeat; ulia.
        }
        split3; [| |split3; [| |split]].
        * apply (dijkstra_correct_nothing_popped g src); trivial.
        * rewrite upd_Znth_same; ulia. 
        * rewrite upd_Znth_same; ulia.
        * intros; rewrite find_src; ulia.
        * intros. split; [inversion 1 | intros; exfalso].
          destruct (Z.eq_dec src v).
          -- subst src. rewrite upd_Znth_same in H3; ulia.
          -- apply (vvalid_meaning g) in H2.
             rewrite upd_Znth_diff in H3
               by (try rewrite Zlength_list_repeat; ulia).
             rewrite Znth_list_repeat_inrange in H3; trivial.
             rewrite Z.add_1_r in H3.
             apply (Z.neq_succ_diag_l inf). ulia.
             
        * split3; red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
          
        * repeat rewrite map_list_repeat. entailer!.

      + (* Now the body of the while loop begins. *)
        unfold dijk_forloop_inv.
        Intros prev priq dist popped.
        rename H4 into H_popped_src_1.
        rename H5 into H_popped_src_2.
        rename H6 into H_popped_priq_link.
        rename H7 into H4.
        rename H8 into H5.
        rename H9 into H6.
        rename H10 into H7.
        assert_PROP (Zlength priq = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (Zlength prev = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (Zlength dist = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        
        forward_call ((pointer_val_val priq_ptr), priq).
        1: split3; [| |split3]; ulia.
        forward_if. (* checking if it's time to break *)
        * (* No, don't break. *)
          rename H11 into Htemp.
          assert (@isEmpty inf priq = Vzero). {
            destruct (@isEmptyTwoCases inf priq);
              rewrite H11 in Htemp; simpl in Htemp;
                now inversion Htemp.
          }
          clear Htemp.
          forward_call ((pointer_val_val priq_ptr), priq).
          1: split3; [| |split3; [| |split]]; ulia.
          
          Intros u.
          rename H12 into Hequ.
          (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

          (* We prove a few useful facts about u: *)
          assert (H_u_valid: vvalid g u). {
            apply (vvalid_meaning g); trivial.
            subst u.
            replace size with (Zlength priq).
            apply find_range.
            apply min_in_list. apply incl_refl.
            destruct priq.
            1: rewrite Zlength_nil in H8; ulia. 
            simpl; left; trivial.
          }
          
          assert (0 <= u < size). {
            apply (vvalid_meaning g) in H_u_valid; trivial.
          } 

          assert (~ (In u popped)). {
            intro.
            rewrite H_popped_priq_link in H13; trivial.
            rewrite <- isEmpty_in' in H11.
            destruct H11 as [? [? ?]].
            subst u.
            rewrite Znth_find in H13.
            1: pose proof (fold_min _ _ H11); lia.
            rewrite <- Znth_0_hd by ulia.
            apply min_in_list;
              [ apply incl_refl | apply Znth_In; ulia].
          }
          
          rewrite Znth_0_hd; [|ulia]. 
          do 2 rewrite upd_Znth_map.
          
          assert (Htemp: 0 <= u < Zlength dist) by lia.
          pose proof (Znth_dist_cases _ _ Htemp H6).
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
               g sh src priq dist prev
               dist_ptr prev_ptr priq_ptr graph_ptr addresses).
          -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
            (* We must prove the for loop's invariants for i = 0 *)
            Exists prev.
            Exists (upd_Znth u priq (inf+1)).
            Exists dist.
            Exists (u :: popped).
            repeat rewrite <- upd_Znth_map.
            entailer!.
            remember (find priq
                           (fold_right Z.min (hd 0 priq)
                                       priq) 0) as u.
            remember (Zlength priq) as size.
            symmetry in Heqsize.
            clear H15 H16 H17 H18 H19 H20 H21 H22
                  H23 H24 H25 H26 H27 H8.
            rename Heqsize into H8.
            
            split3; [| | split3; [| |split3; [| |split3; [| |split]]]]; trivial.
            ++ intros.
               (* if popped = [], then 
                prove inv_popped for [u].
                if popped <> [], then we're set
                *)
               destruct popped eqn:?.
               2: {
                 apply (inv_popped_add_u _ _ _ _ _ _ priq); try ulia.
                 apply H_popped_src_1; inversion 1.
               }
               replace u with src in *.
               2: apply H_popped_src_2; trivial.
               intro.
               simpl in H16; destruct H16; [|lia].
               subst dst; clear H15.
               destruct H14; [left | right].
               ** exfalso. rewrite H14 in H2. ulia.
               ** exists (src, []). split3.
                  --- split3; [| |split3]; trivial.
                      +++ split; trivial.
                      +++ rewrite path_cost.path_cost_zero; ulia.
                      +++ apply Forall_forall.
                          inversion 1.
                  --- unfold path_in_popped.
                      intros. 
                      inversion H15.
                      +++ simpl in H16. 
                          subst step. simpl; left; trivial.
                      +++ destruct H16 as [? [? _]].
                          inversion H16.
                  --- red. intros. rewrite path_cost.path_cost_zero; try ulia.
                      apply path_cost_pos; trivial.
            ++ intros.
               apply (vvalid_meaning g) in H15.
               apply inv_unpopped_weak_add_unpopped; trivial.

            ++ intros.
               apply (vvalid_meaning g) in H15.
               apply (inv_unseen_weak_add_unpopped g prev _ _ src); trivial.

            ++ intros. clear H15.
               destruct popped eqn:?.
               2: right; apply H_popped_src_1; inversion 1.
               simpl. left. symmetry.
               apply H_popped_src_2; trivial.

            ++ intros. inversion H15.
               
            ++ apply in_eq.

            ++ intros.
               assert (H16 := H15).
               rewrite (vvalid_meaning g v) in H16.
               split; intros; destruct (Z.eq_dec v u).
               ** subst v; rewrite upd_Znth_same; ulia.
               ** simpl in H17; destruct H17; [ulia|].
                  rewrite upd_Znth_diff; try ulia.
                  apply H_popped_priq_link; trivial.
               ** left; lia.
               ** right.
                  rewrite upd_Znth_diff in H17; try ulia.
                  apply <- H_popped_priq_link; trivial.
                  
            ++ intros.
               assert (dst <> u). {
                 intro. subst dst. apply H16, in_eq.
               }
               assert (0 <= dst < Zlength priq). {
                 rewrite (vvalid_meaning g) in H15; lia.
               }
               rewrite upd_Znth_diff by lia.
               apply H4; trivial.
               apply not_in_cons in H16; destruct H16 as [_ ?];
                 ulia.

            ++ rewrite upd_Znth_Zlength; ulia.

            ++ apply Forall_upd_Znth; ulia.   

          -- (* We now begin with the for loop's body *)
            rewrite <- Hequ.
            freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
            Intros.
            rename H16 into H_inv_popped.
            rename H17 into H_inv_unpopped.
            rename H18 into H_inv_unpopped_weak.
            rename H19 into H_inv_unseen.
            rename H20 into H_inv_unseen_weak.
            rename H21 into H16.
            rename H22 into H17.
            rename H23 into H18.
            rename H24 into H19.
            rename H25 into H20.
            rename H26 into H_priq_popped_link.
            rename H27 into H_priq_dist_link.
            rename H31 into H21.
            rename H32 into H22.
            rename H33 into H23.
            rename H28 into H24.
            rename H29 into H25.
            rename H30 into H26.

            forward_call (sh, g, graph_ptr, addresses, u, i).
            remember (Znth i (Znth u (@graph_to_mat size g id))) as cost.

            assert (H_i_valid: vvalid g i). {
              apply (vvalid_meaning g); trivial.
            }

            rewrite <- elabel_Znth_graph_to_mat in Heqcost; try ulia.

            forward_if.
            ++ rename H27 into Htemp.
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
                 apply (sublist.Forall_Znth _ _ _ H28) in H23.
                 assumption.
               }
               assert (0 <= Znth i dist' <= inf). {
                 assert (0 <= i < Zlength dist') by lia.
                 apply (sublist.Forall_Znth _ _ _ H29) in H23.
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

               ** rename H31 into H_improvement.
                  (* We know that we are definitely
                   going to make edits in the arrays:
                   we have found a better path to i, via u *)
                  rename H28 into Htemp.
                  assert (H28: 0 <= Znth u dist' < inf) by lia.
                  clear Htemp.

                  assert (H_i_not_popped: ~ In i (popped')). { 
                    apply (not_in_popped g src u i cost prev' dist'); trivial.
                  }
                  assert (Htemp : 0 <= i < Zlength dist') by lia.
                  pose proof (Znth_dist_cases i dist' Htemp H23).
                  clear Htemp.
                  rename H31 into icases.
                  rewrite <- H_priq_dist_link in icases; trivial.
                  
                  forward. forward. forward.
                  forward; rewrite upd_Znth_same; trivial.
                  1: entailer!.
                  1,3: repeat rewrite Zlength_map; lia.
                  forward_call ((pointer_val_val priq_ptr), i,
                                (Znth u dist' + cost), priq').

(* Now we must show that the for loop's invariant
   holds if we take another step,
   ie when i increments
                
   We will provide the arrays as they stand now:
   with the i'th cell updated in all three arrays,
   to log a new improved path via u 
 *)
                  1: split; [|red]; ulia.
                  Exists (upd_Znth i prev' u).
                  Exists (upd_Znth i priq' (Znth u dist' + cost)).
                  Exists (upd_Znth i dist' (Znth u dist' + cost)).
                  Exists popped'.
                  repeat rewrite <- upd_Znth_map.
                  entailer!.

                  clear H31 H32 H33 H34 H35 H36
                        H37 H38 H39 H40 H41 H42 H8.

                  remember (find priq (fold_right Z.min (hd 0 priq)
                                                  priq) 0) as u.
                  remember (Zlength priq) as size.
                  rename Heqsize into H8.
                  symmetry in H8.

                  remember (Znth u dist' + elabel g (u, i)) as newcost.
                  fold V in *. simpl id in *.
                  rewrite <- Heqnewcost in *.

                  assert (u <> i) by (intro; subst; lia).
                  
                  split3; [| | split3;
                               [| | split3;
                                    [| | split3;
                                         [| |split3;
                                             [| | split3]]]]]; intros.
                  (* 13 goals, where the 13th is 
                   3 range-based goals together *)
                  --- apply inv_popped_newcost; ulia.
                  --- apply inv_unpopped_newcost with (priq0 := priq'); ulia. 
                  --- now apply inv_unpopped_weak_newcost.
                  --- apply inv_unseen_newcost; ulia.
                  --- apply inv_unseen_weak_newcost; ulia. 
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- assert (H33 := H32).
                      rewrite (vvalid_meaning g) in H33.
                      split; intros; destruct (Z.eq_dec v i).
                      +++ exfalso. subst v.
                          apply H_i_not_popped; trivial.
                      +++ rewrite upd_Znth_diff; try ulia.
                          apply H_priq_popped_link; trivial.
                      +++ exfalso. subst v.
                          rewrite upd_Znth_same in H34; ulia.
                      +++ rewrite upd_Znth_diff in H34; try ulia.
                          apply <- H_priq_popped_link; trivial.
                  --- destruct (Z.eq_dec dst i).
                      1: subst dst; repeat rewrite upd_Znth_same; ulia.
                      repeat rewrite upd_Znth_diff; trivial; try lia.
                      apply H_priq_dist_link; trivial.
                      all: rewrite (vvalid_meaning g) in H32; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- split3; apply Forall_upd_Znth;  ulia.

               ** (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                 rename H31 into H_non_improvement.
                 forward. 
                 (* The old arrays are just fine. *)
                 Exists prev' priq' dist' popped'.
                 entailer!.
                 remember (find priq (fold_right Z.min
                                                 (hd 0 priq) priq) 0) as u.
                 remember (Zlength priq) as size.
                 
                 clear H31 H32 H33 H34 H35 H36
                       H37 H38 H39 H40 H41 H42 H8.
                 rename Heqsize into H8.
                 symmetry in H8.
                 
                 assert (elabel g (u, i) < inf). {
                   apply Z.le_lt_trans with (m := Int.max_signed / size);
                     trivial.
                   apply H27.
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
                     2: now apply (H_inv_unseen_weak _ H38) with (m:=m).
                     subst m.
                     rename p2m into p2u.
                     rewrite H34 in H_non_improvement.
                     assert (0 <= u < size) by lia.
                     rewrite path_cost_glue_one_step.
                     destruct H37 as [_ [_ [_ [? _]]]].
                     simpl id in *. ulia.
                 --- intros.
                     assert (i <= dst < size) by lia.
                     apply H_inv_unseen_weak; trivial.
            ++  (* i was not a neighbor of u.
                 We must prove the for loop's invariant holds *)
              forward.
              Exists prev' priq' dist' popped'.
              thaw FR.
              entailer!.
              remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
              remember (Zlength priq) as size.

              clear H28 H29 H30 H31 H32 H33
                    H34 H35 H36 H37 H38 H39 H8.
              rename Heqsize into H8.
              symmetry in H8.

              rewrite Int.signed_repr in H27.
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
                     destruct (H_inv_unpopped_weak i H31 H29 H30).
                     1: left; trivial.
                     destruct H32 as [? [[? [? [? [? [? ?]]]]]?]].
                     remember (Znth i prev') as mom.

                     assert (Znth mom dist' < inf). {
                       pose proof (edge_cost_pos g (mom, i)).
                       ulia.
                     }
                     
                     right. split3; [| |split3; [| |split3]]; trivial.
                     
                     intros.
                     destruct (@Znth_dist_cases inf mom' dist')
                       as [e | e]; trivial.
                     1: apply (vvalid_meaning g) in H41; ulia.
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
                            apply (sublist.Forall_Znth _ _ u) in H23.
                            simpl in H23. apply H23.
                            lia.
                          }
                          simpl id in *. ulia.
                     }
                     apply H39; trivial.
                 --- apply H_inv_unpopped; lia.
              ** destruct (Z.eq_dec dst i);
                   [| apply H_inv_unpopped_weak]; lia. 
              ** destruct (Z.eq_dec dst i).
                 2: apply H_inv_unseen; lia.
                 subst dst.
                 assert (i <= i < size) by lia.
                 unfold inv_unseen; intros.
                 destruct (Z.eq_dec m u).
                 2: now apply (H_inv_unseen_weak _ H29)
                   with (m:=m).
                 
                 subst m.
                 assert (0 <= Znth u dist'). {
                   apply (sublist.Forall_Znth _ _ u) in H23.
                   apply H23.
                   ulia.
                 }
                 rewrite path_cost_glue_one_step.
                 destruct H34 as [? _].
                 pose proof (path_cost_pos _ _ H34).
                 simpl id in *. ulia.
              ** apply H_inv_unseen_weak; lia.
          -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
            Intros prev' priq' dist' popped'.
            Exists prev' priq' dist' popped'.
            entailer!.
            remember (find priq (fold_right Z.min (hd 0 priq) priq) 0)
              as u.
            unfold dijkstra_correct.
            split3; [auto | apply H16 | apply H18];
              try rewrite <- (vvalid_meaning g); trivial.
            
        * (* After breaking from the while loop,
           prove break's postcondition *)
          assert (@isEmpty inf priq = Vone). {
            destruct (@isEmptyTwoCases inf priq); trivial;
              rewrite H12 in H11; simpl in H11; now inversion H11.
          }
          clear H11.
          forward. Exists prev priq dist popped.
          entailer!.
          pose proof (@isEmptyMeansInf inf priq).
          rewrite H25 in H12.
          rewrite Forall_forall in H12 |- *.
          intros. specialize (H12 _ H26). lia.
      + (* from the break's postcon, prove the overall postcon *)
        unfold dijk_forloop_break_inv.
        Intros prev priq dist popped.
        freeze FR := (data_at _ _ _ (pointer_val_val prev_ptr))
                       (data_at _ _ _ (pointer_val_val dist_ptr))
                       (SpaceAdjMatGraph _ _ _ _ _).
        forward_call (Tsh, priq_ptr, size, priq).
        entailer!.
        thaw FR.
        forward.
        Exists prev dist popped. entailer!.
        intros. destruct (H2 _ H9) as [? _]; trivial.
  Qed.

End DijkstraProof.
