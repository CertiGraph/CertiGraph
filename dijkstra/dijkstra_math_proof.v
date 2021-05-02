Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_spec_pure.

Local Open Scope Z_scope.

Ltac ulia := trivial; unfold V, DE in *; rep_lia.

(* find better home *)
Lemma Int_signed_strip:
  forall a b, Int.signed a = Int.signed b -> a = b.
Proof.
  intros.
  pose proof (Int.signed_eq a b). unfold zeq in H0.
  destruct (Z.eq_dec (Int.signed a) (Int.signed b)).
  simpl in H0. apply int_eq_e; trivial.
  exfalso. apply n. trivial.
Qed.

(* find better home *)
Lemma Int_repr_eq_small:
  forall a b,
    0 <= a < Int.modulus ->
    0 <= b < Int.modulus ->
    Int.repr a = Int.repr b ->
    a = b.
Proof.
  intros.
  apply Int_eqm_unsigned_repr',
  Int_eqm_unsigned_spec in H1.
  rewrite Int.unsigned_repr_eq in H1.
  rewrite Z.mod_small in H1; trivial.
  pose proof (Int.eqm_small_eq _ _ H1 H H0); trivial.
Qed.

Section DijkstraMathLemmas.

  Context {size : Z}.
  Context {inf : Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.

  Definition inrange_prev prev :=
    Forall (fun x => 0 <= x < size \/ x = inf) prev.

  Definition inrange_dist dist :=
    Forall (fun x => 0 <= x <= (size - 1) * (Int.max_signed / size)
                     \/ x = inf) dist.

  Definition inrange_popped popped :=
    Forall (fun x => 0 <= x < size) popped.
  
  Lemma not_in_popped_popped_short:
    forall (g: @DijkGG size inf) i popped,
      vvalid g i ->
      NoDup popped ->
      inrange_popped popped ->
      ~ In i popped ->
      Zlength popped <= size - 1.
  Proof.
    intros.
    apply (vvalid_meaning g) in H.
    apply (NoDup_all_bounded_Zlength' i); trivial.
    intros. split.
    - red in H1. rewrite Forall_forall in H1.
      apply H1; trivial.
    - intro. subst j; contradiction.
  Qed.

  Lemma Znth_dist_cases:
    forall i dist,
      0 <= i < Zlength dist ->
      inrange_dist dist ->
      Znth i dist = inf \/
      0 <= Znth i dist <= (size - 1) * (Int.max_signed / size).
  Proof.
    intros.
    apply (sublist.Forall_Znth _ _ _ H) in H0. ulia.
  Qed.

  (* Path Correct *)
  
  Lemma path_correct_path_glue_one:
    forall (g: @DijkGG size inf) src u mom p2mom prev dist,
      path_correct g prev dist src mom p2mom ->
      Znth u dist = Znth mom dist + elabel g (mom, u) ->
      Znth mom dist + elabel g (mom, u) <= (size-1) * (Int.max_signed / size) ->
      strong_evalid g (mom, u) ->
      Znth u prev = mom ->
      ~ In_path g u p2mom ->
      path_correct g prev dist src u (path_glue p2mom (mom, [(mom, u)])).
  Proof.
    intros.
    rename H4 into Hb.
    destruct H as [? [? [? [? [? Ha]]]]].
    assert (path_cost g p2mom + elabel g (mom, u) <=
            (size-1) * (Int.max_signed / size)) by ulia. 
    split3; [| | split3; [| |split]]; trivial.
    - destruct H4; apply (valid_path_app_cons g); trivial;
        try rewrite <- surjective_pairing; trivial.
    - destruct H4; apply (path_ends_app_cons g); trivial.
      split; trivial.
      rewrite <- (surjective_pairing p2mom); trivial.
    - rewrite (path_cost_glue_one_step g); ulia.
    - rewrite (path_cost_glue_one_step g).
      rewrite <- H6. ulia.
    - rewrite Forall_forall. intros.
      rewrite Forall_forall in H7.
      apply in_app_or in H9. destruct H9.
      + apply H7; trivial.
      + simpl in H9. destruct H9; [| lia].
        rewrite (surjective_pairing x) in *.
        inversion H9.
        simpl. rewrite <- H11, <- H12. ulia.
    - red in Ha |- *.
      pose proof (epath_to_vpath_path_glue_one_step
                    g src mom u p2mom H H4).
      symmetry in H9.
      apply (Permutation_NoDup H9).
      apply NoDup_cons; trivial.
      intro.
      apply in_path_eq_epath_to_vpath in H10; trivial.
      contradiction.
  Qed.

  Lemma path_correct_unique_path: forall (g : @DijkGG size inf) prev dist src m p2m p2m',
      path_correct g prev dist src m p2m ->
      path_correct g prev dist src m p2m' ->
      p2m = p2m'.
  Proof.
  intros.
  destruct p2m, p2m'. destruct H as [? [? [? [? [? ?]]]]]. destruct H0 as [? [? [? [? [? ?]]]]].
  clear H2 H7 H3 H8. destruct H1, H6. simpl in H1, H3. subst v v0. f_equal. simpl snd in *.
  revert m H H5 H4 H2 l0 H0 H10 H9 H6.
  apply (backwards_list_ind _ (fun l => forall m, 
    valid_path g (src, l) ->
    acyclic_path g (src, l) ->
    Forall (fun x : E => Znth (snd x) prev = fst x) l ->
    pfoot g (src, l) = m ->
    forall l0 : list E,
    valid_path g (src, l0) ->
    acyclic_path g (src, l0) ->
    Forall (fun x : E => Znth (snd x) prev = fst x) l0 ->
    pfoot g (src, l0) = m -> l = l0)); intros.
  simpl in H2. subst m.
  pose proof (acyclic_foot_empty g _ _ H3 H4 H6). auto.
  remember (foot l1). symmetry in Heqo. destruct o.
  2: { apply foot_none_nil in Heqo. subst l1. simpl in H7. subst m.
    symmetry in H7. eapply (acyclic_foot_empty g); eauto. }
  apply foot_explicit in Heqo. destruct Heqo as [l1' ?]. subst l1.
  assert (a = e). { destruct a, e.
  rewrite pfoot_last, (edge_dst_snd g) in H7. rewrite pfoot_last, (edge_dst_snd g) in H3.
  simpl snd in *. subst v0 v2.
  rewrite Forall_forall in H2. rewrite Forall_forall in H6.
  specialize (H2 (v,m)). specialize (H6 (v1, m)). simpl in H2, H6.
  spec H2. apply in_or_app. right. left. trivial.
  spec H6. apply in_or_app. right. left. trivial.
  rewrite H2 in H6. subst v1. trivial. } subst e. f_equal.
  rename src into src'.
  apply (H (src g a)).
  * rewrite valid_path_app in H0. tauto.
  * clear -H0 H1. red in H1 |- *.
    rewrite epath_to_vpath_eq in H1; trivial.
    rewrite valid_path_app in H0.
    rewrite epath_to_vpath_eq. 2: tauto.
    rewrite map_app in H1.
    rewrite app_comm_cons in H1.
    apply NoDup_app_l in H1.
    trivial.
  * rewrite Forall_app_iff in H2. tauto.
  * rewrite valid_path_app in H0. destruct H0.
    simpl in H8. destruct H8. apply H8.
  * rewrite valid_path_app in H4. tauto.
  * clear -H4 H5. red in H5 |- *.
    rewrite epath_to_vpath_eq in H5; trivial.
    rewrite valid_path_app in H4.
    rewrite epath_to_vpath_eq. 2: tauto.
    rewrite map_app in H5.
    rewrite app_comm_cons in H5.
    apply NoDup_app_l in H5.
    trivial.
  * rewrite Forall_app_iff in H6. tauto.
  * rewrite valid_path_app in H4. destruct H4.
    simpl in H8. destruct H8. apply H8.
  Qed.

  Lemma path_correct_upd_dist:
    forall (g: @DijkGG size inf) src i m dist prev newcost p2m,
      vvalid g i ->
      vvalid g m ->
      Zlength dist = size ->
      m <> i ->
      path_correct g prev (upd_Znth i dist newcost) src m p2m ->
      path_correct g prev dist src m p2m.
  Proof.
    intros.
    destruct H3 as [? [? [? [? ?]]]].
    split3; [| |split3]; trivial.
    apply (vvalid_meaning g) in H.
    apply (vvalid_meaning g) in H0.
    rewrite upd_Znth_diff in H6; lia.  
  Qed.

  (* Path in Popped *)
  Lemma path_in_popped_path_glue:
    forall (g: @DijkGG size inf) p1 p2 popped,
      path_in_popped g popped p1 ->
      path_in_popped g popped p2 ->
      path_in_popped g popped (path_glue p1 p2).
  Proof.
    red. intros.
    apply In_path_glue in H1. destruct H1.
    - apply H; trivial.
    - apply H0; trivial.
  Qed.

  Lemma path_in_popped_Zlengths:
    forall (g: @DijkGG size inf) links s popped,
      valid_path g (s, links) ->
      acyclic_path g (s, links) ->
      path_in_popped g popped (s, links) ->
      Zlength links <= Zlength popped - 1.
  Proof.
    intros g.
    induction links; intros; destruct popped.
    + exfalso. apply (H1 s). left; trivial.
    + rewrite Zlength_nil.
      rewrite Zlength_cons_sub_1.
      apply Zlength_nonneg.
    + exfalso. apply (H1 s). left; trivial.
    + rewrite Zlength_cons_sub_1, Zlength_cons.
      replace s with (src g a) in * by (destruct H; lia). clear s.
      assert (In (src g a) (v :: popped)). { apply H1. left. trivial. }
                                           apply In_split in H2. destruct H2 as [l1 [l2 ?]].
      specialize (IHlinks (dst g a) (l1 ++ l2)).
      spec IHlinks.
      1: apply valid_path_cons with (v0 := (src g a)); trivial.
      spec IHlinks.
      1: apply (acyclic_path_cons _ _ _ _ H); trivial.
      spec IHlinks.
      2: { assert (Zlength (v :: popped) = Zlength (l1 ++ src g a :: l2))
          by congruence.
           repeat rewrite Zlength_app in *.
           repeat rewrite Zlength_cons in *. lia.
      }
      clear IHlinks.
      red in H0. rewrite H2 in *. clear H2 popped v.
      rewrite epath_to_vpath_cons_eq in H0; trivial.
      rewrite NoDup_cons_iff in H0. destruct H0.
      do 2 intro. specialize (H1 step).
      spec H1.
      1: {
        destruct H3 as [? | [e' [? ?]]].
        - simpl in H3. right. exists a. split; auto. left. trivial.
        - right. exists e'. simpl in *; auto.
      }
      apply in_app_or in H1. apply in_or_app. destruct H1; auto.
      destruct H1; auto. exfalso.
      apply H0. subst step.
      apply in_path_eq_epath_to_vpath; auto.
      apply valid_path_tail in H. apply H.
  Qed.

  Lemma popped_noninf_has_path:
    forall (g: @DijkGG size inf) mom src popped prev (dist: list Z),
      dijkstra_correct g src popped prev dist ->
      In mom popped ->
      Znth mom dist < inf ->
      vvalid g mom ->
      exists p2mom : path,
        path_correct g prev dist src mom p2mom /\
        (forall step : Z,
            In_path g step p2mom ->
            In step popped) /\
        path_globally_optimal g src mom p2mom.
  Proof.
    intros.
    destruct (H _ H2) as [? _].
    specialize (H3 H0).
    destruct H3; [lia|].
    apply H3; trivial.
  Qed.

  Lemma path_leaving_popped:
    forall (g: @DijkGG size inf) links s u popped,
      valid_path g (s, links) ->
      path_ends g (s, links) s u ->
      In s popped ->
      ~ In u popped ->
      exists (p1 : path) (mom child : V) (p2 : path),
        path_glue p1 (path_glue (mom, [(mom, child)]) p2) = (s, links) /\
        valid_path g p1 /\
        valid_path g p2 /\
        path_ends g p1 s mom /\
        path_ends g p2 child u /\
        In mom popped /\
        ~ In child popped /\
        evalid g (mom, child) /\
        path_in_popped g popped p1.
  Proof.
    intros. 
    generalize dependent s.
    induction links.
    - intros. destruct H0. simpl in H0, H3.
      exfalso. apply H2.
      rewrite <- H3; trivial.
    - intros.
      assert (evalid g a). {
        apply (valid_path_evalid _ _ _ _ H).
        simpl; left; trivial.
      }
      assert (s = fst a). {
        simpl in H. destruct H as [? _].
        rewrite (edge_src_fst g) in H; trivial.
      }
      remember (snd a) as t. 
      assert (a = (s,t)). {
        rewrite (surjective_pairing a).
        subst; trivial.
      }
      
      destruct (in_dec (ZIndexed.eq) t popped).
      + assert (valid_path g (t, links)). {
          rewrite Heqt, <- (edge_dst_snd g); trivial.
          apply valid_path_cons with (v := s); trivial.
        }
        assert (path_ends g (t, links) t u). {
          split; trivial.
          destruct H0.
          rewrite Heqt, <- (edge_dst_snd g); trivial.
          rewrite <- H7. symmetry. apply pfoot_cons.
        }
        specialize (IHlinks _ H6 H7 i).
        destruct IHlinks as
            [p2m [m [c [p2u [? [? [? [? [? [? [? [? Ha]]]]]]]]]]]].
        exists (path_glue (s, [(s,t)]) p2m), m, c, p2u.
        assert (evalid g (s,t)). {
          rewrite H5 in H3; trivial.
        }
        assert (paths_meet g (s, [(s, t)]) p2m). {
          apply (path_ends_meet _ _ _ s t m); trivial.
          split; simpl; trivial.
          rewrite (edge_dst_snd g); trivial.
        }
        assert (fst p2u = c). {
          destruct H12.
          rewrite (surjective_pairing p2u) in H12.
          simpl in H12. lia.
        }
        assert (fst p2m = t). {
          destruct H11.
          rewrite (surjective_pairing p2m) in H11.
          simpl in H11. lia.
        } 

        split3; [| |split3; [| | split3; [| |split3]]]; trivial.
        * rewrite (path_glue_assoc g); trivial.
          -- fold E in *. rewrite H8.
             unfold path_glue; trivial.
             simpl. rewrite H5; trivial.
          -- apply (path_ends_meet _ _ _ t m u); trivial.
             split; trivial.
             unfold path_glue.
             simpl fst; simpl snd; simpl app.
             destruct H12. rewrite <- H20.
             rewrite (surjective_pairing p2u) at 2.
             assert (c = dst g (m, c)). {
               rewrite (edge_dst_snd g); trivial.
             }
             rewrite H18. rewrite H21 at 2.
             apply pfoot_cons.
        * apply valid_path_merge; trivial.
          simpl; unfold strong_evalid.
          rewrite (edge_dst_snd g), (edge_src_fst g); trivial;
            simpl; split3; trivial.
          split.
          -- apply (valid_path_valid _ _ _ H).
             rewrite in_path_or_cons; trivial.
             left; trivial.
             rewrite (edge_src_fst g); trivial.
          -- apply (valid_path_valid _ _ _ H6).
             unfold In_path. left; trivial.
        * split; trivial.
          unfold path_glue.
          simpl fst; simpl snd; simpl app.
          destruct H11. rewrite <- H20.
          rewrite (surjective_pairing p2m) at 2.
          rewrite H19.
          assert (t = dst g (s, t)). {
            rewrite (edge_dst_snd g); trivial.
          }
          rewrite H21 at 2.
          apply pfoot_cons.
        * red. intros.
          unfold path_glue in H20. simpl in H20.
          rewrite in_path_or_cons in H20.
          2: rewrite (edge_src_fst g); trivial.
          red in Ha.
          destruct H20.
          1: subst step; trivial.
          apply Ha.
          rewrite (edge_dst_snd g) in H20.
          simpl in H20. rewrite <- H19,
                        <- surjective_pairing in H20. trivial.
      + clear IHlinks. 
        exists (s, []), s, t, (t, links).
        assert (evalid g (s,t)). {
          rewrite H5 in H3; trivial.
        }

        split3; [| |split3; [| | split3; [| |split3]]]; trivial.
        * rewrite path_glue_nil_l. simpl.
          rewrite H5; trivial.
        * simpl. apply (valid_path_valid _ _ _ H).
          unfold In_path. left; trivial.
        * rewrite Heqt.
          rewrite <- (edge_dst_snd g); trivial.
          apply valid_path_cons with (v := s); trivial.
        * split; trivial.
        * destruct H0. split; trivial.
          rewrite <- H7. symmetry.
          rewrite Heqt, <- (edge_dst_snd g); trivial.
          apply pfoot_cons.
        * red. intros. red in H7.
          destruct H7.
          1: simpl in H7; subst step; trivial.
          destruct H7 as [? [? ?]]. inversion H7.
  Qed.

  Lemma path_leaving_popped_stronger:
    forall (g: @DijkGG size inf) links s u popped,
      valid_path g (s, links) ->
      path_ends g (s, links) s u ->
      In s popped ->
      ~ In u popped ->
      path_cost g (s, links) < inf ->
      exists (p1 : path) (mom child : V) (p2 : path),
        path_glue p1 (path_glue (mom, [(mom, child)]) p2) = (s, links) /\
        valid_path g p1 /\
        valid_path g p2 /\
        path_ends g p1 s mom /\
        path_ends g p2 child u /\
        In mom popped /\
        ~ In child popped /\
        strong_evalid g (mom, child) /\
        path_cost g p1 < inf /\
        0 <= elabel g (mom, child) < inf /\
        path_cost g p2 + elabel g (mom, child) < inf /\
        path_in_popped g popped p1.
  Proof.
    intros.
    destruct (path_leaving_popped g links s u popped H H0 H1 H2)
      as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? [? Ha]]]]]]]]]]]].
    exists p1, mom', child', p2.
    assert (valid_path g (path_glue (mom', [(mom', child')]) p2)). {
      apply valid_path_merge; trivial.
      apply (path_ends_meet _ _ _ mom' child' u); trivial.
      apply (path_ends_one_step g).
      simpl. rewrite (edge_src_fst g); split; trivial.
      split3; trivial.
      rewrite (edge_src_fst g); simpl; trivial.
      apply (path_ends_valid_dst _ s _ p1); trivial.
      rewrite (edge_dst_snd g); simpl; trivial.
      apply (path_ends_valid_src _ _ u p2); trivial.
    }

    assert (elabel g (mom', child') < inf). {
      apply (inf_gt_largest_edge g). trivial. }

    split3; [| |split3; [| |split3;
                            [| |split3;
                                [| |split3;
                                    [| |split]]]]]; trivial.
    - apply strong_evalid_dijk; trivial.
      + apply (path_ends_valid_dst _ s _ p1); trivial.
      + apply (path_ends_valid_src _ _ u p2); trivial.
      + intro. rewrite H14 in H13.
        apply Zlt_not_le in H13. apply H13; reflexivity.
    - rewrite <- H4 in H3.
      apply path_cost_path_glue_lt in H3; trivial.
      destruct H3; trivial.
    - split; trivial. apply edge_cost_pos.
    - rewrite <- H4 in H3.
      apply path_cost_path_glue_lt in H3; trivial.
      destruct H3 as [_ ?].
      rewrite (path_cost_path_glue g) in H3; trivial.
      rewrite (one_step_path_Znth g) in H3. rewrite Z.add_comm. ulia.
  Qed.

  Lemma inv_popped_add_src:
    forall (g: @DijkGG size inf) src popped prev dist,
      dijkstra_correct g src popped prev dist ->
      vvalid g src ->
      Znth src dist = 0 ->
      inv_popped g src (src :: popped) prev dist src.
  Proof.
    intros. right.
    exists (src, []); split3; trivial.
    - split3; [| | split3; [| |split]]; trivial.
      + split; trivial.
      + unfold path_cost. simpl.
        pose proof (size_representable g).
        apply Z.mul_nonneg_nonneg; [|apply Z.div_pos]; try ulia.
      + rewrite Forall_forall; intros; simpl in H3; lia.
      + apply acyclic_nil_path.
    - unfold path_in_popped. intros. destruct H3 as [? | [? [? _]]].
      + simpl in H3.
        simpl. left; lia.
      + simpl in H3; lia.
    - unfold path_globally_optimal; intros.
      unfold path_cost at 1; simpl.
      apply path_cost_pos; trivial.
  Qed.

  Lemma inv_unpopped_weak_add_unpopped:
    forall (g: @DijkGG size inf) prev dist popped src u dst,
      dijkstra_correct g src popped prev dist ->
      ~ In u popped ->
      vvalid g dst ->
      inv_unpopped_weak g src (u :: popped) prev dist dst u.
  Proof.
    (* Any vertex that is
       "seen but not popped"
       is that way without the benefit of unpopped vertices.
       We will be asked to provide a locally optimal   
       path to such a dst, and we will simply provide the 
       old one best-known path
     *)
    intros.
    unfold inv_unpopped_weak. intros.
    apply not_in_cons in H2; destruct H2 as [_ ?].
    destruct (H dst H1) as [_ [? _]].
    specialize (H4 H2 H3) as
        [? | [? [? [? [? [? [? ?]]]]]]]; [left | right]; trivial.
    remember (Znth dst prev) as mom.
    
    assert (evalid g (mom, dst)). {
      rewrite (evalid_meaning g). split.
      apply (edge_representable).
      intro.
      replace (elabel g (mom, dst)) with inf in H7.
      apply Zlt_not_le in H7; apply H7; reflexivity.
    }
    
    assert (Znth mom dist < inf) by
        (pose proof (valid_edge_bounds g _ H11); ulia).
    
    destruct (popped_noninf_has_path _ _ _ _ _ _ H H6 H12) as
        [p2mom [? [? ?]]]; trivial.
    
    (* Several of the proof obligations
       fall away easily, and those that remain
       boil down to showing that
       u was not involved in this
       locally optimal path.
     *)
    assert (mom <> u). {
      intro contra. rewrite contra in *. apply H0; trivial. 
    }
    
    split3; [|split3; [| |split3; [| |split]]|]; trivial.
    1: simpl; right; trivial.
    intros.
    apply H10; trivial.
    simpl in H19; destruct H19; ulia.
  Qed.

  Lemma inv_unseen_weak_add_unpopped:
    forall (g : @DijkGG size inf) prev dist popped src u dst,
      dijkstra_correct g src popped prev dist ->
      ~ In u popped ->
      vvalid g dst ->
      inv_unseen_weak g src (u :: popped) prev dist dst u.
  Proof.
    repeat intro.
    apply not_in_cons in H2; destruct H2.
    destruct (H dst H1) as [_ [_ ?]].
    destruct H5; [ulia|].
    apply (H11 H10 H3 m p2m); trivial.
    red in H8 |- *. intros.
    specialize (H8 _ H12). destruct H8; auto. subst step.
    exfalso.
    pose proof (in_path_split g p2m u H12).
    apply valid_path_split in H9.
    2: { exists m. destruct H7 as [_ [[? ?] _]]. split; auto. }
    destruct H9. destruct H13 as [_ ?]. simpl in H13.
    specialize (H8 H9). destruct H8 as [p1 [p2 [? ?]]].
    destruct (H _ H4) as [? _]. destruct (H15 H5).
    * destruct H16. specialize (H17 p2m). destruct H7 as [? ?]. tauto.
    * destruct H16 as [p2u' [? ?]].
      (* Well, darn.  If we'd had this lemma before, Anshuman could have saved himself a lot
         of plumbing work... *)
      pose proof (path_correct_unique_path _ _ _ _ _ _ _ H7 H16). subst p2u'.
      destruct H17. clear -H17 H12 H0.
      specialize (H17 _ H12). contradiction.
  Qed.

  Lemma dijkstra_correct_nothing_popped:
    forall (g: @DijkGG size inf) src,
      0 <= src < size ->
      dijkstra_correct
        g src []
        (upd_Znth src
                  (repeat inf (Z.to_nat size)) src)
        (upd_Znth src (repeat inf (Z.to_nat size)) 0).
  Proof.
    intros.
    unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen;
      split3; intros; [inversion H1 | left | inversion H4].
    destruct (Z.eq_dec dst src); [trivial | exfalso].
    apply (vvalid_meaning g) in H0. 
    rewrite upd_Znth_diff in H2; trivial.
    rewrite Znth_repeat_inrange in H2; ulia.
    all: rewrite Zlength_repeat; lia.
  Qed.

  Lemma inv_popped_newcost:
    forall (g: @DijkGG size inf) src dst u i newcost popped prev dist,
      vvalid g i ->
      vvalid g dst ->
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      Zlength prev = size ->
      Zlength dist = size ->
      ~ In i popped ->
      inv_popped g src popped
                 (upd_Znth i prev u)
                 (upd_Znth i dist newcost) dst.
  Proof.
    intros. unfold inv_popped; intros.
    assert (n: dst <> i). {
      intro. subst dst. apply H4; trivial.
    }
    assert (0 <= dst < size). {
      apply (vvalid_meaning g) in H0; ulia.
    }
    assert (0 <= i < size). {
      apply (vvalid_meaning g) in H; ulia.
    }
    repeat rewrite upd_Znth_diff; try ulia.
    destruct (H1 dst H0 H5)
      as [? | [p2dst [? [? ?]]]]; [left | right]; trivial.
    exists p2dst. split3; trivial.
    - destruct H8 as [? [? [? [? [? Ha]]]]].
      split3; [| | split3; [| |split]]; trivial.
      1: rewrite upd_Znth_diff; ulia.
      rewrite Forall_forall; intros.
      pose proof (In_links_snd_In_path g _ _ H15).
      specialize (H9 _ H16). 
      rewrite Forall_forall in H14. specialize (H14 _ H15).
      assert (snd x <> i). {
        intro contra.
        rewrite contra in *. apply H4; ulia.
      }
      rewrite upd_Znth_diff; try lia.
      rewrite H2, <- (vvalid_meaning g); trivial.
      apply (valid_path_valid _ p2dst); trivial.
  Qed.

  Lemma inv_unpopped_newcost_dst_neq_i:
    forall (g: @DijkGG size inf) src (dst u i: V) newcost prev dist popped,
      (forall dst : Z,
          0 <= dst < i ->
          inv_unpopped g src popped prev dist dst) ->
      vvalid g i ->
      Zlength prev = size ->
      Zlength dist = size ->
      ~ In i popped ->
      0 <= dst < i + 1 ->
      dst <> i ->
      inv_unpopped g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
  Proof.
    intros. 
    assert (0 <= dst < i) by lia.
    (* We will proceed using the old best-known path for dst *)
    assert (0 <= i < size) by now apply (vvalid_meaning g).
    unfold inv_unpopped. intros.
    rewrite upd_Znth_diff in H9 by ulia.
    rewrite upd_Znth_diff by ulia.
    destruct (H _ H6 H8) as
        [? | [? [? [? [? [? [? ?]]]]]]]; trivial;
      [left | right]; trivial.
    remember (Znth dst prev) as mom. 
    split; trivial.
    assert (Znth mom dist < inf). {
      pose proof (edge_cost_pos g (mom, dst)). ulia.
    }
    assert (vvalid g dst). {
      apply (vvalid_meaning g); ulia.
    }
    assert (mom <> i). {
      intro. subst i. apply H3; trivial.
    }
    assert (0 <= mom < Zlength dist). {
      apply (vvalid_meaning g) in H11; ulia.
    }
    split3; [| |split3; [| |split]]; trivial.
    - rewrite upd_Znth_diff; lia.
    - repeat rewrite upd_Znth_diff; trivial; ulia.
    - intros.
      assert (mom' <> i). {
        intro contra. subst mom'. apply H3; trivial.
      }
      repeat rewrite upd_Znth_diff; trivial.
      apply H16; trivial.
      1: apply (vvalid_meaning g) in H21; ulia.
      all: lia.
  Qed. 

  Lemma inv_unpopped_weak_newcost:
    forall (g: @DijkGG size inf) src dst u i prev dist popped newcost,
      (forall dst : Z,
          i <= dst < size ->
          inv_unpopped_weak g src popped prev dist dst u) ->
      vvalid g i ->
      Zlength prev = size ->
      Zlength dist = size ->
      ~ In i popped ->
      i + 1 <= dst < size ->
      inv_unpopped_weak g src popped
                        (upd_Znth i prev u)
                        (upd_Znth i dist newcost)
                        dst u.
  Proof.
    intros ? ? ? ? ? ? ? ? ? H_inv_unpopped_weak. intros.
    assert (0 <= i < size) by now apply (vvalid_meaning g).
    unfold inv_unpopped_weak. intros.
    assert (i <= dst < size) by lia.
    destruct (Z.eq_dec dst i).
    1: subst dst; lia.
    rewrite upd_Znth_diff in H6 by lia.
    destruct (H_inv_unpopped_weak _ H7 H5 H6)
      as [? | [? [[? [? [? [? [? ?]]]]] ?]]];
      [left | right]; trivial.
    rewrite upd_Znth_diff by ulia.
    remember (Znth dst prev) as mom. 
    assert (mom <> i). {
      intro. subst i. apply H2; trivial.
    }
    assert (0 <= mom < size) by now apply (vvalid_meaning g).
    split3; [| split3; [| | split3; [| |split]]|]; trivial.
    1,2: repeat rewrite upd_Znth_diff; ulia.
    intros.
    assert (mom' <> i). {
      intro contra. subst mom'. apply H2; trivial.
    }
    repeat rewrite upd_Znth_diff; trivial.
    apply H15; ulia. 
    apply (vvalid_meaning g) in H19; ulia.
    all: ulia.
  Qed.

  Lemma inv_unseen_newcost:
    forall (g: @DijkGG size inf) (dst src i u: V) dist prev popped newcost,
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      (forall dst : Z,
          0 <= dst < i ->
          inv_unseen g src popped prev dist dst) ->
      vvalid g i ->
      Zlength dist = size ->
      0 <= dst < i + 1->
      newcost < inf ->
      inv_unseen g src popped (upd_Znth i prev u)
                 (upd_Znth i dist newcost) dst.
  Proof.
    intros ? ? ? ? ? ? ? ? ?
           H_inv_popped H_inv_unseen H_i_valid.
    intros. unfold inv_unseen; intros.
    (* m is popped but we know nothing more about it. 
       We take cases to find out more:
     *)
    destruct (H_inv_popped _ H4 H5) as [[? ?] | [optp2m [? [? ?]]]].
    - (* m was popped @ inf *)
      destruct H6 as [? [? _]].
      specialize (H9 p2m H10). contradiction.
    - (* m was popped @ < inf *)
      (* Since optp2m is optimal, it cannot be worse than p2m.
         We will strengthen the goal and then prove it. *)
      destruct H6 as [? [? _]].
      specialize (H10 p2m H6 H11).
      assert (0 <= dst < i). {
        assert (dst <> i). {
          intro. subst dst.
          rewrite (vvalid_meaning g i) in H_i_valid.
          rewrite upd_Znth_same in H3; ulia.
        }
        lia.
      }
      apply (vvalid_meaning g) in H_i_valid.
      rewrite upd_Znth_diff in H3; try ulia.
      red in H_inv_unseen.
      intro.
      apply (H_inv_unseen _ H12 H2 H3 m optp2m); trivial.
      destruct H8 as [? [? _]].
      apply valid_path_split in H13.
      2: { apply (path_ends_meet _ _ _ src m dst); trivial.
           red. simpl. rewrite (edge_dst_snd g); simpl; split; trivial. }
      destruct H13.
      apply valid_path_merge; trivial.
      apply (path_ends_meet _ _ _ src m dst); trivial.
      red. simpl. rewrite (edge_dst_snd g); simpl; split; trivial. 
  Qed.

  Lemma inv_unseen_weak_newcost:
    forall (g: @DijkGG size inf) (dst src u i: V) dist prev popped newcost,
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      (forall dst : Z,
          i <= dst < size ->
          inv_unseen_weak g src popped prev dist dst u) ->
      vvalid g i ->
      Zlength dist = size ->
      i + 1 <= dst < size ->
      newcost < inf ->
      inv_unseen_weak g src popped
                      (upd_Znth i prev u)
                      (upd_Znth i dist newcost) dst u.
  Proof.
    intros ? ? ? ? ? ? ? ? ?
           H_inv_popped H_inv_unseen_weak H_i_valid.
    intros. unfold inv_unseen_weak; intros.
    (* m is popped but we know nothing more about it. 
       We take cases to find out more:
     *)
    destruct (H_inv_popped _ H4 H5) as [[? ?] | [optp2m [? [? ?]]]].
    - (* m was popped @ inf *)
      destruct H7 as [? [? _]].
      specialize (H10 p2m H11). contradiction.
    - (* m was popped @ < inf *)
      (* Since optp2m is optimal, it cannot be worse than p2m.
         We will strengthen the goal and then prove it. *)
      destruct H7 as [? [? _]].
      specialize (H11 p2m H7 H12).

      assert (dst <> i). {
        intro. subst dst.
        rewrite (vvalid_meaning g i) in H_i_valid.
        rewrite upd_Znth_same in H3; ulia.
      }
      rewrite (vvalid_meaning g i) in H_i_valid.
      rewrite upd_Znth_diff in H3; try ulia.
      assert (i <= dst < size) by lia.
      red in H_inv_unseen_weak.
      intro.
      apply (H_inv_unseen_weak _ H14 H2 H3 m optp2m); trivial.
      destruct H9 as [? [? _]].
      apply valid_path_split in H15.
      2: { apply (path_ends_meet _ _ _ src m dst); trivial.
           red. simpl. rewrite (edge_dst_snd g); simpl; split; trivial.
      }
      destruct H15.
      apply valid_path_merge; trivial.
      apply (path_ends_meet _ _ _ src m dst); trivial.
      red. simpl. rewrite (edge_dst_snd g); simpl; split; trivial. 
  Qed.           

  Lemma inv_unpopped_new_dst:
    forall (g: @DijkGG size inf) (src dst u i: V) dist prev popped,
      vvalid g i ->
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      (forall dst : Z,
          0 <= dst < i ->
          inv_unpopped g src popped prev dist dst) ->
      (forall dst : Z,
          i <= dst < size ->
          inv_unpopped_weak g src popped prev dist dst u) ->
      inrange_dist dist ->
      Zlength dist = size ->
      Znth u dist + elabel g (u, i) >= Znth i dist ->
      0 <= dst < i + 1 ->
      inv_unpopped g src popped prev dist dst.
  Proof.
    intros ? ? ? ? ? ? ? ? ?
           H_inv_popped H_inv_unpopped H_inv_unpopped_weak.
    intros.
    (* Show that moving one more step
     still preserves the for loop invariant *)
    destruct (Z.eq_dec dst i).
    (* when dst <> i, all is well *)
    2: apply H_inv_unpopped; lia.

    (* things get interesting when dst = i
     We must show that i is better off
     NOT going via u *)
    subst dst.
    (* i already obeys the weaker inv_unpopped,
       ie inv_unpopped without going via u.
       Now I must show that it actually satisfies
       inv_unpopped proper
     *)
    unfold inv_unpopped; intros.
    apply (vvalid_meaning g) in H.
    assert (i <= i < size) by lia.
    destruct (H_inv_unpopped_weak i H6 H4 H5) as
        [? | [? [[? [? [? [? [? ?]]]]] ?]]]; [left | right]; trivial.
    remember (Znth i prev) as mom.
    split3; [| |split3; [| |split3]]; trivial.
    intros.
    pose proof (Znth_dist_cases mom' dist).
    rename H17 into e.
    destruct e as [e | e]; trivial.
    1: apply (vvalid_meaning g) in H15; ulia.
    1: {
      rewrite e.
      pose proof (edge_cost_pos g (mom', i)).
      ulia.
    }
    destruct (H_inv_popped _ H15 H16) as [[? ?] | ?].
    1: pose proof (edge_cost_pos g (mom', i)); ulia.

    destruct H17 as [p2mom' [? [? ?]]].
    assert (Hrem := H17).
    
    (*
  This time, we need to prove that since dist[u] +
  graph[u][i] > dist[i], the original path from s to i
  composed by popped vertices (excluding u) is still
  shortest in all paths from s to i composed by popped
  vertices (including u).

  In other words, it is to prove that for any path p' from
  s to i and composed by popped vertices (including u),
  dist[i] < path_cost p'.
     *)

    (* We check if u is in the path p' *)
    destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).
    
    - destruct H17 as [? [? [? [? ?]]]].
      apply in_path_eq_epath_to_vpath in i0; trivial.
      (*
      1. In u p': p' is from s to i, consider the
      vertex mom' which is just before i.
       *)
      destruct (Z.eq_dec mom' u).
      +
        (*
        1.1 mom' = u: dist[u] is global optimal. We have
        dist[i] < dist[u] + graph[u][i]
                <= path_cost [s to u of p'] + graph[u][i]
                = path_cost p'
         *)
        subst mom'.
        specialize (H18 _ i0).
        rename p2mom' into p2u.
        unfold path_globally_optimal in H19.
        apply Z.ge_le in H2.
        destruct (zlt (Znth u dist + elabel g (u, i)) inf); ulia.
      + destruct Hrem as [? [? [? [? ?]]]].
        assert (In_path g mom' p2mom'). {
          destruct H25. apply pfoot_in in H29. trivial.
        }
        destruct (zlt (Znth mom' dist + elabel g (mom', i)) inf).
        2: {
          destruct (zlt (elabel g (mom', i)) inf); lia.
        }
        
        (*
        1.2 ~ mom' = u: 
        Since p2mom' is composed by popped vertex (including u) only,
        mom' must be a popped vertex.
        Then it satisfies inv_popped, which means
        dist[mom'] <= path_cost [s to u] + path_cost [u to mom']
        and the global optimal path from s to mom' is composed by
        popped vertices only.
        Thus dist[mom'] + (mom',i) <= path_cost p'.
         *)
        
        (* 
         Since i has been "seen", 
         we have dist[i] <= dist[mom'] + (mom', i)
         because of inv_unpopped_weak 
         *)
        assert (0 <= mom' < size). {
          apply (vvalid_meaning g) in H15; ulia.
        }
        destruct (H_inv_unpopped_weak _ H6 H4 H5) as
            [? | [? [[? [? [? [? [? ?]]]]]]]].
        1: lia.
        apply H38; trivial.
    - 
      (* 2. ~ In u p': This is an easy case.
   dist[i] < path_cost p' because of Inv2.
       *)
      apply H14; trivial.
      intro. apply n.
      destruct H17 as [? [? [? [? ?]]]].
      rewrite in_path_eq_epath_to_vpath; trivial.
      destruct H21.
      apply pfoot_in in H25. rewrite H20 in *. trivial.
  Qed.

  Lemma not_in_popped:
    forall (g: @DijkGG size inf) src u i cost prev dist popped,
      vvalid g u ->
      vvalid g i ->
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      In u popped ->
      cost = elabel g (u, i) ->
      0 <= Znth i dist <= inf ->
      0 <= Znth u dist + cost <= Int.max_signed ->
      Znth u dist + cost < Znth i dist ->
      0 <= Znth u dist < inf ->
      ~ In i popped.
  Proof.
    intros ? ? ? ? ? ? ? ? H_u_valid H_i_valid
           H_inv_popped ? ? ? ? H_improvement ?.
    (* This useful fact is true because
     the cost to i was just improved.
     This is impossible for popped items.
     *)
    intro.                  
    destruct (H_inv_popped _ H_i_valid H4) as [[? ?]|?].
    1: {
      destruct (H_inv_popped _ H_u_valid H) as [[? _] | [p2u [? [? ?]]]].
      1: lia.
      assert (path_ends g (path_glue p2u (u, [(u,i)])) src i). {
        destruct H7 as [_ [? _]].
        apply (path_ends_app_cons g _ _ _ src); trivial.
        2: rewrite <- surjective_pairing; split.
        all: destruct H7; trivial.
      }
      assert (valid_path g (path_glue p2u (u, [(u,i)]))). {
        destruct H7 as [? [? _]].
        apply valid_path_merge; trivial.
        - apply (path_ends_meet _ _ _ src u i); trivial.
          split; trivial. simpl.
          rewrite (edge_dst_snd g). trivial.
        - simpl. split.
          + rewrite (edge_src_fst g); trivial.
          + apply strong_evalid_dijk; ulia.
      }
      specialize (H6 _ H10). contradiction.
    }

    apply Zlt_not_le in H_improvement; apply H_improvement.
    destruct (H_inv_popped _ H_u_valid H) as [? | [p2u [? _]]].
    1: ulia.
    destruct H5 as [p2i [[_ [_ [_ [? _]]]] [_ ?]]].
    destruct H6 as [? [? [_ [? _]]]].
    rewrite H9, H5.
    specialize (H7 (fst p2u, snd p2u +:: (u,i))).  
    rewrite (path_cost_app_cons g) in H7; trivial.
    rewrite H0. apply H7.
    - apply (valid_path_app_cons g).
      + rewrite <- surjective_pairing; trivial.
      + rewrite (surjective_pairing p2u) in H8.
        destruct H8; simpl in H8; ulia.
      + apply strong_evalid_dijk; ulia.
    - apply (path_ends_app_cons g) with (a' := src); trivial.
      2: rewrite <- surjective_pairing; split.
      all: rewrite (surjective_pairing p2u) in *;
        destruct H8; simpl in H8; trivial.
  Qed.

  Lemma inv_unpopped_newcost:
    forall (g: @DijkGG size inf) src dst (u i: V)
           dist prev popped newcost,
      (forall dst : Z,
          vvalid g dst ->
          inv_popped g src popped prev dist dst) ->
      (forall dst : Z,
          0 <= dst < i ->
          inv_unpopped g src popped prev dist dst) ->
      (forall dst : Z,
          i <= dst < size ->
          inv_unpopped_weak g src popped prev dist dst u) ->
      (forall dst : Z,
          i <= dst < size ->
          inv_unseen_weak g src popped prev dist dst u) ->
      newcost = Znth u dist + elabel g (u, i) ->
      vvalid g u ->
      vvalid g i ->
      u <> i ->
      In u popped ->
      inrange_dist dist ->
      Zlength prev = size ->
      Zlength dist = size ->
      0 <= Znth u dist <= inf ->
      0 <= elabel g (u, i) <= Int.max_signed / size ->
      0 <= Znth i dist <= inf ->
      newcost < Znth i dist ->
      ~ In i popped ->
      Znth i dist = inf \/ Znth i dist < inf ->
      0 <= dst < i + 1 ->
      inv_unpopped g src popped (upd_Znth i prev u)
                   (upd_Znth i dist newcost) dst.
  Proof.
    intros ? ? ? ? ? ? ? ? ?
           H_inv_popped H_inv_unpopped H_inv_unpopped_weak
           H_inv_unseen_weak Heqnewcost.
    intros. destruct (Z.eq_dec dst i).
    2: apply inv_unpopped_newcost_dst_neq_i; trivial.
    
    subst dst; clear H12.
    (* This is a key change --
       i will now be locally optimal,
       _thanks to the new path via u_.
       In other words, it is moving from
       the weaker inv_unpopped clause
       to the stronger
     *)
    unfold inv_unpopped; intros.
    destruct (Z.eq_dec i src); [left | right; split]; trivial.
    destruct (H_inv_popped _ H H2).
    1: ulia.
    assert (0 <= i < size) by now apply (vvalid_meaning g).
    assert (0 <= u < size) by now apply (vvalid_meaning g).
    rewrite upd_Znth_same by lia.
    
    split3; [| |split3; [| |split]]; trivial.
    1: ulia.
    1: rewrite upd_Znth_diff; ulia.
    1: rewrite upd_Znth_same; [rewrite upd_Znth_diff|]; ulia.
    intros. rewrite upd_Znth_same; [|ulia].
    
    (* This is another key point in the proof:
       we must show that the path via u is
       better than all other paths via
       other popped verices 
     *)
    assert (mom' <> i). {
      intro. subst mom'.
      apply H10; trivial.
    }
    rewrite upd_Znth_diff; trivial.
    2: apply (vvalid_meaning g) in H17; ulia.
    2: lia. 
    destruct (Znth_dist_cases mom' dist); trivial.
    1: apply (vvalid_meaning g) in H17; ulia. 
    1: { rewrite H20. pose proof (edge_cost_pos g (mom', i)). ulia.
    }

    destruct (H_inv_popped _ H17 H18) as
        [[? ?] | [p2mom' [? [? ?]]]].
    1: pose proof (edge_cost_pos g (mom', i)); ulia.

    assert (Hrem:= H21).
    destruct H21 as [? [? [? ?]]].
    pose proof (path_ends_In_path_dst _ _ _ _ H24).
    destruct (zlt ((Znth mom' dist) + elabel g (mom', i)) inf).
    2: {
      destruct (zlt (elabel g (mom', i)) inf); lia.
    }
    
    (* 
     The known conditions are:
     - dist[u] + graph[u][i] < dist[i]
     - i is an unpopped vertex.
     
     Now we prove for any other path p' which is from s to i
     and composed by popped vertices (INCLUDING u),
     dist[u] + graph[u][i] <= path_cost p'.
 
     There are two cases about p': In u p' \/ ~ In u p'
     *)

    destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).
    - (* Yes, the path p2mom' goes via u *) 
      (*
        1. In u p': p' is the path from s to i.
        Consider the vertex mom' which is
        just before i. Again, there are two cases:
        mom' = u \/ ~ mom' = u.
       *)

      apply in_path_eq_epath_to_vpath in i0.
      2: trivial.
      
      destruct (Z.eq_dec mom' u).
      1: {
        (*
          1.1 mom' = u: path_cost p' = path_cost [s to u] + graph[u][i].
          As we know, u is just popped, dist[u] is the
          global optimal, so dist[u] <= path_cost [s to u],
          so dist[u] + graph[u][i] <= path_cost p'.
         *)
        subst mom'.
        unfold path_globally_optimal in H13. ulia.
      }
      

      (*
      1.2 ~ mom' = u: 
      p' can conceptually be split up as:
      path s to u ++ path u to mom' + edge (mom', i).
       *)
      (*
      Since p' is composed by popped vertex
      (including u) only, mom' must be a popped
      vertex. Then it satisfies inv_popped, which means
      dist[mom'] <= path_cost [s to u] + path_cost [u to mom']
      and the global optimal path from s to mom' is
      composed by popped vertices only. 
       *)
      
      (* Digression: a brief check to see if i was popped, 
         unseen, or just unpopped. 
       *)
      destruct H11.
      1: {
        (* i was unseen *)
        assert (i <= i < size) by lia.
        exfalso.
        
        apply (H_inv_unseen_weak
                 _ H28 H10 H11 mom'
                 p2mom' H17 H18 n0 Hrem H22).
        apply valid_path_merge; trivial.
          2: { simpl.
               rewrite (edge_src_fst g); split; trivial.
               apply strong_evalid_dijk; ulia.
          }
          apply (path_ends_meet _ _ _ src mom' i); trivial.
          red. simpl. rewrite (edge_dst_snd g). simpl. split; trivial.
      }
      
      (* Now we know that i was seen but unpopped. 
       Great, now we can employ inv_unpopped_weak. *)
      (* Because i is "seen", we know that 
         The best-known path to i via popped vertices is 
         already logged in dist[i]. 
         So dist[i] <= dist[mom'] + (mom', i).
       *)
      assert (Znth i dist <= Znth mom' dist + elabel g (mom', i)). {
        assert (i <= i < size) by lia.
        assert (0 <= mom' < size). {
          apply (vvalid_meaning g); ulia.
        }
        destruct (H_inv_unpopped_weak _ H28 H10 H11).
        1: lia.
        destruct H30 as [_ [_ ?]]. apply H30; trivial.
      }
      
      (*
      So we have 
      dist[u] + graph[u][i] <= dist[i]
                            <= dist[mom'] + (mom', i) 
                            <= path_cost p'.
       *)
      ulia.
    -
      (* Since u is not in the path, 
         we can just tango with
         the step <> u condition from 
         inv_unpopped_weak. 
         This case is okay.
       *)
      assert (mom' <> u). {
        intro. subst mom'. apply n0.
        apply in_path_eq_epath_to_vpath; trivial.
      }
      destruct H11.
      1: {
        (* i was unseen *)
        assert (i <= i < size) by lia.
        pose proof (H_inv_unseen_weak
                      _ H29 H10 H11 mom' p2mom'
                      H17 H18 H28 Hrem H22).
        exfalso. apply H30.
        apply valid_path_merge; trivial.
        2: {
          simpl.
          rewrite (edge_src_fst g); split; trivial.
          apply strong_evalid_dijk; ulia.
        }
        apply (path_ends_meet _ _ _ src mom' i); trivial.
        red. simpl. rewrite (edge_dst_snd g). simpl. split; trivial.
      }
      assert (i <= i < size) by lia.
      destruct (H_inv_unpopped_weak i H29 H10 H11).
      1: subst i; exfalso; lia.
      apply Z.lt_le_incl.
      apply Z.lt_le_trans with (m:=Znth i dist).
      1: lia.
      destruct H30 as [_ [_ ?]]. apply H30; trivial.
  Qed.

  Lemma inv_popped_add_u:
    forall (g: @DijkGG size inf) src dst u popped prev (dist: list Z),
      dijkstra_correct g src popped prev dist ->
      Znth src dist = 0 ->
      inrange_dist dist ->
      Zlength dist = size ->
      ~ In u popped ->
      vvalid g u ->
      Znth u dist < inf ->
      vvalid g dst ->
      In src popped ->
      (forall i,
          vvalid g i ->
          ~ In i popped ->
          Znth u dist <= Znth i dist) ->
      inv_popped g src (u :: popped) prev dist dst.
  Proof.
    intros. rename H8 into H_u_best.
    destruct (Z.eq_dec dst u).

    (* the easy case where dst is old, and not the new u *)
    2: {
      intro. simpl in H8; destruct H8; [lia|].
      destruct (H _ H6) as [? _].
      specialize (H9 H8); destruct H9 as [[? ?]|[? [? [? ?]]]];
        [left | right].
      - split; trivial.
      - exists x; split3; trivial.
        unfold path_in_popped. intros.
        specialize (H10 _ H12). simpl; right; trivial.
    }

    (* now we must show that u is a valid entrant *)
    subst dst. clear H6.
    (* u was seen and is being popped *)
    destruct (H _ H4) as [_ [? _]].
    specialize (H6 H3 H5).
    destruct H6 as [? | [_ [? [? [? [? [? ?]]]]]]].
    
    (* the easy case where src itself is being poppped *)
    1: subst src; apply inv_popped_add_src; trivial.
    
    (* now we are in the main proof: 
         u <> src, and u is the exact new entrant.
         Main point: there is some mom in popped.
         the best path to u is:
         (the optimal path to mom) + (mom, u)
     *)
    
    remember (Znth u prev) as mom.
    destruct (popped_noninf_has_path
                _ _ _ _ _ _ H H8) as [p2mom [? [? ?]]]; trivial.
    1: pose proof (edge_cost_pos g (mom, u)); ulia.
    
    right. clear H16.
    exists (fst p2mom, snd p2mom +:: (mom, u)).              
    assert (Hg: evalid g (mom, u)). {
      rewrite (evalid_meaning g); split.
      apply edge_representable. trivial.
      intro.
      replace (elabel g (mom, u)) with inf in H9.
      apply Zlt_not_le in H9; apply H9; reflexivity.
    }
    assert (strong_evalid g (mom, u)). {
      split3; trivial.
      rewrite (edge_src_fst g); simpl; trivial.
      rewrite (edge_dst_snd g); simpl; trivial.
    }
    
    split3.
    - apply (path_correct_path_glue_one); trivial.
      + replace (Znth mom dist + elabel g (mom, u))
          with (Znth u dist).
        apply (sublist.Forall_Znth _ _ u) in H1.
        destruct H1; try ulia.
        apply (vvalid_meaning g) in H4; lia.
      + lia.
      + intro. apply H3, H14; trivial.
    - unfold path_in_popped. intros.
      destruct H13 as [? [? _]].
      apply (in_path_app_cons g _ _ src) in H17; trivial.
      destruct H17.
      + specialize (H14 _ H17).
        simpl. right; trivial.
      + subst step. simpl; left; trivial.
        
    - (* Heart of the proof:
           we must show that the locally optimal path via mom
           is actually the globally optimal path to u *)
      unfold path_globally_optimal in H15.
      destruct H13 as [? [? [? [? ?]]]].
      unfold path_globally_optimal; intros.
      rewrite (path_cost_app_cons g); trivial.
      destruct (Z_le_gt_dec
                  (path_cost g p2mom + elabel g (mom, u))
                  (path_cost g p')); auto.
      apply Z.gt_lt in g0.
      destruct (zlt (path_cost g p') inf); [|ulia].
      
      (* p' claims to be a strictly better path
           from src to u (see g0).
           We will show that this is impossible. *)
      exfalso. apply Zlt_not_le in g0. apply g0.
      
      rewrite (surjective_pairing p') in *.
      remember (snd p') as links.
      replace (fst p') with src in *.
      2: destruct H22; simpl in H22; lia.
      
      assert (Htemp: In src popped). {
        destruct H22. apply H14; trivial.
        left. rewrite (surjective_pairing p2mom) in *.
        simpl. destruct H17. simpl in H17. lia.
      } 
      
      (* we can split p' into three segments:
           the part inside popped, 
           the hop from popped to unpopped,
           and the part outside popped 
       *)
      destruct (path_leaving_popped_stronger g links src u popped)
        as [p1
              [mom'
                 [child'
                    [p2
                       [? [? [? [? [? [? [? [? [? [? [? Ha]]]]]]]]]]]]]]];
                                       trivial.
      clear Htemp.
      
      (* We clean up the goal *)
      replace (path_cost g (src, links)) with
          (path_cost g p1 +
           elabel g (mom', child') +
           path_cost g p2).
      2: { rewrite <- H23.
           do 2 rewrite (path_cost_path_glue g).
           rewrite (one_step_path_Znth g).
           symmetry. apply Z.add_assoc.
      }
      
      assert (vvalid g mom'). {
        destruct H30 as [_ [? _]].
        rewrite (edge_src_fst g) in H30.
        simpl in H30; trivial.
      }
      
      assert (vvalid g child'). {
        destruct H30 as [_ [_ ?]].
        rewrite (edge_dst_snd g) in H30;
          simpl in H30; trivial.
      }
      
      (* mom' is optimal, and so we know that there exists a 
           path optp2mom', the global minimum from src to mom' *)
      destruct (H mom' H34) as [? _].
      destruct (H36 H28) as [[? ?] | [optp2mom' [? [? ?]]]].
      1: specialize (H38 p1 H26); contradiction. 
      
      (* and path_cost of optp2mom' will be <= that of p1 *)
      pose proof (H39 p1 H24 H26).

      (* so now we can prove something quite a bit stronger *)
      apply Z.le_trans with
          (m := path_cost g optp2mom' + elabel g (mom', child')).
      2: pose proof (path_cost_pos _ _ H25); lia.

      (* Intuitionally this is clear: 
           u was chosen for being the cheapest 
           of the unpopped vertices. child' cannot beat it.
           However, for the purposes of the proof, 
           we must take cases on the status of child'
       *)
      assert (Znth mom' dist + elabel g (mom', child') < inf). {
        destruct H37 as [_ [_ [_ [? _]]]].
        rewrite H37.
        apply Z.le_lt_trans
          with (m := path_cost g p1 + elabel g (mom', child')); [lia|].
        rewrite <- H23 in l.
        replace (path_glue p1 (path_glue (mom', [(mom', child')]) p2))
          with
            (path_glue (path_glue p1 (mom', [(mom', child')])) p2) in l.
        2: { apply (path_glue_assoc g).
             apply (path_ends_meet _ _ _ src mom' child');
               trivial.
             apply (path_ends_one_step g).
             apply (path_ends_meet _ _ _ mom' child' u);
               trivial.
             apply (path_ends_one_step g).
        }
        apply path_cost_path_glue_lt in l; trivial.
        2: { apply valid_path_merge; trivial.
             apply (path_ends_meet _ _ _ src mom' child');
               trivial.
             apply (path_ends_one_step g).
             simpl; split; trivial.
             rewrite (edge_src_fst g); trivial.
        }
        destruct l as [l _].
        rewrite (path_cost_path_glue g) in l; trivial.
      }
      
      assert (0 <= Znth mom' dist). {
        rewrite (vvalid_meaning g) in H34.
        apply (sublist.Forall_Znth _ _ mom') in H1.
        destruct H1; ulia. ulia. 
      }
      assert (Htemp: 0 <= child' < Zlength dist). {
        apply (vvalid_meaning g) in H35; trivial. ulia. 
      }
      
      destruct (Znth_dist_cases child' dist) as [? | [_ ?]];
                                                    trivial; clear Htemp.
      + (* dist[child'] = inf. This is impossible *)
        exfalso.
        destruct (H _ H35) as [_ [_ ?]].
        specialize (H44 H29 H43 mom' optp2mom' H34 H28 H37 H38).
        exfalso. apply H44.
        destruct H37 as [? [? _]].
        apply valid_path_merge; trivial.
        * apply (path_ends_meet _ _ _ src mom' child'); trivial.
          red. simpl. rewrite (edge_dst_snd g). simpl. split; trivial.
        * simpl.
          rewrite (edge_src_fst g). split; trivial.
      + (* dist[child'] < inf. We use inv_unpopped *)
        destruct (H _ H35) as [_ [? _]].
        red in H44.
        assert (Znth child' dist < inf). {
          pose proof (inf_bounded_above_dist g).
          lia.
        }
        specialize (H44 H29 H45).
        destruct H44 as [? | [_ [? [? [? [? [? ?]]]]]]].
        * (* child' = src. Again, impossible *)
          exfalso.
          subst child'.
          apply H29, H38.
          destruct H37 as [_ [[? _] _]]. left.
          rewrite (surjective_pairing optp2mom') in *; simpl.
          simpl in H37; lia.
        * specialize (H50 mom' H34 H28).
          apply Z.le_trans with (m := Znth child' dist); trivial.
          2: destruct H37 as [_ [_ [_ [? _]]]]; ulia.
          rewrite <- H19, <- H11.
          apply H_u_best; trivial.
  Qed.
    
  Lemma sanity_check_postcondition: forall (g: @DijkGG size inf) src dist prev,
    connected_dir g src ->
    (forall dst, vvalid g dst -> @inv_popped size inf g src (VList g) prev dist dst) ->
    forall dst, 
      vvalid g dst -> (exists p,
        path_correct g prev dist src dst p /\
        path_in_popped g (VList g) p /\
        path_globally_optimal g src dst p).
  Proof.
    intros.
    specialize (H0 _ H1). destruct H0. apply VList_vvalid. trivial.
    destruct H0. destruct (H _ H1) as [p [? ?]].
    specialize (H2 _ H3). contradiction. apply H0.
  Qed.

End DijkstraMathLemmas.
