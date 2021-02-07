Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_spec_pure.

Local Open Scope Z_scope.

Ltac ulia := trivial; unfold V, DE in *; rep_lia.

Section DijkstraMathLemmas.

  Context {size : Z}.
  Context {inf : Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.

  Definition inrange_prev prev :=
    Forall (fun x => 0 <= x < size \/ x = inf) prev.

  Definition inrange_priq priq :=
    Forall (fun x => 0 <= x <= inf+1) priq.

  Definition inrange_dist dist :=
    Forall (fun x => 0 <= x <= inf) dist.

  Lemma Forall_upd_Znth: forall (l: list Z) i new F,
      0 <= i < Zlength l ->
      Forall F l -> F new ->
      Forall F (upd_Znth i l new).
  Proof.
    intros. rewrite Forall_forall in *. intros.
    destruct (eq_dec x new); [rewrite e; trivial|].
    rewrite upd_Znth_unfold in H2; auto.
    apply in_app_or in H2; destruct H2.
    - apply sublist_In in H2. apply (H0 x H2).
    - simpl in H2. destruct H2; [lia|].
      apply sublist_In in H2. apply (H0 x H2).
  Qed.

  Lemma Znth_dist_cases:
    forall i dist,
      0 <= i < Zlength dist ->
      inrange_dist dist ->
      Znth i dist = inf \/
      0 <= Znth i dist < inf.
  Proof.
    intros.
    apply (sublist.Forall_Znth _ _ _ H) in H0.
    simpl in H0. lia.
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

  (* Four Dijkstra-specific path-cost lemmas *)
    Lemma path_cost_app_cons:
    forall (g: @DijkGG size inf) path e,
      path_cost g (fst path, snd path +:: e) =
      path_cost g path + elabel g e.
  Proof.
    intros.
    replace (fst path, snd path +:: e) with
        (path_glue path (fst e, [e])).
    rewrite path_cost_path_glue.
    rewrite one_step_path_Znth; trivial.
    unfold path_glue. simpl. trivial.
  Qed.
 
  Lemma path_cost_glue_one_step:
    forall (g: @DijkGG size inf) p2m u i,
      path_cost g (path_glue p2m (u, [(u, i)])) = path_cost g p2m + elabel g (u, i).
  Proof.
    intros.
    rewrite path_cost_path_glue, one_step_path_Znth; trivial.
  Qed.

  Lemma path_cost_pos:
    forall (g: @DijkGG size inf) p,
      valid_path g p ->
      0 <= path_cost g p.
  Proof.
    intros. apply acc_pos; [|lia].
    intros. apply edge_cost_pos.
  Qed.

  Lemma path_cost_path_glue_lt:
    forall (g: @DijkGG size inf) p1 p2 limit,
      valid_path g p1 ->
      valid_path g p2 ->
      path_cost g (path_glue p1 p2) < limit ->
      path_cost g p1 < limit /\ path_cost g p2 < limit.
  Proof.
    intros.
    rewrite path_cost_path_glue in H1.
    pose proof (path_cost_pos _ _ H).
    pose proof (path_cost_pos _ _ H0).
    split; lia.
  Qed.
  
  (* never used, but perhaps handy *)
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

  Lemma path_ends_In_path_src:
    forall (g: @PreGraph V E V_EqDec E_EqDec) a b a2b,
      path_ends g a2b a b ->
      In_path g a a2b.
  Proof.
    intros. left. destruct H.
    rewrite (surjective_pairing a2b) in H.
    simpl in H. symmetry; trivial.
  Qed.

  Lemma path_ends_In_path_dst:
    forall (g: @PreGraph V E V_EqDec E_EqDec) a b a2b,
      path_ends g a2b a b ->
      In_path g b a2b.
  Proof.
    intros. destruct H. apply pfoot_in; trivial.
  Qed.

  Lemma path_ends_valid_src:
    forall (g: @PreGraph V E V_EqDec E_EqDec) a b a2b,
      valid_path g a2b ->
      path_ends g a2b a b ->
      vvalid g a.
  Proof.
    intros.
    apply (valid_path_valid g _ _ H),
    (path_ends_In_path_src _ _ b); trivial.
  Qed.

  Lemma path_ends_valid_dst:
    forall (g: @PreGraph V E V_EqDec E_EqDec) a b a2b,
      valid_path g a2b ->
      path_ends g a2b a b ->
      vvalid g b.
  Proof.
    intros.
    apply (valid_path_valid g _ _ H),
    (path_ends_In_path_dst _ a); trivial.
  Qed.

  Lemma path_ends_one_step:
    forall (g: @DijkGG size inf) a b,
      path_ends g (a, [(a, b)]) a b.
  Proof.
    intros. split; trivial.
    simpl. rewrite (edge_dst_snd g); trivial.
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
      apply path_ends_one_step.
      simpl. rewrite (edge_src_fst g); split; trivial.
      split3; trivial.
      rewrite (edge_src_fst g); simpl; trivial.
      apply (path_ends_valid_dst _ s _ p1); trivial.
      rewrite (edge_dst_snd g); simpl; trivial.
      apply (path_ends_valid_src _ _ u p2); trivial.
    }

    assert (elabel g (mom', child') < inf). {
      apply Z.le_lt_trans with (m := Int.max_signed / size - 1).
      apply valid_edge_bounds; trivial.
      apply (inf_further_restricted g).
    }
    
    split3; [| |split3; [| |split3;
                            [| |split3;
                                [| |split3;
                                    [| |split]]]]]; trivial.
    - apply strong_evalid_dijk; trivial.
      + apply (path_ends_valid_dst _ s _ p1); trivial.
      + apply (path_ends_valid_src _ _ u p2); trivial.
    - rewrite <- H4 in H3.
      apply path_cost_path_glue_lt in H3; trivial.
      destruct H3; trivial.
    - split; trivial. apply edge_cost_pos.
    - rewrite <- H4 in H3.
      apply path_cost_path_glue_lt in H3; trivial.
      destruct H3 as [_ ?].
      rewrite path_cost_path_glue in H3; trivial.
      rewrite one_step_path_Znth in H3. ulia.
  Qed.

  Lemma evalid_dijk:
    forall (g: @DijkGG size inf) a b cost,
      cost = elabel g (a,b) ->
      0 <= cost <= Int.max_signed / size - 1 ->
      evalid g (a,b).
  Proof.
    intros.
    rewrite (evalid_meaning g); split.
    1: apply edge_representable.
    destruct H0.
    apply Z.le_lt_trans with (m := Int.max_signed / size - 1);
      trivial.
    rewrite H in H1; trivial.
    apply (inf_further_restricted g).
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
    - split3; [| | split3]; trivial.
      + split; trivial.
      + unfold path_cost. simpl.
        apply (inf_bounds g).
      + rewrite Forall_forall; intros; simpl in H3; lia.
    - unfold path_in_popped. intros. destruct H3 as [? | [? [? _]]].
      + simpl in H3.
        simpl. left; lia.
      + simpl in H3; lia.
    - unfold path_globally_optimal; intros.
      unfold path_cost at 1; simpl.
      apply path_cost_pos; trivial.
  Qed.

  Lemma path_correct_app_cons:
    forall (g: @DijkGG size inf) src u mom p2mom prev dist,
      path_correct g prev dist src mom p2mom ->
      Znth u dist = Znth mom dist + elabel g (mom, u) ->
      Znth mom dist + elabel g (mom, u) < inf ->
      strong_evalid g (mom, u) ->
      Znth u prev = mom ->
      path_correct g prev dist src u (fst p2mom, snd p2mom +:: (mom, u)).
  Proof.
    intros.
    destruct H as [? [[? ?] [? [? ?]]]].
    assert (path_cost g p2mom + elabel g (mom, u) < inf) by
        ulia. 
    split3; [| | split3]; trivial.
    - apply (valid_path_app_cons g); trivial;
        try rewrite <- surjective_pairing; trivial.
    - apply (path_ends_app_cons g); trivial.
      split; trivial.
      rewrite <- (surjective_pairing p2mom); trivial.
    - destruct H2; rewrite path_cost_app_cons; trivial; ulia.
    - destruct H2; rewrite path_cost_app_cons; trivial; try ulia.
    - rewrite Forall_forall. intros.
      rewrite Forall_forall in H8.
      apply in_app_or in H10. destruct H10.
      + apply H8; trivial.
      + simpl in H10. destruct H10; [| lia].
        rewrite (surjective_pairing x) in *.
        inversion H10.
        simpl. rewrite <- H12, <- H13. ulia.
  Qed.

  Lemma in_path_app_cons:
    forall (g: @DijkGG size inf) step p2a src a b,
      valid_path g p2a ->
      evalid g (a,b) ->
      path_ends g p2a src a ->
      In_path g step (fst p2a, snd p2a +:: (a, b)) ->
      In_path g step p2a \/ step = b.
  Proof.
    intros. destruct H2; simpl in H2.
    1: left; unfold In_path; left; trivial.
    destruct H2 as [? [? ?]].
    assert (evalid g x). {
      apply in_app_or in H2. simpl in H2.
      destruct H2 as [? | [? | ?]]; [| | lia]; [|subst;trivial].
      rewrite (surjective_pairing p2a) in H.
      apply (valid_path_evalid _ _ _ _ H H2).
    }
    rewrite (edge_src_fst g) in H3; trivial.
    apply in_app_or in H2; simpl in H2.
    destruct H2 as [? | [? | ?]]; [| | lia]; destruct H3.
    - left. unfold In_path. right.
      exists x. rewrite (edge_src_fst g); trivial.
      split; [|left]; trivial.
    - left. unfold In_path. right.
      exists x. rewrite (edge_src_fst g); trivial.
      split; [|right]; trivial.
    - left. apply pfoot_in.
      destruct H1. rewrite H3, <- H2; simpl; trivial.
    - unfold In_path. right.
      rewrite H3, <- H2; simpl; trivial.
      rewrite (edge_dst_snd g); trivial.
  Qed.

  Lemma inv_popped_add_u:
    forall (g: @DijkGG size inf) src dst u popped prev (priq dist: list Z),
      dijkstra_correct g src popped prev dist ->
      Znth src dist = 0 ->
      (forall dst : Z,
          vvalid g dst ->
          ~ In dst popped -> Znth dst priq = Znth dst dist) ->
      inrange_dist dist ->
      Zlength priq = size ->
      Zlength dist = size ->
      ~ In u popped ->
      vvalid g u ->
      Znth u dist <= inf ->
      vvalid g dst ->
      u = find priq (fold_right Z.min (hd 0 priq) priq) 0 ->
      In src popped ->
      inv_popped g src (u :: popped) prev dist dst.
  Proof.
    intros. rename H9 into Hequ. rename H10 into Hb.
    destruct (Z.eq_dec dst u).

    (* the easy case where dst is old, and not the new u *)
    2: {
      intro. simpl in H9; destruct H9; [lia|].
      destruct (H _ H8) as [? _].
      specialize (H10 H9); destruct H10 as [[? ?]|[? [? [? ?]]]];
        [left | right].
      - split; trivial.
      - exists x; split3; trivial.
        unfold path_in_popped. intros.
        specialize (H11 _ H13). simpl; right; trivial.
    }

    (* now we must show that u is a valid entrant *)
    subst dst. clear H8.
    apply Zle_lt_or_eq in H7.
    destruct H7.
    - (* u was seen and is being popped *) {
        destruct (H _ H6) as [_ [? _]].
        specialize (H8 H5 H7).
        destruct H8 as [? | [_ [? [? [? [? [? ?]]]]]]].

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
                    _ _ _ _ _ _ H H9) as [p2mom [? [? ?]]]; trivial.
        1: pose proof (edge_cost_pos g (mom, u)); ulia.

        right. clear H17.
        exists (fst p2mom, snd p2mom +:: (mom, u)).              
        assert (Hg: evalid g (mom, u)). {
          rewrite (evalid_meaning g); split.
          apply edge_representable. trivial.
        }
        assert (strong_evalid g (mom, u)). {
          split3; trivial.
          rewrite (edge_src_fst g); simpl; trivial.
          rewrite (edge_dst_snd g); simpl; trivial.
        }
        
        split3.
        - apply path_correct_app_cons; trivial. lia.
        - unfold path_in_popped. intros.
          destruct H14 as [? [? _]].
          apply (in_path_app_cons _ _ _ src) in H18; trivial.
          destruct H18.
          + specialize (H15 _ H18).
            simpl. right; trivial.
          + subst step. simpl; left; trivial.

        - (* Heart of the proof:
             we must show that the locally optimal path via mom
             is actually the globally optimal path to u *)
          unfold path_globally_optimal in H16.
          destruct H14 as [? [? [? [? ?]]]].
          unfold path_globally_optimal; intros.
          rewrite path_cost_app_cons; trivial.
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
          2: destruct H23; simpl in H23; lia.

          assert (Htemp: In src popped). {
            destruct H23. apply H15; trivial.
            left. rewrite (surjective_pairing p2mom) in *.
            simpl. destruct H18. simpl in H18. lia.
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
          2: { rewrite <- H24.
               do 2 rewrite path_cost_path_glue.
               rewrite one_step_path_Znth. ulia.
          }

          assert (vvalid g mom'). {
            destruct H31 as [_ [? _]].
            rewrite (edge_src_fst g) in H31.
            simpl in H31; trivial.
          }

          assert (vvalid g child'). {
            destruct H31 as [_ [_ ?]].
            rewrite (edge_dst_snd g) in H31;
              simpl in H31; trivial.
          }

          (* mom' is optimal, and so we know that there exists a 
             path optp2mom', the global minimum from src to mom' *)
          destruct (H mom' H35) as [? _].
          destruct (H37 H29) as [[? ?] | [optp2mom' [? [? ?]]]].
          1: specialize (H39 p1 H25 H27); lia.
          
          (* and path_cost of optp2mom' will be <= that of p1 *)
          pose proof (H40 p1 H25 H27).

          (* so now we can prove something quite a bit stronger *)
          apply Z.le_trans with
              (m := path_cost g optp2mom' + elabel g (mom', child')).
          2: pose proof (path_cost_pos _ _ H26); lia.

          (* Intuitionally this is clear: 
             u was chosen for being the cheapest 
             of the unpopped vertices. child' cannot beat it.
             However, for the purposes of the proof, 
             we must take cases on the status of child'
           *)
          assert (Znth mom' dist + elabel g (mom', child') < inf). {
            destruct H38 as [_ [_ [_ [? _]]]].
            rewrite H38.
            apply Z.le_lt_trans
              with (m := path_cost g p1 + elabel g (mom', child')); [lia|].
            rewrite <- H24 in l.
            replace (path_glue p1 (path_glue (mom', [(mom', child')]) p2))
              with
                (path_glue (path_glue p1 (mom', [(mom', child')])) p2) in l.
            2: { apply (path_glue_assoc g).
                 apply (path_ends_meet _ _ _ src mom' child');
                   trivial.
                 apply path_ends_one_step.
                 apply (path_ends_meet _ _ _ mom' child' u);
                   trivial.
                 apply path_ends_one_step.
            }
            apply path_cost_path_glue_lt in l; trivial.
            2: { apply valid_path_merge; trivial.
                 apply (path_ends_meet _ _ _ src mom' child');
                   trivial.
                 apply path_ends_one_step.
                 simpl; split; trivial.
                 rewrite (edge_src_fst g); trivial.
            }
            destruct l as [l _].
            rewrite path_cost_path_glue in l; trivial.
          }
          
          assert (0 <= Znth mom' dist). {
            rewrite (vvalid_meaning g) in H35.
            apply (sublist.Forall_Znth _ _ mom') in H2.
            apply H2. ulia.
          }
          assert (Htemp: 0 <= child' < Zlength dist). {
            apply (vvalid_meaning g) in H36; trivial. ulia. 
          }
          
          destruct (Znth_dist_cases child' dist) as [? | [_ ?]];
                                                        trivial; clear Htemp.
          + (* dist[child'] = inf. This is impossible *)
            exfalso.
            destruct (H _ H36) as [_ [_ ?]].
            specialize (H45 H30 H44 mom' optp2mom' H35 H29 H38).
            rewrite path_cost_path_glue, one_step_path_Znth in H45.
            destruct H38 as [_ [? [_ [Hc _]]]]. ulia.
          + (* dist[child'] < inf. We use inv_unpopped *)
            destruct (H _ H36) as [_ [? _]].
            red in H45.
            specialize (H45 H30 H44).
            destruct H45 as [? | [_ [? [? [? [? [? ?]]]]]]].
            * (* child' = src. Again, impossible *)
              exfalso.
              subst child'.
              apply H30, H39.
              destruct H38 as [_ [[? _] _]]. left.
              rewrite (surjective_pairing optp2mom') in *; simpl.
              simpl in H38; lia.
            * specialize (H50 mom' H35 H29).
              apply Z.le_trans with (m := Znth child' dist); trivial.
              2: destruct H38 as [_ [_ [_ [? _]]]]; ulia.
              rewrite <- H20, <- H12.
              repeat rewrite <- H1; trivial.
              subst u.
              rewrite (Znth_find priq (fold_right Z.min (hd 0 priq) priq)).
              1: { apply fold_min_general.
                   apply Znth_In.
                   apply (vvalid_meaning g) in H36; trivial.
                   ulia.
              }
              apply min_in_list.
              1: apply incl_refl.
              pose proof (size_representable g).
              rewrite <- Znth_0_hd; [apply Znth_In|];
                rewrite H3; lia.
      }
    - (* u was unseen and is being popped *)
      intro. clear H8.
      left. destruct (H _ H6) as [_ [_ ?]].
      specialize (H8 H5 H7).
      split; trivial.
      intros.

      destruct p as [s links].
      replace s with src in *.
      2: destruct H10 as [? _]; simpl in H10; lia.
      assert (H11: 1 = 1) by trivial.
      destruct (path_leaving_popped _ _ _ _ popped H9 H10 Hb H5) as
          [p1 [mom [child [p2 [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
      rewrite <- H12.

      assert (vvalid g mom). {
        apply (path_ends_valid_dst _ src _ p1); trivial.
      }
      
      (* we don't know enough about mom. 
         let's destruct dijkstra_correct to take cases *)
      destruct (H _ H21) as [? _].
      destruct (H22 H17) as [[? ?] | [optp2mom [? [? ?]]]].

      + (* mom was popped @ inf *)
        repeat rewrite path_cost_path_glue.
        rewrite one_step_path_Znth.
        specialize (H24 p1 H13 H15).
        pose proof (edge_cost_pos g (mom, child)).
        pose proof (path_cost_pos _ _ H14).
        ulia.

      + (* mom was popped @ < inf *)
        (* it turns out we can prove something stronger *)
        specialize (H25 p1 H13 H15).
        cut (path_cost g
                       (path_glue optp2mom
                                  (path_glue (mom, [(mom, child)]) p2)) >= inf).
        1: repeat rewrite path_cost_path_glue; lia.

        (* child was ~In popped, but we don't know any more. 
           We take cases on child to learn more
         *)
        assert (vvalid g child). {
          apply (path_ends_valid_src _ _ u p2); trivial.
        }
        assert (0 <= child < Zlength dist). {
          rewrite (vvalid_meaning g) in H26. ulia.
        }
        destruct (Znth_dist_cases _ _ H27 H2) as [? | [_ ?]].
        * (* child is unseen *)
          destruct (H _ H26) as [_ [_ ?]].
          specialize (H29 H18 H28 mom optp2mom H21 H17 H23).
          rewrite path_cost_path_glue in H29.
          repeat rewrite path_cost_path_glue.
          pose proof (path_cost_pos _ _ H14).
          ulia.
        * (* child is seen but unpopped *)
          (* this is impossible: 
             dist[u] = inf and u was chosen minimally!
           *)
          exfalso.
          apply Zlt_not_le in H28.
          apply H28. rewrite <- H7.
          repeat rewrite <- H1; trivial.
          subst u.
          rewrite Znth_find.
          1: { apply fold_min_general.
               apply Znth_In.
               apply (vvalid_meaning g) in H26; ulia.
          }
          apply min_in_list.
          1: apply incl_refl.
          rewrite <- Znth_0_hd; [apply Znth_In|]; ulia.
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
      apply (edge_representable). trivial.
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
    intros.
    intro. intros.
    assert (e: dst <> u) by (simpl in H2; lia).
    apply not_in_cons in H2; destruct H2 as [_ ?].
    destruct (H dst H1) as [_ [_ ?]].
    apply H8 with (m:= m); trivial.
    simpl in H5; destruct H5; [lia | trivial].
  Qed.

  Lemma list_repeat1:
    forall {A} (a: A),
      list_repeat (Z.to_nat 1) a = [a].
  Proof. trivial. Qed.

  Lemma upd_Znth_list_repeat:
    forall {A} i size (a b : A),
      0 <= i < size ->
      upd_Znth i (list_repeat (Z.to_nat i) a ++
                              list_repeat (Z.to_nat (size - i)) b) a
      =
      list_repeat (Z.to_nat (i + 1)) a ++
                  list_repeat (Z.to_nat (size - (i + 1))) b.
  Proof.
    intros.
    rewrite upd_Znth_app2.
    2: repeat rewrite Zlength_list_repeat; lia. 
    rewrite Zlength_list_repeat by lia.
    replace (i-i) with 0 by lia.
    rewrite <- list_repeat_app' by lia.
    rewrite app_assoc_reverse; f_equal.
    rewrite upd_Znth0_old.
    2: rewrite Zlength_list_repeat; lia.
    rewrite Zlength_list_repeat, sublist_list_repeat by lia.
    rewrite list_repeat1, Z.sub_add_distr. easy.
  Qed.


  Lemma dijkstra_correct_nothing_popped:
    forall (g: @DijkGG size inf) src,
      0 <= src < size ->
      dijkstra_correct g src [] (upd_Znth src
                                          (list_repeat (Z.to_nat size) inf) src)
                       (upd_Znth src (list_repeat (Z.to_nat size) inf) 0).
  Proof.
    intros.
    unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen;
      split3; intros; [inversion H1 | left | inversion H4].
    destruct (Z.eq_dec dst src); [trivial | exfalso].
    apply (vvalid_meaning g) in H0. 
    rewrite upd_Znth_diff in H2; trivial.
    rewrite Znth_list_repeat_inrange in H2; ulia.
    all: rewrite Zlength_list_repeat; lia.
  Qed.

  Lemma In_links_snd_In_path:
    forall (g: @DijkGG size inf) step path,
      In step (snd path) ->
      In_path g (snd step) path.
  Proof.
    intros. unfold In_path. right.
    exists step. split; trivial.
    right. rewrite (edge_dst_snd g); trivial.
  Qed.

  Lemma In_links_fst_In_path:
    forall (g: @DijkGG size inf) step path,
      In step (snd path) ->
      In_path g (fst step) path.
  Proof.
    intros. unfold In_path. right.
    exists step. split; trivial.
    left. rewrite (edge_src_fst g); trivial.
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
    - destruct H8 as [? [? [? [? ?]]]].
      split3; [| | split3]; trivial.
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

  Lemma inv_unpopped_newcost:
    forall (g: @DijkGG size inf) src dst (u i: V)
           dist prev (priq: list Z) popped newcost,
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
      (forall dst : Z,
          vvalid g dst ->
          ~ In dst popped ->
          Znth dst priq = Znth dst dist) ->
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
      Znth i priq = inf \/ Znth i priq < inf ->
      0 <= dst < i + 1 ->
      inv_unpopped g src popped (upd_Znth i prev u)
                   (upd_Znth i dist newcost) dst.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ?
           H_inv_popped H_inv_unpopped H_inv_unpopped_weak
           H_inv_unseen_weak H_priq_dist_link Heqnewcost.
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
        [? | [p2mom' [? [? ?]]]]; [ulia|].
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
        rewrite H_priq_dist_link in H11; trivial.
        pose proof (H_inv_unseen_weak
                      _ H28 H10 H11 mom'
                      p2mom' H17 H18 n0 Hrem).
        rewrite path_cost_path_glue, one_step_path_Znth in H29.
        ulia.
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
        rewrite H_priq_dist_link in H11; trivial.
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
        rewrite H_priq_dist_link in H11; trivial.
        pose proof (H_inv_unseen_weak
                      _ H29 H10 H11 mom' p2mom'
                      H17 H18 H28 Hrem).
        rewrite path_cost_path_glue, one_step_path_Znth in H30.
        ulia.
      }
      assert (i <= i < size) by lia.
      rewrite H_priq_dist_link in H11; trivial.
      destruct (H_inv_unpopped_weak i H29 H10 H11).
      1: subst i; exfalso; lia.
      apply Z.lt_le_incl.
      apply Z.lt_le_trans with (m:=Znth i dist).
      1: lia.
      destruct H30 as [_ [_ ?]]. apply H30; trivial.
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
      specialize (H8 p2m H6 H9).
      pose proof (edge_cost_pos g (m, dst)).
      rewrite path_cost_path_glue, one_step_path_Znth.
      ulia.
    - (* m was popped @ < inf *)
      (* Since optp2m is optimal, it cannot be worse than p2m.
         We will strengthen the goal and then prove it. *)
      destruct H6 as [? [? _]].
      specialize (H9 p2m H6 H10).
      cut (path_cost g (path_glue optp2m (m, [(m, dst)])) >= inf).
      1: repeat rewrite path_cost_path_glue, one_step_path_Znth;
        ulia.
      assert (0 <= dst < i). {
        assert (dst <> i). {
          intro. subst dst.
          rewrite (vvalid_meaning g i) in H_i_valid.
          rewrite upd_Znth_same in H3; ulia.
        }
        lia.
      }
      rewrite upd_Znth_diff in H3; try ulia.
      apply (H_inv_unseen _ H11) with (m:=m); trivial.
      all: rewrite (vvalid_meaning g) in H_i_valid; ulia.
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
      specialize (H9 p2m H7 H10).
      pose proof (edge_cost_pos g (m, dst)).
      rewrite path_cost_path_glue, one_step_path_Znth.
      ulia.
    - (* m was popped @ < inf *)
      (* Since optp2m is optimal, it cannot be worse than p2m.
         We will strengthen the goal and then prove it. *)
      destruct H7 as [? [? _]].
      specialize (H10 p2m H7 H11).
      cut (path_cost g (path_glue optp2m (m, [(m, dst)])) >= inf).
      1: repeat rewrite path_cost_path_glue, one_step_path_Znth;
        ulia.
      assert (dst <> i). {
        intro. subst dst.
        rewrite (vvalid_meaning g i) in H_i_valid.
        rewrite upd_Znth_same in H3; ulia.
      }
      rewrite (vvalid_meaning g i) in H_i_valid.
      rewrite upd_Znth_diff in H3; try ulia.
      assert (i <= dst < size) by lia.
      apply (H_inv_unseen_weak _ H13) with (m:=m); trivial.
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
    destruct (H_inv_popped _ H15 H16); [ulia|].  
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
      specialize (H6 _ H11 H10).
      rewrite path_cost_path_glue, one_step_path_Znth in H6.
      destruct H7 as [_ [_ [_ [? _]]]]. ulia.
    }

    apply Zlt_not_le in H_improvement; apply H_improvement.
    destruct (H_inv_popped _ H_u_valid H) as [? | [p2u [? _]]].
    1: ulia.
    destruct H5 as [p2i [[_ [_ [_ [? _]]]] [_ ?]]].
    destruct H6 as [? [? [_ [? _]]]].
    rewrite H9, H5.
    specialize (H7 (fst p2u, snd p2u +:: (u,i))).  
    rewrite path_cost_app_cons in H7; trivial.
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

  Lemma inv_unpopped_newcost':
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
        [? | [p2mom' [? [? ?]]]]; [ulia|].
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
        (* rewrite H_priq_dist_link in H11; trivial. *)
        pose proof (H_inv_unseen_weak
                      _ H28 H10 H11 mom'
                      p2mom' H17 H18 n0 Hrem).
        rewrite path_cost_path_glue, one_step_path_Znth in H29.
        ulia.
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
                      H17 H18 H28 Hrem).
        rewrite path_cost_path_glue, one_step_path_Znth in H30.
        ulia.
      }
      assert (i <= i < size) by lia.
      destruct (H_inv_unpopped_weak i H29 H10 H11).
      1: subst i; exfalso; lia.
      apply Z.lt_le_incl.
      apply Z.lt_le_trans with (m:=Znth i dist).
      1: lia.
      destruct H30 as [_ [_ ?]]. apply H30; trivial.
  Qed.

  Lemma inv_popped_add_u':
    forall (g: @DijkGG size inf) src dst u popped prev (dist: list Z),
      dijkstra_correct g src popped prev dist ->
      Znth src dist = 0 ->
      inrange_dist dist ->
      Zlength dist = size ->
      ~ In u popped ->
      vvalid g u ->
      Znth u dist <= inf ->
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
    apply Zle_lt_or_eq in H5.
    destruct H5.
    - (* u was seen and is being popped *) {
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
        }
        assert (strong_evalid g (mom, u)). {
          split3; trivial.
          rewrite (edge_src_fst g); simpl; trivial.
          rewrite (edge_dst_snd g); simpl; trivial.
        }
        
        split3.
        - apply path_correct_app_cons; trivial. lia.
        - unfold path_in_popped. intros.
          destruct H13 as [? [? _]].
          apply (in_path_app_cons _ _ _ src) in H17; trivial.
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
          rewrite path_cost_app_cons; trivial.
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
               do 2 rewrite path_cost_path_glue.
               rewrite one_step_path_Znth. ulia.
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
          1: specialize (H38 p1 H24 H26); lia.
          
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
                 apply path_ends_one_step.
                 apply (path_ends_meet _ _ _ mom' child' u);
                   trivial.
                 apply path_ends_one_step.
            }
            apply path_cost_path_glue_lt in l; trivial.
            2: { apply valid_path_merge; trivial.
                 apply (path_ends_meet _ _ _ src mom' child');
                   trivial.
                 apply path_ends_one_step.
                 simpl; split; trivial.
                 rewrite (edge_src_fst g); trivial.
            }
            destruct l as [l _].
            rewrite path_cost_path_glue in l; trivial.
          }
          
          assert (0 <= Znth mom' dist). {
            rewrite (vvalid_meaning g) in H34.
            apply (sublist.Forall_Znth _ _ mom') in H1.
            apply H1. ulia.
          }
          assert (Htemp: 0 <= child' < Zlength dist). {
            apply (vvalid_meaning g) in H35; trivial. ulia. 
          }
          
          destruct (Znth_dist_cases child' dist) as [? | [_ ?]];
                                                        trivial; clear Htemp.
          + (* dist[child'] = inf. This is impossible *)
            exfalso.
            destruct (H _ H35) as [_ [_ ?]].
            specialize (H44 H29 H43 mom' optp2mom' H34 H28 H37).
            rewrite path_cost_path_glue, one_step_path_Znth in H44.
            destruct H37 as [_ [? [_ [Hc _]]]]. ulia.
          + (* dist[child'] < inf. We use inv_unpopped *)
            destruct (H _ H35) as [_ [? _]].
            red in H44.
            specialize (H44 H29 H43).
            destruct H44 as [? | [_ [? [? [? [? [? ?]]]]]]].
            * (* child' = src. Again, impossible *)
              exfalso.
              subst child'.
              apply H29, H38.
              destruct H37 as [_ [[? _] _]]. left.
              rewrite (surjective_pairing optp2mom') in *; simpl.
              simpl in H37; lia.
            * specialize (H49 mom' H34 H28).
              apply Z.le_trans with (m := Znth child' dist); trivial.
              2: destruct H37 as [_ [_ [_ [? _]]]]; ulia.
              rewrite <- H19, <- H11.
              apply H_u_best; trivial.
      }
    - (* u was unseen and is being popped *)
      intro. clear H6.
      left. destruct (H _ H4) as [_ [_ ?]].
      specialize (H6 H3 H5).
      split; trivial.
      intros.

      destruct p as [s links].
      replace s with src in *.
      2: destruct H9 as [? _]; simpl in H9; lia.
      destruct (path_leaving_popped _ _ _ _ popped H8 H9 H7 H3) as
          [p1 [mom [child [p2 [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
      rewrite <- H10.

      assert (vvalid g mom). {
        apply (path_ends_valid_dst _ src _ p1); trivial.
      }
      
      (* we don't know enough about mom. 
         let's destruct dijkstra_correct to take cases *)
      destruct (H _ H19) as [? _].
      destruct (H20 H15) as [[? ?] | [optp2mom [? [? ?]]]].

      + (* mom was popped @ inf *)
        repeat rewrite path_cost_path_glue.
        rewrite one_step_path_Znth.
        specialize (H22 p1 H11 H13).
        pose proof (edge_cost_pos g (mom, child)).
        pose proof (path_cost_pos _ _ H12).
        ulia.

      + (* mom was popped @ < inf *)
        (* it turns out we can prove something stronger *)
        specialize (H23 p1 H11 H13).
        cut (path_cost g
                       (path_glue optp2mom
                                  (path_glue (mom, [(mom, child)]) p2)) >= inf).
        1: repeat rewrite path_cost_path_glue; lia.

        (* child was ~In popped, but we don't know any more. 
           We take cases on child to learn more
         *)
        assert (vvalid g child). {
          apply (path_ends_valid_src _ _ u p2); trivial.
        }
        assert (0 <= child < Zlength dist). {
          rewrite (vvalid_meaning g) in H24. ulia.
        }
        destruct (Znth_dist_cases _ _ H25 H1) as [? | [_ ?]].
        * (* child is unseen *)
          destruct (H _ H24) as [_ [_ ?]].
          specialize (H27 H16 H26 mom optp2mom H19 H15 H21).
          rewrite path_cost_path_glue in H27.
          repeat rewrite path_cost_path_glue.
          pose proof (path_cost_pos _ _ H12).
          ulia.
        * (* child is seen but unpopped *)
          (* this is impossible: 
             dist[u] = inf and u was chosen minimally!
           *)
          exfalso.
          apply Zlt_not_le in H26.
          apply H26. rewrite <- H5.
          repeat rewrite <- H1; trivial.
          apply H_u_best; trivial.
  Qed.
    
End DijkstraMathLemmas.
