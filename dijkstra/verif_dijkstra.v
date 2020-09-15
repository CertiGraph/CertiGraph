Require Import CertiGraph.priq.priq_arr_utils.
(* remove once a better PQ is in place *)

Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.SpaceDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_spec.
Require Import CertiGraph.dijkstra.path_cost.

Require Import VST.floyd.sublist.
(* seems this has to be imported after the others *)

Local Open Scope Z_scope.

(** CONSTANTS AND RANGES **)

Ltac trilia := trivial; lia.
Ltac ulia := unfold V, E, DE in *; trilia.

Section PreProof.

Context (size : Z).
Context (inf : Z).
        
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
  apply (Forall_Znth _ _ _ H) in H0.
  simpl in H0. lia.
Qed.
  
(** MISC HELPER LEMMAS **)

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


(** LEMMAS ABOUT GET_POPPED **)

Lemma popped_noninf_has_path:
  forall {g mom src popped prev dist},
    dijkstra_correct inf size g src popped prev dist ->
    In mom popped ->
    Znth mom dist < inf ->
    vvalid g mom ->
    exists p2mom : path,
      path_correct inf size g prev dist src mom p2mom /\
      (forall step : Z,
          In_path g step p2mom ->
          In step popped) /\
      path_globally_optimal inf size g src mom p2mom.
Proof.
  intros.
  destruct (H _ H2) as [? _].
  specialize (H3 H0).
  destruct H3; [ulia|].
  apply H3; trivial.
Qed.
                  
Lemma path_leaving_popped:
  forall (g: DijkGG inf size) links s u popped,
    valid_path g (s, links) ->
    path_ends g (s, links) s u ->
    In s popped ->
    ~ In u popped ->
    exists (p1 : path) (mom child : Z) (p2 : path),
      path_glue p1 (path_glue (mom, [(mom, child)]) p2) = (s, links) /\
      valid_path g p1 /\
      valid_path g p2 /\
      path_ends g p1 s mom /\
      path_ends g p2 child u /\
      In mom popped /\
      ~ In child popped /\
      evalid g (mom, child) /\
      path_in_popped inf size g popped p1.
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
      destruct IHlinks as [p2m [m [c [p2u [? [? [? [? [? [? [? [? Ha]]]]]]]]]]]].
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
        -- unfold E, V in *. rewrite H8.
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
        simpl in H20. rewrite <- H19, <- surjective_pairing in H20. trivial.
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
  forall (g: DijkGG inf size) a b,
    path_ends g (a, [(a, b)]) a b.
Proof.
  intros. split; trivial.
  simpl. rewrite (edge_dst_snd g); trivial.
Qed. 

Lemma path_leaving_popped_stronger:
  forall (g: DijkGG inf size) links s u popped,
    valid_path g (s, links) ->
    path_ends g (s, links) s u ->
    In s popped ->
    ~ In u popped ->
    path_cost inf size g (s, links) < inf ->
    exists (p1 : path) (mom child : Z) (p2 : path),
      path_glue p1 (path_glue (mom, [(mom, child)]) p2) = (s, links) /\
      valid_path g p1 /\
      valid_path g p2 /\
      path_ends g p1 s mom /\
      path_ends g p2 child u /\
      In mom popped /\
      ~ In child popped /\
      strong_evalid g (mom, child) /\
      path_cost inf size g p1 < inf /\
      0 <= elabel g (mom, child) < inf /\
      path_cost inf size g p2 + elabel g (mom, child) < inf /\
      path_in_popped inf size g popped p1.
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
        apply Z.le_lt_trans with (m := Int.max_signed / size).
        apply valid_edge_bounds; trivial.
        admit.
        (* rewrite inf_eq. compute; trivial. *)
      }
      
      split3; [| |split3; [| |split3; [| |split3; [| |split3; [| |split]]]]]; trivial.
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
    rewrite one_step_path_Znth in H3. lia.
Admitted.

Lemma evalid_dijk:
  forall (g: DijkGG inf size) a b cost,
    cost = elabel g (a,b) ->
    0 <= cost <= Int.max_signed / size ->
    evalid g (a,b).
Proof.
  intros.
  rewrite (evalid_meaning g); split.
  1: apply edge_representable.
  apply not_eq_sym, Zaux.Zgt_not_eq.
  destruct H0.
  apply Z.le_lt_trans with (m := Int.max_signed / size);
    trivial.
  rewrite H in H1; trivial.
  admit.
Admitted.

Lemma inv_popped_add_src:
  forall (g: DijkGG inf size) src popped prev dist,
    dijkstra_correct inf size g src popped prev dist ->
    vvalid g src ->
    Znth src dist = 0 ->
    inv_popped inf size g src (src :: popped) prev dist src.
Proof.
  intros. right.
  exists (src, []); split3; trivial.
  - split3; [| | split3]; trivial.
    + split; trivial.
    + unfold path_cost. simpl.
      apply (inf_further_restricted _ _ g).
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
  forall (g: DijkGG inf size) src u mom p2mom prev dist,
  path_correct inf size g prev dist src mom p2mom ->
  Znth u dist = Znth mom dist + elabel g (mom, u) ->
  Znth mom dist + elabel g (mom, u) < inf ->
  strong_evalid g (mom, u) ->
  Znth u prev = mom ->
  path_correct inf size g prev dist src u (fst p2mom, snd p2mom +:: (mom, u)).
Proof.
  intros.
  destruct H as [? [[? ?] [? [? ?]]]].
  assert (path_cost inf size g p2mom + elabel g (mom, u) < inf) by
      ulia. 
  split3; [| | split3]; trivial.
  - apply (valid_path_app_cons g); trivial; try rewrite <- surjective_pairing; trivial.
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
  forall (g: DijkGG inf size) step p2a src a b,
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
  forall (g: DijkGG inf size) src dst u popped prev priq dist,
    dijkstra_correct inf size g src popped prev dist ->
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
    inv_popped inf size g src (u :: popped) prev dist dst.
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
  destruct (popped_noninf_has_path H H9) as [p2mom [? [? ?]]]; trivial.
  1: pose proof (edge_cost_pos inf size g (mom, u)); ulia.

  right. clear H17.
  exists (fst p2mom, snd p2mom +:: (mom, u)).              
  assert (Hg: evalid g (mom, u)). {
    rewrite (evalid_meaning g); split.
    apply edge_representable.
    apply not_eq_sym, Zaux.Zgt_not_eq; trivial.
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
                (path_cost inf size g p2mom + elabel g (mom, u))
                (path_cost inf size g p')); auto.
    apply Z.gt_lt in g0.
    destruct (zlt (path_cost inf size g p') inf); [|ulia].

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
      as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? [? [? [? [? Ha]]]]]]]]]]]]]]]; trivial.
    clear Htemp.

    (* We clean up the goal *)
    replace (path_cost inf size g (src, links)) with
        (path_cost inf size g p1 +
         elabel g (mom', child') +
         path_cost inf size g p2).
    2: { rewrite <- H24.
         do 2 rewrite path_cost_path_glue.
         rewrite one_step_path_Znth. lia.
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
        (m := path_cost inf size g optp2mom' + elabel g (mom', child')).
    2: pose proof (path_cost_pos _ _ _ _ H26); lia.

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
        with (m := path_cost inf size g p1 + elabel g (mom', child')); [lia|].
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
      apply (Forall_Znth _ _ mom') in H2.
      apply H2. ulia.
    }
    assert (Htemp: 0 <= child' < Zlength dist). {
      apply (vvalid_meaning g) in H36; trivial. ulia. 
    }
    
    destruct (Znth_dist_cases child' dist) as [? | [_ ?]]; trivial; clear Htemp.
    + (* dist[child'] = inf. This is impossible *)
      exfalso.
      destruct (H _ H36) as [_ [_ ?]].
      specialize (H45 H30 H44 mom' optp2mom' H35 H29 H38).
      rewrite path_cost_path_glue, one_step_path_Znth in H45.
      destruct H38 as [_ [? [_ [Hc _]]]].
      ulia.
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
        unfold V, E in *.
        rewrite <- H20, <- H12.
        repeat rewrite <- H1; trivial.
        subst u.
        rewrite Znth_find.
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
    destruct (path_leaving_popped _ _ _ _ popped H9 H10 Hb H5) as [p1 [mom [child [p2 [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
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
      pose proof (edge_cost_pos inf size g (mom, child)).
      pose proof (path_cost_pos _ _ _ _ H14).
      ulia.

    + (* mom was popped @ < inf *)
      (* it turns out we can prove something stronger *)
      specialize (H25 p1 H13 H15).
      cut (path_cost inf size g (path_glue optp2mom (path_glue (mom, [(mom, child)]) p2)) >= inf).
      1: repeat rewrite path_cost_path_glue; lia.

      (* 
         child was ~In popped, but we don't know any more. 
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
        pose proof (path_cost_pos _ _ _ _ H14).
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

Definition dijk_setup_loop_inv g sh src dist prev v_pq arr :=
  EX i : Z,
  PROP ()
  LOCAL (temp _dist (pointer_val_val dist);
        temp _prev (pointer_val_val prev);
        temp _src (Vint (Int.repr src));
        temp _pq (pointer_val_val v_pq);
        temp _graph (pointer_val_val arr);
        temp _size (Vint (Int.repr size)); 
        temp _inf (Vint (Int.repr inf)))
  SEP (data_at Tsh
               (tarray tint size)
               ((list_repeat (Z.to_nat i)
                             (Vint (Int.repr inf)))
                  ++ (list_repeat (Z.to_nat (size-i))
                                  Vundef)) (pointer_val_val v_pq);
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
      DijkGraph sh CompSpecs g (pointer_val_val arr) size).

Definition dijk_forloop_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr :=
  EX prev : list V,
  EX priq : list V,
  EX dist : list V,
  EX popped : list V,
  PROP (
    (* The overall correctness condition *)
    dijkstra_correct inf size g src popped prev dist;
    
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
    inrange_prev prev;
    inrange_dist dist;
    inrange_priq priq)
       
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
              (map Vint (map Int.repr priq)) (pointer_val_val priq_ptr);
      data_at Tsh
              (tarray tint size)
              (map Vint (map Int.repr dist))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size).

Definition dijk_forloop_break_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr :=
  EX prev: list V,
  EX priq: list V,
  EX dist: list V,
  EX popped: list V,
  PROP (
      (* This fact comes from breaking while *)
      Forall (fun x => x >= inf) priq;
      (* And the correctness condition is established *)
      dijkstra_correct inf size g src popped prev dist)
  LOCAL (temp _pq (pointer_val_val priq_ptr))
  SEP (data_at Tsh
               (tarray tint size)
               (map Vint (map Int.repr prev))
               (pointer_val_val prev_ptr);
      (data_at Tsh
               (tarray tint size)
               (map Vint (map Int.repr priq)) (pointer_val_val priq_ptr));
      data_at Tsh
              (tarray tint size)
              (map Vint (map Int.repr dist))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size).

Definition dijk_inner_forloop_inv (g: DijkGG inf size) sh src priq dist_ptr prev_ptr priq_ptr graph_ptr :=
  EX i : Z,
  EX prev' : list V,
  EX priq' : list V,
  EX dist' : list V,
  EX popped' : list V,
  let u :=
      find priq (fold_right Z.min (hd 0 priq) priq) 0 in
  PROP (
      (* inv_popped is not affected *)
      forall dst,
        vvalid g dst ->
        inv_popped inf size g src popped' prev' dist' dst;
    
    (* inv_unpopped is restored for those vertices
       that the for loop has scanned and repaired *)
    forall dst,
      0 <= dst < i ->
      inv_unpopped inf size g src popped' prev' dist' dst;
    
    (* a weaker version of inv_popped is
       true for those vertices that the
       for loop has not yet scanned *)
    forall dst,
      i <= dst < size ->
      inv_unpopped_weak inf size g src popped' prev' dist' dst u;
    
    (* similarly for inv_unseen,
       the invariant has been
       restored until i:
       u has been taken into account *)
    forall dst,
      0 <= dst < i ->
      inv_unseen inf size g src popped' prev' dist' dst;
    
    (* and a weaker version of inv_unseen is
       true for those vertices that the
       for loop has not yet scanned *)
    forall dst,
      i <= dst < size ->
      inv_unseen_weak inf size g src popped' prev' dist' dst u;

    (* further, some useful facts about src... *)
    Znth src dist' = 0;
    Znth src prev' = src;
    popped' <> [] -> In src popped';
    popped' = [] -> src = find priq' (fold_right Z.min (hd 0 priq') priq') 0;

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
    
    (* and ranges of the three arrays *)
    inrange_prev prev';
    inrange_priq priq';
    inrange_dist dist')
       
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
              (map Vint (map Int.repr priq')) (pointer_val_val priq_ptr);
      data_at Tsh
              (tarray tint size)
              (map Vint (map Int.repr dist'))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size).

Lemma inv_unpopped_weak_add_unpopped:
  forall (g: DijkGG inf size) prev dist popped src u dst,
    dijkstra_correct inf size g src popped prev dist ->
    ~ In u popped ->
    vvalid g dst ->
    inv_unpopped_weak inf size g src (u :: popped) prev dist dst u.
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
    rewrite <- H11 in H7. 
    apply Zlt_not_le in H7.
    apply H7; reflexivity.
  }
  
  assert (Znth mom dist < inf) by
      (pose proof (valid_edge_bounds inf size g _ H11); ulia).
  
  destruct (popped_noninf_has_path H H6 H12) as [p2mom [? [? ?]]]; trivial.
            
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
  simpl in H19; destruct H19; trilia.
Qed.

Lemma inv_unseen_weak_add_unpopped:
  forall (g : DijkGG inf size) prev dist popped src u dst,
    dijkstra_correct inf size g src popped prev dist ->
    ~ In u popped ->
    vvalid g dst ->
    inv_unseen_weak inf size g src (u :: popped) prev dist dst u.
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
    upd_Znth i (list_repeat (Z.to_nat i) a ++ list_repeat (Z.to_nat (size - i)) b) a
    =
    list_repeat (Z.to_nat (i + 1)) a ++ list_repeat (Z.to_nat (size - (i + 1))) b.
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
  forall g src,
    0 <= src < size ->
    dijkstra_correct inf size g src [] (upd_Znth src (list_repeat (Z.to_nat size) inf) src)
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
  forall (g: DijkGG inf size) step path,
    In step (snd path) ->
    In_path g (snd step) path.
Proof.
  intros. unfold In_path. right.
  exists step. split; trivial.
  right. rewrite (edge_dst_snd g); trivial.
Qed.

Lemma In_links_fst_In_path:
  forall (g: DijkGG inf size) step path,
    In step (snd path) ->
    In_path g (fst step) path.
Proof.
  intros. unfold In_path. right.
  exists step. split; trivial.
  left. rewrite (edge_src_fst g); trivial.
Qed.
  
Lemma inv_popped_newcost:
  forall (g: DijkGG inf size) src dst u i newcost popped prev dist,
    vvalid g i ->
    vvalid g dst ->
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
    Zlength prev = size ->
    Zlength dist = size ->
    ~ In i popped ->
    inv_popped inf size g src popped
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
      intro contra. unfold V in *.
      rewrite contra in *. apply H4; ulia.
    }
    unfold V in *.
    rewrite upd_Znth_diff; try lia.
    rewrite H2, <- (vvalid_meaning g); trivial.
    apply (valid_path_valid _ p2dst); trivial.
Qed.

Lemma inv_unpopped_newcost_dst_neq_i:
  forall (g: DijkGG inf size) src dst u i newcost prev dist popped,
    (forall dst : Z,
        0 <= dst < i ->
        inv_unpopped inf size g src popped prev dist dst) ->
    vvalid g i ->
    Zlength prev = size ->
    Zlength dist = size ->
    ~ In i popped ->
    0 <= dst < i + 1 ->
    dst <> i ->
    inv_unpopped inf size g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
Proof.
  intros. 
  assert (0 <= dst < i) by lia.
  (* We will proceed using the old best-known path for dst *)
  assert (0 <= i < size) by now apply (vvalid_meaning g).
  unfold inv_unpopped. intros.
  rewrite upd_Znth_diff in * by ulia.
  destruct (H _ H6 H8) as
      [? | [? [? [? [? [? [? ?]]]]]]]; trivial;
    [left | right]; trivial.
  unfold V in *.
  remember (Znth dst prev) as mom. 
  split; trivial.
  assert (Znth mom dist < inf). {
    pose proof (edge_cost_pos inf size g (mom, dst)); ulia.
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
  forall (g: DijkGG inf size) src dst u i
         dist prev priq popped newcost,
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        0 <= dst < i ->
        inv_unpopped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        i <= dst < size ->
        inv_unpopped_weak inf size g src popped prev dist dst u) ->
    (forall dst : Z,
        i <= dst < size ->
        inv_unseen_weak inf size g src popped prev dist dst u) ->
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
    inv_unpopped inf size g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
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
  unfold V in *.
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
  1: { rewrite H20. pose proof (edge_cost_pos inf size g (mom', i)). ulia.
  }

  destruct (H_inv_popped _ H17 H18) as
      [? | [p2mom' [? [? ?]]]]; [ulia|].
  assert (Hrem:= H21).
  destruct H21 as [? [? [? ?]]].
  pose proof (path_ends_In_path_dst _ _ _ _ H24).
  destruct (zlt ((Znth mom' dist) + elabel g (mom', i)) inf).
  2: {
    unfold V in *.
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
      unfold V in *. subst mom'.
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
  forall (g: DijkGG inf size) src dst u i prev dist popped newcost,
    (forall dst : Z,
        i <= dst < size ->
        inv_unpopped_weak inf size g src popped prev dist dst u) ->
    vvalid g i ->
    Zlength prev = size ->
    Zlength dist = size ->
    ~ In i popped ->
    i + 1 <= dst < size ->
    inv_unpopped_weak inf size g src popped
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
  unfold V in *.
  rewrite upd_Znth_diff in H6 by lia.
  destruct (H_inv_unpopped_weak _ H7 H5 H6)
    as [? | [? [[? [? [? [? [? ?]]]]] ?]]];
    [left | right]; trivial.
  unfold V in *.
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
  forall (g: DijkGG inf size) src i m dist prev newcost p2m,
    vvalid g i ->
    vvalid g m ->
    Zlength dist = size ->
    m <> i ->
    path_correct inf size g prev (upd_Znth i dist newcost) src m p2m ->
    path_correct inf size g prev dist src m p2m.
Proof.
  intros.
  destruct H3 as [? [? [? [? ?]]]].
  split3; [| |split3]; trivial.
  apply (vvalid_meaning g) in H.
  apply (vvalid_meaning g) in H0.
  rewrite upd_Znth_diff in H6; lia.  
Qed.

Lemma inv_unseen_newcost:
  forall (g: DijkGG inf size) dst src i u dist prev popped newcost,
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        0 <= dst < i ->
        inv_unseen inf size g src popped prev dist dst) ->
    vvalid g i ->
    Zlength dist = size ->
    0 <= dst < i + 1->
    newcost < inf ->
    inv_unseen inf size g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
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
   pose proof (edge_cost_pos inf size g (m, dst)).
   rewrite path_cost_path_glue, one_step_path_Znth.
   ulia.
 - (* m was popped @ < inf *)
   (* Since optp2m is optimal, it cannot be worse than p2m.
      We will strengthen the goal and then prove it. *)
   destruct H6 as [? [? _]].
   specialize (H9 p2m H6 H10).
   cut (path_cost inf size g (path_glue optp2m (m, [(m, dst)])) >= inf).
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
  forall (g: DijkGG inf size) dst src u i dist prev popped newcost,
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        i <= dst < size ->
        inv_unseen_weak inf size g src popped prev dist dst u) ->
    vvalid g i ->
    Zlength dist = size ->
    i + 1 <= dst < size ->
    newcost < inf ->
    inv_unseen_weak inf size g src popped
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
    pose proof (edge_cost_pos inf size g (m, dst)).
    rewrite path_cost_path_glue, one_step_path_Znth.
    ulia.
  - (* m was popped @ < inf *)
    (* Since optp2m is optimal, it cannot be worse than p2m.
       We will strengthen the goal and then prove it. *)
    destruct H7 as [? [? _]].
    specialize (H10 p2m H7 H11).
    cut (path_cost inf size g (path_glue optp2m (m, [(m, dst)])) >= inf).
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
  forall (g: DijkGG inf size) src dst u i dist prev popped,
    vvalid g i ->
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        0 <= dst < i ->
        inv_unpopped inf size g src popped prev dist dst) ->
    (forall dst : Z,
        i <= dst < size ->
        inv_unpopped_weak inf size g src popped prev dist dst u) ->
    inrange_dist dist ->
    Zlength dist = size ->
    Znth u dist + elabel g (u, i) >= Znth i dist ->
    0 <= dst < i + 1 ->
    inv_unpopped inf size g src popped prev dist dst.
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
  unfold V in *.
  remember (Znth i prev) as mom.
  split3; [| |split3; [| |split3]]; trivial.
  intros.
  pose proof (Znth_dist_cases mom' dist).
  rename H17 into e.
  destruct e as [e | e]; trivial.
  1: apply (vvalid_meaning g) in H15; ulia.
  1: {
    rewrite e.
    pose proof (edge_cost_pos inf size g (mom', i)).
    ulia.
  }
  destruct (H_inv_popped _ H15 H16); [unfold V in *; ulia|].  
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
        unfold V in *.
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
    apply pfoot_in in H25. rewrite H20 in *. trivial.       Qed.

Lemma path_in_popped_path_glue:
  forall g p1 p2 popped,
    path_in_popped inf size g popped p1 ->
    path_in_popped inf size g popped p2 ->
    path_in_popped inf size g popped (path_glue p1 p2).
Proof.
  red. intros.
  apply In_path_glue in H1. destruct H1.
  - apply H; trivial.
  - apply H0; trivial.
Qed.

Lemma not_in_popped:
  forall (g: DijkGG inf size) src u i cost prev dist popped,
    vvalid g u ->
    vvalid g i ->
    (forall dst : Z,
        vvalid g dst ->
        inv_popped inf size g src popped prev dist dst) ->
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
  unfold V, E in *. rewrite H9, H5.
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

(** PROOF BEGINS **)

End PreProof.

Lemma body_getCell inf size: semax_body Vprog (Gprog inf size) f_getCell (getCell_spec inf size).
Proof.
  start_function.
  unfold DijkGraph.
  rewrite (SpaceAdjMatGraph_unfold _ _ id _ _ u); trivial.
  Intros.
  unfold list_rep.
  Fail forward.
  
  assert_PROP (force_val
                 (sem_add_ptr_int
                    (tptr tint)
                    Signed
                    (pointer_val_val graph_ptr)
                    (Vint (Int.repr u))) =
               field_address
                 (Tarray tint size noattr)
                 [ArraySubsc u]
                 (pointer_val_val graph_ptr)
              ). {
    entailer!. simpl.
    rewrite field_address_offset.
    1: f_equal.
    admit. (* even if we admit this... *)
  }
  Fail forward.
  (* Why is THIS the error message? *)
Abort.

    (*
    - destruct H2 as [? [? [? [? ?]]]].
      unfold field_compatible; split3; [| | split3]; auto.
      + destruct graph_ptr; trivial.
      + destruct graph_ptr; trivial; simpl in H6 |- *.
        apply Z.le_lt_trans
          with
            (m:= Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (u * (4 * Z.max 0 size)))) +
                 4 * Z.max 0 size); trivial.
        apply Zplus_le_compat_r.

        clear -H6 g.
        replace Ptrofs.modulus with (Z.succ Ptrofs.max_unsigned) in H6.
        2: compute; trivial.
        apply Zlt_succ_le in H6.
        
        rewrite Ptrofs.add_unsigned in *.
        pose proof (Ptrofs.unsigned_range_2 (Ptrofs.repr (u * (4 * Z.max 0 size)))).
        pose proof (Ptrofs.unsigned_range_2 i0).
        rewrite Ptrofs.unsigned_repr; [lia|].
        admit.
      + clear -H7 g.
        destruct graph_ptr; trivial.
        simpl. constructor. simpl. intros.
        admit.
      + admit.
  } *)


Lemma body_dijkstra inf size: semax_body Vprog (Gprog inf size) f_dijkstra (dijkstra_spec inf size).
Proof.
  start_function.
  pose proof (size_further_restricted _ _ g).
  rename H1 into Hsz.
  forward_call (sh, size * sizeof(tint)).
  1: {
    simpl. split; [lia|].
    apply Z.le_trans with (m:= Int.max_signed).
    lia. compute; inversion 1.
  } 
  Intro priq_ptr.
  forward_for_simple_bound
    size
    (dijk_setup_loop_inv size inf g sh src dist_ptr prev_ptr priq_ptr graph_ptr).
  - rewrite list_repeat_0, app_nil_l, Z.sub_0_r, Z_div_mult, data_at__tarray.
    entailer!.
    simpl; lia.
  - forward. forward.
    forward_call ((pointer_val_val priq_ptr), i, inf,
                  (list_repeat (Z.to_nat i)
                               (Vint (Int.repr inf)) ++
                               list_repeat (Z.to_nat (size - i)) Vundef), size, inf).
    1: { split; trivial.
         unfold weight_inrange_priq.
         pose proof (inf_representable g).
         split; [|reflexivity].
         apply Z.le_trans with (m:=0); [|lia].
         compute; inversion 1.
    }
    rewrite upd_Znth_list_repeat; [|lia].
    entailer!.     
  - (* At this point we are done with the
       first for loop. The arrays are all set to inf. *)
    replace (size - size) with 0 by lia;
      rewrite list_repeat_0, <- (app_nil_end).
    forward. forward.
    do 2 rewrite <- map_list_repeat.
    forward_call ((pointer_val_val priq_ptr), src, 0, (list_repeat (Z.to_nat size) inf), size, inf).
    1: { split; trivial.
         pose proof (inf_representable g).
         unfold weight_inrange_priq.
         split; [compute; inversion 1 | lia].
    }
    do 2 rewrite map_list_repeat.
    assert (H_src_valid: vvalid g src). {
      rewrite (vvalid_meaning g); trivial.
    }

    (* Special values for src have been inserted *)

    (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
     *)
  
    forward_loop
    (dijk_forloop_inv size inf g sh src dist_ptr prev_ptr priq_ptr graph_ptr)
    break: (dijk_forloop_break_inv size inf g sh src dist_ptr prev_ptr priq_ptr graph_ptr).
    + unfold dijk_forloop_inv.
      Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) src).
      Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
      Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
      Exists (@nil V).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat size) inf) = size). {
        rewrite Zlength_list_repeat. lia.
        pose proof (size_representable g). lia.
      }
      split3; [| |split3; [| |split]].
      * apply (dijkstra_correct_nothing_popped size inf g src); trivial.
      * rewrite upd_Znth_same; trivial. ulia. 
      * rewrite upd_Znth_same; trivial. ulia.
      * intros; rewrite find_src; trivial.
        apply (inf_further_restricted _ _ g).
      * intros. split; [inversion 1 | intros; exfalso].
        destruct (Z.eq_dec src v).
        -- subst src. rewrite upd_Znth_same in H15 by ulia.
           pose proof (inf_further_restricted _ _ g).
           lia. 
        -- assert (0 <= v < size) by now apply (vvalid_meaning g).
           rewrite upd_Znth_diff in H15 by ulia.
           rewrite Znth_list_repeat_inrange in H15; trivial.
           rewrite Z.add_1_r in H15.
           apply (Z.neq_succ_diag_l inf). lia.
           
      * pose proof (inf_further_restricted _ _ g).
        split3; red; apply Forall_upd_Znth;
          try apply Forall_list_repeat;
          try rewrite inf_eq; ulia.
      * repeat rewrite map_list_repeat. entailer!.

    + (* Now the body of the while loop begins. *)
      unfold dijk_forloop_inv.
      Intros prev priq dist popped.
      rename H4 into Hb.
      rename H5 into Hc.
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

      assert (H_inrange_priq_trans:
                forall priq,
                  inrange_priq inf priq ->
                  priq_arr_utils.inrange_priq priq inf). {
        intros.
        red in H11 |- *.
        rewrite Forall_forall in H11 |- *.
        intros ? H_in. specialize (H11 _ H_in). rep_lia.
      }
      forward_call ((pointer_val_val priq_ptr),
                    priq, size, inf).
      1: { pose proof (size_representable g).
           pose proof (inf_further_restricted _ _ g).
           split3; [| |split3]; try ulia.
           apply H_inrange_priq_trans; trivial.
           apply Z.lt_trans with (m:=0);
             [compute; trivial | ulia].
      }
      forward_if. (* checking if it's time to break *)
      * (* No, don't break. *)
        rename H11 into Htemp.
        assert (isEmpty priq inf = Vzero). {
          destruct (isEmptyTwoCases priq inf);
            rewrite H11 in Htemp; simpl in Htemp;
              now inversion Htemp.
        }
        clear Htemp.
        forward_call ((pointer_val_val priq_ptr), priq, size, inf).
        1: { pose proof (size_representable g).
             pose proof (inf_further_restricted _ _ g).
             split3; [| |split3; [| |split]]; try ulia.
             apply H_inrange_priq_trans; trivial.
             apply Z.lt_trans with (m:=0);
               [compute; trivial | ulia].
        }
          
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
          1: { rewrite Zlength_nil in H8.
               pose proof (size_representable g).
               lia.
          }
          simpl. left; trivial.
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
        
        assert (H_inf_reppable: Int.min_signed <= inf <= Int.max_signed). {
          pose proof (inf_representable g).
          split; [|lia].
          apply Z.le_trans with (m:=0); [compute; inversion 1 | ulia].
        }

        rewrite Znth_0_hd.
        2: ulia. 
        do 2 rewrite upd_Znth_map.
        
        unfold V in *.
        assert (Htemp: 0 <= u < Zlength dist) by lia.
        pose proof (Znth_dist_cases _ _ _ Htemp H6).
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
          (dijk_inner_forloop_inv _ _ g sh src priq dist_ptr
                                  prev_ptr priq_ptr graph_ptr).
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
          remember (Zlength priq) as size.
          remember (find priq
                         (fold_right Z.min (hd 0 priq)
                                     priq) 0) as u.
          clear H15 H16 H17 H18 H19 H20 H21 H22
                H23 H24 H25 H26 H27. 
          
          split3; [| | split3; [| |split3; [| |split3]]]; trivial.
          ++ intros.
             (* if popped = [], then 
                prove inv_popped for [u].
                if popped <> [], then we're set
              *)
             destruct popped eqn:?.
             2: {
               apply (inv_popped_add_u _ _ _ _ _ _ _ _ priq); try ulia.
               apply Hb; inversion 1.
             }
             replace u with src in *.
             2: apply Hc; trivial.

             intro.
             simpl in H16; destruct H16; [|lia].
             subst dst; clear H15.
             destruct H14; [left | right].
             ** exfalso. rewrite H14 in H2.
                pose proof (inf_further_restricted _ _ g).
                ulia.
             ** exists (src, []). split3.
                --- split3; [| |split3]; trivial.
                    +++ split; trivial.
                    +++ unfold path_cost.
                        simpl. ulia.
                    +++ apply Forall_forall.
                        inversion 1.
                --- unfold path_in_popped.
                    intros. 
                    inversion H15.
                    +++ simpl in H16. 
                        subst step. simpl; left; trivial.
                    +++ destruct H16 as [? [? _]].
                        inversion H16.
                --- red. intros.
                    unfold path_cost at 1; simpl.
                    apply path_cost_pos; trivial.
          ++ intros.
             apply (vvalid_meaning g) in H15.
             apply inv_unpopped_weak_add_unpopped; trivial.

          ++ intros.
             apply (vvalid_meaning g) in H15.
             apply (inv_unseen_weak_add_unpopped _ _ g prev _ _ src); trivial.

          ++ intros. clear H15.
             destruct popped eqn:?.
             2: right; apply Hb; inversion 1.
             simpl. left. symmetry.
             apply Hc; trivial.

          ++ intros. inversion H15.
            
          ++ apply in_eq.

          ++ intros.
             assert (0 <= v < size) by now apply (vvalid_meaning g).
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
             rewrite upd_Znth_diff; trivial.
             apply H4; trivial.
             apply not_in_cons in H16; destruct H16 as [_ ?].
             trivial. ulia.

          ++ apply Forall_upd_Znth; trivial.
             ulia. split; [|reflexivity].
             pose proof (inf_further_restricted _ _ g); lia.
        -- (* We now begin with the for loop's body *)
          rewrite <- Hequ.
          freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
(*
          unfold DijkGraph.
          rewrite (SpaceAdjMatGraph_unfold _ _ id _ _ u).
          2: ulia.
 *)
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
          rename H28 into H21.
          rename H29 into H22.
          rename H30 into H23.

          forward_call (sh, g, graph_ptr, u, i).

(*
this is how it was done, in one fell swoop, earlier
 *)
          (*
          assert_PROP (force_val
                         (sem_add_ptr_int
                            tint
                            Signed
                            (force_val
                               (sem_add_ptr_int
                                  (tarray tint size)
                                  Signed
                                  (pointer_val_val graph_ptr)
                                  (Vint (Int.repr u))))
                            (Vint (Int.repr i))) =
                       field_address
                         (tarray tint size)
                         [ArraySubsc i]
                         (@list_address
                            size
                            CompSpecs
                            (pointer_val_val graph_ptr)
                            u)). {
            entailer!.
            clear H8 H24 H25 H26 H27 H29. rename H28 into H24.
            unfold list_address. simpl.
            rewrite field_address_offset.
            1: { rewrite offset_offset_val; simpl; f_equal.
                 rewrite Z.add_0_l. f_equal. lia. }            
            destruct H24 as [? [? [? [? ?]]]].
            unfold field_compatible; split3; [| | split3]; simpl; auto.
          }
           *)

          remember (Znth i (Znth u (@graph_to_mat size g id))) as cost.

          assert (H_i_valid: vvalid g i). {
            apply (vvalid_meaning g); trivial.
          }

          rewrite <- elabel_Znth_graph_to_mat in Heqcost; trivial.

          assert_PROP (Zlength priq' = size). {
            (* add to invariant *)
            admit.
          }

          assert_PROP (Zlength prev' = size). {
            admit.
          }
          assert_PROP (Zlength dist' = size). {
            admit.
          }
          
          forward_if.
          ++ rename H27 into Htemp.
             assert (0 <= cost <= Int.max_signed / size). {
               pose proof (edge_representable _ _ g (u, i)).
               rewrite Heqcost in *.
               apply (valid_edge_bounds _ _ g).
               rewrite (evalid_meaning g). split; trivial.
               intro.
               rewrite Int.signed_repr in Htemp; trivial.
               rewrite <- H28 in Htemp.
               apply Zlt_not_le in Htemp.
               apply Htemp; reflexivity. (* lemma-fy *)
             }
             clear Htemp.
             assert (H_ui_valid: evalid g (u,i)). {
               apply evalid_dijk with (cost := cost);
                 trivial.
             }
             
             assert (0 <= Znth u dist' <= inf). {
               assert (0 <= u < Zlength dist') by lia.
               apply (Forall_Znth _ _ _ H28) in H23.
               assumption.
             }
             assert (0 <= Znth i dist' <= inf). {
               assert (0 <= i < Zlength dist') by lia.
               apply (Forall_Znth _ _ _ H29) in H23.
               assumption.
             }
             assert (0 <= Znth u dist' + cost <= Int.max_signed). {
               split; [lia|].
               assert (inf <= Int.max_signed - (Int.max_signed / size)). {
                 admit.
               }
               
               rep_lia.
             }
             unfold V, DE in *.
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
                  apply (not_in_popped _ _ g src u i cost prev' dist'); trivial.
                }
                assert (Htemp : 0 <= i < Zlength dist') by lia.
                pose proof (Znth_dist_cases inf i dist' Htemp H23).
                clear Htemp.
                rename H31 into icases.
                rewrite <- H_priq_dist_link in icases; trivial.
  
                forward. forward. forward.
                forward; rewrite upd_Znth_same; trivial.
                1: entailer!.
                1,3: repeat rewrite Zlength_map; lia.
                forward_call ((pointer_val_val priq_ptr), i, (Znth u dist' + cost), priq', size, inf).

(* Now we must show that the for loop's invariant
   holds if we take another step,
   ie when i increments
                
   We will provide the arrays as they stand now:
   with the i'th cell updated in all three arrays,
   to log a new improved path via u 
 *)
                1: split; trivial; red; rep_lia.
                Exists (upd_Znth i prev' u).
                Exists (upd_Znth i priq' (Znth u dist' + cost)).
                Exists (upd_Znth i dist' (Znth u dist' + cost)).
                Exists popped'.
                repeat rewrite <- upd_Znth_map.
                unfold V, DE in *.
                entailer!.

                clear H31 H32 H33 H34 H35 H36
                      H37 H38 H39 H40 H41 H42 H8.

                remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
                remember (Zlength priq) as size.
                
                Set Printing All.
                remember (Znth u dist' + elabel g (u, i)) as newcost.
                unfold V, DE in *.
                
                rewrite <- Heqnewcost in *.
                Unset Printing All.

                assert (u <> i) by (intro; subst; lia).
                
                split3; [| | split3; [| | split3; [| | split3;[| |split]]]]; intros.
                (* 9 goals, where the 9th is 
                   3 range-based goals together *)
                --- apply inv_popped_newcost; try ulia.
                --- apply inv_unpopped_newcost with (priq := priq'); ulia.
                --- now apply inv_unpopped_weak_newcost.
                --- apply inv_unseen_newcost; ulia.
                --- apply inv_unseen_weak_newcost; ulia. 
                --- rewrite upd_Znth_diff; try lia;
                      intro; subst src; lia.
                --- rewrite upd_Znth_diff; try lia;
                      intro; subst src; lia.
                --- assert (0 <= v < size) by now apply (vvalid_meaning g).
                    split; intros; destruct (Z.eq_dec v i).
                    +++ exfalso. subst v.
                        apply H_i_not_popped; trivial.
                    +++ rewrite upd_Znth_diff; try ulia.
                        apply H_priq_popped_link; trivial.
                    +++ exfalso. subst v.
                        rewrite upd_Znth_same in H33; ulia.
                    +++ rewrite upd_Znth_diff in H33; try ulia.
                        apply <- H_priq_popped_link; trivial.
                --- destruct (Z.eq_dec dst i).
                    1: subst dst; repeat rewrite upd_Znth_same; ulia.
                    repeat rewrite upd_Znth_diff; trivial; try lia.
                    apply H_priq_dist_link; trivial.
                    all: rewrite (vvalid_meaning g) in H31; ulia.
                --- split3; apply Forall_upd_Znth; ulia.
                    
             ** (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                rename H31 into H_non_improvement.
                forward. 
                (* The old arrays are just fine. *)
                Exists prev' priq' dist' popped'.
                entailer!.
                remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
                remember (Zlength priq) as size.
                clear H31 H32 H33 H34 H35 H36
                      H37 H38 H39 H40 H41 H42.
                assert (elabel g (u, i) < inf). {
                  apply Z.le_lt_trans with (m := Int.max_signed / size);
                    trivial.
                  apply H27. admit.
                }
                
                split3; [| |split].
                --- intros. apply inv_unpopped_new_dst with (u:= u) (i := i); trivial.
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
                    unfold V in *.
                    rewrite H34 in H_non_improvement.
                    assert (0 <= u < size) by lia.
                    rewrite path_cost_path_glue, one_step_path_Znth.
                    destruct H37 as [_ [_ [_ [? _]]]].
                    ulia.
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
            rewrite Int.signed_repr in H27.
            2: apply edge_representable.
            clear H28 H29 H30 H31 H32 H33
                  H34 H35 H36 H37 H38 H39.
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
                   unfold V in *.
                   remember (Znth i prev') as mom.

                   assert (Ha: Znth mom dist' < inf). {
                     pose proof (edge_cost_pos _ _ g (mom, i)).
                     ulia.
                   }
                   
                   right. split3; [| |split3; [| |split3]]; trivial.
                   
                   intros.
                   destruct (Znth_dist_cases inf mom' dist') as [e | e]; trivial.
                   1: apply (vvalid_meaning g) in H40; ulia.
                   1: { rewrite e.
                        pose proof (edge_cost_pos _ _ g (mom', i)).
                        ulia.
                   }
                   unfold V in *.
                   
                   destruct (zlt (Znth mom' dist' + elabel g (mom', i)) inf).
                   2: ulia.
                   assert (vvalid g i). { trivial. }
                   
                   destruct (Z.eq_dec mom' u).
                   1: { subst mom'.
                        assert (0 <= Znth u dist'). {
                          apply (Forall_Znth _ _ u) in H23.
                          simpl in H23. apply H23.
                          lia.
                        }
                        ulia.
                   }
                   apply H39; trivial.
               --- apply H_inv_unpopped; lia.
            ** destruct (Z.eq_dec dst i).
               --- lia. 
               --- apply H_inv_unpopped_weak; lia.
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
                 apply (Forall_Znth _ _ u) in H23.
                 apply H23.
                 ulia.
               }
               rewrite path_cost_path_glue, one_step_path_Znth.
               destruct H34 as [? _].
               pose proof (path_cost_pos _ _ _ _ H34).
               ulia.
            ** apply H_inv_unseen_weak; lia.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
          Intros prev' priq' dist' popped'.
          Exists prev' priq' dist' popped'.
          entailer!.
          remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
          remember (Zlength priq) as size.
          clear H30 H31 H32 H33 H34
                H35 H36 H37 H38 H38 H39 H40 H41.
          unfold dijkstra_correct.
          split3; [auto | apply H16 | apply H18];
            try rewrite <- (vvalid_meaning g); trivial.
          
      * (* After breaking from the while loop,
           prove break's postcondition *)
        assert (isEmpty priq inf = Vone). {
          destruct (isEmptyTwoCases priq inf); trivial.
            rewrite H12 in H11; simpl in H11; now inversion H11.
        }
        clear H11.
        forward. Exists prev priq dist popped.
        entailer!.
        pose proof (isEmptyMeansInf priq inf).
        rewrite H25 in H12.
        rewrite Forall_forall in H12 |- *.
        intros. specialize (H12 _ H26). lia.
    + (* from the break's postcon, prove the overall postcon *)
      unfold dijk_forloop_break_inv.
      Intros prev priq dist popped.
(*      freeze FR :=
        (data_at _ _ _ (pointer_val_val prev_ptr))
          (data_at _ _ _ (pointer_val_val dist_ptr))
          (DijkGraph _ _ _ _ _).
       forward_call ((wshare_share sh), priq_ptr, size, priq). 
*)
      (* the call to free *)
      forward.
      Exists prev dist popped. entailer!.
      intros. destruct (H2 _ H12) as [? _]; trivial.
      admit.
Admitted.
