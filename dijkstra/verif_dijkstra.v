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

Opaque inf.

Definition inrange_prev prev :=
  Forall (fun x => 0 <= x < SIZE \/ x = inf) prev.

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
    Znth i dist < inf.
Proof.
  intros.
  apply (Forall_Znth _ _ _ H) in H0.
  simpl in H0. lia.
Qed.
  
(** MISC HELPER LEMMAS **)

Lemma sublist_nil: forall lo hi A,
    sublist lo hi (@nil A) = (@nil A).
Proof.
  intros. unfold sublist.
  rewrite firstn_nil.
  apply sublist.skipn_nil.
Qed.

Lemma sublist_cons:
  forall a (l: list Z) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by lia.
  rewrite sublist_one by lia.
  simpl. rewrite Znth_0_cons.
  rewrite sublist_1_cons; trivial.
Qed.

Lemma sublist_cons':
  forall a (l: list (Z*Z)) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by lia.
  rewrite sublist_one by lia. simpl.
  rewrite Znth_0_cons.
  rewrite sublist_1_cons. reflexivity.
Qed.

Lemma combine_same_length:
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros.
  repeat rewrite Zlength_correct in *.
  rewrite combine_length.
  rewrite min_l. reflexivity. rep_lia.
Qed.

Lemma sublist_skip: forall A lo (l: list A) a,
    0 < lo ->
    sublist lo (Z.succ (Zlength l)) (a::l) =
    sublist (lo - 1) (Zlength l) l.
Proof.
  intros. unfold sublist.
  destruct (Z.to_nat lo) eqn:?.
  - exfalso.
    unfold Z.to_nat in Heqn.
    destruct lo; try inversion H.
    pose proof (Pos2Nat.is_pos p); lia.
  - assert (Z.to_nat (lo - 1) = n) by
        now rewrite <- (juicy_mem_lemmas.nat_of_Z_lem1 n lo).
    rewrite H0.
    assert (Z.to_nat (Z.succ(Zlength l)) = S (Z.to_nat (Zlength l))). {
      rewrite Z2Nat.inj_succ; auto. apply Zlength_nonneg. }
    rewrite H1. now simpl.
Qed.

Lemma combine_sublist_gen:
  forall (l1 l2 : list Z) lo,
    0 <= lo < Zlength l1 + 1 ->
    Zlength l1 = Zlength l2 ->
    combine (sublist lo (Zlength l1) l1) (sublist lo (Zlength l2) l2) =
    sublist lo (Zlength (combine l1 l2)) (combine l1 l2).
Proof.
  induction l1, l2; intros; simpl; autorewrite with sublist.
  - rewrite !sublist_nil. easy.
  - rewrite Zlength_nil in H0. rewrite Zlength_cons in H0.
    pose proof (Zlength_nonneg l2). exfalso. lia.
  - rewrite Zlength_nil in H0. rewrite Zlength_cons in H0.
    pose proof (Zlength_nonneg l1). exfalso. lia.
  - destruct (Z.eq_dec 0 lo).
    + subst lo. autorewrite with sublist. now simpl.
    + assert (0 < lo) by lia. rewrite !sublist_skip; auto.
      rewrite !Zlength_cons in *. apply IHl1; lia.
Qed.

Lemma combine_sublist_specific:
  forall (l1 l2: list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (sublist 0 i l1) (sublist 0 i l2) =
    sublist 0 i (combine l1 l2).
Proof.
  induction l1, l2; intros; simpl; autorewrite with sublist.
  - rewrite !sublist_nil. easy.
  - rewrite Zlength_nil in H0. lia.
  - rewrite Zlength_nil in H. rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg l1). lia.
  - destruct (Z.eq_dec i 0).
    + subst i. autorewrite with sublist. now simpl.
    + rewrite !Zlength_cons in *. repeat rewrite sublist_cons.
      * simpl. rewrite sublist_cons'.
        -- f_equal. apply IHl1; lia.
        -- rewrite Zlength_cons. rewrite combine_same_length; lia.
      * rewrite Zlength_cons. lia.
      * rewrite Zlength_cons. lia.
Qed.

Lemma combine_upd_Znth:
  forall (l1 l2: list Z) i new,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (upd_Znth i l1 new) l2 =
    upd_Znth i (combine l1 l2) (new , Znth i l2).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l2) l2) at 1 by reflexivity.
  repeat rewrite (sublist_split 0 i (Zlength l2) l2) by lia.
  rewrite !upd_Znth_unfold; auto. 2: now rewrite combine_same_length.
  rewrite combine_app.
  2: { repeat rewrite <- ZtoNat_Zlength.
       f_equal. repeat rewrite Zlength_sublist; lia. }
  f_equal.
  1: apply combine_sublist_specific; assumption.
  rewrite (sublist_split i (i+1) (Zlength l2) l2) by lia.
  rewrite sublist_len_1 by lia. simpl.
  simpl combine. f_equal.
  apply combine_sublist_gen. lia. lia.
Qed.

Lemma Znth_combine:
  forall (l1 l2 : list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros. generalize dependent i.
  generalize dependent l2.
  induction l1.
  - intros. rewrite Zlength_nil in H0; exfalso; lia.
  - intros.
    rewrite <- (sublist_same 0 (Zlength l2) l2) by lia.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by lia.
    rewrite sublist_len_1 by lia.
    simpl. destruct (Z.eq_dec i 0).
    1: subst i; repeat rewrite Znth_0_cons; reflexivity.
    repeat rewrite Znth_pos_cons by lia.
    apply IHl1.
    rewrite Zlength_sublist by lia.
    rewrite Zlength_cons in H; rep_lia.
    rewrite Zlength_cons in H0; rep_lia.
Qed.

Lemma behead_list:
  forall (l: list Z),
    0 < Zlength l -> l = Znth 0 l :: tl l.
Proof.
  intros. destruct l.
  - rewrite Zlength_nil in H. inversion H.
  - simpl. rewrite Znth_0_cons. reflexivity.
Qed.

Lemma nat_inc_list_hd:
  forall n,
    0 < n ->
    Znth 0 (nat_inc_list (Z.to_nat n)) = 0.
Proof.
  intros. induction (Z.to_nat n); trivial.
  simpl. destruct n0; trivial.
  rewrite app_Znth1; [lia|].
  rewrite nat_inc_list_Zlength.
  rewrite <- Nat2Z.inj_0.
  apply inj_lt; lia.
Qed.

Lemma tl_app:
  forall (l1 l2: list Z),
    0 < Zlength l1 ->
    tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
  intros. destruct l1; trivial. inversion H.
Qed.

Lemma in_tl_nat_inc_list:
  forall i n,
    In i (tl (nat_inc_list n)) -> 1 <= i.
Proof.
  destruct n. inversion 1.
  induction n. inversion 1.
  intros. simpl in H.
  rewrite Zpos_P_of_succ_nat in H.
  rewrite tl_app in H.
  2: { rewrite Zlength_app.
       replace (Zlength [Z.of_nat n]) with 1 by reflexivity.
       rep_lia.
  }
  apply in_app_or in H; destruct H.
  - apply IHn. simpl. assumption.
  - simpl in H. destruct H; lia.
Qed.

Lemma nat_inc_list_app:
  forall n m p i,
    0 <= i < m ->
    0 <= n ->
    n + m <= p ->
    Znth i (nat_inc_list (Z.to_nat m)) =
    Znth i (sublist n (n + m)
                    (nat_inc_list (Z.to_nat p))) - n.
Proof.
  symmetry. rewrite Znth_sublist by rep_lia.
  repeat rewrite nat_inc_list_i by rep_lia. lia.
Qed.

Lemma nat_inc_list_sublist:
  forall n m,
    0 <= n ->
    n <= m ->
    sublist 0 n (nat_inc_list (Z.to_nat m)) =
    nat_inc_list (Z.to_nat n).
Proof.
  intros.
  apply Zle_lt_or_eq in H0. destruct H0.
  2: { subst. rewrite sublist_same; trivial.
       rewrite nat_inc_list_Zlength; lia.
  }
  apply Znth_eq_ext.
  1: { rewrite Zlength_sublist;
       try rewrite nat_inc_list_Zlength; lia.
  }
  intros. rewrite nat_inc_list_i.
  2: { rewrite Zlength_sublist in H1; 
       try rewrite nat_inc_list_Zlength; lia.
  }
  rewrite <- Z.sub_0_r at 1.
  replace n with (0 + n) by lia.
  rewrite Zlength_sublist in H1.
  rewrite <- nat_inc_list_app.
  rewrite nat_inc_list_i.
  all: try rewrite nat_inc_list_Zlength; lia.
Qed.

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
    dijkstra_correct g src popped prev dist ->
    In mom popped ->
    Znth mom dist < inf ->
    vvalid g mom ->
    exists p2mom : path,
      path_correct g prev dist src mom p2mom /\
      (forall step : Z,
          In_path g step p2mom ->
          In step popped /\
          Znth step dist < inf) /\
      path_globally_optimal g src mom p2mom.
Proof.
  intros.
  destruct (H _ H2) as [? _].
  specialize (H3 H0).
  destruct H3; [ulia|].
  apply H3; trivial.
Qed.
                  
Lemma path_leaving_popped:
  forall (g: DijkGG) links s u popped,
    valid_path g (s, links) ->
    path_ends g (s, links) s u ->
    In s popped ->
    ~ In u popped ->
    exists (p1 : path) (mom' child' : Z) (p2 : path),
      path_glue p1 (path_glue (mom', [(mom', child')]) p2) = (s, links) /\
      valid_path g p1 /\
      valid_path g p2 /\
      path_ends g p1 s mom' /\
      path_ends g p2 child' u /\
      In mom' popped /\
      ~ In child' popped /\
      evalid g (mom', child').
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
      destruct IHlinks as [p2m [m [c [p2u [? [? [? [? [? [? [? ?]]]]]]]]]]].
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

      split3; [| |split3; [| | split3; [| |split]]]; trivial.
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
    + clear IHlinks. 
      exists (s, []), s, t, (t, links).
      assert (evalid g (s,t)). {
        rewrite H5 in H3; trivial.
      }

      split3; [| |split3; [| | split3; [| |split]]]; trivial.
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
  forall (g: DijkGG) a b,
    path_ends g (a, [(a, b)]) a b.
Proof.
  intros. split; trivial.
  simpl. rewrite (edge_dst_snd g); trivial.
Qed. 

Lemma path_leaving_popped_stronger:
  forall (g: DijkGG) links s u popped,
    valid_path g (s, links) ->
    path_ends g (s, links) s u ->
    In s popped ->
    ~ In u popped ->
    path_cost g (s, links) < inf ->
    exists (p1 : path) (mom' child' : Z) (p2 : path),
      path_glue p1 (path_glue (mom', [(mom', child')]) p2) = (s, links) /\
      valid_path g p1 /\
      valid_path g p2 /\
      path_ends g p1 s mom' /\
      path_ends g p2 child' u /\
      In mom' popped /\
      ~ In child' popped /\
      strong_evalid g (mom', child') /\
      path_cost g p1 < inf /\
      0 <= elabel g (mom', child') < inf /\
      path_cost g p2 + elabel g (mom', child') < inf.
Proof.
  intros.
  destruct (path_leaving_popped g links s u popped H H0 H1 H2)
        as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? ? ]]]]]]]]]]].
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
        apply Z.le_lt_trans with (m := Int.max_signed / SIZE).
        apply valid_edge_bounds; trivial.
        rewrite inf_eq. compute; trivial.
      }
      
      split3; [| |split3; [| |split3; [| |split3; [| |split3]]]]; trivial.
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
Qed.

Lemma evalid_dijk:
  forall (g: DijkGG) a b cost,
    cost = elabel g (a,b) ->
    0 <= cost <= Int.max_signed / SIZE ->
    evalid g (a,b).
Proof.
  intros.
  rewrite (evalid_meaning g); split.
  1: apply edge_representable.
  apply not_eq_sym, Zaux.Zgt_not_eq.
  destruct H0.
  apply Z.le_lt_trans with (m := Int.max_signed / SIZE);
    trivial.
  rewrite H in H1; trivial.
  rewrite inf_eq. compute; trivial.
Qed.

Lemma inv_popped_add_u_dst_neq_u:
  forall (g: DijkGG) src dst u popped prev dist,
    dijkstra_correct g src popped prev dist ->
    vvalid g dst ->
    dst <> u ->
    inv_popped g src (u :: popped) prev dist dst.
Proof.
  intros. intro. simpl in H2; destruct H2; [lia|].
  destruct (H _ H0) as [? _].
  specialize (H3 H2); destruct H3 as [[? ?]|[? [? [? ?]]]];
         [left | right]; trivial.
  - split; trivial.
    intros. destruct (H4 _ H5).
    destruct (Z.eq_dec m u); [subst m|];
      split; trivial; intro;
        apply not_in_cons in H8; destruct H8 as [_ ?];
          apply H7; trivial.
  - exists x; split3; trivial.
    unfold path_in_popped. intros.
    destruct (H4 _ H6); split; [simpl; right|]; trivial.
Qed.

Lemma inv_popped_add_src:
  forall (g: DijkGG) src popped prev dist,
    dijkstra_correct g src popped prev dist ->
    vvalid g src ->
    Znth src dist = 0 ->
    inv_popped g src (src :: popped) prev dist src.
Proof.
  intros. right.
  exists (src, []); split3; trivial.
  - split3; [| | split3]; trivial.
    + split; trivial.
    + split; trivial.
    + rewrite Forall_forall; intros; simpl in H3; lia.
  - unfold path_in_popped. intros. destruct H3 as [? | [? [? _]]].
    + simpl in H3. unfold V, E in *.
      rewrite H3, H1; split; trivial.
      rewrite inf_eq; compute; trivial.
    + simpl in H3; lia.
  - unfold path_globally_optimal; intros.
    unfold path_cost at 1; simpl.
    apply path_cost_pos; trivial.
Qed.  

Lemma path_correct_app_cons:
  forall (g: DijkGG) src u mom p2mom prev dist,
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
  - apply valid_path_app_cons; trivial; try rewrite <- surjective_pairing; trivial.
  - apply path_ends_app_cons with (a' := src); trivial.
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
  forall (g: DijkGG) step p2a src a b,
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
  forall (g: DijkGG) src dst popped prev priq dist,
 let u :=
      find priq (fold_right Z.min (hd 0 priq) priq) 0 in
    dijkstra_correct g src popped prev dist ->
    Znth src dist = 0 ->
    (forall dst : Z,
        vvalid g dst ->
        ~ In dst popped -> Znth dst priq = Znth dst dist) ->
    inrange_dist dist ->
    Zlength priq = SIZE ->
    Zlength dist = SIZE ->
    ~ In u popped ->
    vvalid g u ->
    Znth u dist < inf ->
    vvalid g dst ->
    inv_popped g src (u :: popped) prev dist dst.
Proof.
  intros.
  destruct (Z.eq_dec dst u).
  (* the easy case where dst is old, and not the new u *)
  2: apply inv_popped_add_u_dst_neq_u; trivial.

  (* now we must show that u is a valid entrant *)
  subst dst. clear H8.
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
  1: pose proof (edge_cost_pos g (mom, u)); ulia.

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
    + destruct (H15 _ H18).
      split; trivial.
      simpl. right; trivial.
    + subst step. split; simpl; [left|]; trivial.

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
      as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]; trivial.
    clear Htemp.

    (* We will clean up the goal later *)
    replace (path_cost g (src, links)) with
        (path_cost g p1 +
         elabel g (mom', child') +
         path_cost g p2).
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
    1: {
      destruct (H39 u); trivial.
      specialize (H41 H5). ulia.
    }
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
      apply (Forall_Znth _ _ mom') in H2; [|ulia].
      apply H2. }

    assert (Htemp: 0 <= child' < Zlength dist). {
      apply (vvalid_meaning g) in H36; trivial; lia.
    }
    
    destruct (Znth_dist_cases child' dist); trivial; clear Htemp.
    + (* dist[child'] = inf. This is impossible *)
      exfalso.
      destruct (H _ H36) as [_ [_ ?]].
      specialize (H45 H30 H44 mom' H35 H29). ulia.
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
             apply (vvalid_meaning g) in H36; trivial; lia.
        }
        apply min_in_list.
        1: apply incl_refl.
        rewrite <- Znth_0_hd; [apply Znth_In|];
          rewrite H3; unfold SIZE; lia.
Qed.

(*
Lemma get_popped_empty:
  forall l,
    Forall (fun x => x <> inf + 1) l ->
    get_popped l = [].
Proof.
  intros. unfold get_popped.
  replace (filter (fun x : Z * Z => (fst x) =? (inf + 1))
                  (combine l (nat_inc_list (Z.to_nat (Zlength l)))))
    with (@nil (Z*Z)).
  trivial. symmetry.
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2.
  clear Heql2.
  generalize dependent l2. induction l; trivial.
  intros. simpl. destruct l2; trivial. simpl.
  pose proof (Forall_inv H). pose proof (Forall_tl _ _ _ H).
  simpl in H0. destruct (a =? inf + 1) eqn:?.
  1: rewrite Z.eqb_eq in Heqb; lia.
  apply IHl; assumption.
Qed.

Lemma get_popped_unchanged:
  forall l new i,
    0 <= i < Zlength l ->
    new <> inf + 1 ->
    Znth i l <> inf + 1 ->
    get_popped (upd_Znth i l new) = get_popped l.
Proof.
  intros. unfold get_popped.
  remember (fun x : Z * Z => fst x =? inf + 1) as F.
  rewrite upd_Znth_Zlength by lia.
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2.
  assert (Zlength l = Zlength l2). {
    rewrite Heql2. rewrite nat_inc_list_Zlength; lia.
  }
  f_equal. pose proof (combine_same_length l l2 H2).
  rewrite combine_upd_Znth by assumption.
  unfold_upd_Znth_old.
  rewrite <- (sublist_same 0 (Zlength (combine l l2)) (combine l l2))
          at 4 by reflexivity.
  rewrite (sublist_split 0 i (Zlength (combine l l2))
                         (combine l l2)) by lia.
  do 2 rewrite filter_app.
  f_equal. rewrite H3.
  rewrite (sublist_split i (i+1) (Zlength l)) by lia.
  rewrite (sublist_one i (i+1) (combine l l2)) by lia.
  rewrite filter_app. f_equal. simpl.
  destruct (F (new, Znth i l2)) eqn:?; rewrite HeqF in Heqb; simpl in Heqb.
  - exfalso. apply H1. rewrite <- inf_eq.
    simpl. rewrite Z.eqb_eq in Heqb. rewrite <- inf_eq in *. lia.
  - destruct (F (Znth i (combine l l2))) eqn:?; trivial.
    rewrite HeqF, Znth_combine, Z.eqb_eq in Heqb0 by lia.
    simpl in Heqb0. exfalso. apply H1. rewrite <- inf_eq. lia.
Qed.

Lemma in_get_popped:
  forall i l1 l2,
    0 <= i < Zlength l1 + Zlength l2 ->
    Zlength l1 <= i  ->
    In i (get_popped (l1 ++ l2)) <-> In (i - Zlength l1) (get_popped l2).
Proof.
  intros.
  split; unfold get_popped; intros.
  - rewrite In_map_snd_iff in H1; destruct H1.
    rewrite filter_In in H1; destruct H1; simpl in H2.
    rewrite In_map_snd_iff.
    exists x.
    rewrite filter_In; split; trivial. clear H2.
    rewrite <-
            (sublist_same 0 (Zlength (l1 ++ l2))
                          (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))) in H1.
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))) in H1.
    5,3: rewrite (Zlength_correct (nat_inc_list (Z.to_nat
                                                   (Zlength (l1 ++ l2)))));
      rewrite nat_inc_list_length;
      rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.
    all: try rep_lia.
    rewrite combine_app in H1.
    2: { rewrite Zlength_correct.
         repeat rewrite <- ZtoNat_Zlength.
         f_equal.
         pose proof (Zlength_nonneg l1).
         rewrite Zlength_sublist.
         all: rewrite Z2Nat.id.
         all: try lia.
         rewrite Zlength_app.
         rewrite nat_inc_list_Zlength.
         rewrite Z2Nat.id by lia. lia.
    }
    apply in_app_or in H1. destruct H1.
    + exfalso.
      pose proof (in_combine_r _ _ _ _ H1).
      clear H1.
      rewrite nat_inc_list_sublist in H2.
      2: apply Zlength_nonneg.
      2: rewrite Zlength_app; lia.
      apply nat_inc_list_in_iff in H2.
      rewrite Z2Nat.id in H2 by (apply Zlength_nonneg). lia.
    + apply In_Znth_iff in H1. destruct H1 as [? [? ?]].
      rewrite In_Znth_iff. exists x0.
      split.
      * rewrite combine_same_length in *; trivial.
        rewrite Zlength_sublist.
        rewrite Zlength_app. lia.
        rewrite Zlength_app. rep_lia.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
      * rewrite Znth_combine in *; trivial.
        2: {
          rewrite Zlength_sublist.
          rewrite Zlength_app. lia.
          rewrite Zlength_app. rep_lia.
          rewrite nat_inc_list_Zlength.
          rewrite Z2Nat.id. reflexivity. rep_lia.
        }
        2, 4: rewrite combine_same_length in H1; trivial.
        2, 3: rewrite Zlength_sublist, Zlength_app; [|rewrite Zlength_app|]; try rep_lia;
          repeat rewrite Zlength_correct;
          rewrite nat_inc_list_length;
          rewrite Nat2Z.id; lia.
        2: repeat rewrite nat_inc_list_Zlength; rep_lia.
        inversion H2.
        rewrite Zlength_app.
        rewrite <- nat_inc_list_app; trivial.
        rewrite combine_same_length in H1. lia.
        rewrite Zlength_sublist. rewrite Zlength_app. lia.
        rewrite Zlength_app. rep_lia.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id; trivial. reflexivity.
        rep_lia. rep_lia. reflexivity.
  - rewrite In_map_snd_iff in H1; destruct H1.
    rewrite filter_In in H1; destruct H1; simpl in H2.
    rewrite In_map_snd_iff. exists x.
    rewrite filter_In; split; trivial. clear H2.
    rewrite <-
            (sublist_same 0 (Zlength (l1 ++ l2))
                          (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))).
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))).
    5,3: rewrite (Zlength_correct
                    (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2)))));
      rewrite nat_inc_list_length;
      rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.
    all: try rep_lia.
    rewrite combine_app.
    2: { repeat rewrite <- ZtoNat_Zlength. f_equal.
         rewrite Zlength_sublist. lia.
         pose proof (Zlength_nonneg l1); lia.
         rewrite Zlength_app.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id; lia.
    }
    rewrite in_app_iff. right.
    rewrite In_Znth_iff in H1; destruct H1 as [? [? ?]].
    rewrite In_Znth_iff.
    exists x0. split.
    1: { rewrite combine_same_length in *.
         assumption.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id. reflexivity.
         lia.
         rewrite Zlength_sublist.
         rewrite Zlength_app. lia.
         rewrite Zlength_app.
         pose proof (Zlength_nonneg l2).
         rep_lia.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id. reflexivity.
         lia.
    }
    rewrite Znth_combine in *.
    2: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; lia.
    3: rewrite Zlength_sublist, Zlength_app;
      [|rewrite Zlength_app|]; try rep_lia;
      repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; lia.
    2, 3: rewrite combine_same_length in H1; [rep_lia|].
    2, 3: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; lia.
    inversion H2.
    rewrite (nat_inc_list_app (Zlength l1) _ (Zlength (l1 ++ l2))) in H5.
    rewrite Z.sub_cancel_r in H5.
    rewrite Zlength_app at 1.
    rewrite H5. reflexivity.
    rewrite combine_same_length in H1. lia.
    repeat rewrite Zlength_correct.
    rewrite nat_inc_list_length.
    rewrite Z2Nat.id. reflexivity.
    lia. rep_lia.
    rewrite Zlength_app. rep_lia.
Qed.
 *)

(* The above can be deleted, but I'm keeping them until my new PQ comes in *)

Lemma get_popped_meaning:
  forall popped priq i,
    0 <= i < Zlength priq ->
    In i popped <-> Znth i priq = inf + 1.
Admitted.

Definition dijk_setup_loop_inv g sh src dist prev v_pq arr :=
  EX i : Z,
  PROP ()
  LOCAL (temp _dist (pointer_val_val dist);
        temp _prev (pointer_val_val prev);
        temp _src (Vint (Int.repr src));
        lvar _pq (tarray tint SIZE) v_pq;
        temp _graph (pointer_val_val arr))
  SEP (data_at Tsh
               (tarray tint SIZE)
               ((list_repeat (Z.to_nat i)
                             (Vint (Int.repr inf)))
                  ++ (list_repeat (Z.to_nat (SIZE-i))
                                  Vundef)) v_pq;
      data_at Tsh
              (tarray tint SIZE)
              ((list_repeat (Z.to_nat i)
                            (Vint (Int.repr inf)))
                 ++ (list_repeat (Z.to_nat (SIZE-i))
                                 Vundef)) (pointer_val_val prev);
      data_at Tsh
              (tarray tint SIZE)
              ((list_repeat (Z.to_nat i) (Vint (Int.repr inf)))
                 ++ (list_repeat (Z.to_nat (SIZE-i))
                                 Vundef)) (pointer_val_val dist);
      DijkGraph sh CompSpecs g (pointer_val_val arr)).

Definition dijk_forloop_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr :=
  EX prev : list V,
  EX priq : list V,
  EX dist : list V,
  EX popped : list V,
  PROP (
      (* The overall correctness condition *)
      dijkstra_correct g src popped prev dist;
    
      (* Some special facts about src *)
      Znth src dist = 0;
      Znth src prev = src;
    
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
        lvar _pq (tarray tint SIZE) priq_ptr;
        temp _graph (pointer_val_val graph_ptr))
  SEP (data_at Tsh
               (tarray tint SIZE)
               (map Vint (map Int.repr prev))
               (pointer_val_val prev_ptr);
      data_at Tsh
              (tarray tint SIZE)
              (map Vint (map Int.repr priq)) priq_ptr;
      data_at Tsh
              (tarray tint SIZE)
              (map Vint (map Int.repr dist))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr)).

Definition dijk_forloop_break_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr :=
  EX prev: list V,
  EX priq: list V,
  EX dist: list V,
  EX popped: list V,
  PROP (
      (* This fact comes from breaking while *)
      Forall (fun x => x >= inf) priq;
      (* And the correctness condition is established *)
      dijkstra_correct g src popped prev dist)
  LOCAL (lvar _pq (tarray tint SIZE) priq_ptr)
  SEP (data_at Tsh
               (tarray tint SIZE)
               (map Vint (map Int.repr prev))
               (pointer_val_val prev_ptr);
      (data_at Tsh
               (tarray tint SIZE)
               (map Vint (map Int.repr priq)) priq_ptr);
      data_at Tsh
              (tarray tint SIZE)
              (map Vint (map Int.repr dist))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr)).

Definition dijk_inner_forloop_inv (g: DijkGG) sh src priq dist_ptr prev_ptr priq_ptr graph_ptr :=
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
        inv_popped g src popped' prev' dist' dst;
    
    (* and, because we broke out when dist[u] = inf,
       we know that none of the popped items have dist inf.
       Essentially, the first disjunct of inv_popped
       is impossible inside the for loop.
     *)
    forall dst,
      vvalid g dst ->
      In dst popped' ->
      Znth dst dist' <> inf;
    
    (* inv_unpopped is restored for those vertices
       that the for loop has scanned and repaired *)
    forall dst,
      0 <= dst < i ->
      inv_unpopped g src popped' prev' dist' dst;
    
    (* a weaker version of inv_popped is
       true for those vertices that the
       for loop has not yet scanned *)
    forall dst,
      i <= dst < SIZE ->
      inv_unpopped_weak g src popped' prev' dist' dst u;
    
    (* similarly for inv_unseen,
       the invariant has been
       restored until i:
       u has been taken into account *)
    forall dst,
      0 <= dst < i ->
      inv_unseen g popped' dist' dst;
    
    (* and a weaker version of inv_unseen is
       true for those vertices that the
       for loop has not yet scanned *)
    forall dst,
      i <= dst < SIZE ->
      inv_unseen_weak g popped' dist' dst u;
    (* further, some useful facts about src... *)
    Znth src dist' = 0;
    Znth src prev' = src;
    (* Znth src priq' <> inf; *)
    
    (* a useful fact about u *)
    In u popped';
    
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
        lvar _pq (tarray tint SIZE) priq_ptr;
        temp _graph (pointer_val_val graph_ptr))
  SEP (data_at Tsh
               (tarray tint SIZE)
               (map Vint (map Int.repr prev'))
               (pointer_val_val prev_ptr);
      data_at Tsh
              (tarray tint SIZE)
              (map Vint (map Int.repr priq')) priq_ptr;
      data_at Tsh
              (tarray tint SIZE)
              (map Vint (map Int.repr dist'))
              (pointer_val_val dist_ptr);
      DijkGraph sh CompSpecs g (pointer_val_val graph_ptr)).

Lemma inv_unpopped_weak_add_unpopped:
  forall (g: DijkGG) prev dist popped src u dst,
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
    intro. rewrite <- H11 in H7. 
    apply Zlt_not_le in H7.
    apply H7; reflexivity.
  }
  
  assert (Znth mom dist < inf) by
      (pose proof (valid_edge_bounds g _ H11); ulia).
  
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
  forall (g : DijkGG) prev dist popped src u dst,
    dijkstra_correct g src popped prev dist ->
    ~ In u popped ->
    vvalid g dst ->
    inv_unseen_weak g (u :: popped) dist dst u.
Proof.
  intros.
  unfold inv_unseen_weak. intros.
  assert (e: dst <> u) by (simpl in H2; lia).
  apply not_in_cons in H2; destruct H2 as [_ ?].
  destruct (H dst H1) as [_ [_ ?]].
  apply H7; trivial.
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
    0 <= src < SIZE ->
    dijkstra_correct g src [] (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) src)
                     (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
Proof.
  intros.
  unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen;
    split3; intros; [inversion H1 | left | inversion H4].
  destruct (Z.eq_dec dst src); [trivial | exfalso].
  apply (vvalid_meaning g) in H0. 
  rewrite upd_Znth_diff in H2; trivial.
  rewrite Znth_list_repeat_inrange in H2; ulia.
Qed.

Lemma In_links_snd_In_path:
  forall (g: DijkGG) step path,
    In step (snd path) ->
    In_path g (snd step) path.
Proof.
  intros. unfold In_path. right.
  exists step. split; trivial.
  right. rewrite (edge_dst_snd g); trivial.
Qed.

Lemma In_links_fst_In_path:
  forall (g: DijkGG) step path,
    In step (snd path) ->
    In_path g (fst step) path.
Proof.
  intros. unfold In_path. right.
  exists step. split; trivial.
  left. rewrite (edge_src_fst g); trivial.
Qed.
  
Lemma inv_popped_newcost:
  forall (g: DijkGG) src dst u i newcost popped prev dist,
    vvalid g i ->
    vvalid g dst ->
    (forall dst : Z,
        vvalid g dst ->
        inv_popped g src popped prev dist dst) ->
    (forall dst : Z,
        vvalid g dst ->
        In dst popped ->
        Znth dst dist <> inf) ->
    Zlength prev = SIZE ->
    Zlength dist = SIZE ->
    ~ In i popped ->
    inv_popped g src popped
               (upd_Znth i prev u)
               (upd_Znth i dist newcost) dst.
Proof.
  intros.
  unfold inv_popped; intros.
  assert (n: dst <> i). {
    intro. subst dst. apply H5; trivial.
  }
  assert (0 <= dst < SIZE). {
  apply (vvalid_meaning g) in H0; ulia.
  }
  assert (0 <= i < SIZE). {
    apply (vvalid_meaning g) in H; ulia.
  }
  repeat rewrite upd_Znth_diff; try ulia.
  destruct (H1 dst H0 H6)
    as [[? ?] | [p2dst [? [? ?]]]]; [exfalso | right].
  1: specialize (H2 _ H0 H6); ulia.
  exists p2dst. split3; trivial.
  - destruct H9 as [? [? [? [? ?]]]].
    split3; [| | split3]; trivial.
    1: rewrite upd_Znth_diff; ulia.
    rewrite Forall_forall; intros.
    pose proof (In_links_snd_In_path g _ _ H16).
    specialize (H10 _ H17). destruct H10.
    rewrite Forall_forall in H15. specialize (H15 _ H16).
    assert (snd x <> i). {
      intro contra. unfold V in *.
      rewrite contra in *. apply H5; ulia.
    }
    unfold V in *.
    rewrite upd_Znth_diff; try lia.
    rewrite H3, <- (vvalid_meaning g); trivial.
    apply (valid_path_valid _ p2dst); trivial.
  - unfold path_in_popped. intros.
    specialize (H10 _ H12). destruct H10.
    assert (step <> i). {
      intro contra. subst step. apply H5; ulia.
    }
    split; trivial. unfold V in *.
    rewrite upd_Znth_diff; trivial; [|ulia].
    rewrite H4, <- (vvalid_meaning g); trivial.
    destruct H9. apply (valid_path_valid _ p2dst); trivial.
Qed.

Lemma inv_unpopped_newcost_dst_neq_i:
  forall (g: DijkGG) src dst u i newcost prev dist popped,
    (forall dst : Z,
        0 <= dst < i ->
        inv_unpopped g src popped prev dist dst) ->
    vvalid g i ->
    Zlength prev = SIZE ->
    Zlength dist = SIZE ->
    ~ In i popped ->
    0 <= dst < i + 1 ->
    dst <> i ->
    inv_unpopped g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
Proof.
  intros. 
  assert (0 <= dst < i) by lia.
  (* We will proceed using the old best-known path for dst *)
  assert (0 <= i < SIZE) by now apply (vvalid_meaning g).
  unfold inv_unpopped. intros.
  rewrite upd_Znth_diff in * by ulia.
  destruct (H _ H6 H8) as
      [? | [? [? [? [? [? [? ?]]]]]]]; trivial;
    [left | right]; trivial.
  unfold V in *.
  remember (Znth dst prev) as mom. 
  split; trivial.
  assert (Znth mom dist < inf). {
    pose proof (edge_cost_pos g (mom, dst)); ulia.
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
  forall (g: DijkGG) src dst u i
         dist prev priq popped newcost,
    (forall dst : Z,
        vvalid g dst ->
        inv_popped g src popped prev dist dst) ->
    (forall dst : Z,
        0 <= dst < i ->
        inv_unpopped g src popped prev dist dst) ->
    (forall dst : Z,
        i <= dst < SIZE ->
        inv_unpopped_weak g src popped prev dist dst u) ->
    (forall dst : Z,
        i <= dst < SIZE ->
        inv_unseen_weak g popped dist dst u) ->
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
    Zlength prev = SIZE ->
    Zlength dist = SIZE ->
    0 <= Znth u dist <= inf ->
    0 <= elabel g (u, i) <= Int.max_signed / SIZE ->
    0 <= Znth i dist <= inf ->
    newcost < Znth i dist ->
    ~ In i popped ->
    Znth i priq = inf \/ Znth i priq < inf ->
    0 <= dst < i + 1 ->
    inv_unpopped g src popped (upd_Znth i prev u) (upd_Znth i dist newcost) dst.
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
  destruct (H_inv_popped _ H H2) as [[? ?] | ?].
  1: ulia.
  unfold V in *.
  assert (0 <= i < SIZE) by now apply (vvalid_meaning g).
  assert (0 <= u < SIZE) by now apply (vvalid_meaning g).
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
      [? | [p2mom' [[? [? [? [? ?]]]] [? ?]]]]; [ulia|].
  pose proof (path_ends_In_path_dst _ _ _ _ H22).
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
      assert (i <= i < SIZE) by lia.
      rewrite H_priq_dist_link in H11; trivial.
      pose proof (H_inv_unseen_weak _ H29 H10 H11 mom' H17 H18 n0).
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
      assert (i <= i < SIZE) by lia.
      assert (0 <= mom' < SIZE). {
        apply (vvalid_meaning g); ulia.
      }
      rewrite H_priq_dist_link in H11; trivial.
      destruct (H_inv_unpopped_weak _ H29 H10 H11).
      1: lia.
      destruct H31 as [_ [_ ?]]. apply H31; trivial.
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
      assert (i <= i < SIZE) by lia.
      rewrite H_priq_dist_link in H11; trivial.
      pose proof (H_inv_unseen_weak _ H30 H10 H11 mom' H17 H18 H29).
      ulia.
    }
    assert (i <= i < SIZE) by lia.
    rewrite H_priq_dist_link in H11; trivial.
    destruct (H_inv_unpopped_weak i H30 H10 H11).
    1: subst i; exfalso; lia.
    apply Z.lt_le_incl.
    apply Z.lt_le_trans with (m:=Znth i dist).
    1: lia.
    destruct H31 as [_ [_ ?]]. apply H31; trivial.
Qed.

Lemma inv_unpopped_weak_newcost:
  forall (g: DijkGG) src dst u i prev dist popped newcost,
    (forall dst : Z,
        i <= dst < SIZE ->
        inv_unpopped_weak g src popped prev dist dst u) ->
    vvalid g i ->
    Zlength prev = SIZE ->
    Zlength dist = SIZE ->
    ~ In i popped ->
    i + 1 <= dst < SIZE ->
    inv_unpopped_weak g src popped
                      (upd_Znth i prev u)
                      (upd_Znth i dist newcost)
                      dst u.
Proof.
  intros ? ? ? ? ? ? ? ? ? H_inv_unpopped_weak. intros.
  assert (0 <= i < SIZE) by now apply (vvalid_meaning g).
  unfold inv_unpopped_weak. intros.
  assert (i <= dst < SIZE) by lia.
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
  assert (0 <= mom < SIZE) by now apply (vvalid_meaning g).
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
  forall (g: DijkGG) dst i dist popped newcost,
    (forall dst : Z,
        0 <= dst < i ->
        inv_unseen g popped dist dst) ->
    vvalid g i ->
    Zlength dist = SIZE ->
    ~ In i popped ->
    0 <= dst < i + 1->
    newcost < inf ->
    inv_unseen g popped (upd_Znth i dist newcost) dst.
Proof.
  intros ? ? ? ? ? ? H_inv_unseen. intros.
  rewrite (vvalid_meaning g i) in H.
  unfold inv_unseen; intros.
  assert (dst <> i). {
    intro. subst dst. rewrite upd_Znth_same in H5; lia.
  }
  assert (0 <= dst < i) by lia.
  rewrite upd_Znth_diff in H5 |- *; try ulia.
  1: apply H_inv_unseen; ulia.
  1: apply (vvalid_meaning g) in H6; ulia.
  intro contra. subst m.
  apply H1; trivial.
Qed.

Lemma inv_unseen_weak_newcost:
  forall (g: DijkGG) dst u i dist popped newcost,
    (forall dst : Z,
        i <= dst < SIZE ->
        inv_unseen_weak g popped dist dst u) ->
    vvalid g i ->
    Zlength dist = SIZE ->
    ~ In i popped ->
    i + 1 <= dst < SIZE ->
    dst <> i ->
    inv_unseen_weak g popped (upd_Znth i dist newcost) dst u.
Proof.
  intros.
  unfold inv_unseen_weak; intros.
  unfold V in *.
  apply (vvalid_meaning g) in H0.
  rewrite upd_Znth_diff in H6 by ulia.
  repeat rewrite upd_Znth_diff by lia.
  assert (i <= dst < SIZE) by lia.
  destruct (Z.eq_dec m i).
  1: exfalso; subst m; apply H2; trivial. 
  rewrite upd_Znth_diff; trivial.
  - apply H; trivial.
  - apply (vvalid_meaning g) in H7; ulia.
  - lia.
Qed.

(** PROOF BEGINS **)

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function.
  rename v_pq into priq_ptr.
  forward_for_simple_bound
    SIZE
    (dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr).
  - unfold SIZE. rep_lia.
  - unfold data_at, data_at_, field_at_, SIZE; entailer!.
  - forward. forward.
    forward_call (priq_ptr, i, inf,
                  (list_repeat (Z.to_nat i)
                               (Vint (Int.repr inf)) ++
                               list_repeat (Z.to_nat (SIZE - i)) Vundef)).
    1: split; trivial;
      rewrite inf_eq; compute; split; inversion 1.
    rewrite inf_eq2, upd_Znth_list_repeat; [|lia].
    entailer!.
  - (* At this point we are done with the
       first for loop. The arrays are all set to INF. *)
    replace (SIZE - SIZE) with 0 by lia;
      rewrite list_repeat_0, <- (app_nil_end).
    forward. forward. 
    forward_call (priq_ptr, src, 0, (list_repeat (Z.to_nat SIZE) (inf: V))).
    1: split; trivial; compute; split; inversion 1.
   
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
    (dijk_forloop_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr)
    break: (dijk_forloop_break_inv g sh src dist_ptr prev_ptr priq_ptr graph_ptr).
    + unfold dijk_forloop_inv.
      Exists (upd_Znth src (@list_repeat V (Z.to_nat SIZE) inf) src).
      Exists (upd_Znth src (@list_repeat V (Z.to_nat SIZE) inf) 0).
      Exists (upd_Znth src (@list_repeat V (Z.to_nat SIZE) inf) 0).
      Exists (@nil V).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat SIZE) inf) = SIZE). {
        rewrite Zlength_list_repeat; [|unfold SIZE]; lia.
      }
      split.
      (* dijkstra_correct for the initial arrays *)
      1: apply (dijkstra_correct_nothing_popped g src); trivial.
      split3; [| |split3].
        1,2: rewrite upd_Znth_same; trivial.
        all: red; apply Forall_upd_Znth;
          try apply Forall_list_repeat;
          try rewrite inf_eq; trilia.
        
    + (* Now the body of the while loop begins. *)
      unfold dijk_forloop_inv.
      Intros prev priq dist popped.
      assert_PROP (Zlength priq = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength prev = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength dist = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }

      assert (H_inrange_priq_trans: forall priq,
                 inrange_priq priq ->
                 priq_arr_utils.inrange_priq priq). {
        intros.
        red in H11 |- *.
        rewrite Forall_forall in H11 |- *.
        intros ? H_in. specialize (H11 _ H_in). rep_lia.
      }
      forward_call (priq_ptr, priq).
      forward_if. (* checking if it's time to break *)
      * (* No, don't break. *)
        rename H11 into Htemp.
        assert (isEmpty priq = Vzero). {
          destruct (isEmptyTwoCases priq);
            rewrite H11 in Htemp; simpl in Htemp;
              now inversion Htemp.
        }
        clear Htemp.
        forward_call (priq_ptr, priq).
        Intros u.
        rename H12 into Hequ.
        (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

        (* We prove a few useful facts about u: *)
        assert (H_u_valid: vvalid g u). {
          apply (vvalid_meaning g); trivial.
          subst u.
          replace SIZE with (Zlength priq).
          apply find_range.
          apply min_in_list. apply incl_refl.
          destruct priq. rewrite Zlength_nil in H8.
          inversion H8. simpl. left; trivial.
        }
        
        assert (0 <= u < SIZE). {
          apply (vvalid_meaning g) in H_u_valid; trivial.
        } 

        (* todo: prove without get_popped_meaning *)
        assert (~ (In u popped)). {
          intro.
          rewrite (get_popped_meaning _ priq _) in H13.
          2: ulia.
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
          split; rewrite inf_eq; compute; inversion 1.
        }

        rewrite Znth_0_hd.
        2: ulia. 
        do 2 rewrite upd_Znth_map.
        
        
        (* but u could be either 
           - unseen, in which case the min-popped
             was unseen, which means we will break
           - seen, in which case there is a 
             whole lot of ground to cover   
         *)
        unfold V in *.
        
        forward.
        forward_if. 
        1: {  (* todo: lemma-fy *)
          (* dist[u] = inf. We will break. *)
          assert (Ha: 0 <= inf < Int.modulus). {
            rewrite inf_eq; compute; split; [inversion 1 | trivial].
          }
          rewrite inf_eq2 in H14.
          apply Int_repr_eq_small in H14; trivial.
          2: { assert (0 <= u < Zlength dist) by lia.
               apply (Forall_Znth _ _ _ H15) in H6.
               simpl in H6. split; lia. 
          }
          
          forward.
          Exists prev (upd_Znth u priq (inf + 1)) dist (u :: popped).

          entailer!.
          remember (find priq
                         (fold_right Z.min
                                     (hd 0 priq) priq) 0) as u.
          clear H15 H16 H17 H18 Ppriq_ptr HPpriq_ptr Ppriq_ptr0 H19 H20 H21
                H22 H23 H24 H25 H26 H27.
          split.
          - rewrite Forall_forall; intros.
            apply In_Znth_iff in H15.
            destruct H15 as [index [? ?]].
            destruct (Z.eq_dec index u).
            + subst index. rewrite upd_Znth_same in H16; lia.
            + rewrite upd_Znth_Zlength in H15; trivial; [|lia].
              rewrite upd_Znth_diff in H16; trivial; [|lia].
              rewrite <- H16.
              rewrite Hequ, <- H4, Znth_find in H14.
              * rewrite <- H14.
                apply Z.le_ge, fold_min, Znth_In; trivial.
              * apply min_in_list. apply incl_refl.
                   rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
              * apply (vvalid_meaning g); trivial.
                replace SIZE with (Zlength priq).
                apply find_range.
                apply min_in_list. apply incl_refl.
                rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
              * rewrite <- Hequ; trivial.
          - unfold dijkstra_correct in H1 |- *.
            intros. specialize (H1 _ H15).
            destruct H1 as [? [? ?]].
            split3.
            + unfold inv_popped in *.
              intros.
              destruct (Z.eq_dec dst u).
              * subst dst. left.
                split; trivial.
                intros.
                assert (Znth u priq = inf). {
                  rewrite H4; trivial.
                }
                unfold inv_unseen in H17.
                rewrite H4 in H20; trivial.
                specialize (H17 H13 H20).
                split.
                --
                  destruct (in_dec
                              (ZIndexed.eq)
                              m
                              popped).
                  1: intuition.
                  assert ((Znth m dist) = inf). {
                    rewrite <- H4, Hequ in H20; trivial.
                    rewrite Znth_find in H20.
                    2: { apply min_in_list.
                         apply incl_refl.
                         rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
                    }
                    pose proof (fold_min priq (Znth m dist)).
                    rewrite H20 in H21.
                    assert (0 <= m < Zlength dist).
                    { apply (vvalid_meaning g) in H19; trivial.
                      ulia.
                    }
                    destruct (Znth_dist_cases m dist H22); trivial.
                    exfalso.
                    - apply Zlt_not_le in H23.
                      apply H23. apply H21.
                      rewrite <- H4; trivial.
                      apply Znth_In. lia.
                  }
                  pose proof (edge_cost_pos g (m,u)). ulia.
                -- intros.
                   assert (0 <= m < SIZE). {
                     apply (vvalid_meaning g) in H19; trilia.
                   }
                   destruct (Z.eq_dec m u).
                   1: rewrite e; trivial.
                   apply not_in_cons in H21. destruct H21 as [_ ?].
                   assert (Hrem:= H21).
                   rewrite (get_popped_meaning _ priq) in H21 by lia.
                   rewrite <- H4; trivial.
                   rewrite <- H4, Hequ, Znth_find in H20; trivial.
                   2: apply fold_min_in_list; lia.
                   pose proof (fold_min priq (Znth m priq)).
                   rewrite H20 in H23.
                   assert (In (Znth m priq) priq). {
                     apply Znth_In. lia.
                   }
                   specialize (H23 H24).
                   apply Z.le_antisymm; trivial.
                   apply (Forall_Znth _ _ m) in H7.
                   simpl in H7.
                   all: ulia.
              * apply in_inv in H18; destruct H18; [lia|].
                destruct (H1 H18); [left | right].
                -- destruct H19; split; trivial. 
                   intros. destruct (Z.eq_dec m u).
                   ++ unfold V in *; rewrite e, H14.
                      split; trivial.
                      pose proof (edge_cost_pos g (u, dst)).
                      ulia.
                   ++ split.
                      1: apply H20; trivial.
                      intros.
                      apply not_in_cons in H22. destruct H22 as [_ ?].
                      destruct (H20 _ H21).
                      apply H24; trivial.
                -- destruct H19 as [p2dst [? [? ?]]].
                   exists p2dst. split3; trivial.
                   unfold path_in_popped in *.
                   intros.
                   specialize (H20 _ H22).
                   destruct H20; split; trivial.
                   destruct (Z.eq_dec step u).
                   ++ rewrite e. apply in_eq.
                   ++ apply in_cons; trivial.
            + unfold inv_unpopped in *.
              intros.
              assert (n0: dst <> u). {
                intro. apply H18.
                rewrite H20.
                apply in_eq.
              }
              apply not_in_cons in H18; destruct H18 as [_ ?].
              specialize (H16 H18 H19).
              destruct H16; [left | right]; trivial.
              remember (Znth dst prev) as mom.
              destruct H16 as [? [? [? [? [? [? ?]]]]]].
              split3; [| |split3; [| |split3]]; trivial.
              1: destruct (Z.eq_dec mom u);
                subst mom; apply in_cons; trivial.
              intros. destruct (Z.eq_dec mom' u).
              * rewrite e in *.
                unfold V in *.
                rewrite H14.
                pose proof (edge_cost_pos g (u, dst)).
                ulia.
              * apply H25; trivial.
                simpl in H27; destruct H27; [lia|]; trivial.
            + unfold inv_unseen in *. intros.
              assert (n: dst <> u). {
                intro contra. apply H18.
                rewrite contra; apply in_eq.
              }
              apply not_in_cons in H18; destruct H18 as [_ ?].
              specialize (H17 H18 H19).
              destruct (Z.eq_dec m u).
              1: { unfold V in *; rewrite e, H14.
                   pose proof (edge_cost_pos g (u, dst)).
                   ulia.
              }
              apply H17; trivial.
              simpl in H21; destruct H21; [lia | trivial].
        }
        
        (* Now we're in the main proof. We will run through
           the for loop and relax u's neighbors when possible.
         *)
        rename H14 into Htemp.
        assert (H14: Znth u dist < inf). {
          rewrite inf_eq2 in Htemp.
          apply repr_neq_e in Htemp.
          pose proof (Znth_dist_cases u dist).
          destruct H14; trilia.
        }
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
          SIZE
          (dijk_inner_forloop_inv g sh src priq dist_ptr
                                  prev_ptr priq_ptr graph_ptr).
        -- unfold SIZE; rep_lia.
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
          clear H15 H16 H17 H18 H19 H20 H21 H22
                H23 H24 H25 H26 H27 Ppriq_ptr HPpriq_ptr Ppriq_ptr0.
          
          split3; [| | split3; [| |split3]]; trivial.
          ++ (* We must show inv_popped for all
                dst that are in range. *)
            intros. subst u.
            apply (inv_popped_add_u g src dst popped prev
                  priq dist); trivial.

          ++ intros.
             destruct (Z.eq_dec dst u).
             1: subst dst; ulia.
             simpl in H16; destruct H16; [lia | intro].
             destruct (H1 dst) as [? _]; trivial.
             destruct (H18 H16) as [[? ?] | [src2dst [? [? ?]]]].
             2: destruct H19 as [? [? [? [? ?]]]]; lia.
             assert (vvalid g u). {
               apply (vvalid_meaning g); trivial; lia.
             }
             destruct (H20 u H21).
             specialize (H23 H13). ulia.
          
          ++ intros.
             apply (vvalid_meaning g) in H15.
             apply inv_unpopped_weak_add_unpopped; trivial.
     
          ++ intros.
             apply (vvalid_meaning g) in H15.
             apply (inv_unseen_weak_add_unpopped g prev _ _ src); trivial.

          ++ apply in_eq.

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
             ulia. rewrite inf_eq; rep_lia.

        -- (* We now begin with the for loop's body *)
          rewrite <- Hequ.
          freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
          unfold DijkGraph.
          rewrite (SpaceAdjMatGraph_unfold _ _ id _ _ u).
          2: ulia.
          Intros.
          rename H16 into H_inv_popped.
          rename H17 into H16.
          rename H18 into H_inv_unpopped.
          rename H19 into H_inv_unpopped_weak.
          rename H20 into H_inv_unseen.
          rename H21 into H_inv_unseen_weak.
          rename H22 into H17.
          rename H23 into H18.
          rename H25 into H_priq_dist_link.
          rename H26 into H19.
          rename H27 into H20.
          rename H28 into H21. 

          freeze FR2 := (iter_sepcon _ _) (iter_sepcon _ _).
          unfold list_rep.
          assert_PROP (force_val
                         (sem_add_ptr_int tint Signed
                                          (force_val (sem_add_ptr_int (tarray tint 8) Signed (pointer_val_val graph_ptr) (Vint (Int.repr u))))
                                          (Vint (Int.repr i))) = field_address (tarray tint SIZE) [ArraySubsc i] (@list_address SIZE CompSpecs (pointer_val_val graph_ptr) u)). {
            entailer!.
            unfold list_address. simpl.
            rewrite field_address_offset.
            1: rewrite offset_offset_val; simpl; f_equal; rep_lia.
            destruct H26 as [? [? [? [? ?]]]].
            unfold field_compatible; split3; [| | split3]; simpl; auto.
          }
          
          assert (Htemp1: Zlength (@graph_to_mat SIZE g id) = SIZE). {
            rewrite graph_to_mat_Zlength; trivial. lia.
          }
          
          assert (Htemp2: Zlength (Znth u (@graph_to_mat SIZE g id)) = SIZE). {
            rewrite Forall_forall in H0. apply H0. apply Znth_In.
            ulia.
          }
          
          forward.
          clear Htemp1 Htemp2 H22.
          thaw FR2.
          gather_SEP (iter_sepcon _ _) (data_at _ _ _ _) (iter_sepcon _ _).
          rewrite sepcon_assoc.
          rewrite <- (@SpaceAdjMatGraph_unfold SIZE); trivial. thaw FR.
          remember (Znth i (Znth u (@graph_to_mat SIZE g id))) as cost.

          assert (H_i_valid: vvalid g i). {
            apply (vvalid_meaning g); trivial.
          }

          rewrite <- elabel_Znth_graph_to_mat in Heqcost; trivial.

          assert_PROP (Zlength priq' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          assert_PROP (Zlength prev' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          assert_PROP (Zlength dist' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          
          forward_if.
          ++ rename H26 into Htemp.
             assert (0 <= cost <= Int.max_signed / SIZE). {
               pose proof (edge_representable g (u, i)).
               rewrite Heqcost in *.
               apply (valid_edge_bounds g).
               rewrite (evalid_meaning g). split; trivial.
               intro.
               rewrite inf_eq2 in Htemp.
               do 2 rewrite Int.signed_repr in Htemp; trivial.
               rewrite <- H27 in Htemp.
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
               apply (Forall_Znth _ _ _ H27) in H21.
               assumption.
             }
             assert (0 <= Znth i dist' <= inf). {
               assert (0 <= i < Zlength dist') by lia.
               apply (Forall_Znth _ _ _ H28) in H21.
               assumption.
             }
             assert (0 <= Znth u dist' + cost <= Int.max_signed). {
               split; [lia|].
               assert (inf <= Int.max_signed - (Int.max_signed / SIZE)). {
                 rewrite inf_eq. compute; inversion 1.
               }
               rep_lia.
             }
             unfold V, DE in *.
             
             forward. forward. forward_if.
             ** rename H30 into H_improvement.
                (* We know that we are definitely
                   going to make edits in the arrays:
                   we have found a better path to i, via u *)
                
                assert (~ In i (popped')).
                { (* todo: lemma-fy *)
                  (* This useful fact is true because
                     the cost to i was just improved.
                     This is impossible for popped items.
                   *)
                  intro.
                  destruct (H_inv_popped _ H_i_valid H30) as [[? ?] | ?].
                  1: destruct (H32 u H_u_valid); ulia.
                  apply Zlt_not_le in H_improvement.
                  apply H_improvement.
                  destruct (H_inv_popped _ H_u_valid H24) as [[? ?] | [p2u [? [? ?]]]].
                  1: ulia.
                  destruct H32 as [? [? [? [? ?]]]].
                  destruct H31 as [p2i [? [? ?]]].
                  destruct H31 as [? [? [? [? ?]]]].
                  unfold V, E in *. rewrite H37, H43.
                  
                  unfold path_globally_optimal in H40.
                  specialize (H40 (fst p2u, snd p2u +:: (u,i))).

                  rewrite path_cost_app_cons in H40; trivial.
                  rewrite Heqcost.
                  apply H40.
                  - apply valid_path_app_cons.
                    + rewrite <- surjective_pairing; trivial.
                    + rewrite (surjective_pairing p2u) in H35.
                      destruct H35; simpl in H35.
                      ulia.
                    + apply strong_evalid_dijk; trivial. ulia.
                  - apply path_ends_app_cons with (a' := src); trivial.
                      3: rewrite <- surjective_pairing; trivial.
                      all: rewrite (surjective_pairing p2u) in *;
                        destruct H35; simpl in H35; trivial.
                }
                 
                assert (Htemp : 0 <= i < Zlength dist') by lia.
                pose proof (Znth_dist_cases i dist' Htemp H21).
                clear Htemp.
                rename H31 into icases.
                rewrite <- H_priq_dist_link in icases; trivial.

                (* assert (0 <= i < Zlength (map Vint (map Int.repr dist'))) by *)
                    (* (repeat rewrite Zlength_map; lia). *)
                forward. forward. forward.
                forward; rewrite upd_Znth_same; trivial.
                1: entailer!.
                1,3: repeat rewrite Zlength_map; lia.
                (* unfold V, DE in *. *)
                forward_call (priq_ptr, i, (Znth u dist' + cost), priq').

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
                      H37 H38 H39 H40 H41 H42
                      HPpriq_ptr Ppriq_ptr Ppriq_ptr0.

                remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
                
                Set Printing All.
                remember (Znth u dist' + elabel g (u, i)) as newcost.
                unfold V, DE in *.
                
                rewrite <- Heqnewcost in *.
                Unset Printing All.

                assert (u <> i) by (intro; subst; lia).
                
                split3; [| | split3; [| | split3; [| | split3; [| | split]]]]; intros.
                (* 10 goals, where the 10th is 
                   3 range-based goals together *)
                --- now apply inv_popped_newcost.
                --- destruct (Z.eq_dec dst i).
                    1: subst dst; rewrite upd_Znth_same; trivial; lia.
                    rewrite upd_Znth_diff.
                    apply H16; trivial.
                    apply (vvalid_meaning g) in H32.
                    all: ulia.
                --- now apply inv_unpopped_newcost with (priq := priq').
                --- now apply inv_unpopped_weak_newcost.
                --- apply inv_unseen_newcost; ulia.
                --- apply inv_unseen_weak_newcost; ulia.
                --- rewrite upd_Znth_diff; try lia;
                      intro; subst src; lia.
                --- rewrite upd_Znth_diff; try lia;
                      intro; subst src; lia.
                --- destruct (Z.eq_dec dst i).
                    1: subst dst; repeat rewrite upd_Znth_same; ulia.
                    repeat rewrite upd_Znth_diff; trivial; try lia.
                    apply H_priq_dist_link; trivial.
                    all: rewrite (vvalid_meaning g) in H32; ulia.
                --- split3; apply Forall_upd_Znth; ulia.

             (* done until here *)
                    
             ** (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                rename H41 into improvement.
                forward. 
                (* The old arrays are just fine. *)
                Exists prev' priq' dist' popped'.
                entailer!.
                remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
                clear H51 H52.
                assert (elabel g (u, i) < inf). {
                  apply Z.le_lt_trans with (m := Int.max_signed / SIZE);
                    trivial.
                  apply H36.
                  rewrite inf_eq.
                  compute; trivial.
                }
                  
                split3; [| |split].
                --- intros.
                    (* Show that moving one more step
                       still preserves the for loop invariant *)
                    destruct (Z.eq_dec dst i).
                    (* when dst <> i, all is well *)
                    2: apply H21; lia.
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
                    assert (i <= i < SIZE) by lia.
                    destruct (H_inv_unpopped_weak i H55 H53 H54).
                    1: left; trivial.
                    destruct H56 as [? [[? [? [? [? [? ?]]]]] ?]].
                    unfold V in *.
                    remember (Znth i prev') as mom.
                    right.
                    split3; [| |split3; [| |split3]]; trivial.
                    intros.
                    pose proof (Znth_dist_cases mom' dist').
                    rename H66 into e.
                    destruct e as [e | e]; trivial.
                    1: apply (vvalid_meaning g) in H64; ulia.
                    1: {
                      rewrite e.
                      pose proof (edge_cost_pos g (mom', i)).
                      ulia.
                    }
                    destruct (H_inv_popped _ H64 H65); [unfold V in *; ulia|].
                    
                    destruct H66 as [p2mom' [? [? ?]]].
                    assert (Hrem := H66).

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
                        
                    *** destruct H66 as [? [? [? [? ?]]]].
                        apply in_path_eq_epath_to_vpath in i0; trivial.
(*
  1. In u p': p' is from s to i, consider the
  vertex mom' which is just before i.
 *)
                        destruct (Z.eq_dec mom' u).
                        ----
(*
  1.1 mom' = u: dist[u] is global optimal. We have
  dist[i] < dist[u] + graph[u][i]
          <= path_cost [s to u of p'] + graph[u][i]
          = path_cost p'
                               *)
                              subst mom'.
                              specialize (H67 _ i0).
                              rename p2mom' into p2u.
                              unfold path_globally_optimal in H68.
                              apply Z.ge_le in improvement.

                              destruct (zlt (Znth u dist' + elabel g (u, i)) inf); ulia.
                        ----
                          destruct Hrem as [? [? [? [? ?]]]].
                          
                          assert (In_path g mom' p2mom'). {
                            destruct H74.
                            apply pfoot_in in H78. 
                            trivial.
                          }

                          destruct (zlt (Znth mom' dist' + elabel g (mom', i)) inf).
                          2: {
                            unfold V in *.
                            destruct (zlt (elabel g (mom', i)) inf); lia.
                          }

                          assert (vvalid g i). { trivial. }
                           
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
                          assert (0 <= mom' < SIZE). {
                            apply (vvalid_meaning g) in H64; ulia.
                          }
                          red in H21.

                          destruct (H_inv_unpopped_weak _ H55 H53 H54).
                          1: lia.
                          destruct H81 as [? [[? [? [? [? [? ?]]]]]]].
                          apply H88; trivial.
                    ***

(* 2. ~ In u p': This is an easy case.
   dist[i] < path_cost p' because of Inv2.
 *)
                      apply H63; trivial.
                      intro. apply n.
                      destruct H66 as [? [? [? [? ?]]]].
                      rewrite in_path_eq_epath_to_vpath; trivial.
                      destruct H70.
                      apply pfoot_in in H74. rewrite H69 in *. trivial.           
                --- intros. destruct (Z.eq_dec dst i).
                    +++ subst dst. lia.
                    +++ apply H_inv_unpopped_weak; lia.
                --- unfold inv_unseen; intros.
                    destruct (Z.eq_dec dst i).
                    2: apply H_inv_unseen; ulia.                     
                    subst dst.
                    assert (i <= i < SIZE) by lia.
                    destruct (Z.eq_dec m u).
                    2: apply H_inv_unseen_weak; trivial.
                    subst m.
                    unfold V in *.
                    rewrite H54 in improvement.
                    assert (0 <= u < SIZE) by lia.
                    destruct (Znth_dist_cases u dist'); trivial.
                    lia.
                --- intros.
                    assert (i <= dst < SIZE) by lia.
                    apply H_inv_unseen_weak; trivial.
          ++  (* i was not a neighbor of u.
                 We must prove the for loop's invariant holds *)
            rewrite inf_eq2 in H36.
            forward.
            Exists prev' priq' dist' popped'.
            entailer!.
            remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
            do 2 rewrite Int.signed_repr in H36.
            3,4: apply edge_representable.
            2: lia.
            clear H48.
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
                   assert (i <= i < SIZE) by lia.
                   destruct (H_inv_unpopped_weak i H51 H49 H50).
                   1: left; trivial.
                   destruct H52 as [? [[? [? [? [? [? ?]]]]]?]].
                   unfold V in *.
                   remember (Znth i prev') as mom.

                   assert (Ha: Znth mom dist' < inf). {
                     assert (0 <= elabel g (mom, i)). {
                       apply edge_cost_pos; trivial.
                     }
                     ulia.
                   }
                   
                   right. split3; [| |split3; [| |split3]]; trivial.
                   
                   intros.
                   destruct (Znth_dist_cases mom' dist') as [e | e]; trivial.
                   1: apply (vvalid_meaning g) in H60; ulia.
                   1: { rewrite e.
                        pose proof (edge_cost_pos g (mom', i)).
                        ulia.
                   }
                   unfold V in *.
                   
                   destruct (zlt (Znth mom' dist' + elabel g (mom', i)) inf).
                   2: ulia.
                   assert (vvalid g i). { trivial. }
                   
                   destruct (Z.eq_dec mom' u).
                   1: { subst mom'.
                        assert (0 <= Znth u dist'). {
                          apply (Forall_Znth _ _ u) in H31.
                          simpl in H31. apply H31.
                          lia.
                        }
                        ulia.
                   }
                   apply H59; trivial.
               --- apply H21; lia.
            ** destruct (Z.eq_dec dst i).
               --- lia. 
               --- apply H_inv_unpopped_weak; lia.
            ** destruct (Z.eq_dec dst i).
               2: apply H_inv_unseen; lia.
               subst dst.
               assert (i <= i < SIZE) by lia.
               unfold inv_unseen; intros.
               destruct (Z.eq_dec m u).
               2: apply H_inv_unseen_weak; trivial.
               subst m.
               assert (0 <= Znth u dist'). {
                 apply (Forall_Znth _ _ u) in H31.
                 simpl in H31. apply H31.
                 ulia.
               }
               ulia.
            ** apply H_inv_unseen_weak; lia.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
          Intros prev' priq' dist' popped'.
          Exists prev' priq' dist' popped'.
          entailer!.
          remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
          unfold dijkstra_correct.
          split3; [auto | apply H17 | apply H_inv_popped];
            try rewrite <- (vvalid_meaning g); trivial.
      * (* After breaking from the while loop,
           prove break's postcondition *)
        assert (isEmpty priq = Vone). {
          destruct (isEmptyTwoCases priq); trivial.
            rewrite H12 in H11; simpl in H11; now inversion H11.
        }
        clear H11.
        forward. Exists prev priq dist popped.
        entailer!.
        pose proof (isEmptyMeansInf _ H12).
        rewrite Forall_forall in H25 |- *.
        intros. specialize (H25 _ H26). lia.
    + (* from the break's postcon, prove the overall postcon *)
      unfold dijk_forloop_break_inv.
      Intros prev priq dist popped. 
      forward. Exists prev dist popped. entailer!.
Admitted.

