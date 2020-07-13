Require Import VST.msl.iter_sepcon.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.floyd_ext.share.

(* maybe the above can go into env *)
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import RamifyCoq.sample_mark.priq_utils.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_macros.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_spec.
Require Import VST.floyd.sublist. (* this has to go last *)

(* We must use the CompSpecs and Vprog that were
   centrally defined in dfijksta's environment. 
   This lets us be consistent and call PQ functions in Dijkstra. 
 *)
Local Definition CompSpecs := env_dijkstra_arr.CompSpecs.
Local Definition Vprog := env_dijkstra_arr.Vprog.
Local Definition Gprog := dijk_pq_arr_spec.Gprog.

Local Open Scope Z_scope.

(** CONSTANTS AND RANGES **)

Ltac trilia := trivial; lia.
Ltac ulia := unfold VType in *; trilia.

Lemma inf_eq: 1879048192 = inf.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute; trivial. Qed.

Opaque inf.

Definition inrange_prev prev_contents :=
  Forall (fun x => 0 <= x < SIZE \/ x = inf) prev_contents.

Definition inrange_priq priq_contents :=
  Forall (fun x => 0 <= x <= inf+1) priq_contents.

Definition inrange_dist dist_contents :=
  Forall (fun x => 0 <= x <= inf) dist_contents.

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

Lemma g2m_Znth2_range:
  forall a b g,
    0 <= a < SIZE ->
    0 <= b < SIZE ->
    inrange_graph (graph_to_mat g) ->
    0 <= Znth a (Znth b (graph_to_mat g)).
Proof.
  intros.
  specialize (H1 _ _ H H0).
  destruct H1; try lia.
  rewrite H1. rewrite <- inf_eq; lia.
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
    sound_dijk_graph g ->
    dijkstra_correct g src popped prev dist ->
    True ->
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
  destruct (H0 _ H4) as [? _].
  unfold inv_popped in H5.
  specialize (H5 H2).
  destruct H5; [ulia|].
  apply H5; trivial.
Qed.
                  
Lemma path_leaving_popped:
  forall g links s u popped priq,
    Zlength priq = SIZE ->
    inrange_priq priq ->
    sound_dijk_graph g ->
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
  - intros. destruct H3. simpl in H3, H6.
    exfalso. apply H5.
    rewrite <- H6; trivial.
  - intros.
    assert (Hrem := H1).
    red in H1. destruct H1 as [Ha [Hb [Hc Hd]]].
    rewrite (surjective_pairing a) in *.
    assert (fst a = s). {
      simpl in H2. destruct H2 as [? _].
      rewrite Hc in H1. simpl in H1. lia. 
    }
    rewrite H1 in *.
    remember (snd a) as t.
    rewrite <- Hd in Heqt.
    destruct (in_dec (ZIndexed.eq) t popped).
    + assert (valid_path g (t, links)). {
        rewrite Heqt.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing, H1 in H2.
        apply valid_path_cons with (v := s); trivial.
      }
      assert (path_ends g (t, links) t u). {
        split; trivial.
        destruct H3.
        rewrite <- H7. symmetry.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing, H1, <- Hd.
        apply pfoot_cons.
      }
      specialize (IHlinks _ H6 H7 i).
      destruct IHlinks as [p2m [m [c [p2u [? [? [? [? [? [? [? ?]]]]]]]]]]].
      exists (path_glue (s, [(s,t)]) p2m), m, c, p2u.
      assert (paths_meet g (s, [(s, t)]) p2m). {
        apply (path_ends_meet _ _ _ s t m); trivial.
        split; simpl; trivial. rewrite Hd; trivial.
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
      assert (evalid g (s,t)). {
        apply (valid_path_evalid _ s ((s,t)::links)); trivial.
        apply in_eq.
      }
      apply Hb in H19. destruct H19.

      split3; [| |split3; [| | split3; [| |split]]]; trivial.
      * rewrite (path_glue_assoc g); trivial.
        -- unfold EType, VType in *. rewrite H8.
           unfold path_glue; trivial.
        -- apply (path_ends_meet _ _ _ t m u); trivial.
           split; trivial.
           unfold path_glue.
           simpl fst; simpl snd; simpl app.
           destruct H12. rewrite <- H21.
           rewrite (surjective_pairing p2u) at 2.
           rewrite H17.
           assert (c = dst g (m, c)) by now rewrite Hd.
           rewrite H22 at 2.
           apply pfoot_cons.
      * apply valid_path_merge; trivial.
        simpl; unfold strong_evalid.
        rewrite Hc, Hd; simpl; split3; trivial.
        apply vvalid2_evalid; trivial; split; trivial.
        split; trivial.
      * split; trivial.
        unfold path_glue.
        simpl fst; simpl snd; simpl app.
        destruct H11. rewrite <- H21.
        rewrite (surjective_pairing p2m) at 2.
        rewrite H18.
        assert (t = dst g (s, t)) by now rewrite Hd.
        rewrite H22 at 2.
        apply pfoot_cons.
    + clear IHlinks. 
      exists (s, []), s, t, (t, links).
      assert (evalid g (s,t)). {
        apply (valid_path_evalid _ s ((s,t)::links)); trivial.
        apply in_eq.
      }
      apply Hb in H6. destruct H6.
      split3; [| |split3; [| | split3; [| |split]]]; trivial.
      * rewrite Heqt.
        apply valid_path_cons with (v := s).
        rewrite (surjective_pairing a).
        rewrite H1, <- Hd, <- Heqt; trivial.
      * split; trivial.
      * destruct H3. split; trivial.
        rewrite <- H8. symmetry.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing.
        rewrite <- Hd. apply pfoot_cons.
      * apply vvalid2_evalid; trivial.
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

Lemma get_popped_meaning:
  forall l i,
    0 <= i < Zlength l ->
    In i (get_popped l) <-> Znth i l = inf + 1.
Proof.
  intros. generalize dependent i.
  induction l; intros.
  1: rewrite Zlength_nil in H; lia.
  destruct (Z.eq_dec i 0).
  - subst i.
    split; intros.
    + rewrite Znth_0_cons.
      unfold get_popped in H0.
      rewrite In_map_snd_iff in H0; destruct H0.
      rewrite filter_In in H0; destruct H0.
      simpl in H1.
      rewrite (behead_list (nat_inc_list (Z.to_nat (Zlength (a :: l))))) in H0.
      2: { rewrite Zlength_correct.
           rewrite nat_inc_list_length.
           rewrite Z2Nat.id; lia.
      }
      rewrite nat_inc_list_hd in H0 by lia.
      simpl in H0. destruct H0.
      * inversion H0. rewrite Z.eqb_eq in H1; trivial.
      * pose proof (in_combine_r _ _ _ _ H0).
        exfalso.
        apply in_tl_nat_inc_list in H2.
        lia.
    + unfold get_popped.
      rewrite (behead_list (nat_inc_list (Z.to_nat (Zlength (a :: l))))).
      2: { rewrite Zlength_correct.
           rewrite nat_inc_list_length.
           rewrite Z2Nat.id; lia.
      }
      rewrite nat_inc_list_hd by lia. simpl.
      destruct (a =? inf + 1) eqn:?.
      simpl; left; trivial.
      rewrite Z.eqb_neq in Heqb.
      exfalso; apply Heqb.
      rewrite Znth_0_cons in H0; trivial.
  - rewrite Znth_pos_cons by lia.
    rewrite Zlength_cons in H.
    assert (0 <= (i-1) < Zlength l) by lia.
    assert (Zlength [a] = 1) by reflexivity.
    change (a :: l) with ([a] ++ l).
    rewrite in_get_popped by lia. apply IHl; lia.
Qed.

Lemma get_popped_irrel_upd:
  forall l i j new,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    In i (get_popped l) <->
    In i (get_popped (upd_Znth j l new)).
Proof.
  intros.
  repeat rewrite get_popped_meaning; [| rewrite upd_Znth_Zlength; lia | lia].
  rewrite upd_Znth_diff; trivial; reflexivity.
Qed.

Lemma get_popped_range:
  forall n l,
    In n (get_popped l) -> 0 <= n < Zlength l.
Proof.
  intros.
  unfold get_popped in H.
  rewrite In_map_snd_iff in H. destruct H.
  rewrite filter_In in H. destruct H as [? _].
  apply in_combine_r in H.
  apply nat_inc_list_in_iff in H.
  rewrite Z2Nat.id in H by (apply Zlength_nonneg).
  assumption.
Qed.

Lemma get_popped_path:
  forall {g mom src prev priq dist},
    sound_dijk_graph g ->
    dijkstra_correct g src prev priq dist ->
    Zlength priq = SIZE ->
    In mom (get_popped priq) ->
    Znth mom dist < inf ->
    exists p2mom : path,
      path_correct g prev dist src mom p2mom /\
      (forall step : Z,
          In_path g step p2mom ->
          In step (get_popped priq) /\
          Znth step dist < inf) /\
      path_globally_optimal g src mom p2mom.
Proof.
  intros.
  assert (vvalid g mom). {
    apply get_popped_range in H2.
    apply vvalid_range; trivial. unfold VType in *. lia.
  }
  destruct (H0 _ H4) as [? _].
  unfold inv_popped in H5.
  specialize (H5 H2).
  unfold VType in *.
  destruct H5; [lia|].
  apply H5; trivial.
Qed.
  
Lemma path_leaving_popped:
  forall g links s u priq,
    Zlength priq = SIZE ->
    inrange_priq priq ->
    sound_dijk_graph g ->
    valid_path g (s, links) ->
    path_ends g (s, links) s u ->
    In s (get_popped priq) ->
    ~ In u (get_popped priq) ->
    exists (p1 : path) (mom' child' : Z) (p2 : path),
      path_glue p1 (path_glue (mom', [(mom', child')]) p2) = (s, links) /\
      valid_path g p1 /\
      valid_path g p2 /\
      path_ends g p1 s mom' /\
      path_ends g p2 child' u /\
      In mom' (get_popped priq) /\
      ~ In child' (get_popped priq) /\
      evalid g (mom', child').
Proof.
  intros.
  generalize dependent s.
  induction links.
  - intros. destruct H3. simpl in H3, H6.
    exfalso. apply H5.
    rewrite <- H6; trivial.
  - intros.
    assert (Hrem := H1).
    red in H1. destruct H1 as [Ha [Hb [Hc Hd]]].
    rewrite (surjective_pairing a) in *.
    assert (fst a = s). {
      simpl in H2. destruct H2 as [? _].
      rewrite Hc in H1. simpl in H1. lia. 
    }
    rewrite H1 in *.
    remember (snd a) as t.
    rewrite <- Hd in Heqt.
    destruct (in_dec (ZIndexed.eq) t (get_popped priq)).
    + assert (valid_path g (t, links)). {
        rewrite Heqt.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing, H1 in H2.
        apply valid_path_cons with (v := s); trivial.
      }
      assert (path_ends g (t, links) t u). {
        split; trivial.
        destruct H3.
        rewrite <- H7. symmetry.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing, H1, <- Hd.
        apply pfoot_cons.
      }
      specialize (IHlinks _ H6 H7 i).
      destruct IHlinks as [p2m [m [c [p2u [? [? [? [? [? [? [? ?]]]]]]]]]]].
      unfold VType in *.
      exists (path_glue (s, [(s,t)]) p2m), m, c, p2u.
      assert (paths_meet g (s, [(s, t)]) p2m). {
        apply (path_ends_meet _ _ _ s t m); trivial.
        split; simpl; trivial. rewrite Hd; trivial.
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
      assert (evalid g (s,t)). {
        apply (valid_path_evalid _ s ((s,t)::links)); trivial.
        apply in_eq.
      }
      apply Hb in H19. destruct H19.

      split3; [| |split3; [| | split3; [| |split]]]; trivial.
      * rewrite (path_glue_assoc g); trivial.
        -- unfold EType, VType in *. rewrite H8.
           unfold path_glue; trivial.
        -- apply (path_ends_meet _ _ _ t m u); trivial.
           split; trivial.
           unfold path_glue.
           simpl fst; simpl snd; simpl app.
           destruct H12. rewrite <- H21.
           rewrite (surjective_pairing p2u) at 2.
           rewrite H17.
           assert (c = dst g (m, c)) by now rewrite Hd.
           rewrite H22 at 2.
           apply pfoot_cons.
      * apply valid_path_merge; trivial.
        simpl; unfold strong_evalid.
        rewrite Hc, Hd; simpl; split3; trivial.
        apply vvalid2_evalid; trivial; split; trivial.
        split; trivial.
      * split; trivial.
        unfold path_glue.
        simpl fst; simpl snd; simpl app.
        destruct H11. rewrite <- H21.
        rewrite (surjective_pairing p2m) at 2.
        rewrite H18.
        assert (t = dst g (s, t)) by now rewrite Hd.
        rewrite H22 at 2.
        apply pfoot_cons.
    + clear IHlinks. 
      exists (s, []), s, t, (t, links).
      assert (evalid g (s,t)). {
        apply (valid_path_evalid _ s ((s,t)::links)); trivial.
        apply in_eq.
      }
      apply Hb in H6. destruct H6.
      split3; [| |split3; [| | split3; [| |split]]]; trivial.
      * rewrite Heqt.
        apply valid_path_cons with (v := s).
        rewrite (surjective_pairing a).
        rewrite H1, <- Hd, <- Heqt; trivial.
      * split; trivial.
      * destruct H3. split; trivial.
        rewrite <- H8. symmetry.
        rewrite Heqt, <- H1, Hd, <- surjective_pairing.
        rewrite <- Hd. apply pfoot_cons.
      * apply vvalid2_evalid; trivial.
Qed.

 *)
(* The above can be deleted, but I'm keeping them until my new PQ comes in *)

(* HIGHLY TEMPORARY *)
(* Definition get_unpopped pq : list VType := *)
  (* map snd (filter (fun x => (fst x) <? (inf + 1)) *)
                  (* (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))). *)

Lemma get_popped_meaning:
  forall popped priq i,
    0 <= i < Zlength priq ->
    In i popped <-> Znth i priq = inf + 1.
Admitted.

(** PROOF BEGINS **)

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP (inrange_graph (graph_to_mat g))
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
          DijkGraph sh (graph_to_mat g) (pointer_val_val arr))).
  - unfold SIZE. rep_lia.
  - unfold data_at, data_at_, field_at_, SIZE; entailer!.
  - forward. forward.
    forward_call (v_pq, i, inf,
                  (list_repeat (Z.to_nat i)
                               (Vint (Int.repr inf)) ++
                               list_repeat (Z.to_nat (SIZE - i)) Vundef)).
    replace 8 with SIZE by (unfold SIZE; rep_lia).
    rewrite inf_eq2.
    assert ((upd_Znth i (list_repeat (Z.to_nat i) (Vint (Int.repr inf))
                                     ++ list_repeat (Z.to_nat (SIZE - i))
                                     Vundef) (Vint (Int.repr inf))) =
            (list_repeat (Z.to_nat (i + 1)) (Vint (Int.repr inf))
                         ++ list_repeat (Z.to_nat (SIZE - (i + 1))) Vundef)). {
      rewrite upd_Znth_app2 by
          (repeat rewrite Zlength_list_repeat by lia; lia).
      rewrite Zlength_list_repeat by lia.
      replace (i-i) with 0 by lia.
      rewrite <- list_repeat_app' by lia.
      rewrite app_assoc_reverse; f_equal.
      rewrite upd_Znth0_old. 2: rewrite Zlength_list_repeat; lia.
      rewrite Zlength_list_repeat by lia.
      rewrite sublist_list_repeat by lia.
      replace (SIZE - (i + 1)) with (SIZE - i - 1) by lia.
      replace (list_repeat (Z.to_nat 1) (Vint (Int.repr inf))) with
          ([Vint (Int.repr inf)]) by reflexivity. easy.
    }
    rewrite H5. entailer!.
  - (* At this point we are done with the
       first for loop. The arrays are all set to INF. *)
    replace (SIZE - SIZE) with 0 by lia; rewrite list_repeat_0,
                                         <- (app_nil_end).
    forward. forward. 
    forward_call (v_pq, src, 0, (list_repeat (Z.to_nat SIZE) (inf: VType))).
    do 2 rewrite map_list_repeat.
    (* Special values for src have been inserted *)

    (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
     *)
    forward_loop
      (EX prev_contents : list VType,
       EX priq_contents : list VType,
       EX dist_contents : list VType,
       EX popped_verts : list VType,
       PROP (
           (* The overall correctness condition *)
           dijkstra_correct g src popped_verts prev_contents dist_contents;

           (* Some special facts about src *)
           Znth src dist_contents = 0;
           Znth src prev_contents = src;
           (* Znth src priq_contents <> inf; *)
           True;
      
           (* A fact about the relationship b/w 
              dist and priq arrays *)
           forall dst, vvalid g dst ->
                       ~ In dst popped_verts ->
                       Znth dst priq_contents = Znth dst dist_contents;

           (* Information about the ranges of the three arrays *)
           inrange_prev prev_contents;
           inrange_dist dist_contents;
           inrange_priq priq_contents)
       LOCAL (temp _dist (pointer_val_val dist);
              temp _prev (pointer_val_val prev);
              temp _src (Vint (Int.repr src));
              lvar _pq (tarray tint SIZE) v_pq;
              temp _graph (pointer_val_val arr))
       SEP (data_at Tsh
                    (tarray tint SIZE)
                    (map Vint (map Int.repr prev_contents))
                    (pointer_val_val prev);
            data_at Tsh
                    (tarray tint SIZE)
                    (map Vint (map Int.repr priq_contents)) v_pq;
       data_at Tsh
                    (tarray tint SIZE)
                    (map Vint (map Int.repr dist_contents))
                    (pointer_val_val dist);
            DijkGraph sh (graph_to_mat g) (pointer_val_val arr)))
      break:
      (EX prev_contents: list VType,
       EX priq_contents: list VType,
       EX dist_contents: list VType,
       EX popped_verts: list VType,
       PROP (
           (* This fact comes from breaking while *)
           Forall (fun x => x >= inf) priq_contents;
           (* And the correctness condition is established *)
           dijkstra_correct g src popped_verts prev_contents dist_contents)
       LOCAL (lvar _pq (tarray tint SIZE) v_pq)
       SEP (data_at Tsh
                    (tarray tint SIZE)
                    (map Vint (map Int.repr prev_contents))
                    (pointer_val_val prev);
            (data_at Tsh
                     (tarray tint SIZE)
                     (map Vint (map Int.repr priq_contents)) v_pq);
            data_at Tsh
                    (tarray tint SIZE)
                    (map Vint (map Int.repr dist_contents))
                    (pointer_val_val dist);
            DijkGraph sh (graph_to_mat g) (pointer_val_val arr))).
    + Exists (upd_Znth src (@list_repeat VType (Z.to_nat SIZE) inf) src).
      Exists (upd_Znth src (@list_repeat VType (Z.to_nat SIZE) inf) 0).
      Exists (upd_Znth src (@list_repeat VType (Z.to_nat SIZE) inf) 0).
      Exists (@nil VType).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat SIZE) inf) = SIZE). {
        rewrite Zlength_list_repeat; lia. }
      split.
      (* We take care of the easy items first... *)
      2: {
        assert (inrange_prev (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_prev. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new. right; trivial.
        }
        assert (inrange_dist (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_dist. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new.
          rewrite new. compute. split; inversion 1.
        }
        assert (inrange_priq (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_priq. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new.
          rewrite new. compute. split; inversion 1.
        }
        split3; [| |split3];
        try apply Forall_upd_Znth;
        try rewrite upd_Znth_same; try lia; trivial.
        all: rewrite <- inf_eq; unfold SIZE in *; lia.
      }
      (* And now we must show dijkstra_correct for the initial arrays *)
      (* First, worth noting that _nothing_ has been popped so far *)
      assert (H15: 1 = 1) by trivial.
      (* Now we get into the proof of dijkstra_correct proper.
         This is not very challenging... *)
      unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen; split3; intros.
      * inversion H17.
      * assert (src = dst). {
          destruct (Z.eq_dec src dst); trivial. exfalso.
          assert (0 <= dst < SIZE) by
              (rewrite <- (vvalid_range g); trivial).
          rewrite upd_Znth_diff in H18; try lia.
          rewrite Znth_list_repeat_inrange in H18; lia.
          apply vvalid_range in H16; trilia. 
          ulia.
        }
        subst dst. left; trivial.
      * inversion H20. 
    + (* Now the body of the while loop begins. *)
      Intros prev_contents priq_contents dist_contents popped_verts.
      rename H10 into H11.
      rename H9 into H10.
      rename H8 into H9.
      rename H7 into H8.
      assert (H7: 1 = 1) by trivial.
      assert_PROP (Zlength priq_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength prev_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength dist_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }      
      forward_call (v_pq, priq_contents).
      forward_if. (* checking if it's time to break *)
      * (* No, don't break. *)
        assert (isEmpty priq_contents = Vzero). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H16 in H15; simpl in H15;
              now inversion H15.
        }
        clear H15.
        forward_call (v_pq, priq_contents). Intros u.
        (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

        (* We prove a few useful facts about u: *)
        assert (vvalid g u). {
          apply vvalid_range; trivial.
          rewrite H15.
          replace SIZE with (Zlength priq_contents).
          apply find_range.
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H12.
          inversion H12. simpl. left; trivial.
        }
        apply vvalid_range in H17; trivial. 
        rewrite Znth_0_hd, <- H15.
        2: { ulia. }
        do 2 rewrite upd_Znth_map.
        assert (~ (In u popped_verts)). {
          intro.
          rewrite (get_popped_meaning _ priq_contents _) in H18.
          2: ulia.
          rewrite <- isEmpty_in' in H16.
          destruct H16 as [? [? ?]].
          rewrite H15 in H18.
          rewrite Znth_find in H18.
          2: {
            rewrite <- Znth_0_hd by ulia.
            apply min_in_list;
              [ apply incl_refl | apply Znth_In; ulia].
          }
          pose proof (fold_min _ _ H16).
          lia.
        }
        (* but u could be either 
           - unseen, in which case the min-popped
             was unseen, which means we will break
           - seen, in which case there is a 
             whole lot of ground to cover   
         *)
        unfold VType in *.
        
        forward.
        forward_if. 
        1: { 
          (* dist[u] = inf. We will break. *)
          replace 8 with SIZE in H19 by (now compute).
          rewrite inf_eq2 in H19.
          
          assert (Htemp : inf < Int.modulus). {
            rewrite <- inf_eq. compute; trivial.
          }
          apply Int_repr_eq_small in H19.
          2: { assert (0 <= u < Zlength dist_contents) by lia.
               apply (Forall_Znth _ _ _ H20) in H10.
               simpl in H10. lia.
          }
          2: rewrite <- inf_eq; compute; split; [inversion 1 | trivial]. 
          clear Htemp.
          
          forward.  
          Exists prev_contents (upd_Znth u priq_contents (inf + 1)) dist_contents (u :: popped_verts).
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents)
             0) as u.
          split.
          - rewrite Forall_forall; intros.
            apply In_Znth_iff in H15.
            destruct H15 as [index [? ?]].
            destruct (Z.eq_dec index u).
            + subst index. rewrite upd_Znth_same in H33; lia.
            + rewrite upd_Znth_Zlength in H15; trivial; [|lia].
              rewrite upd_Znth_diff in H33; trivial; [|lia].
              rewrite <- H33.
              rewrite Hequ, <- H8, Znth_find in H19.
              * rewrite <- H19.
                apply Z.le_ge.
                apply fold_min.
                apply Znth_In; trivial.
              * apply min_in_list. apply incl_refl.
                   rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
              * apply vvalid_range; trivial.
                replace SIZE with (Zlength priq_contents).
                apply find_range.
                apply min_in_list. apply incl_refl.
                rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
              * rewrite <- Hequ; trivial.
          - unfold dijkstra_correct in H4 |- *.
            intros. specialize (H4 _ H15).
            destruct H4 as [? [? ?]].
            split3.
            + unfold inv_popped in *.
              intros.
              destruct (Z.eq_dec dst u).
              * subst dst. left.
                split; trivial.
                intros.
                assert (Znth u priq_contents = inf). {
                  rewrite H8; trivial.
                }
                unfold inv_unseen in H34.
                rewrite H8 in H37; trivial.
                specialize (H34 H18 H37).
                assert (H38: 1 = 1) by trivial.
                assert (H39: 1 = 1) by trivial.
                split.
                --
                  destruct (in_dec
                              (ZIndexed.eq)
                              m
                              popped_verts).
                  1: intuition.
                  assert ((Znth m dist_contents) = inf). {
                    rewrite <- H8, Hequ in H37; trivial.
                    rewrite Znth_find in H37.
                    2: { apply min_in_list.
                         apply incl_refl.
                         rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
                    }
                    pose proof (fold_min priq_contents (Znth m dist_contents)).
                    rewrite H37 in H40.
                    assert (0 <= m < Zlength dist_contents).
                    { apply vvalid_range in H36; trivial.
                      ulia.
                    }
                    destruct (Znth_dist_cases m dist_contents H41); trivial.
                    exfalso.
                    - apply Zlt_not_le in H42.
                      apply H42. apply H40.
                      rewrite <- H8; trivial.
                      apply Znth_In. lia.
                  }
                  unfold VType in *. rewrite H40.
                  rewrite careful_add_comm, careful_add_inf; trivial.
                  apply g2m_Znth2_range; trivial.
                  apply vvalid_range in H36; trilia.
                -- intros.
                   assert (0 <= m < SIZE). {
                     apply vvalid_range in H36; trilia.
                   }
                   destruct (Z.eq_dec m u).
                   1: rewrite e; trivial.
                   apply not_in_cons in H40. destruct H40 as [_ ?].
                   assert (Hrem:= H40).
                   rewrite (get_popped_meaning _ priq_contents) in H40 by lia.
                   rewrite <- H8; trivial.
                   rewrite <- H8, Hequ, Znth_find in H37; trivial.
                   2: apply fold_min_in_list; lia.
                   pose proof (fold_min priq_contents (Znth m priq_contents)).
                   rewrite H37 in H42.
                   assert ( In (Znth m priq_contents) priq_contents). {
                     apply Znth_In. lia.
                   }
                   specialize (H42 H43).
                   apply Z.le_antisymm; trivial.
                   apply (Forall_Znth _ _ m) in H11.
                   simpl in H11.
                   all: ulia.
              * apply in_inv in H35; destruct H35; [lia|].
                destruct (H4 H35); [left | right].
                -- destruct H36; split; trivial. 
                   intros. destruct (Z.eq_dec m u).
                   ++ unfold VType in *; rewrite e, H19, careful_add_comm, careful_add_inf; [split; trivial|].
                      apply g2m_Znth2_range; trivial.
                      apply vvalid_range in H15; trilia.
                   ++ split.
                      ** apply H37; trivial.
                      ** intros.
                         apply not_in_cons in H39. destruct H39 as [_ ?].
                         destruct (H37 _ H38).
                         apply H41; trivial.
                -- destruct H36 as [p2dst [? [? ?]]].
                   exists p2dst. split3; trivial.
                   unfold path_in_popped in *.
                   intros.
                   specialize (H37 _ H39).
                   destruct H37; split; trivial.
                   destruct (Z.eq_dec step u).
                   ++ rewrite e. apply in_eq.
                   ++ apply in_cons; trivial.
            + unfold inv_unpopped in *.
              intros.
              assert (n0: dst <> u). {
                intro. apply H35.
                rewrite H37.
                apply in_eq.
              }
              apply not_in_cons in H35; destruct H35 as [_ ?].
              specialize (H33 H35 H36).
              destruct H33; [left | right]; trivial.
              remember (Znth dst prev_contents) as mom.
              destruct H33 as [? [? [? [? [? ?]]]]].
              split3; [| |split3; [| |split3]]; trivial.
              * destruct (Z.eq_dec mom u).
                1: subst mom; apply in_cons; trivial.
                simpl; right; trivial.
              * destruct H41; trivial.
              * intros. destruct (Z.eq_dec mom' u).
                -- rewrite e in *.
                   unfold VType in *.
                   rewrite H19.
                   rewrite careful_add_comm, careful_add_inf; trivial.
                   lia.
                   apply g2m_Znth2_range; trivial.
                   apply vvalid_range in H15; trivial.
                -- apply H41; trivial.
                   simpl in H43; destruct H43; [lia|]; trivial.
            + unfold inv_unseen in *. intros.
              assert (n: dst <> u). {
                intro contra. apply H35.
                rewrite contra; apply in_eq.
              }
              apply not_in_cons in H35; destruct H35 as [_ ?].
              specialize (H34 H35 H36).
              destruct (Z.eq_dec m u).
              1: { unfold VType in *; rewrite e, H19, careful_add_comm, careful_add_inf; trivial.
                   apply g2m_Znth2_range; trivial.
                   apply vvalid_range in H15; trivial; lia.
              }
              apply H34; trivial.
              simpl in H38; destruct H38; [lia | trivial].
              }

        (* Now we're in the main proof. We will run through
           the for loop and relax u's neighbors when possible.
         *)
        assert (Znth u dist_contents < inf). {
          replace 8 with SIZE in H19. 2: compute; trivial.
          rewrite inf_eq2 in H19.
          apply repr_neq_e in H19.
          pose proof (Znth_dist_cases u dist_contents).
          destruct H20; trivial. 1: lia. lia.
        }
        clear H19.
        rename H20 into Hx. 
        
        remember (upd_Znth u priq_contents (inf+1)) as priq_contents_popped.
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
          (EX i : Z,
           EX prev_contents' : list VType,
           EX priq_contents' : list VType,
           EX dist_contents' : list VType,
           EX popped_verts' : list VType,
           PROP (
               (* inv_popped is not affected *)
               forall dst,
                 vvalid g dst ->
                 inv_popped g src popped_verts' prev_contents'
                            dist_contents' dst;

                 (* and, because we broke out when dist[u] = inf,
                    we know that none of the popped items have dist inf.
                    Essentially, the first disjunct of inv_popped
                    is impossible inside the for loop.
                  *)
               forall dst,
                 vvalid g dst ->
                 In dst popped_verts' ->
                 Znth dst dist_contents' <> inf;
                 
                 (* inv_unpopped is restored for those vertices
                 that the for loop has scanned and repaired *)
               forall dst,
                 0 <= dst < i ->
                 inv_unpopped g src popped_verts' prev_contents'
                              dist_contents' dst;
                 
                 (* a weaker version of inv_popped is
                    true for those vertices that the
                    for loop has not yet scanned *)
               forall dst,
                 i <= dst < SIZE ->
                 inv_unpopped_weak g src popped_verts' prev_contents'
                                   dist_contents' dst u;
                       
                   (* similarly for inv_unseen,
                      the invariant has been
                      restored until i:
                      u has been taken into account *)
               forall dst,
                 0 <= dst < i ->
                 inv_unseen g popped_verts'
                            dist_contents' dst;

                 (* and a weaker version of inv_unseen is
                    true for those vertices that the
                    for loop has not yet scanned *)
               forall dst,
                 i <= dst < SIZE ->
                 inv_unseen_weak g popped_verts' 
                                 dist_contents' dst u;
                 (* further, some useful facts about src... *)
                 Znth src dist_contents' = 0;
                 Znth src prev_contents' = src;
                 (* Znth src priq_contents' <> inf; *)
                 1 = 1;
                 
                 (* a useful fact about u *)
                 In u popped_verts';
                 
                 (* A fact about the relationship b/w 
                    dist and priq arrays *)
               forall dst,
                 vvalid g dst ->
                 ~ In dst popped_verts' ->
                 Znth dst priq_contents' = Znth dst dist_contents';
                       
                 (* and ranges of the three arrays *)
                 inrange_prev prev_contents';
                 inrange_priq priq_contents';
                 inrange_dist dist_contents')
                
                LOCAL (temp _u (Vint (Int.repr u));
                       temp _dist (pointer_val_val dist);
                       temp _prev (pointer_val_val prev);
                       temp _src (Vint (Int.repr src));
                       lvar _pq (tarray tint SIZE) v_pq;
                       temp _graph (pointer_val_val arr))
                SEP (data_at Tsh
                             (tarray tint SIZE)
                             (map Vint (map Int.repr prev_contents'))
                             (pointer_val_val prev);
                     data_at Tsh
                             (tarray tint SIZE)
                             (map Vint (map Int.repr priq_contents')) v_pq;
                     data_at Tsh
                             (tarray tint SIZE)
                             (map Vint (map Int.repr dist_contents'))
                             (pointer_val_val dist);
                     DijkGraph sh (graph_to_mat g) (pointer_val_val arr))).
        -- unfold SIZE; rep_lia.
        -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
          (* We must prove the for loop's invariants for i = 0 *)
          Exists prev_contents.
          Exists priq_contents_popped.
          Exists dist_contents.
          Exists (u :: popped_verts).
          repeat rewrite <- upd_Znth_map.
          entailer!.
          remember (find priq_contents
                         (fold_right Z.min (hd 0 priq_contents)
                                     priq_contents) 0) as u. 
          split3; [| | split3; [| |split3]]; trivial.
          ++ (* We must show inv_popped for all
                dst that are in range. *)
            unfold inv_popped. intros.
            rename H32 into temp.
            rename H15 into H32.
            rename temp into H15.
            destruct (H4 dst H32) as [? [? ?]].
            unfold inv_popped in H33.
            (* now we must distinguish between those
                 vertices that were already popped
                 and u, which was just popped
             *)
            destruct (Z.eq_dec dst u).
            ** (* show that u is a valid entrant *)
              subst dst.
              unfold inv_unpopped in H34.
              assert (Znth u dist_contents < inf). {
                trivial.
              }
              specialize (H34 H18 H36).
              destruct H34.
              1: { (* src is being popped *)
                rewrite H34 in *.
                right.
                exists (u, []); split3; trivial.
                - split3; [| | split3]; trivial.
                  + simpl. destruct H2 as [? [? [? ?]]].
                    red in H2. rewrite H2. lia.
                  + split; trivial.
                  + split; trivial.
                  + rewrite Forall_forall; intros.
                    simpl in H37. lia.
                - unfold path_in_popped. intros. destruct H37.
                  + simpl in H37.
                    rewrite H37, H34; split; trivial.
                  + destruct H37 as [? [? ?]].
                    simpl in H37; lia.
                - unfold path_globally_optimal; intros.
                  unfold path_cost at 1; simpl.
                  apply path_cost_pos; trivial.
              }
              destruct H34 as [? [? [? [? [? ?]]]]].
              unfold VType in *.
              remember (Znth u prev_contents) as mom.
              assert (Htemp : True) by trivial.
              destruct (popped_noninf_has_path H2 H4 Htemp H38) as [p2mom [? [? ?]]]; trivial.
              1: { assert (0 <= Znth u (Znth mom (graph_to_mat g))). {
                     apply g2m_Znth2_range; trivial. 
                     apply vvalid_range in H37; trilia.
                   }
                   ulia.
              }

              (* this the best path to u:
                    go, optimally, to mom, and then take one step
               *)
              right.
              exists (fst p2mom, snd p2mom +:: (mom, u)).

              assert (vvalid g mom). { trivial. }
              split3; trivial.
              --- destruct H42 as [? [? [? [? ?]]]].
                  assert (path_cost g p2mom + elabel g (mom, u) < inf).
                  { rewrite elabel_Znth_graph_to_mat; trivial; simpl.
                    2: apply vvalid2_evalid; trivial.
                    ulia.
                  }
                  destruct H46.
                  split3; [| | split3]; trivial.
                  +++ apply valid_path_app_cons; trivial;
                        try rewrite <- surjective_pairing; trivial.
                      apply vvalid2_evalid; trivial.
                  +++
                    rewrite (surjective_pairing p2mom) in *.
                    simpl.
                    replace (fst p2mom) with src in *.
                    apply path_ends_app_cons; trivial. 
                    split; trivial.
                  +++ 
                    rewrite path_cost_app_cons; trivial.
                    ulia.
                    all: apply vvalid2_evalid; trivial.
                  +++ unfold VType in *.
                      rewrite path_cost_app_cons, elabel_Znth_graph_to_mat; trivial.
                      1: lia.
                      1,3: apply vvalid2_evalid; trivial.
                      ulia.
                  +++ rewrite Forall_forall. intros.
                      rewrite Forall_forall in H49.
                      apply in_app_or in H52.
                      destruct H52.
                      *** specialize (H49 _ H52). trivial.
                      *** simpl in H52.
                          destruct H52; [| lia].
                          rewrite (surjective_pairing x) in *.
                          inversion H52.
                          simpl.
                          rewrite <- H54, <- H55.
                          ulia.
              --- unfold path_in_popped. intros.
                  destruct H42 as [_ [? _]].
                  apply (in_path_app_cons _ _ _ src) in H46; trivial.
                  destruct H46.
                  +++ specialize (H43 _ H46).
                      destruct H43 as [? Hb].
                      split; trivial.
                      simpl. right; trivial.
                  +++ subst step. split; simpl; trivial.
              --- (* We must show that the locally optimal path via mom
                        is actually the globally optimal path to u *)
                unfold path_globally_optimal; intros.
                unfold path_globally_optimal in H44.
                destruct H42 as [? [? [? [? ?]]]].
                assert (evalid g (mom, u)) by
                    (apply vvalid2_evalid; trivial).
                rewrite path_cost_app_cons; trivial.
                2: rewrite elabel_Znth_graph_to_mat; simpl; trivial; ulia.
                rewrite elabel_Znth_graph_to_mat; trivial.
                simpl.
                destruct (Z_le_gt_dec
                            (path_cost g p2mom
                             + Znth u (Znth mom (graph_to_mat g)))
                            (path_cost g p')); auto.
                apply Z.gt_lt in g0.
                destruct (zlt (path_cost g p') inf).
                2: ulia.
                 
                assert (exists p1 mom' child' p2,
                           path_glue p1 (path_glue (mom', [(mom',child')]) p2) = p' /\
                           valid_path g p1 /\ 
                           valid_path g p2 /\
                           path_ends g p1 src mom' /\
                           path_ends g p2 child' u /\
                           In mom' popped_verts /\
                           ~ In child' popped_verts /\
                           evalid g (mom', child') /\
                           path_cost g p1 < inf /\
                           0 <= Znth child' (Znth mom' (graph_to_mat g)) < inf /\
                           path_cost g p2 + Znth child' (Znth mom' (graph_to_mat g)) < inf).
                {
                  
                  assert (In src popped_verts). {
                    destruct H48.
                    apply H43; trivial.
                    left.
                    rewrite (surjective_pairing p2mom) in *.
                    simpl. simpl in H48. lia.
                  } 
                  rewrite (surjective_pairing p') in *.
                  remember (snd p') as links.
                  replace (fst p') with src in *.
                  2: destruct H47; simpl in H47; lia.
                  destruct (path_leaving_popped
                              g links src u popped_verts priq_contents
                              H12 H11 H2 H46 H47 H53 H18)
                    as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? ? ]]]]]]]]]]].
                  exists p1, mom', child', p2.
                  split3; [| |split3; [| |split3; [| |split3]]]; trivial.
                  rewrite <- H54 in l.
                  assert (valid_path g (mom', [(mom', child')])). {
                    simpl. unfold strong_evalid.
                    red in H2. destruct H2 as [a [b [c d]]].
                    rewrite c, d. simpl. split3; trivial.
                    apply b in H61. trivial.
                  }
                  assert (valid_path g (path_glue
                                          (mom', [(mom', child')]) p2)). {
                    apply valid_path_merge; trivial.
                    apply (path_ends_meet _ _ _ mom' child' u); trivial.
                    unfold path_ends. simpl. red in H2. destruct H2 as [_ [_ [_ ?]]].
                    rewrite H2. simpl. lia.
                  }
                  assert (path_cost g (mom', [(mom', child')]) < inf). {
                    apply path_cost_path_glue_lt in l; destruct l; trivial.
                    apply path_cost_path_glue_lt in H65; destruct H65; trivial.
                  }
                  pose proof (one_step_path_Znth _ _ _ H2 H61).
                  split3; trivial.
                  - apply path_cost_path_glue_lt in l; destruct l; trivial.
                  -
                    unfold EType, VType in *.
                    rewrite <- H65.
                    split; try lia.                           
                    apply path_cost_pos; trivial.
                  - apply path_cost_path_glue_lt in l; destruct l; trivial.
                    rewrite path_cost_path_glue in H67; trivial.
                    unfold VType in *.
                    rewrite <- H65.
                    apply careful_add_inf_clean; trivial.
                    1,2: apply path_cost_pos; trivial.
                    rewrite careful_add_comm; trivial.
                }
                
                destruct H53 as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]].
                rewrite <- H53 in g0.
                
                assert (0 <= path_cost g (mom', [(mom', child')]) < inf). {
                  rewrite one_step_path_Znth; trivial.
                  
                }
                (* unfold VType in *. *)
                do 2 rewrite path_cost_path_glue in g0; trivial; [|ulia].
                rewrite careful_add_clean in g0; trivial; try lia;
                  try apply path_cost_pos; trivial.
                rewrite careful_add_clean in g0; trivial; try lia;
                  try apply path_cost_pos; trivial.
                2: {
                  unfold path_cost at 1. simpl.
                  rewrite careful_add_comm, careful_add_id.
                  rewrite elabel_Znth_graph_to_mat; trivial; simpl; trivial; lia.
                }
                2: {
                  apply careful_add_pos; apply path_cost_pos; trivial.
                  simpl.
                  red in H2. destruct H2 as [? [? [? ?]]].
                  unfold strong_evalid.
                  rewrite H66, H67; simpl.
                  split3; [| | split]; trivial;
                    apply H65 in H60; destruct H60; trivial.
                }
                2: {
                  rewrite <- H53 in l.
                  rewrite path_cost_path_glue in l; trivial.
                  assert (valid_path g (path_glue (mom', [(mom', child')]) p2)). {
                    Opaque valid_path.
                    unfold path_glue. simpl.
                    rewrite valid_path_cons_iff.
                    red in H2. destruct H2 as [? [? [? ?]]].
                    unfold strong_evalid.
                    rewrite H66, H67. simpl.
                    split3; trivial.
                    - split3; trivial.
                      + apply (valid_path_valid _ p1); trivial.
                        destruct H56. apply pfoot_in; trivial.
                      + apply (valid_path_valid _ p2); trivial.
                        destruct H57.
                        rewrite (surjective_pairing p2) in *.
                        simpl in H57. rewrite H57 in *.
                        unfold In_path. left. simpl; trivial.
                    - rewrite (surjective_pairing p2) in *.
                      simpl. replace (fst p2) with child' in H55; trivial.
                      destruct H57. simpl in H57. lia.
                      Transparent valid_path.
                  }
                  rewrite careful_add_clean in l; try apply path_cost_pos; trivial.
                  2: apply careful_add_inf_clean; trivial;
                    apply path_cost_pos; trivial.
                  rewrite path_cost_path_glue in l; trivial.
                  rewrite one_step_path_Znth; trivial; lia.
                }

                unfold path_cost at 2 in g0. simpl in g0.
                rewrite careful_add_clean in g0; [|lia| |].
                2: { rewrite elabel_Znth_graph_to_mat; simpl; trivial.
                     rewrite one_step_path_Znth in H64; trivial. lia.
                }
                2: rewrite elabel_Znth_graph_to_mat; simpl; trivial; lia.

                rewrite Z.add_0_l in g0.
                rewrite elabel_Znth_graph_to_mat in g0 by assumption.
                rewrite Z.add_assoc in g0. 

                (* mom' is optimal, and so we know that there exists a 
                   path p2mom', the global minimum from src to mom' *)
                assert (vvalid g mom'). {
                  destruct H2 as [_ [? _]].
                  red in H2. rewrite H2 in H60.
                  destruct H60; trivial.
                }
                destruct (H4 mom' H65) as [? _].
                unfold inv_popped in H66.
                destruct (H66 H58).
                1: {
                  destruct H67.
                  destruct (H68 u); trivial.
                  specialize (H70 H18).
                  ulia.
                }
                exfalso.
                
                destruct H67 as [p2mom' [? [? ?]]].
                (* and path_cost of p2mom' will be <= that of p1 *)
                pose proof (H69 p1 H54 H56).  
                
                assert (path_cost g p2mom'
                        + Znth child' (Znth mom' (graph_to_mat g))
                        + path_cost g p2 <
                        path_cost g p2mom
                        + Znth u (Znth mom (graph_to_mat g))). {     
                  apply (Z.le_lt_trans _
                                       (path_cost g p1
                                        + Znth child' (Znth mom' (graph_to_mat g))
                                        + path_cost g p2) _); trivial.
                  do 2 rewrite <- Z.add_assoc.
                  apply Zplus_le_compat_r; trivial.
                }
                
                (* we can show that child' <> u *)
                assert (0 <= path_cost g p2) by
                    (apply (path_cost_pos g); trivial).
                assert (child' <> u). { 
                  intro. subst child'.
                  destruct H41.
                  specialize (H73 _ H65).
                  destruct H67 as [? [? [? [? ?]]]].
                  destruct (zlt ((Znth mom' dist_contents)
                                 + (Znth u (Znth mom' (graph_to_mat g)))) inf).                  
                  2: {
                    apply Z.lt_asymm in H71. apply H71.
                    rewrite careful_add_dirty in H73; trivial; ulia.
                  }
                  unfold VType in *.
                  rewrite careful_add_clean in H73; trivial.
                  - specialize (H73 H58). lia.
                  - rewrite H76; apply path_cost_pos; trivial.
                  - rewrite <- elabel_Znth_graph_to_mat; trivial.
                    apply inrange_graph_cost_pos; trivial.
                }
                
                assert (vvalid g child'). {
                  destruct H2 as [_ [? _]]. red in H2.
                  rewrite H2 in H60. destruct H60; trivial.
                }
                  
                destruct H67 as [? [? [? [? ?]]]].
                (* now we know that child' is not minimal, and thus... *)
                assert (Znth u dist_contents <=
                        Znth mom' dist_contents
                        + Znth child' (Znth mom' (graph_to_mat g))).
                {
                  assert (0 <= child' < Zlength priq_contents). {
                    apply vvalid_range in H74; trivial; lia.
                  }
                  rewrite (get_popped_meaning _ priq_contents) in H59; trivial.

                  apply (Forall_Znth _ _ _ H79) in H11.
                  simpl in H11.
                  destruct H11 as [_ ?].
                  apply Z.lt_eq_cases in H11.
                  destruct H11; [|exfalso; lia].
                  apply Z.lt_succ_r in H11.
                  apply Z.lt_eq_cases in H11.
                  assert (In_path g src p2mom'). {
                    destruct H75. left.
                    rewrite (surjective_pairing p2mom') in *; simpl.
                    simpl in H75; lia.
                  }

                  assert (Znth mom' dist_contents +
                          (Znth child' (Znth mom' (graph_to_mat g))) < inf). {
                    ulia.
                  }
                  
                  destruct H11.
                  - (* priq[child'] < inf *)
                    destruct (H4 _ H74) as [_ [H82 _]].
                    rewrite <- (get_popped_meaning popped_verts) in H59; trivial.
                    rewrite H8 in H11; trivial.
                    specialize (H82 H59 H11).
                    destruct H82. 
                    1: {
                      specialize (H68 _ H80).
                      rewrite <- H82  in H68.
                      destruct H68.
                      exfalso.
                      apply H59; trivial.
                    } 
                    destruct H82 as [? [? [Hc [? [? [? ?]]]]]].
                    specialize (H87 mom' H65 H58).
                    rewrite careful_add_clean in H87; trivial; try lia.
                    2: {
                      apply (Forall_Znth _ _ mom') in H10.
                      simpl in H10.
                      ulia. apply vvalid_range in H65; trivial; lia.
                    }
                    
                    apply Z.le_trans with (m := Znth child' dist_contents); trivial.
                    repeat rewrite <- H8; trivial.
                    rewrite Hequ.
                    rewrite Znth_find.
                    1: { apply fold_min_general.
                         apply Znth_In.
                         apply vvalid_range in H74; trivial; lia.
                    }
                    apply min_in_list.
                    1: apply incl_refl.
                    rewrite <- Znth_0_hd; [apply Znth_In|]; lia.
                  - destruct (H4 _ H74) as [_ [_ ?]].
                    assert (Ha: ~ In child' popped_verts). {
                      rewrite (get_popped_meaning _ priq_contents); lia.
                    }
                    rewrite H8 in H11; trivial.
                    specialize (H82 Ha H11 mom' H65 H58).
                    apply careful_add_clean in H81; trivial.
                    rewrite <- H81.
                    unfold VType in *. rewrite H82.
                    lia.
                    apply (Forall_Znth _ _ mom') in H10.
                    simpl in H10.
                      ulia. apply vvalid_range in H65; trivial; lia.
                    unfold VType in *.
                    rewrite <- elabel_Znth_graph_to_mat; trivial.
                    apply inrange_graph_cost_pos; trivial.
                }
                ulia.
            ** (* Here we must show that the
                    vertices that were popped earlier
                    are not affected by the addition of
                    u to the popped set.
                *)
              simpl in H15; destruct H15; [lia|].
              specialize (H33 H15).
              destruct H33; [left | right]; trivial.
              
              --- destruct H33; split; trivial. 
                  intros.
                  destruct (H36 _ H37).
                  destruct (Z.eq_dec m u).
                  1: { split; trivial.
                       rewrite e. intro.
                       apply not_in_cons in H40; destruct H40 as [_ ?].
                       subst m. apply H39; trivial.
                  }
                  split; trivial. intros.
                  apply not_in_cons in H40; destruct H40 as [_ ?].
                  apply H39; trivial.
              --- destruct H33 as [? [? [? ?]]].
                  exists x. split3; trivial.
                  unfold path_in_popped.
                  intros.
                  specialize (H36 _ H38).
                  destruct H33.
                  destruct H36 as [? He].
                  split; trivial.
                  simpl. right; trivial.
          ++ intros.
             destruct (Z.eq_dec dst u).
             1: subst dst; ulia.
             simpl in H32; destruct H32; [lia|].
             intro.
             
             destruct (H4 dst) as [? _]; trivial.
             specialize (H34 H32).
             destruct H34.
             2: { destruct H34 as [? [? _]].
                  destruct H34 as [? [? [? [? ?]]]].
                  lia.
             }
             destruct H34 as [_ ?].
             assert (vvalid g u). {
               apply vvalid_range; trivial; lia.
             }
             destruct (H34 u H35).
             specialize (H37 H18). ulia.
          
          ++ (* ... in fact, any vertex that is
                 "seen but not popped"
                 is that way without the benefit of u.

                 We will be asked to provide a locally optimal
                 path to such a dst, and we will simply provide the
                 old one best-known path
              *)
            unfold inv_unpopped_weak. intros.
            assert (n: dst <> u). {
              intro. subst dst; simpl in H32; lia.
            }
            apply not_in_cons in H32; destruct H32 as [_ ?].
            rewrite <- (vvalid_range g) in H15; trivial.
            destruct (H4 dst H15) as [_ [? _]].
            unfold inv_unpopped in H33.
            specialize (H34 H32 H33).
            destruct H34.
            1: subst dst; left; trivial.           
            destruct H34 as [? [? [? [? [? ?]]]]].
            unfold VType in *.
            remember (Znth dst prev_contents) as mom.
            assert (temp: True) by trivial.
            destruct (popped_noninf_has_path H2 H4 temp H36) as [p2mom [? [? ?]]]; trivial.
            1: {
              assert (0 <= Znth dst (Znth mom (graph_to_mat g))). {
                apply g2m_Znth2_range; trivial.
                apply vvalid_range in H15; trivial.
                apply vvalid_range in H35; trilia. 
              }
              unfold VType in *. lia.
            }

            (* Several of the proof obligations
               fall away easily, and those that remain
               boil down to showing that
               u was not involved in this
               locally optimal path.
             *)
            assert (mom <> u). {
              intro contra. rewrite contra in *. apply H18; trivial. 
            }
            right. split3; [| |split3; [| |split3; [| |split]]]; trivial.
            ** simpl; right; trivial.
            ** destruct H39; trivial.
            ** intros. destruct H39.
               apply H47; trivial.
               simpl in H46; destruct H46; [lia|]; trivial.
          ++ unfold inv_unseen_weak. intros.
             assert (e: dst <> u). {
               intro e. rewrite e in H32.
               simpl in H32. lia.
             }
             apply not_in_cons in H32; destruct H32 as [_ ?].
             rewrite <- (vvalid_range g) in H15; trivial.
             destruct (H4 dst H15) as [_ [_ ?]].
             apply H37; trivial.
             simpl in H35; destruct H35; [lia | trivial].
          ++ apply in_eq.
          ++ intros.
             assert (dst <> u). {
               intro. subst dst.
               apply H32, in_eq.
             }
             assert (0 <= dst < Zlength priq_contents). {
               destruct H2 as [? _]. red in H2.
                  rewrite H2 in H15. lia.
             }
             rewrite upd_Znth_diff; trivial.
             apply H8; trivial.
             apply not_in_cons in H32; destruct H32 as [_ ?]. trivial. ulia.
          ++ apply Forall_upd_Znth; trivial.
             ulia.
             rewrite <- inf_eq; rep_lia.
        -- (* We now begin with the for loop's body *)
          assert (0 <= u < Zlength (graph_to_mat g)). {
            unfold graph_to_mat.
            repeat rewrite Zlength_map.
            rewrite nat_inc_list_Zlength.
            rep_lia.
          }
          assert (Zlength (Znth u (graph_to_mat g)) = SIZE). {
            rewrite Forall_forall in H0. apply H0. apply Znth_In.
            ulia.
          }
          freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
          rewrite (graph_unfold _ _ _ u) by lia.
          Intros.
          rename H34 into H35.
          rename H33 into H34.
          rename H32 into H33.
          rename H31 into H32.
          rename H30 into H31.
          assert (H30: 1 = 1) by trivial.
          
          freeze FR2 :=
            (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                         (sublist 0 u (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g))))))
              (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                           (sublist (u + 1) (Zlength (graph_to_mat g))
                                    (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g)))))).
          unfold list_rep.
          assert_PROP (force_val
                         (sem_add_ptr_int tint Signed
                                          (force_val (sem_add_ptr_int (tarray tint SIZE) Signed (pointer_val_val arr) (Vint (Int.repr u))))
                                          (Vint (Int.repr i))) = field_address (tarray tint SIZE) [ArraySubsc i] (list_address (pointer_val_val arr) u SIZE)). {
            entailer!.
            unfold list_address. simpl.
            rewrite field_address_offset.
            1: rewrite offset_offset_val; simpl; f_equal; rep_lia.
            destruct H39 as [? [? [? [? ?]]]].
            unfold field_compatible; split3; [| | split3]; auto.
            unfold legal_nested_field; split; [auto | simpl; lia].
          }
          forward. thaw FR2.
          gather_SEP
            (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                         (sublist 0 u (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g))))))
            (data_at sh (tarray tint SIZE)
                     (map Vint (map Int.repr (Znth u (graph_to_mat g))))
                     (list_address (pointer_val_val arr) u SIZE))
            (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                         (sublist (u + 1) (Zlength (graph_to_mat g))
                                  (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g)))))).
          rewrite sepcon_assoc.
          rewrite <- graph_unfold; trivial. thaw FR.
          remember (Znth i (Znth u (graph_to_mat g))) as cost.
          assert_PROP (Zlength priq_contents' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          assert_PROP (Zlength prev_contents' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          assert_PROP (Zlength dist_contents' = SIZE). {
            entailer!. repeat rewrite Zlength_map in *. trivial. }
          assert_PROP (Zlength (graph_to_mat g) = SIZE) by entailer!.
          forward_if.
          ++ assert (0 <= cost <= Int.max_signed / SIZE). {
               replace 8 with SIZE in H41.
               assert (0 <= i < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; lia).
               assert (0 <= u < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; lia).
               specialize (H1 i u H42 H43).
               rewrite inf_eq2 in H41.
               rewrite Heqcost in *.
               rewrite Int.signed_repr in H41.
               2: { destruct H1.
                    - unfold VType in *.
                      replace SIZE with 8 in H1.
                      destruct H1.
                      pose proof (Int.min_signed_neg).
                      assert (Int.max_signed / 8 <= Int.max_signed). {
                        compute. inversion 1.
                      }
                      split; try lia.
                    - unfold VType in *.
                      rewrite H1.
                      rewrite <- inf_eq.
                      compute; split; inversion 1.
               }
               rewrite Int.signed_repr in H41.
               2: rewrite <- inf_eq; compute; split; inversion 1.
               destruct H1; unfold VType in *; lia.
             }

             
             assert (0 <= Znth u dist_contents' <= inf). {
               assert (0 <= u < Zlength dist_contents') by lia.
               apply (Forall_Znth _ _ _ H43) in H35.
               assumption.
             }
             assert (0 <= Znth i dist_contents' <= inf). {
               assert (0 <= i < Zlength dist_contents') by lia.
               apply (Forall_Znth _ _ _ H44) in H35.
               assumption.
             }
             assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
               split; [lia|].
               assert (inf <= Int.max_signed - (Int.max_signed / SIZE)). {
                 rewrite <- inf_eq. compute; inversion 1.
               }
               rep_lia.
             }
             unfold VType in *.
             forward. forward. forward_if.
             ** rewrite Int.signed_repr in H46
                 by (rewrite <- inf_eq in *; rep_lia).
                (* We know that we are definitely
                   going to make edits in the arrays:
                   we have found a better path to i, via u *)
                rename H46 into improvement.
                
                assert (Hivalid: vvalid g i). {
                  apply vvalid_range; ulia.
                }
                
                assert (~ In i (popped_verts')).
                {
                  (* This useful fact is true because
                     the cost to i was just improved.
                     This is impossible for popped items.
                   *)
                  intro.
                  destruct (H22 _ Hivalid H46).
                  - destruct H47.
                    destruct (H48 u).
                    1: apply vvalid_range; ulia.
                    rewrite careful_add_clean in H49.
                    all: ulia.
                  -  destruct H47 as [p2i [? [? ?]]].
                     unfold path_globally_optimal in H49.
                     assert (vvalid g u). {
                       apply vvalid_range; ulia.
                     }
                     destruct (H22 _ H50 H31).
                     + destruct H51. ulia.
                     + destruct H51 as [p2u [? [? ?]]].
                       specialize (H49 (fst p2u, snd p2u +:: (u,i))).
                       rewrite Heqcost in improvement.
                       destruct H51 as [? [? [? [? ?]]]].
                       destruct H47 as [? [? [? [? ?]]]].
                       unfold VType in *.
                       rewrite H60, H56 in improvement.
                       apply Zlt_not_le in improvement.
                       apply improvement.
                       rewrite path_cost_app_cons in H49; trivial.
                       2: { rewrite elabel_Znth_graph_to_mat; trivial.
                            2: { apply vvalid2_evalid; 
                                 try apply vvalid_range;
                                 trivial.
                            }
                            simpl. lia.
                       }
                       rewrite elabel_Znth_graph_to_mat in H49; trivial.
                       2: { apply vvalid2_evalid; 
                            try apply vvalid_range;
                            trivial.
                       }
                       simpl fst in H49.
                       simpl snd in H49.
                       apply H49. 
                       * destruct H54.
                         apply valid_path_app_cons;
                           try rewrite <- surjective_pairing;
                           trivial.
                         apply vvalid2_evalid;
                           try apply vvalid_range;
                           trivial.
                       * rewrite (surjective_pairing p2u) in *.
                         simpl.
                         replace (fst p2u) with src in *.
                         apply path_ends_app_cons; trivial.
                         destruct H54. simpl in H54; lia.
                       * apply vvalid2_evalid;
                           try apply vvalid_range; trivial.
                }
                
                assert (Htemp : 0 <= i < Zlength dist_contents') by lia.
                pose proof (Znth_dist_cases i dist_contents' Htemp H35).
                clear Htemp.
                rename H47 into icases.
                rewrite <- H32 in icases; trivial.

                assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
                    (repeat rewrite Zlength_map; lia).
                forward. forward. forward.
                forward; rewrite upd_Znth_same; trivial.
                1: entailer!.
                forward_call (v_pq, i, (Znth u dist_contents' + cost), priq_contents').

(* Now we must show that the for loop's invariant
   holds if we take another step,
   ie when i increments
                
   We will provide the arrays as they stand now:
   with the i'th cell updated in all three arrays,
   to log a new improved path via u 
*)
                Exists (upd_Znth i prev_contents' u).
                Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
                Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)).
                Exists popped_verts'.
                repeat rewrite <- upd_Znth_map. entailer!.
                remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                assert (u <> i) by (intro; subst; lia).
                split3; [| | split3; [| | split3; [| | split3; [| | split]]]]; intros.
                --- unfold inv_popped; intros.
                    pose proof (H22 dst H60 H61).
                    assert (n: dst <> i). {
                      intro contra.
                      rewrite contra in *.
                      apply H46; trivial.
                    }
                    assert (0 <= dst < SIZE). {
                      apply vvalid_range in H60; ulia.
                    }
                    repeat rewrite upd_Znth_diff; try lia.
                    destruct H62; [exfalso | right].
                    +++ destruct H62.
                        specialize (H23 _ H60 H61).
                        unfold VType in *. lia.
                    +++ destruct H62 as [p2dst [? [? ?]]].
                        exists p2dst. split3; trivial.
                        *** 
                          destruct H62 as [? [? [? [? ?]]]].
                          split3; [| | split3]; trivial.
                          1: unfold VType in *;
                            rewrite upd_Znth_diff; lia.
                          rewrite Forall_forall; intros.
                          assert (In_path g (snd x) p2dst). {
                            unfold In_path. right.
                            exists x. split; trivial.
                            destruct H2 as [? [? [? ?]]].
                            red in H73; rewrite H73.
                            right; trivial.
                          }
                          specialize (H64 _ H71).
                          rewrite Forall_forall in H69.
                          specialize (H69 _ H70).
                          destruct H64.
                          assert (snd x <> i). {
                            intro contra.
                            unfold VType in *.
                            rewrite contra in *.
                            apply H46; trivial; lia.
                          }
                          unfold VType in *.
                          rewrite upd_Znth_diff; try lia.
                          replace (Zlength prev_contents') with SIZE by lia.
                          rewrite <- (vvalid_range g); trivial.
                          apply (valid_path_valid _ p2dst); trivial.
                        ***
                          unfold path_in_popped. intros.
                          specialize (H64 _ H66).
                          destruct H64.
                          assert (step <> i). {
                            intro contra.
                            subst step.
                            apply H46; trivial; lia.
                          }
                          split; trivial.
                          rewrite upd_Znth_diff; trivial.
                          replace (Zlength dist_contents') with SIZE by lia.
                          rewrite <- (vvalid_range g); trivial.
                          destruct H62.
                          apply (valid_path_valid _ p2dst); trivial.
                          lia.
                    +++ unfold VType in *; lia.
                    +++ unfold VType in *; lia.
                --- 
                  destruct (Z.eq_dec dst i).
                    1: subst dst; rewrite upd_Znth_same; trivial; lia.
                    rewrite upd_Znth_diff.
                    apply H23; trivial.
                    all: trivial; try lia.
                    apply vvalid_range in H60; ulia.
                --- intros.
                    destruct (Z.eq_dec dst i).
                    +++ subst dst.
               (* This is a key change --
                i will now be locally optimal,
                _thanks to the new path via u_.

                In other words, it is moving from
                the weaker inv_unpopped clause
                to the stronger
                *)
                        unfold inv_unpopped; intros.
                        destruct (Z.eq_dec i src).
                        1: left; trivial.
                        right; split; trivial.

                        assert (Hu: vvalid g u). {
                          apply vvalid_range; ulia.
                        }
                        
                        destruct (H22 _ Hu H31).
                        1: unfold VType in *; lia.
                        clear H62.
                        unfold VType in *.
                        rewrite upd_Znth_same by lia.
                        split3; [| |split3; [| |split]]; trivial.
                        *** rewrite elabel_Znth_graph_to_mat; trivial. 
                            lia. apply vvalid2_evalid; trivial;
                                   rewrite vvalid_range; trivial.
                        *** rewrite upd_Znth_diff; trivial; lia.
                        *** rewrite upd_Znth_same; trivial; [|lia].
                            rewrite upd_Znth_diff; trivial; lia.
                        *** intros. rewrite upd_Znth_same; trivial; [|lia].
                            
 (* This is another key point in the proof:
    we must show that the path via u is
    better than all other paths via
    other popped verices *)
                            assert (mom' <> i). {
                              intro. subst mom'.
                              apply H46; trivial.
                            }
                            rewrite upd_Znth_diff; trivial.
                            2: apply vvalid_range in H62; ulia.
                            2: lia.
                            destruct (Znth_dist_cases mom' dist_contents'); trivial.
                            1: apply vvalid_range in H62; ulia. 
                            1: { rewrite H66.
                                 rewrite careful_add_comm,
                                 careful_add_inf.
                                 1: lia.
                                 assert (evalid g (mom', i)). {
                                 apply vvalid2_evalid; trivial.
                                 }
                                 rewrite <- elabel_Znth_graph_to_mat; trivial.
                                 apply inrange_graph_cost_pos; trivial.
                            }
                            rename H66 into Hk.
                            assert (H66: 1 = 1) by trivial.
                            assert (H67: 1 = 1) by trivial.

                            destruct (H22 _ H62 H64); trivial.
                            1: unfold VType in *; lia.

                            
                            destruct H68 as [p2mom' [? [? ?]]].
                            destruct H68 as [? [? [? [? ?]]]].

                            assert (In_path g mom' p2mom'). {
                              destruct H71.
                              apply pfoot_in in H75.
                              trivial.
                            }

                            
                            destruct (zlt ((Znth mom' dist_contents') + (Znth i (Znth mom' (graph_to_mat g)))) inf).
                              2: {
                                unfold VType in *.
                                destruct (zlt (Znth i (Znth mom' (graph_to_mat g))) inf).
                                - rewrite careful_add_dirty; trivial;
                                    lia.
                                - unfold careful_add.
                                  destruct (path_cost g p2mom' =? 0) eqn:?.
                                  + rewrite Z.eqb_eq in Heqb.
                                    unfold VType in *.
                                    rewrite Heqb in H73.
                                    rewrite H73. simpl.
                                    lia.
                                  + unfold VType in *.
                                    rewrite <- H73 in Heqb.
                                    rewrite Heqb.
                                    rewrite if_false_bool.
                                    rewrite if_false_bool.
                                    rewrite if_true_bool. lia.
                                    rewrite Z.leb_le. lia.
                                    rewrite orb_false_iff; split; rewrite Z.ltb_nlt.
                                    pose proof (path_cost_pos g p2mom' H2 H68 H1).
                                    unfold VType in *.
                                    lia. lia. 
                                    rewrite Z.eqb_neq. lia.
                              }
                              assert (vvalid g i). {
                                destruct H2 as [? _].
                                     red in H2; rewrite H2; trivial.
                              }

                              assert (careful_add (Znth mom' dist_contents') (Znth i (Znth mom' (graph_to_mat g)))
                                      = (Znth mom' dist_contents') + (Znth i (Znth mom' (graph_to_mat g)))). {
                                rewrite careful_add_clean; trivial.
                                - unfold VType in *;
                                    rewrite H73;
                                    apply path_cost_pos; trivial.
                                - rewrite <- elabel_Znth_graph_to_mat; trivial.
                                     apply inrange_graph_cost_pos; trivial.
                                     all: apply vvalid2_evalid; trivial.
                              }
                              
                              assert (vvalid g i). {
                                destruct H2 as [? _].
                                red in H2; rewrite H2; trivial.
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
                            ++++ (* Yes, the path p2mom' goes via u *) 
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
                                unfold VType in *.
                                rewrite H77.
                                subst mom'.
                                unfold path_globally_optimal in H64.
                                lia.
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
                              destruct icases.
                              1: {
                                (* i was unseen *)
                                assert (i <= i < SIZE) by lia.
                                rewrite H32 in H79; trivial.
                                specialize (H27 _ H80 H46 H79).
                                rewrite H27; trivial.
                                ulia.
                              }

(* Now we know that i was seen but unpopped. 
   Great, now we can employ inv_unpopped_weak. *)
                              
                              unfold VType in *.
                              rewrite H77.
                              

(* Because i is "seen", we know that 
   The best-known path to i via popped vertices is 
   already logged in dist[i]. 
   So dist[i] <= dist[mom'] + (mom', i).
 *)

                              assert (Znth i dist_contents' <= Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))). {
                                assert (i <= i < SIZE) by lia.
                                assert (0 <= mom' < SIZE). {
                                  apply vvalid_range in H62;ulia.
                                }
                                rewrite H32 in H79; trivial.
                                destruct (H25 _ H80 H46 H79).
                                - rewrite H82 at 1. rewrite H28.
                                  apply (Forall_Znth _ _ mom') in H35.
                                  2: lia.  
                                  simpl in H35.
                                  unfold VType in *.
                                  destruct (H1 _ _ H19 H81);
                                    apply Z.add_nonneg_nonneg; lia.
                                - destruct H82 as [? [? [? [? [? [? ?]]]]]].
                                  destruct H88.
                                  unfold VType in *.
                                  rewrite <- H77.
                                  apply H89; trivial.
                              }
                              
(*
  So we have 
  dist[u] + graph[u][i] <= dist[i]
                        <= dist[mom'] + (mom', i) 
                        <= path_cost p'.
 *)
                              unfold VType in *.
                              lia.
                            ++++
(* Since u is not in the path, 
   we can just tango with
   the step <> u condition from 
   inv_unpopped_weak. 
   This case is okay.
 *)
                              assert (mom' <> u). {
                                intro. rewrite <- H79 in n0.
                                apply n0.
                                apply in_path_eq_epath_to_vpath; trivial.
                              }

                              destruct icases.
                              1: {
                                (* i was unseen *)
                                assert (i <= i < SIZE) by lia.
                                rewrite H32 in H80; trivial.
                                specialize (H27 _ H81 H46 H80).
                                rewrite H27; ulia.
                              }
                              assert (i <= i < SIZE) by lia.
                              rewrite H32 in H80; trivial.
                              destruct (H25 i H81 H46 H80).
                              1: subst i; exfalso; lia.
                                destruct H82 as [_ [? [? [? [? [? ?]]]]]].
                              apply Z.lt_le_incl.
                              apply Z.lt_le_trans with (m:=Znth i dist_contents').
                              1: lia.
                              apply H87; trivial. 
                    +++ assert (0 <= dst < i) by lia.
(* We will proceed using the old best-known path for dst *)
                        specialize (H24 _ H61).
                        unfold inv_unpopped in *.
                        intros.
                        unfold VType in *;
                          rewrite upd_Znth_diff in * by lia.
                        specialize (H24 H62). destruct H24; trivial.
                        1: left; trivial.
                        destruct H24 as [? [? [? [? [? [? ?]]]]]].
                        unfold VType in *.
                        remember (Znth dst prev_contents') as mom. right.
                        split; trivial.

                        assert (Ha: Znth mom dist_contents' < inf). {
                          assert (0 <= Znth dst (Znth mom (graph_to_mat g))). {
                            apply g2m_Znth2_range; trivial.
                            lia.
                            apply vvalid_range in H64; ulia.
                          }
                          unfold VType in *.
                          lia.
                        }
                        assert (vvalid g dst). {
                          apply vvalid_range; ulia.
                        }
                        assert (mom <> i). {
                          intro. subst i. 
                          apply H46; trivial.
                        }
                        assert (0 <= mom < Zlength priq_contents'). {
                          apply vvalid_range in H64; ulia.
                        }
                        split3; [| |split3; [| |split]]; trivial.
                        *** rewrite upd_Znth_diff; lia.
                        *** repeat rewrite upd_Znth_diff; trivial; ulia.
                        *** intros.
                            assert (mom' <> i). {
                              intro contra. rewrite contra in H74.
                              rewrite (get_popped_meaning _ (upd_Znth i priq_contents' (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))))) in H74.
                              rewrite upd_Znth_same in H74; trivial.
                              ulia. lia. rewrite upd_Znth_Zlength; lia.
                            }
                            repeat rewrite upd_Znth_diff; trivial.
                            apply H69; trivial.
                            1: apply vvalid_range in H73; ulia.
                            all: lia.
                --- unfold inv_unpopped_weak. intros.
                    assert (i <= dst < SIZE) by lia.
                    destruct (Z.eq_dec dst i).
                    1: subst dst; lia.
                    unfold VType in *.
                    rewrite upd_Znth_diff in H62 by lia.
                    destruct (H25 _ H63 H61 H62); [left | right]; trivial.
                    destruct H64 as [? [? [Ha [? [? [? [? ?]]]]]]].
                    unfold VType in *.
                    rewrite upd_Znth_diff by lia.
                    remember (Znth dst prev_contents') as mom. 
                    rename H67 into Hrem.
                    assert (mom <> i). {
                      intro. subst i.
                      apply H46; trivial.
                    }
                    assert (0 <= mom < Zlength priq_contents'). {
                      apply vvalid_range in Ha; ulia.
                    }

                    split3; [| | split3; [| | split3; [| |split]]]; trivial.
                    +++ repeat rewrite upd_Znth_diff; trivial; lia.
                    +++ repeat rewrite upd_Znth_diff; trivial; try lia.
                    +++ intros.
                        assert (mom' <> i). intro contra.
                        rewrite contra in H74.
                        rewrite (get_popped_meaning _ (upd_Znth i priq_contents' (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))))), upd_Znth_same in H74; trivial.
                        unfold VType in *;
                          lia. lia. rewrite upd_Znth_Zlength; lia.
                        repeat rewrite upd_Znth_diff; trivial.
                        apply H70; trivial; try lia.
                        apply vvalid_range in H73; ulia.
                        all: lia.
                --- unfold inv_unseen; intros.
                    assert (dst <> i). {
                      intro. subst dst.
                      unfold VType in *; rewrite upd_Znth_same in H62; lia.
                    }
                    assert (0 <= dst < i) by lia.
                    rewrite upd_Znth_diff in H62; try lia.
                    rewrite upd_Znth_diff; try lia.
                    apply H26; trivial.
                    +++ apply vvalid_range in H63; ulia.
                    +++ ulia.
                    +++ intro contra. subst m.
                        rewrite (get_popped_meaning _ (upd_Znth i priq_contents' (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))))) in H64.
                        rewrite upd_Znth_same in H64.
                         unfold VType in *; lia. lia.
                         rewrite upd_Znth_Zlength; lia.
                    +++ ulia.
                    +++ ulia.
                --- unfold inv_unseen_weak; intros.
                    assert (dst <> i) by lia.
                    unfold VType in *.
                    rewrite upd_Znth_diff in H62 by lia.
                    repeat rewrite upd_Znth_diff by lia.
                    assert (i <= dst < SIZE) by lia.
                    destruct (Z.eq_dec m i).
                    1: { exfalso. subst m.
                         rewrite (get_popped_meaning _ (upd_Znth i priq_contents' (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))))) in H64.
                         rewrite upd_Znth_same in H64.
                         unfold VType in *; lia. lia.
                         rewrite upd_Znth_Zlength; lia.
                    }
                    rewrite upd_Znth_diff; trivial.
                    apply H27; trivial.
                    1: apply vvalid_range in H63; ulia.
                    all: lia.
                --- rewrite upd_Znth_diff; try lia.
                    intro. subst src; lia.
                --- rewrite upd_Znth_diff; try lia.
                    intro. subst src; lia.
                --- destruct (Z.eq_dec dst i).
                    +++ rewrite e.
                        repeat rewrite upd_Znth_same; trivial; lia.
                    +++ rewrite vvalid_range in H60; trivial.
                        repeat rewrite upd_Znth_diff; trivial; try lia.
                        apply H32; trivial.
                        rewrite vvalid_range; trivial.
                --- split3; apply Forall_upd_Znth; trivial; try lia.
             ** rewrite Int.signed_repr in H46
                 by (rewrite <- inf_eq in *; rep_lia).
                (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                rename H46 into improvement.
                forward. 
                (* The old arrays are just fine. *)
                Exists prev_contents' priq_contents' dist_contents' popped_verts'.
                entailer!.
                remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                split3; [| |split].
                --- intros.
                    (* Show that moving one more step
                       still preserves the for loop invariant *)
                    destruct (Z.eq_dec dst i).
                    (* when dst <> i, all is well *)
                    2: apply H24; lia.
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
                    destruct (H25 i H60 H58 H59).
                    1: left; trivial.
                    destruct H61 as [? [? [? [? [? [? ?]]]]]].
                    unfold VType in *.
                    remember (Znth i prev_contents') as mom.
                    destruct (Z.eq_dec i src); [left | right]; trivial.
                    split; trivial.
                    split3; [| |split3; [| |split]]; trivial.
                    1: destruct H67; trivial.
                    intros.
                    pose proof (Znth_dist_cases mom' dist_contents').
                    rename H70 into e.
                    destruct e as [e | e]; trivial.
                    1: apply vvalid_range in H68; ulia.
                    1: {
                      rewrite e.
                      rewrite careful_add_comm,
                      careful_add_inf.
                      lia.
                      assert (evalid g (mom', i)). {
                        apply vvalid2_evalid; trivial.
                        apply vvalid_range; trivial.
                      }
                      rewrite <- elabel_Znth_graph_to_mat; trivial.
                      apply inrange_graph_cost_pos; trivial.
                    }
                    assert (Hb: vvalid g mom'). {
                      apply vvalid_range; trivial.
                      apply vvalid_range in H68; ulia.
                    }
                    destruct (H22 _ H68 H69); [unfold VType in *; ulia|].
                    
                    destruct H70 as [p2mom' [? [? ?]]].
                    assert (Hrem := H70).

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
                        
                    *** destruct H70 as [? [? [? [? ?]]]].
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
                              specialize (H71 _ i0).
                              rename p2mom' into p2u.
                              unfold path_globally_optimal in H70.
                              apply Z.ge_le in improvement.

                              destruct (zlt (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))) inf).
                              ++++ rewrite careful_add_clean; try lia; trivial.

                                   
                              ++++ rewrite careful_add_dirty; trivial.
                                   lia.
                                   
                                   replace 8 with SIZE in H41 by lia.
                                   rewrite inf_eq2 in H41.
                                   rewrite Int.signed_repr in H41.
                                   2: rep_lia.
                                   rewrite Int.signed_repr in H41.
                                   2: { rewrite <- inf_eq.
                                        unfold VType in *.
                                        unfold Int.min_signed, Int.max_signed.
                                        unfold Int.half_modulus.
                                        simpl. lia.
                                   }
                                   lia.
                        ----
                          destruct Hrem as [? [? [? [? ?]]]].
                          
                          assert (In_path g mom' p2mom'). {
                            destruct H78.
                            apply pfoot_in in H82. 
                            trivial.
                          }

                          destruct (zlt (Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))) inf).
                          2: {
                            unfold VType in *.
                            destruct (zlt (Znth i (Znth mom' (graph_to_mat g))) inf).
                            - rewrite careful_add_dirty; trivial;
                                lia.
                            - unfold careful_add.
                              destruct (Znth mom' dist_contents' =? 0) eqn:?.
                              + unfold VType in *. lia.
                              + unfold VType in *.
                                rewrite if_false_bool.
                                rewrite if_false_bool.
                                rewrite if_true_bool. lia.
                                rewrite Z.leb_le. lia.
                                rewrite orb_false_iff; split; rewrite Z.ltb_nlt.
                                pose proof (path_cost_pos g p2mom' H2 H70 H1).
                                unfold VType in *.
                                lia. lia. 
                                rewrite Z.eqb_neq. lia.
                          }                              
                          assert (vvalid g i). {
                            destruct H2 as [? _].
                            red in H2; rewrite H2; trivial.
                          }
                          assert (vvalid g mom'). {
                            apply (valid_path_valid g p2mom'); trivial.
                          }
                          assert (careful_add (Znth mom' dist_contents') (Znth i (Znth mom' (graph_to_mat g))) = Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))). {
                            rewrite careful_add_clean; trivial.
                            - unfold VType in *; rewrite H75. apply path_cost_pos; trivial.
                            - rewrite <- elabel_Znth_graph_to_mat; trivial.
                              apply inrange_graph_cost_pos; trivial.
                              all: apply vvalid2_evalid; trivial.
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
                          unfold VType in *.
                          rewrite H85.
                          
(* 
   Since i has been "seen", 
   we have dist[i] <= dist[mom'] + (mom', i)
   because of inv_unpopped_weak 
 *)
                          assert (0 <= mom' < SIZE). {
                            apply vvalid_range in H84; ulia.
                          }
                          destruct (H25 _ H60 H58 H59).
                          ++++ rewrite H87 at 1.
                               rewrite H28.
                               apply (Forall_Znth _ _ mom') in H35.
                               2: lia.  
                               simpl in H35.
                               unfold VType in *.
                               destruct (H1 _ _ H19 H86);
                                 apply Z.add_nonneg_nonneg; lia.
                          ++++ destruct H87 as [? [? [? [? [? [? ?]]]]]].
                               destruct H93.
                               specialize (H94 _ n0 H68 H69).
                               unfold VType in *;
                               rewrite H85 in H94; trivial.

                    ***

(* 2. ~ In u p': This is an easy case.
   dist[i] < path_cost p' because of Inv2.
 *)
                      apply H67; trivial.
                      intro. apply n0.
                      destruct H70 as [? [? [? [? ?]]]].
                      rewrite in_path_eq_epath_to_vpath; trivial.
                      destruct H74.
                      apply pfoot_in in H78. rewrite H73 in *. trivial.           
                --- intros. destruct (Z.eq_dec dst i).
                    +++ subst dst. lia.
                    +++ apply H25; lia.
                --- unfold inv_unseen; intros.
                    destruct (Z.eq_dec dst i).
                    2: apply H26; ulia.                     
                    subst dst.
                    assert (i <= i < SIZE) by lia.
                    destruct (Z.eq_dec m u).
                    2: apply H27; trivial.
                    subst m.
                    unfold VType in *.
                    rewrite H59 in improvement.
                    assert (0 <= u < SIZE) by lia.
                    assert (vvalid g u). {
                      destruct H2 as [? _]. red in H2. rewrite H2. lia.
                    }
                    destruct (Znth_dist_cases u dist_contents'); trivial.
                    1: lia.
                    all: rename H65 into e.
                    1: { rewrite e.
                         rewrite careful_add_comm,
                         careful_add_inf; trivial.
                         assert (evalid g (u, i)). {
                         apply vvalid2_evalid; trivial;
                           apply vvalid_range; trivial.
                         }
                         rewrite <- elabel_Znth_graph_to_mat; trivial.
                         apply inrange_graph_cost_pos; trivial.
                    }

                    destruct (zlt (Znth i (Znth u (graph_to_mat g))) inf).
                    1: apply careful_add_dirty; trivial; lia.
                    assert (Znth i (Znth u (graph_to_mat g)) = inf). {
                      assert (Int.max_signed / SIZE < inf) by (rewrite <- inf_eq; now compute). 
                      unfold inrange_graph in H1;
                        destruct (H1 _ _ H19 H63); trivial.
                      replace 8 with SIZE in H41 by lia.
                      rewrite inf_eq2 in H41.
                      rewrite Int.signed_repr in H41.
                      2: { unfold VType in *. replace SIZE with 8 in H55, H54.
                           unfold Int.min_signed, Int.max_signed, Int.half_modulus in *.
                           simpl. simpl in H55, H54.
                           assert (2147483647 / 8 < 2147483647) by now compute.
                           lia.
                      }
                      rewrite Int.signed_repr in H41.
                      2: rewrite <- inf_eq; rep_lia.
                      unfold VType in *; lia.
                    }
                    unfold VType in *; rewrite H65.
                    rewrite careful_add_inf; trivial; lia.
                --- intros.
                    assert (i <= dst < SIZE) by lia.
                    apply H27; trivial.
          ++  (* i was not a neighbor of u.
                 We must prove the for loop's invariant holds *)
            replace 8 with SIZE in H41 by lia.
            rewrite inf_eq2 in H41.
            forward.
            Exists prev_contents' priq_contents' dist_contents' popped_verts'.
            entailer!.
            remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
            assert (Znth i (Znth u (graph_to_mat g)) = inf). {
              assert (0 <= i < SIZE) by lia.
              assert (0 <= u < SIZE) by lia.
              assert (Int.max_signed / SIZE < inf) by now compute. 
              unfold inrange_graph in H1;
                destruct (H1 _ _ H15 H54); trivial.
              rewrite Int.signed_repr in H41.
              2: { unfold VType in *. replace SIZE with 8 in H55, H56.
                   unfold Int.min_signed, Int.max_signed, Int.half_modulus in *.
                   simpl. simpl in H55, H56.
                   assert (2147483647 / 8 < 2147483647) by now compute.
                   lia.
              }
              rewrite Int.signed_repr in H41.
              2: rewrite <- inf_eq; rep_lia.
              unfold VType in *; lia.
            }
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
                   destruct (H25 i H57 H55 H56).
                   1: left; trivial.
                   destruct H58 as [? [? [? [? [? [? ?]]]]]].
                   unfold VType in *.
                   remember (Znth i prev_contents') as mom.

                   assert (Ha: Znth mom dist_contents' < inf). {
                     assert (0 <= Znth i (Znth mom (graph_to_mat g))). {
                       apply g2m_Znth2_range; trivial.
                       apply vvalid_range in H60; ulia.
                          }
                          unfold VType in *.
                          lia.
                        }
                   
                   destruct (H22 _ H60 H61); [unfold VType in *;lia|].
                   destruct H65 as [p2mom [? [? ?]]].
                   
                   right. split.
                   1: { assert (In src (popped_verts')). {
                          assert (In_path g src p2mom). {
                         left. destruct H65 as [_ [[? _] _]].
                         destruct p2mom. 
                         now simpl in H56 |- *.
                          }
                          specialize (H66 _ H68).
                          destruct H66;
                          destruct H65; trivial.
                          
                        }
                     intro contra. rewrite <- contra in H68.
                     rewrite get_popped_meaning in H68.
                     lia. lia.
                   }

                   split3; [| |split3; [| |split]]; trivial.
                   +++ destruct H64; trivial.
                   +++
                     intros.
                     destruct H64.
                     destruct (Znth_dist_cases mom' dist_contents') as [e | e]; trivial.
                     1: apply vvalid_range in H68; ulia.
                     1: { rewrite e.
                          rewrite careful_add_comm, careful_add_inf.
                            lia.
                            assert (evalid g (mom', i)). {
                              apply vvalid2_evalid; trivial.
                              apply vvalid_range; trivial.
                            }                               
                            rewrite <- elabel_Znth_graph_to_mat; trivial.
                            apply inrange_graph_cost_pos; trivial.
                       }
                       unfold VType in *.

                     destruct (zlt (Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))) inf).
                     2: {
                       unfold VType in *.
                       clear H64.
                       destruct (zlt (Znth i (Znth mom' (graph_to_mat g))) inf).
                       - rewrite careful_add_dirty; trivial;
                           lia.
                       - unfold careful_add.
                         destruct (Znth mom' dist_contents' =? 0) eqn:?.
                         + unfold VType in *. lia.
                         + assert (evalid g (mom', i)). {
                             apply vvalid2_evalid; trivial. apply vvalid_range; trivial. }
                           unfold VType in *.
                           rewrite if_false_bool.
                           rewrite if_false_bool.
                           rewrite if_true_bool. lia.
                           rewrite Z.leb_le. lia.
                           rewrite orb_false_iff; split; rewrite Z.ltb_nlt.
                           intro.
                           apply (Forall_Znth _ _ mom') in H35.
                           simpl in H35. lia.
                           apply vvalid_range in H68; ulia.
                           rewrite <- elabel_Znth_graph_to_mat; trivial.
                           apply Zle_not_lt.
                           apply inrange_graph_cost_pos; trivial.
                           rewrite Z.eqb_neq. lia.
                       }
                       assert (vvalid g i). {
                         destruct H2 as [? _].
                         red in H2; rewrite H2; trivial.
                       }
                       
                       assert (careful_add (Znth mom' dist_contents') (Znth i (Znth mom' (graph_to_mat g))) = Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))). {
                         rewrite careful_add_clean; trivial.
                         - apply (Forall_Znth _ _ mom') in H35.
                           simpl in H35; ulia.
                           apply vvalid_range in H68; ulia.
                         - rewrite <- elabel_Znth_graph_to_mat; trivial.
                           apply inrange_graph_cost_pos; trivial.
                           all: apply vvalid2_evalid; trivial.
                     }
                     destruct (Z.eq_dec mom' u).
                     1: { subst mom'.
                          rewrite H15, careful_add_inf. lia.
                          apply (Forall_Znth _ _ u) in H35.
                          simpl in H35; ulia.
                          lia.
                     }
                     apply H70; trivial.
               --- apply H24; lia.
            ** destruct (Z.eq_dec dst i).
               --- lia. 
               --- apply H25; lia.
            ** destruct (Z.eq_dec dst i).
               2: apply H26; lia.
               subst dst.
               assert (i <= i < SIZE) by lia.
               unfold inv_unseen; intros.
               destruct (Z.eq_dec m u).
               2: apply H27; trivial.
               subst m. rewrite H15.
               rewrite careful_add_inf; trivial.
               unfold inrange_dist in H35.
               rewrite Forall_forall in H35.
               apply H35.
               apply Znth_In. unfold VType in *; lia.
            ** apply H27; lia.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
          Intros prev_contents' priq_contents' dist_contents' popped_verts'.
          Exists prev_contents' priq_contents' dist_contents' popped_verts'.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
          unfold dijkstra_correct.
          split3; [apply H19 | apply H21 | apply H23];
            try rewrite <- (vvalid_range g); trivial.
      * (* After breaking, the while loop,
           prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H16 in H15; simpl in H15; now inversion H15.
        }
        clear H15.
        forward. Exists prev_contents priq_contents dist_contents popped_verts.
        entailer!. apply (isEmptyMeansInf _ H16).
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents popped_verts.
      forward. Exists prev_contents dist_contents popped_verts. entailer!. 
      Unshelve. trivial.
Qed.
