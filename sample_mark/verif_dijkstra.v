Require Import VST.msl.iter_sepcon.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import RamifyCoq.sample_mark.verif_priorityqueue.
Require Import Coq.Lists.List.
Require Import RamifyCoq.sample_mark.priq_utils.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_macros.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_spec.
Require Import VST.floyd.sublist.


(* We must use the CompSpecs and Vprog that were
   centrally defined in dijksta's environment. 
   This lets us be consistent and call PQ functions in Dijkstra. 
 *)
Local Definition CompSpecs := env_dijkstra_arr.CompSpecs.
Local Definition Vprog := env_dijkstra_arr.Vprog.
Local Definition Gprog := dijk_pq_arr_spec.Gprog.

Local Open Scope Z_scope.

(** CONSTANTS AND RANGES **)

Lemma inf_eq: 1879048192 = inf.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute; trivial. Qed.

Definition inrange_prev prev_contents :=
  Forall (fun x => 0 <= x < SIZE \/ x = inf) prev_contents.

Definition inrange_priq priq_contents :=
  Forall (fun x => 0 <= x <= inf+1) priq_contents.

Definition inrange_dist dist_contents :=
  Forall (fun x => 0 <= x <= inf) dist_contents.

Lemma inrange_upd_Znth: forall (l: list Z) i new F,
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


(** LEMMAS ABOUT GET_POPPED **)

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
  simpl in H0. destruct (a =? 1879048193) eqn:?.
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
      * inversion H0. rewrite Z.eqb_eq in H1.
        rewrite <- inf_eq. rep_lia.
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
      rewrite nat_inc_list_hd by lia.
      simpl.
      destruct (a =? 1879048193) eqn:?.
      simpl; left; trivial.
      rewrite Z.eqb_neq in Heqb.
      exfalso; apply Heqb.
      rewrite Znth_0_cons in H0.
      rewrite <- inf_eq in H0. lia.
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
    exists p2mom : path,
      path_correct g prev dist src mom p2mom /\
      (forall step : VType, In_path g step p2mom -> In step (get_popped priq)) /\
      path_globally_optimal g src mom p2mom.
Proof.
  intros.
  assert (vvalid g mom). {
    apply get_popped_range in H2.
    apply vvalid_range; trivial. unfold VType in *. lia.
  }
  destruct (H0 _ H3) as [? _].
  specialize (H4 H2). trivial.
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
          graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
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
    forward. forward. forward.
    (* Special values for src have been inserted *)

    (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
     *)
    forward_loop
      (EX prev_contents : list Z,
       EX priq_contents : list Z,
       EX dist_contents : list Z,
       PROP (
           (* The overall correctness condition *)
           dijkstra_correct g src prev_contents priq_contents dist_contents;

           (* Some special facts about src *)
           Znth src dist_contents = 0;
           Znth src prev_contents = src;
           Znth src priq_contents <> inf;

           (* A fact about the relationship b/w 
              dist and priq arrays *)
           forall dst, vvalid g dst ->
                       Znth dst priq_contents <> Z.add inf 1 ->
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
            graph_rep sh (graph_to_mat g) (pointer_val_val arr)))
      break:
      (EX prev_contents: list Z,
       EX priq_contents: list Z,
       EX dist_contents: list Z,
       PROP (
           (* This fact comes from breaking while *)
           Forall (fun x => x >= inf) priq_contents;
           (* And the correctness condition is established *)
           dijkstra_correct g src prev_contents priq_contents dist_contents)
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
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
    + Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) src).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
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
          rewrite new. rewrite <- inf_eq. lia.
        }
        split3; [| |split3; [| |split]];
         try apply inrange_upd_Znth;
         try rewrite upd_Znth_same; try lia; trivial.
        all: rewrite <- inf_eq; unfold SIZE in *; lia.
      }
      (* And now we must show dijkstra_correct for the initial arrays *)
      (* First, worth noting that _nothing_ has been popped so far *)
      assert (get_popped (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) = []).
      { apply get_popped_empty. rewrite Forall_forall; intros.
        rewrite upd_Znth_unfold in H15. 2: lia.
        apply in_app_or in H15.
        destruct H15; [| apply in_inv in H15; destruct H15].
        1,3: rewrite sublist_list_repeat in H15 by lia;
          apply in_list_repeat in H15; lia.
        rewrite <- H15. compute; lia.
      }
      (* Now we get into the proof of dijkstra_correct proper.
         This is not very challenging... *)
      unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen.
      rewrite H15. split3; intros.
      * inversion H17.
      * unfold VType in *.
        assert (src = dst). {
          destruct (Z.eq_dec src dst); trivial. exfalso.
          assert (0 <= dst < SIZE) by
              (rewrite <- (vvalid_range g); trivial).
          rewrite upd_Znth_diff in H17; try lia.
          rewrite Znth_list_repeat_inrange in H17; lia.
        }
        subst dst. left; trivial.
      * split3; trivial.
        assert (0 <= dst < SIZE) by
            (rewrite <- (vvalid_range g dst); trivial).
        rewrite upd_Znth_diff; try lia.
        rewrite Znth_list_repeat_inrange. trivial. lia.
        intro. subst dst. rewrite upd_Znth_same in H17.
        inversion H17. lia.
        inversion 1.
    + (* Now the body of the while loop begins. *)
      Intros prev_contents priq_contents dist_contents.
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
        assert (0 <= u < Zlength priq_contents). {
          rewrite H15.
          apply find_range.
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H12.
          inversion H12. simpl. left; trivial.
        }
        rewrite Znth_0_hd, <- H15 by lia.
        do 2 rewrite upd_Znth_map.
        assert (~ (In u (get_popped priq_contents))). {
          intro.
          rewrite get_popped_meaning in H18 by lia.
          rewrite <- isEmpty_in' in H16.
          destruct H16 as [? [? ?]].
          rewrite H15 in H18.
          rewrite Znth_find in H18.
          2: {
            rewrite <- Znth_0_hd by (unfold SIZE in *; lia).
            apply min_in_list;
              [ apply incl_refl | apply Znth_In; unfold SIZE in *; lia].
          }
          pose proof (fold_min _ _ H16).
          lia.
        }

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
           EX prev_contents' : list Z,
           EX priq_contents' : list Z,
           EX dist_contents' : list Z,
           PROP (
               (* popped items are not affected by the for loop *)
               forall dst, inv_popped g src prev_contents'
                                      priq_contents' dist_contents' dst;
              (* inv_unpopped is restored for those vertices
                 that the for loop has scanned and repaired *)
               forall dst,
                 0 <= dst < i ->
                 inv_unpopped g src prev_contents'
                              priq_contents' dist_contents' dst;
                 
                 (* a weaker version of inv_popped is
                    true for those vertices that the
                    for loop has not yet scanned *)
                 forall dst,
                   i <= dst < SIZE ->
                   inv_unpopped_weak g src prev_contents'
                                     priq_contents' dist_contents' dst u;
                       
                   (* similarly for inv_unseen,
                      the invariant has been
                      restored until i:
                      u has been taken into account *)
                   forall dst,
                     0 <= dst < i ->
                     inv_unseen g prev_contents'
                                priq_contents' dist_contents' dst;
                     (* and a weaker version of inv_unseen is
                        true for those vertices that the
                        for loop has not yet scanned *)
                     forall dst,
                       i <= dst < SIZE ->
                       inv_unseen_weak g prev_contents'
                                       priq_contents' dist_contents' dst u;
                     (* further, some useful facts about src... *)
                       Znth src dist_contents' = 0;
                       Znth src prev_contents' = src;
                       Znth src priq_contents' <> inf;
                       
                     (* a few useful facts about u *)
                       In u (get_popped priq_contents');
                       
                     (* A fact about the relationship b/w 
                        dist and priq arrays *)
                       forall dst, vvalid g dst ->
                       Znth dst priq_contents' <> Z.add inf 1 ->
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
                     graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
        -- unfold SIZE; rep_lia.
        -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
          (* We must prove the for loop's invariants for i = 0 *)
          Exists prev_contents.
          Exists priq_contents_popped.
          Exists dist_contents.
          repeat rewrite <- upd_Znth_map.
          entailer!.
          remember (find priq_contents
                         (fold_right Z.min (hd 0 priq_contents)
                                     priq_contents) 0) as u. 
          split3; [| | split3; [| |split3]]; trivial. 
          ++ (* We must show inv_popped for all
                 dst that are in range. *)
            unfold inv_popped. intros.
            pose proof (get_popped_range _ _ H15).
            rewrite upd_Znth_Zlength in H32 by lia.
            rewrite H12 in H32.
            rewrite <- (vvalid_range g) in H32.
            destruct (H4 dst H32) as [? [? ?]].
            unfold inv_popped in H33.
            (* now we must distinguish between those
                 vertices that were already popped
                 and u, which was just popped
             *)
            destruct (Z.eq_dec dst u).
            **  (* show that u is a valid entrant *)
              subst dst.
              unfold inv_unpopped in H34.
              assert (Znth u priq_contents < inf).
              { apply find_min_lt_inf; auto. unfold SIZE in H11. lia. }
              specialize (H34 H36).
              destruct H34.
              1: { (* src is being popped *)
                rewrite H34 in *.
                exists (u, []); split3.
                - split3; [| | split3]; trivial.
                  + simpl. destruct H2 as [? [? [? ?]]].
                    red in H2. rewrite H2. lia.
                  + split; trivial.
                  + unfold path_cost. simpl. rewrite <- inf_eq. lia.
                  + rewrite Forall_forall; intros.
                    simpl in H37. lia.
                - intros. destruct H37.
                  + simpl in H37. rewrite H37, H34; trivial.
                  + destruct H37 as [? [? ?]].
                    simpl in H37; lia.
                - unfold path_globally_optimal; intros.
                  unfold path_cost at 1; simpl.
                  apply path_cost_pos; trivial.
              }
              destruct H34 as [? [? [? [? [? ?]]]]].
              unfold VType in *.
              remember (Znth u prev_contents) as mom.
              destruct (get_popped_path H2 H4 H12 H37) as [p2mom [? [? ?]]].              
              (* this the best path to u:
                    go, optimally, to mom, and then take one step
               *)
              exists (fst p2mom, snd p2mom +:: (mom, u)).

              assert (vvalid g mom). {
                  pose proof (get_popped_range _ _  H37).
                  destruct H2 as [? _]. red in H2. rewrite H2.
                  unfold VType in *. lia.
              }
              unfold VType in *.

              split3; trivial.
              --- destruct H42 as [? [? [? [? ?]]]].
                  assert (path_cost g p2mom + elabel g (mom, u) < inf).
                  { rewrite elabel_Znth_graph_to_mat; trivial; simpl.
                    2: apply vvalid2_evalid; trivial.
                    unfold VType in *. lia.
                  }
                  destruct H46.
                  split3; [| | split3].
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
                    *** unfold VType in *. lia.
                    *** apply vvalid2_evalid; trivial.
                  +++
                    rewrite path_cost_app_cons; trivial.
                    rewrite elabel_Znth_graph_to_mat; simpl;
                      try lia; trivial.
                    apply vvalid2_evalid; trivial.
                    unfold VType in *. lia.
                    apply vvalid2_evalid; trivial.
                  +++ unfold VType in *.
                      rewrite Forall_forall. intros.
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
                          lia.
              --- intros.
                  destruct H42 as [_ [? _]].
                  apply (in_path_app_cons _ _ _ src) in H46; trivial.
                  destruct H46.
                  +++ specialize (H43 _ H46).
                      rewrite <- get_popped_irrel_upd; try lia; trivial.
                      apply get_popped_range in H43; lia.
                      intro. subst step. 
                      apply H18; trivial.
                  +++ subst step. rewrite get_popped_meaning.
                      rewrite upd_Znth_same; lia.
                      rewrite upd_Znth_Zlength; lia.
              --- (* We must show that the locally optimal path via mom
                        is actually the globally optimal path to u *)
(*
  When we get in the while loop, u is popped.
  We must prove that dist[u] is the global shortest.
  Since u is in pq before, u satisfies inv_unpopped.

  We can prove that dist[u] is either global shortest or not. If so, done.

  If not, the global shortest path to u
  must contain an unpopped vertex w because of inv_unpopped.

  Thus we have dist[u] > dist[w] + length(w to u).
  But wait, u is popped from pq because dist[u] is minimum.
  It is impossible to have another unpopped w satisfying
  dist[w] < dist[u].
  So the "not" case is False.
  So this pop operation maintains inv_popped for u.
 *)
                unfold path_globally_optimal; intros.
                unfold path_globally_optimal in H44.
                destruct H42 as [? [? [? [? ?]]]].
                assert (evalid g (mom, u)) by
                    (apply vvalid2_evalid; trivial).
                rewrite path_cost_app_cons; trivial.
                2: rewrite elabel_Znth_graph_to_mat; simpl; trivial; lia.
                rewrite elabel_Znth_graph_to_mat; trivial.
                simpl.
                destruct (Z_le_gt_dec
                            (path_cost g p2mom
                             + Znth u (Znth mom (graph_to_mat g)))
                            (path_cost g p')); auto.
                apply Z.gt_lt in g0.
                destruct (zlt (path_cost g p') inf).
                2: unfold VType in *; lia.
                
                exfalso.
                unfold VType in *.   
                assert (exists p1 mom' child' p2,
                           path_glue p1 (path_glue (mom', [(mom',child')]) p2) = p' /\
                           valid_path g p1 /\ 
                           valid_path g p2 /\
                           path_ends g p1 src mom' /\
                           path_ends g p2 child' u /\
                           In mom' (get_popped priq_contents) /\
                           ~ In child' (get_popped priq_contents) /\
                           evalid g (mom', child') /\
                           path_cost g p1 < inf /\
                           0 <= Znth child' (Znth mom' (graph_to_mat g)) < inf /\
                           path_cost g p2 + Znth child' (Znth mom' (graph_to_mat g)) < inf).
                {
                  
                  assert (In src (get_popped priq_contents)). {
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
                              g links src u priq_contents
                              H12 H11 H2 H46 H47 H53 H18)
                    as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? ?]]]]]]]]]]].
                         
                  exists p1, mom', child', p2.
                  split3; [| |split3; [| |split3; [| |split3]]]; trivial.
                  unfold EType, VType in *.
                  rewrite <- H54 in l.
                  assert ( valid_path g (mom', [(mom', child')])). {
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
                  - unfold EType, VType in *.
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
                unfold VType in *.
                do 2 rewrite path_cost_path_glue in g0; trivial; [|lia].
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

                (* and now just a little cleanup...  *)
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
                destruct (H66 H58) as [p2mom' [? [? ?]]].

                (* and path_cost of p2mom' will be <= that of p1 *)
                pose proof (H69 p1 H54 H56).  
                
                (* assert by transitivity that
                   path_cost (p2mom' +++ (mom', child') +++ p2) 
                   < path_cost p2mom +++ ...   *)   
                
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
                
                (* show that child' <> u *)
                assert (0 <= path_cost g p2) by
                    (apply (path_cost_pos g); trivial).
                assert (child' <> u). { 
                  intro. subst child'.
                  specialize (H41 _ H58).
                  destruct H67 as [? [? [? [? ?]]]].
                  unfold VType in *.
                  destruct (zlt ((Znth mom' dist_contents)
                                 + (Znth u (Znth mom' (graph_to_mat g)))) inf).                  
                  2: {
                    apply Z.lt_asymm in H71. apply H71.
                    unfold VType in *.
                    rewrite careful_add_dirty in H41; trivial; lia.
                  }
                  rewrite careful_add_clean in H41; trivial.
                  - unfold VType in *; lia.
                  - rewrite H75; apply path_cost_pos; trivial.
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
                  rewrite get_popped_meaning in H59; trivial.

                  apply (Forall_Znth _ _ _ H79) in H11.
                  Opaque inf. simpl in H11. Transparent inf.
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
                    unfold VType in *. lia.
                  }
                  
                  destruct H11.
                  - destruct (H4 _ H74) as [_ [? _]].
                    specialize (H82 H11). destruct H82.
                    1: {
                      specialize (H68 _ H80).
                      rewrite <- H82 in H68.
                      rewrite get_popped_meaning in H68; lia.
                    }
                    destruct H82 as [? [? [? [? [? ?]]]]].
                    
                    specialize (H87 mom' H58).
                    rewrite careful_add_clean in H87; trivial; try lia.
                    2: {
                      apply (Forall_Znth _ _ mom') in H10.
                      simpl in H10. lia. apply vvalid_range in H65; trivial; lia.
                    } 
                    apply Z.le_trans with (m:=Znth child' dist_contents); trivial.
                    repeat rewrite <- H8; trivial.
                    2: intro; subst; lia.
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
                    specialize (H82 H11).
                    destruct H82 as [? [? ?]].
                    specialize (H84 _ H58).
                    rewrite careful_add_clean in H84; trivial; try lia.
                    2: {
                      apply (Forall_Znth _ _ mom') in H10.
                      simpl in H10. lia. apply vvalid_range in H65; trivial; lia.
                    }
                    unfold VType in *.
                    rewrite H84. lia.
                }
                unfold VType in *. lia.
            ** (* Here we must show that the
                    vertices that were popped earlier
                    are not affected by the addition of
                    u to the popped set.
                    As expected, this is significantly easier.
                *)
              rewrite <- get_popped_irrel_upd in H15; try lia.
              2: { replace (Zlength priq_contents) with SIZE by lia.
                   apply (vvalid_range g dst); trivial.
              }
              specialize (H33 H15).
              destruct H33 as [? [? [? ?]]].
              exists x. split3; trivial.
              intros.
              specialize (H36 _ H38).
              destruct H33.
              rewrite <- get_popped_irrel_upd; try lia; trivial.
              apply get_popped_range in H36; lia.
              intro contra. rewrite contra in H36.
              apply H18; trivial.
            ** trivial.
          ++ (* ... in fact, any vertex that is
                 "seen but not popped"
                 is that way without the benefit of u.

                 We will be asked to provide a locally optimal
                 path to such a dst, and we will simply provide the
                 old one best-known path
              *)
            unfold inv_unpopped_weak. intros.
            destruct (Z.eq_dec dst u).
            1: subst dst; rewrite upd_Znth_same in H32; lia.
            rewrite upd_Znth_diff in H32 by lia.
            rewrite <- (vvalid_range g) in H15; trivial.
            destruct (H4 dst H15) as [_ [? _]].
            unfold inv_unpopped in H33.
            specialize (H33 H32).
            destruct H33.
            1: subst dst; left; trivial.           
            destruct H33 as [? [? [? [? [? ?]]]]].
            unfold VType in *.
            remember (Znth dst prev_contents) as mom.
            destruct (get_popped_path H2 H4 H12 H34) as [p2mom [? [? ?]]].

            (*Several of the proof obligations
                fall away easily, and those that remain
                boil down to showing that
                u was not involved in this
                locally optimal path.
             *)
            assert (mom <> u). {
              intro. rewrite H42 in H34. apply H18; trivial.
            }
            right. split3; [| |split3; [| |split3]]; trivial.
            ** rewrite <- get_popped_irrel_upd; trivial.
               apply get_popped_range in H34. lia.
            ** intros.
               apply H38; trivial.
               rewrite <- get_popped_irrel_upd in H44; trivial.
               apply get_popped_range in H44. rewrite upd_Znth_Zlength in H44; lia.
          ++ unfold inv_unseen_weak. intros.
             destruct (Z.eq_dec dst u).
             1: { rewrite e in H32.
                  rewrite upd_Znth_same in H32 by lia.
                  inversion H32.
             }
             rewrite upd_Znth_diff in H32 by lia.
             rewrite <- (vvalid_range g) in H15; trivial.
             destruct (H4 dst H15) as [_ [_ ?]].
             unfold inv_unseen in H33.
             specialize (H33 H32).
             destruct H33 as [? [? ?]].
             split3; trivial.
             intros.
             rewrite <- get_popped_irrel_upd in H36; trivial.
             2: { apply get_popped_range in H36.
                  rewrite upd_Znth_Zlength in H36; trivial.
             }
             apply H35; trivial.
          ++ destruct (Z.eq_dec src u).
             1: subst src; rewrite upd_Znth_same; lia.
             rewrite upd_Znth_diff; lia.
          ++ apply get_popped_meaning.
             rewrite upd_Znth_Zlength; lia.
             rewrite upd_Znth_same; lia.
          ++ intros.
             assert (dst <> u). {
               intro. subst dst. rewrite upd_Znth_same in H32; lia.
             }
             assert (0 <= dst < Zlength priq_contents). {
               destruct H2 as [? _]. red in H2.
                  rewrite H2 in H15. lia.
             }
             rewrite upd_Znth_diff; trivial.
             apply H8; trivial.
             rewrite upd_Znth_diff in H32; trivial.
          ++ apply inrange_upd_Znth; trivial;
               rewrite <- inf_eq; rep_lia.
        -- (* We now begin with the for loop's body *)
          assert (0 <= u < Zlength (graph_to_mat g)). {
            unfold graph_to_mat.
            repeat rewrite Zlength_map.
            rewrite nat_inc_list_Zlength.
            rep_lia.
          }
          assert (Zlength (Znth u (graph_to_mat g)) = SIZE). {
            rewrite Forall_forall in H0. apply H0. apply Znth_In. lia.
          }
          freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
          rewrite (graph_unfold _ _ _ u) by lia.
          Intros.
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
            destruct H38 as [? [? [? [? ?]]]].
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
               replace 8 with SIZE in H40.
               assert (0 <= i < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; lia).
               assert (0 <= u < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; lia).
               specialize (H1 i u H41 H42).
               rewrite inf_eq2 in H40.
               rewrite Heqcost in *.
               rewrite Int.signed_repr in H40.
               2: { destruct H1.
                    - unfold VType in *.
                      replace SIZE with 8 in H1.
                      destruct H1.
                      pose proof (Int.min_signed_neg).
                      assert (Int.max_signed / 8 <= Int.max_signed). {
                        compute.
                        intro. inversion H45.
                      }
                      split; try lia.
                    - rewrite H1.
                      rewrite <- inf_eq.
                      compute; split; inversion 1.
               }
               rewrite Int.signed_repr in H40.
               2: rewrite <- inf_eq; compute; split; inversion 1.
               destruct H1; lia.
             }

             
             assert (0 <= Znth u dist_contents' <= inf). {
               assert (0 <= u < Zlength dist_contents') by lia.
               apply (Forall_Znth _ _ _ H42) in H34.
               assumption.
             }
             assert (0 <= Znth i dist_contents' <= inf). {
               assert (0 <= i < Zlength dist_contents') by lia.
               apply (Forall_Znth _ _ _ H43) in H34.
               assumption.
             }
             assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
               split; [lia|].
               unfold inf in *. rep_lia.
             }
             forward. forward. forward_if.
             ** rewrite Int.signed_repr in H45
                 by (unfold inf in *; rep_lia).
                (* At this point we know that we are definitely
        going to make edits in the arrays:
        we have found a better path to i, via u *)
                assert (~ In i (get_popped priq_contents')). {
                  (* This useful fact is true because
          the cost to i was just improved.
          This is impossible for popped items.
                   *)
                  intro.
                  unfold inv_popped in H22.
                  destruct (H22 _ H46) as [p2i [? [? ?]]].
                  destruct (H22 _ H30) as [p2u [? [? ?]]].
                  unfold path_globally_optimal in H49.
                  specialize (H49 (fst p2u, snd p2u +:: (u,i))).
                  rewrite Heqcost in H45.
                  destruct H50 as [? [? [? [? ?]]]].
                  destruct H47 as [? [? [? [? ?]]]].
                  rewrite H59, H55 in H45.
                  apply Zlt_not_le in H45.
                  unfold VType in *.
                  apply H45.
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
                  - destruct H53.
                    apply valid_path_app_cons;
                      try rewrite <- surjective_pairing;
                      trivial.
                    apply vvalid2_evalid;
                      try apply vvalid_range;
                      trivial.
                  - rewrite (surjective_pairing p2u) in *.
                    simpl.
                    replace (fst p2u) with src in *.
                    apply path_ends_app_cons; trivial.
                    destruct H53. simpl in H53; lia.
                  - apply vvalid2_evalid;
                      try apply vvalid_range; trivial.
                }
                assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
                    (repeat rewrite Zlength_map; lia).
                forward. forward. forward.
                forward; rewrite upd_Znth_same; trivial.
                (* The above "forward" commands are tweaking the
        three arrays! *)
                1: entailer!.
                forward_call (v_pq, i, (Znth u dist_contents' + cost), priq_contents').

                (* Now we must show that the for loop's invariant
        holds if we take another step,
        ie when i increments *)

                (* We will provide the arrays as they stand now:
        with the i'th cell updated in all three arrays,
        to log a new improved path via u *)
                Exists (upd_Znth i prev_contents' u).
                Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
                Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)).
                repeat rewrite <- upd_Znth_map. entailer!.
                remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                assert (u <> i) by (intro; subst; lia).
                split3; [| | split3; [| | split3; [| | split3]]].
                --- 
                  intros. pose proof (H22 dst).
                  unfold inv_popped in H60.
                  unfold inv_popped.
                  intros.
                  destruct (Z.eq_dec dst i).
                  +++ subst dst.
                      rewrite get_popped_meaning, upd_Znth_same in H61.
                      3: rewrite upd_Znth_Zlength.
                      all: lia.  
                  +++ pose proof (get_popped_range _ _ H61).
                      rewrite upd_Znth_Zlength in H62 by lia.
                      rewrite <- get_popped_irrel_upd in H61; try lia.
                      specialize (H60 H61).
                      destruct H60 as [p2dst [? [? ?]]].
                      exists p2dst; split3; trivial.
                      *** destruct H60 as [? [? [? [? ?]]]].
                          split3; [| | split3]; trivial.
                          1: rewrite upd_Znth_diff; lia.
                          rewrite Forall_forall; intros.
                          assert (In_path g (snd x) p2dst). {
                            unfold In_path. right.
                            exists x. split; trivial.
                            destruct H2 as [? [? [? ?]]].
                            red in H72; rewrite H72.
                            right; trivial.
                          }
                          specialize (H63 _ H70).
                          rewrite Forall_forall in H68.
                          specialize (H68 _ H69).
                          assert (snd x <> i). {
                            intro contra.
                            unfold VType in *.
                            rewrite contra in H63.
                            apply H46. trivial.
                          }
                          unfold VType in *.
                          rewrite upd_Znth_diff; try lia.
                          apply get_popped_range in H63; lia.
                      *** intros.
                          specialize (H63 _ H65).
                          rewrite <- get_popped_irrel_upd; try lia; trivial.
                          apply get_popped_range in H63; lia.
                          intro contra. rewrite contra in H63.
                          apply H46. trivial.
                --- intros.
                    destruct (Z.eq_dec dst i).
                    +++ subst dst.
               (* This is a key change --
                i will now be locally optimal,
                _thanks to the new path via u_.

                In other words, it is moving from
                the weaker inv_popped clause
                to the stronger
                *)
                        unfold inv_unpopped; intros.
                        unfold inv_popped in H22.
                        destruct (H22 _ H30) as [p2u [? [? ?]]].
                        unfold VType in *.
                        rewrite upd_Znth_same by lia.
                        right.
                        split.
                        1: { intro. assert (In_path g src p2u). {
                               left. destruct H62 as [_ [[? _] _]].
                               destruct p2u. now simpl in H62 |- *. }
                             specialize (H63 _ H66).
                             now subst. }
                        rewrite upd_Znth_same in H61; trivial; [|lia].
                        split3; [| |split3].
                        *** rewrite <- get_popped_irrel_upd; trivial; lia.
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
                            
                            assert (vvalid g mom'). {
                              apply get_popped_range in H65.
                              rewrite upd_Znth_Zlength in H65; [|lia].
                              apply vvalid_range; trivial; lia.
                            }

                            assert (mom' <> i). {
                              intro. subst mom'.
                              rewrite get_popped_meaning in H65.
                              rewrite upd_Znth_same in H65; lia.
                              rewrite upd_Znth_Zlength; trivial.
                              lia. lia.
                            }
                            
                            rewrite upd_Znth_diff; trivial.
                            2: apply get_popped_range in H65;
                              rewrite upd_Znth_Zlength in H65.
                            2,3,4: lia.

                            rewrite <- get_popped_irrel_upd in H65; trivial.
                            2: apply get_popped_range in H65;
                              rewrite upd_Znth_Zlength in H65.
                            2,3,4: lia.
                            destruct (H22 _ H65) as [p2mom' [? [? ?]]].
                            destruct H68 as [? [? [? [? ?]]]].

                            assert (In_path g mom' p2mom'). {
                              destruct H71.
                              apply pfoot_in in H75.
                              trivial.
                            }

                            
                            destruct (zlt ((Znth mom' dist_contents') + (Znth i (Znth mom' (graph_to_mat g)))) inf).
                              2: {
                                unfold VType in *.
                                destruct H62 as [_ [_ [_ [? _]]]].
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
                                - rewrite H73;
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
                                specialize (H64 _ H68 H71).
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

(* Digression: a brief check to see if i was unseen, or just unpopped. *)              
                              destruct (Z.eq_dec (Znth i priq_contents') inf).
                              1: {
                                (* if it was unseen, our job is easy *)
                                assert (i <= i < SIZE) by lia.
                                   destruct (H26 _ H79 e) as [? [? ?]].
                                   specialize (H82 _ H65 n).
                                   lia.
                              }
                              (* if not, we have some info: *)
                              assert (Znth i priq_contents' < inf). {
                                assert (0 <= i < Zlength priq_contents') by lia.
                                pose proof (Forall_Znth _ priq_contents' i H79 H33).
                                Opaque inf. simpl in H80. Transparent inf.
                                rewrite get_popped_meaning in H46.
                                lia. lia.
                              }
 (* Great, so now I can employ inv_unpopped_weak. *)
 
                              clear n0.
                              unfold VType in *.
                              rewrite H77.
                              
                              


(* Because i is "seen", we know that 
   The best-known path to i via popped vertices is 
   already logged in dist[i]. 
   So dist[i] <= dist[mom'] + (mom', i).
 *)

                              assert (Znth i dist_contents' <= Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))). {
                                assert (i <= i < SIZE) by lia.
                                assert (0 <= mom' < SIZE) by
                                    (apply get_popped_range in H65; lia).
                                destruct (H24 _ H80 H79).
                                - rewrite H82 at 1. rewrite H27.
                                  apply (Forall_Znth _ _ mom') in H34.
                                  2: lia.  
                                  simpl in H34.
                                  unfold VType in *.
                                  destruct (H1 _ _ H19 H81);
                                    apply Z.add_nonneg_nonneg; lia.
                                - destruct H82 as [? [? [? [? [? [? ?]]]]]].
                                  specialize (H88 _ n H65).
                                  rewrite H77 in H88; trivial.
                              }
                              
(*
  So we have 
  dist[u] + graph[u][i] <= dist[i] <=
                        <= dist[mom'] + (mom', i) 
                        <= path_cost p'.
 *)
                              unfold VType in *.
                              lia.
                            ++++
                              (* since u is not in the path, 
                                 we can just tango with
                                 the step <> u condition from 
                                 inv_unpopped_weak. 
                                 This case is okay.
                               *)
                              assert (mom' <> u). {
                                intro. rewrite <- H79 in n.
                                apply n.
                                apply in_path_eq_epath_to_vpath; trivial.
                              }
                             
                              destruct (Z.eq_dec (Znth i priq_contents') inf).
                              1: { assert (i <= i < SIZE) by lia.
                                   destruct (H26 _ H80 e) as [? [? ?]].
                                   specialize (H83 _ H65 H79).
                                   rewrite H83. lia.
                              }
                              assert (Znth i priq_contents' < inf). {
                                assert (0 <= i < Zlength priq_contents') by lia.
                                pose proof (Forall_Znth _ priq_contents' i H80 H33).
                                Opaque inf. simpl in H81. Transparent inf.
                                rewrite get_popped_meaning in H46.
                                lia. lia.
                              }

                              assert (i <= i < SIZE) by lia.
                              destruct (H24 i H81 H80).
                              1: subst i; exfalso; lia.
                                destruct H82 as [_ [? [? [? [? [? ?]]]]]].
                              apply Z.lt_le_incl.
                              apply Z.lt_le_trans with (m:=Znth i dist_contents').
                              1: lia.
                              apply H87; trivial.
                    +++ assert (0 <= dst < i) by lia.
                        (* We will proceed using the
                           old best-known path for dst *)
                        specialize (H23 _ H61).
                        unfold inv_unpopped in *.
                        intros.
                        rewrite upd_Znth_diff in H62 by lia.
                        specialize (H23 H62). destruct H23.
                        1: left; trivial.
                        destruct H23 as [? [? [? [? [? ?]]]]].
                        unfold VType in *.
                        remember (Znth dst prev_contents') as mom. right.
                        split; trivial.

                        destruct (H22 _ H63) as [p2mom [? [? ?]]].
                        rewrite upd_Znth_diff; trivial; [|lia..].
                        rewrite <- Heqmom.
                        
                        assert (mom <> i). {
                          intro. rewrite H71 in *.
                          apply H46; trivial.
                        }
                        assert (0 <= mom < Zlength priq_contents'). {
                          apply get_popped_range in H63; lia.
                        }
                        split3; [| |split3]; trivial.
                        *** rewrite <- get_popped_irrel_upd; trivial; lia.
                        *** rewrite upd_Znth_diff; lia.
                        *** repeat rewrite upd_Znth_diff; trivial; lia.
                        *** intros.
                            assert (mom' <> i). {
                              intro. rewrite H74 in H73.
                              rewrite get_popped_meaning in H73.
                              rewrite upd_Znth_same in H73; trivial.
                              lia. lia. rewrite upd_Znth_Zlength; lia.
                            }
                            rewrite <- get_popped_irrel_upd in H73; trivial.
                            repeat rewrite upd_Znth_diff; trivial.
                            apply H67; trivial.
                            1,5: apply get_popped_range in H73.
                            2: rewrite upd_Znth_Zlength in H73.
                            all: lia.
                --- unfold inv_unpopped_weak. intros.
                    assert (i <= dst < SIZE) by lia.
                    destruct (Z.eq_dec dst i).
                    1: subst dst; lia.
                    rewrite upd_Znth_diff in H61 by lia.
                    destruct (H24 _ H62 H61); [left | right]; trivial.
                    destruct H63 as [? [? [? [? [? [? ?]]]]]].
                    unfold VType in *.
                    rewrite upd_Znth_diff by lia.
                    remember (Znth dst prev_contents') as mom.
                    clear H66.
                    assert (mom <> i). {
                      intro. rewrite H66 in H65.
                      apply H46; trivial.
                    }

                    assert (0 <= mom < Zlength priq_contents'). {
                      apply get_popped_range in H65; lia.
                    }
                    

                    split3; [| | split3; [| | split3]]; trivial.
                    +++ rewrite <- get_popped_irrel_upd; trivial; lia.
                    +++ rewrite elabel_Znth_graph_to_mat; trivial.
                        assert (0 <= Znth mom dist_contents'). {
                          apply (Forall_Znth _ _ mom) in H34;
                            [simpl in H34|]; lia.
                        }
                        unfold VType in *. lia.
                        apply vvalid2_evalid; try apply vvalid_range; trivial; lia.
                    +++ repeat rewrite upd_Znth_diff; trivial; lia.
                    +++ repeat rewrite upd_Znth_diff; trivial; try lia.
                    +++ intros.
                        assert (mom' <> i). intro. rewrite H73 in H72.
                        rewrite get_popped_meaning, upd_Znth_same in H72; trivial.
                        lia. lia. rewrite upd_Znth_Zlength; lia.
                        repeat rewrite upd_Znth_diff; trivial.
                        apply H69; trivial; try lia.
                        rewrite <- get_popped_irrel_upd in H72; trivial.
                        1,3: apply get_popped_range in H72; rewrite upd_Znth_Zlength in H72.
                        all: lia.

                --- unfold inv_unseen; intros.
                    assert (dst <> i). {
                      intro. subst dst. rewrite upd_Znth_same in H61; lia.
                    }
                    assert (0 <= dst < i) by lia.
                    pose proof (H25 dst H63).
                    rewrite upd_Znth_diff in H61; try lia.
                    rewrite upd_Znth_diff; try lia.
                    rewrite upd_Znth_diff; try lia.
                    unfold inv_unseen in H64.
                    specialize (H64 H61).
                    destruct H64 as [? [? ?]].
                    split3; trivial.
                    intros.
                    destruct (Z.eq_dec m i).
                    1: { exfalso. subst m.
                         rewrite get_popped_meaning in H67.
                         rewrite upd_Znth_same in H67.
                         lia. lia.
                         rewrite upd_Znth_Zlength; lia.
                    }
                    rewrite upd_Znth_diff; trivial.
                    rewrite <- get_popped_irrel_upd in H67.
                    apply H66; trivial.
                    1,4: apply get_popped_range in H67; rewrite upd_Znth_Zlength in H67.
                    all: lia. 
                --- unfold inv_unseen_weak; intros.
                    assert (dst <> i) by lia.
                    rewrite upd_Znth_diff in H61 by lia.
                    repeat rewrite upd_Znth_diff by lia.
                    assert (i <= dst < SIZE) by lia.
                    destruct (H26 _ H63 H61) as [? [? ?]].
                    split3; trivial.
                    intros.
                    destruct (Z.eq_dec mom i).
                    1: { exfalso. subst mom.
                         rewrite get_popped_meaning in H67.
                         rewrite upd_Znth_same in H67.
                         lia. lia.
                         rewrite upd_Znth_Zlength; lia.
                    }
                    rewrite upd_Znth_diff; trivial.
                    rewrite <- get_popped_irrel_upd in H67.
                    apply H66; trivial.
                    1,4: apply get_popped_range in H67; rewrite upd_Znth_Zlength in H67.
                    all: lia. 
                --- rewrite upd_Znth_diff; try lia.
                    intro. subst src; lia.
                --- rewrite upd_Znth_diff; try lia.
                    intro. subst src; lia.
                --- rewrite upd_Znth_diff; try lia.
                    intro. subst src; lia.
                --- split3.
                    +++ apply get_popped_irrel_upd; try lia; trivial.
                    +++ intros.
                        destruct (Z.eq_dec dst i).
                        *** rewrite e.
                            repeat rewrite upd_Znth_same; trivial; lia.
                        ***
                          rewrite vvalid_range in H60; trivial.
                          rewrite upd_Znth_diff in H61; trivial; try lia.
                          repeat rewrite upd_Znth_diff; trivial; try lia.
                          apply H31; trivial.
                          rewrite vvalid_range; trivial.
                    +++ split3; apply inrange_upd_Znth; trivial; try lia. 
             ** rewrite Int.signed_repr in H45
                 by (unfold inf in *; rep_lia).
                (* This is the branch where I didn't
                   make a change to the i'th vertex. *)
                forward. 
                (* The old arrays are just fine. *)
                Exists prev_contents' priq_contents' dist_contents'.
                entailer!.
                remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                split3; [| |split].
                --- intros.
                    (* Show that moving one more step
                       still preserves the for loop invariant *)
                    destruct (Z.eq_dec dst i).
                    (* when dst <> i, all is well *)
                    2: apply H23; lia.
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
                    destruct (H24 i H59 H58).
                    1: left; trivial.
                    destruct H60 as [? [? [? [? [? [? ?]]]]]].
                    unfold VType in *.
                    remember (Znth i prev_contents') as mom.
                    destruct (Z.eq_dec i src); [left | right]; trivial.
                    split; trivial.
                    split3; [| |split3]; trivial.
                    intros.

                    destruct (H22 _ H67) as [p2mom' [? [? ?]]].
                    assert (Hrem := H68).

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
                        
                    *** destruct H68 as [? [? [? [? ?]]]].
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
                              specialize (H69 _ i0).
                              rename p2mom' into p2u.
                              unfold path_globally_optimal in H70.
                              apply Z.ge_le in H45.

                              destruct (zlt (Znth u dist_contents' + Znth i (Znth u (graph_to_mat g))) inf).
                              ++++ rewrite careful_add_clean; try lia; trivial.

                                   
                              ++++ rewrite careful_add_dirty; trivial.
                                   lia. lia.
                                   replace 8 with SIZE in H40 by lia.
                                   rewrite inf_eq2 in H40.
                                   rewrite Int.signed_repr in H40.
                                   2: rep_lia.
                                   rewrite Int.signed_repr in H40.
                                   2: { rewrite <- inf_eq.
                                        unfold VType in *.
                                        unfold Int.min_signed, Int.max_signed.
                                        unfold Int.half_modulus.
                                        simpl. lia.
                                   }
                                   lia.
                        ----
                          (* mom' <> u *)
                          destruct Hrem as [? [? [? [? ?]]]].
                          
                          assert (In_path g mom' p2mom'). {
                            destruct H76.
                            apply pfoot_in in H80. 
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
                                pose proof (path_cost_pos g p2mom' H2 H68 H1).
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
                            - rewrite H73. apply path_cost_pos; trivial.
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
                          rewrite H83.
                          
(* Since i has been "seen", 
   we have dist[i] <= dist[mom'] + (mom', i)
   because of inv_unpopped_weak 
 *)
                          assert (0 <= mom' < SIZE) by
                              (apply get_popped_range in H67; lia).
                          destruct (H24 _ H59 H58).
                          ++++ rewrite H85 at 1. rewrite H27.
                               apply (Forall_Znth _ _ mom') in H34.
                               2: lia.  
                               simpl in H34.
                               unfold VType in *.
                               destruct (H1 _ _ H19 H84);
                                 apply Z.add_nonneg_nonneg; lia.
                          ++++ destruct H85 as [? [? [? [? [? [? ?]]]]]].
                               specialize (H91 _ n0 H67).
                               rewrite H83 in H91; trivial.

                    ***

(* 2. ~ In u p': This is an easy case.
   dist[i] < path_cost p' because of Inv2.
 *)
                      apply H66; trivial.
                      intro. apply n0.
                      destruct H68 as [? [? [? [? ?]]]].
                      rewrite in_path_eq_epath_to_vpath; trivial.
                      destruct H72.
                      apply pfoot_in in H76. rewrite H71 in *. trivial.
                      
                --- intros. destruct (Z.eq_dec dst i).
                    +++ subst dst. lia.
                    +++ apply H24; lia.
                --- unfold inv_unseen; intros.
                    destruct (Z.eq_dec dst i).
                    2: apply H25; lia.
                    subst dst.
                    assert (i <= i < SIZE) by lia.
                    destruct (H26 _ H59 H58) as [? [? ?]].
                    split3; trivial.
                    intros.
                    destruct (Z.eq_dec m u).
                    2: apply H62; trivial.
                    subst m.
                    rewrite H60 in H45.
                    assert (0 <= u < SIZE) by lia.
                    assert (vvalid g u). {
                      destruct H2 as [? _]. red in H2. rewrite H2. lia.
                    }
                    assert (Znth u dist_contents' < inf). {
                      destruct (H22 _ H63) as [? [? [? ?]]].
                      destruct H66 as [? [? [? [? ?]]]].
                      lia.
                    }
                    destruct (zlt (Znth i (Znth u (graph_to_mat g))) inf).
                    1: apply careful_add_dirty; trivial; lia.
                    assert (Znth i (Znth u (graph_to_mat g)) = inf). {
                      assert (Int.max_signed / SIZE < inf) by now compute. 
                      unfold inrange_graph in H1;
                        destruct (H1 _ _ H19 H64); trivial.
                      replace 8 with SIZE in H40 by lia.
                      rewrite inf_eq2 in H40.
                      rewrite Int.signed_repr in H40.
                      2: { unfold VType in *. replace SIZE with 8 in H55, H54.
                           unfold Int.min_signed, Int.max_signed, Int.half_modulus in *.
                           simpl. simpl in H55, H54.
                           assert (2147483647 / 8 < 2147483647) by now compute.
                           lia.
                      }
                      rewrite Int.signed_repr in H40.
                      2: rewrite <- inf_eq; rep_lia.
                      lia.
                    }
                    rewrite H67.
                    rewrite careful_add_inf; trivial; lia.
                --- intros.
                    assert (i <= dst < SIZE) by lia.
                    apply H26; trivial.
          ++  (* i was not a neighbor of u.
                 prove the for loop's invariant holds *)
            replace 8 with SIZE in H40 by lia.
            rewrite inf_eq2 in H40.
            forward.
            Exists prev_contents' priq_contents' dist_contents'.
            entailer!.
            remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
            assert (Znth i (Znth u (graph_to_mat g)) = inf). {
              assert (0 <= i < SIZE) by lia.
              assert (0 <= u < SIZE) by lia.
              assert (Int.max_signed / SIZE < inf) by now compute. 
              unfold inrange_graph in H1;
                destruct (H1 _ _ H15 H53); trivial.
              rewrite Int.signed_repr in H40.
              2: { unfold VType in *. replace SIZE with 8 in H55, H54.
                   unfold Int.min_signed, Int.max_signed, Int.half_modulus in *.
                   simpl. simpl in H55, H54.
                   assert (2147483647 / 8 < 2147483647) by now compute.
                   lia.
              }
              rewrite Int.signed_repr in H40.
              2: rewrite <- inf_eq; rep_lia.
              lia.
            }
            split3; [| |split]; intros.
            ** destruct (Z.eq_dec dst i).
               --- subst dst. 
                   (* Will need to use the second half of the 
                      for loop's invariant.          
                      Whatever path worked for i then will 
                      continue to work for i now:
                      i cannot be improved
                      by going via u *)
                   unfold inv_unpopped; intros.
                   assert (i <= i < SIZE) by lia.
                   destruct (H24 i H55 H54).
                   1: left; trivial.
                   destruct H56 as [? [? [? [? [? [? ?]]]]]].
                   unfold VType in *.
                   remember (Znth i prev_contents') as mom.

                   destruct (H22 _ H58) as [p2mom [? [? ?]]].
                   
                   right. split.
                   1: { assert (In src (get_popped priq_contents')). {
                          assert (In_path g src p2mom). {
                         left. destruct H63 as [_ [[? _] _]].
                         destruct p2mom. 
                         now simpl in H56 |- *. }
                       specialize (H64 _ H66).
                       now subst. }
                     intro contra. rewrite <- contra in H66.
                     rewrite get_popped_meaning in H66.
                     lia. lia.
                   }
                   
                   split3; [| |split3]; trivial.
                   +++ intros.
                       destruct (H22 _ H66) as [p2mom' [? [? ?]]].
                       assert (In_path g mom' p2mom'). {
                         destruct H67 as [_ [[_ ?] _]].
                         apply pfoot_in in H67.
                         trivial.
                       }

                       assert (vvalid g mom'). {
                         destruct H67.
                         apply (valid_path_valid g p2mom'); trivial.
                       }

                       destruct (zlt (Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))) inf).
                       2: {
                         unfold VType in *.
                         destruct H67 as [? [? [? [? ?]]]].
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
                             pose proof (path_cost_pos g p2mom' H2 H67 H1).
                             unfold VType in *.
                             lia. lia. 
                             rewrite Z.eqb_neq. lia.
                       }
                       assert (vvalid g i). {
                         destruct H2 as [? _].
                         red in H2; rewrite H2; trivial.
                       }
                       
                       assert (careful_add (Znth mom' dist_contents') (Znth i (Znth mom' (graph_to_mat g))) = Znth mom' dist_contents' + Znth i (Znth mom' (graph_to_mat g))). {
                         rewrite careful_add_clean; trivial.
                         - destruct H67 as [? [? [? [? ?]]]].
                           rewrite H75;
                           apply path_cost_pos; trivial.
                         - rewrite <- elabel_Znth_graph_to_mat; trivial.
                           apply inrange_graph_cost_pos; trivial.
                           all: apply vvalid2_evalid; trivial.
                       }
                       assert (mom' <> i). {
                         intro.
                         specialize (H68 _ H70).
                         subst mom'. 
                         rewrite get_popped_meaning in H68; lia. 
                       }
                              
                       assert (In mom' (get_popped priq_contents')). {
                         specialize (H68 _ H70). trivial.
                       }
                       assert (vvalid g i). {
                         destruct H2 as [? _].
                         red in H2; rewrite H2; trivial.
                       }


                       
                       destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).
                       ***

                         apply in_path_eq_epath_to_vpath in i0.
                         2: destruct H67; trivial.

                         destruct (Z.eq_dec mom' u).
                         1: { subst mom'. rewrite H15.
                              rewrite careful_add_inf; trivial.
                              - lia.
                              - destruct (H22 _ H75) as [p2u [[? [? [? [? ?]]]] _]].
                                rewrite H80. 

                                apply path_cost_pos; destruct H63; trivial.
                         }

                         destruct H63 as [? [? [? [? ?]]]].
                         unfold VType in *.
                         rewrite H73.
                         assert (0 <= mom' < SIZE) by
                             (apply get_popped_range in H75; lia).
                         destruct (H24 _ H55 H54).
                         ---- rewrite H82 at 1. rewrite H27.
                              apply (Forall_Znth _ _ mom') in H34.
                              2: lia.  
                              simpl in H34.
                              unfold VType in *.
                              destruct (H1 _ _ H19 H81);
                                    apply Z.add_nonneg_nonneg; lia.
                         ---- destruct H82 as [? [? [? [? [? [? ?]]]]]].
                              specialize (H88 _ n H75).
                              rewrite H73 in H88; trivial.
                             
                       *** apply H62; trivial.
                           intro. apply n.
                           rewrite in_path_eq_epath_to_vpath.
                           destruct H67 as [_ [[? ?] _]]. 
                           apply pfoot_in in H78. rewrite H77 in *; trivial.
                           destruct H67; trivial.
                           
               --- apply H23; lia.
            ** destruct (Z.eq_dec dst i).
               --- lia. 
               --- apply H24; lia.
            ** destruct (Z.eq_dec dst i).
               2: apply H25; lia.
               subst dst.
               assert (i <= i < SIZE) by lia.
               unfold inv_unseen; intros.
               destruct (H26 _ H54 H55) as [? [? ?]].
               split3; trivial.
               intros.
               destruct (Z.eq_dec m u).
               2: apply H58; trivial.
               subst m. rewrite H15.
               rewrite careful_add_inf; trivial.
               unfold inrange_dist in H34.
               rewrite Forall_forall in H34.
               apply H34.
               apply Znth_In. lia.
            ** apply H26; lia.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
          unfold dijkstra_correct.
          split3; trivial;
            [apply H20 | apply H22];
            rewrite <- (vvalid_range g); trivial.
      * (* After breaking, the while loop,
           prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H16 in H15; simpl in H15; now inversion H15.
        }
        clear H15.
        forward. Exists prev_contents priq_contents dist_contents.
        entailer!. apply (isEmptyMeansInf _ H16).
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents.
      forward. Exists prev_contents dist_contents priq_contents. entailer!.
Qed.
