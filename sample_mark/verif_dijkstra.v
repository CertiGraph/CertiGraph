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
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import RamifyCoq.sample_mark.priq_utils.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_macros.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_spec.

(* We must use the CompSpecs and Vprog that were
   centrally defined in dijksta's environment. 
   This lets us be consistent and call PQ functions in Dijkstra. 
 *)
Local Definition CompSpecs := env_dijkstra_arr.CompSpecs.
Local Definition Vprog := env_dijkstra_arr.Vprog.
Local Definition Gprog := dijk_pq_arr_spec.Gprog.

Local Open Scope Z_scope.
 
Lemma inf_eq: 1879048192 = inf.
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute. trivial. Qed.

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
  rewrite upd_Znth_unfold in H2; auto. apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2; [omega|].
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Lemma sublist_nil: forall lo hi A,
    sublist lo hi (@nil A) = (@nil A).
Proof. intros. unfold sublist. rewrite firstn_nil. apply sublist.skipn_nil. Qed.

Lemma sublist_cons:
  forall a (l: list Z) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by omega.
  rewrite sublist_one by omega. simpl.
  rewrite Znth_0_cons.
  rewrite sublist_1_cons. reflexivity.
Qed.

Lemma sublist_cons':
  forall a (l: list (Z*Z)) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by omega.
  rewrite sublist_one by omega. simpl.
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
  rewrite min_l. reflexivity. rep_omega.
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
    pose proof (Pos2Nat.is_pos p); omega.
  - assert (Z.to_nat (lo - 1) = n) by
        now rewrite <- (juicy_mem_lemmas.nat_of_Z_lem1 n lo). rewrite H0.
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
    pose proof (Zlength_nonneg l2). exfalso. omega.
  - rewrite Zlength_nil in H0. rewrite Zlength_cons in H0.
    pose proof (Zlength_nonneg l1). exfalso. omega.
  - destruct (Z.eq_dec 0 lo).
    + subst lo. autorewrite with sublist. now simpl.
    + assert (0 < lo) by omega. rewrite !sublist_skip; auto.
      rewrite !Zlength_cons in *. apply IHl1; omega.
Qed.

Lemma combine_sublist_specific:
  forall (l1 l2: list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (sublist 0 i l1) (sublist 0 i l2) = sublist 0 i (combine l1 l2).
Proof.
  induction l1, l2; intros; simpl; autorewrite with sublist.
  - rewrite !sublist_nil. easy.
  - rewrite Zlength_nil in H0. omega.
  - rewrite Zlength_nil in H. rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg l1). omega.
  - destruct (Z.eq_dec i 0).
    + subst i. autorewrite with sublist. now simpl.
    + rewrite !Zlength_cons in *. repeat rewrite sublist_cons.
      * simpl. rewrite sublist_cons'.
        -- f_equal. apply IHl1; omega.
        -- rewrite Zlength_cons. rewrite combine_same_length; omega.
      * rewrite Zlength_cons. omega.
      * rewrite Zlength_cons. omega.
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
  repeat rewrite (sublist_split 0 i (Zlength l2) l2) by omega.
  rewrite !upd_Znth_unfold; auto. 2: now rewrite combine_same_length.
  rewrite combine_app.
  2: { repeat rewrite <- ZtoNat_Zlength.
       f_equal. repeat rewrite Zlength_sublist; omega. }
  f_equal.
  1: apply combine_sublist_specific; assumption.
  rewrite (sublist_split i (i+1) (Zlength l2) l2) by omega.
  rewrite sublist_len_1 by omega. simpl.
  simpl combine. f_equal.
  apply combine_sublist_gen. omega. omega.
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
  - intros. rewrite Zlength_nil in H0; exfalso; omega.
  - intros.
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite sublist_len_1 by omega.
    simpl. destruct (Z.eq_dec i 0).
    1: subst i; repeat rewrite Znth_0_cons; reflexivity.
    repeat rewrite Znth_pos_cons by omega.
    apply IHl1.
    rewrite Zlength_sublist by omega.
    rewrite Zlength_cons in H; rep_omega.
    rewrite Zlength_cons in H0; rep_omega.
Qed.

Lemma behead_list:
  forall (l: list Z),
    0 < Zlength l ->
    l = Znth 0 l :: tl l.
Proof.
  intros.
  destruct l.
  - rewrite Zlength_nil in H. inversion H.
  - simpl. rewrite Znth_0_cons. reflexivity.
Qed.

Lemma nat_inc_list_hd:
  forall n,
    0 < n ->
    Znth 0 (nat_inc_list (Z.to_nat n)) = 0.
Proof.
  intros. induction (Z.to_nat n).
  - reflexivity.
  - simpl.
    destruct n0.
    + reflexivity.
    + rewrite app_Znth1. omega.
      rewrite nat_inc_list_Zlength.
      rewrite <- Nat2Z.inj_0.
      apply inj_lt. omega.
Qed.

Lemma tl_app:
  forall (l1 l2: list Z),
    0 < Zlength l1 ->
    tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
  intros. destruct l1.
  - inversion H.
  - intros. simpl. reflexivity.
Qed.

Lemma in_tl_nat_inc_list:
  forall i n,
    In i (tl (nat_inc_list n)) ->
    1 <= i.
Proof.
  destruct n. inversion 1.
  induction n. inversion 1.
  intros.
  simpl in H.
  rewrite Zpos_P_of_succ_nat in H.
  rewrite tl_app in H.
  2: { rewrite Zlength_app.
       replace (Zlength [Z.of_nat n]) with 1 by reflexivity.
       rep_omega.
  }
  apply in_app_or in H; destruct H.
  - apply IHn. simpl. assumption.
  - simpl in H. destruct H; omega.
Qed.

Lemma nat_inc_list_app:
  forall n m p i,
    0 <= i < m ->
    0 <= n ->
    n + m <= p ->
    Znth i (nat_inc_list (Z.to_nat m)) =
    Znth i
         (sublist n (n + m)
                  (nat_inc_list (Z.to_nat p))) - n.
Proof.
  symmetry.
  rewrite Znth_sublist by rep_omega.
  repeat rewrite nat_inc_list_i by rep_omega.
  omega.
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
  2: { subst. rewrite sublist_same.
       reflexivity. reflexivity.
       rewrite nat_inc_list_Zlength. rep_omega. }
  apply Znth_eq_ext.
  1: { rewrite Zlength_sublist.
       rewrite nat_inc_list_Zlength. rep_omega.
       rep_omega.
       rewrite nat_inc_list_Zlength. rep_omega.
  }
  intros.
  rewrite nat_inc_list_i.
  2: { rewrite Zlength_sublist in H1.
       rep_omega.
       rep_omega.
       rewrite nat_inc_list_Zlength. rep_omega.
  }
  rewrite <- Z.sub_0_r at 1.
  replace n with (0 + n) by omega.
  rewrite Zlength_sublist in H1.
  rewrite <- nat_inc_list_app.
  rewrite nat_inc_list_i.
  all: try rep_omega.
  rewrite nat_inc_list_Zlength. rep_omega.
Qed.

Lemma get_popped_empty:
  forall l,
    Forall (fun x => x <> inf + 1) l -> get_popped l = [].
Proof.
  intros.
  unfold get_popped.
  replace (filter (fun x : Z * Z => (fst x) =? (inf + 1))
                  (combine l (nat_inc_list (Z.to_nat (Zlength l))))) with (@nil (Z*Z)).
  trivial. symmetry.
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2. clear Heql2.
  generalize dependent l2. induction l; trivial.
  intros. simpl. destruct l2; [reflexivity|].
  simpl. pose proof (Forall_inv H). pose proof (Forall_tl _ _ _ H).
  simpl in H0. destruct (a =? 1879048193) eqn:?.
  1: rewrite Z.eqb_eq in Heqb; omega.
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
  rewrite upd_Znth_Zlength by omega.
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2.
  assert (Zlength l = Zlength l2). {
    rewrite Heql2.
    rewrite nat_inc_list_Zlength. rep_omega.
  }
  f_equal.
  pose proof (combine_same_length l l2 H2).
  rewrite combine_upd_Znth by assumption.
  unfold_upd_Znth_old.
  rewrite <- (sublist_same 0 (Zlength (combine l l2)) (combine l l2)) at 4 by reflexivity.
  rewrite (sublist_split 0 i (Zlength (combine l l2))
                         (combine l l2)) by omega.
  do 2 rewrite filter_app.
  f_equal. rewrite H3.
  rewrite (sublist_split i (i+1) (Zlength l)) by omega.
  rewrite (sublist_one i (i+1) (combine l l2)) by omega.
  rewrite filter_app.
  f_equal. simpl.
  destruct (F (new, Znth i l2)) eqn:?; rewrite HeqF in Heqb; simpl in Heqb.
  - exfalso. apply H1. rewrite <- inf_eq.
    simpl. rewrite Z.eqb_eq in Heqb. rewrite <- inf_eq in *.
    omega.
  - destruct (F (Znth i (combine l l2))) eqn:?; trivial.
    rewrite HeqF, Znth_combine, Z.eqb_eq in Heqb0 by omega.
    simpl in Heqb0. exfalso. apply H1. rewrite <- inf_eq. omega.
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
    rewrite <- (sublist_same 0 (Zlength (l1 ++ l2)) (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))) in H1.
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))) in H1.
    5,3: rewrite (Zlength_correct (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2)))));
      rewrite nat_inc_list_length;
      rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.
    all: try rep_omega.
    rewrite combine_app in H1.
    2: { rewrite Zlength_correct.
         repeat rewrite <- ZtoNat_Zlength.
         f_equal.
         pose proof (Zlength_nonneg l1).
         rewrite Zlength_sublist.
         all: rewrite Z2Nat.id.
         all: try omega.
         rewrite Zlength_app.
         rewrite nat_inc_list_Zlength.
         rewrite Z2Nat.id by omega. omega.
    }
    apply in_app_or in H1.
    destruct H1.
    + exfalso.
      pose proof (in_combine_r _ _ _ _ H1).
      clear H1.
      rewrite nat_inc_list_sublist in H2.
      2: apply Zlength_nonneg.
      2: rewrite Zlength_app; omega.
      apply nat_inc_list_in_iff in H2.
      rewrite Z2Nat.id in H2 by (apply Zlength_nonneg).
      omega.
    + apply In_Znth_iff in H1. destruct H1 as [? [? ?]].
      rewrite In_Znth_iff. exists x0.
      split.
      * rewrite combine_same_length in *.
        assumption.
        rewrite Zlength_sublist.
        rewrite Zlength_app. omega.
        rewrite Zlength_app.
        rep_omega.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
      * rewrite Znth_combine in *; trivial.
        2: {
          rewrite Zlength_sublist.
          rewrite Zlength_app. omega.
          rewrite Zlength_app. rep_omega.
          rewrite nat_inc_list_Zlength.
          rewrite Z2Nat.id. reflexivity.
          rep_omega. }
        2, 4: rewrite combine_same_length in H1; trivial.
        2, 3: rewrite Zlength_sublist, Zlength_app; [|rewrite Zlength_app|]; try rep_omega;
          repeat rewrite Zlength_correct;
          rewrite nat_inc_list_length;
          rewrite Nat2Z.id; omega.
        2: repeat rewrite nat_inc_list_Zlength; rep_omega.
        inversion H2.
        rewrite Zlength_app.
        rewrite <- nat_inc_list_app.
        reflexivity.
        rewrite combine_same_length in H1. omega.
        rewrite Zlength_sublist. rewrite Zlength_app.
        omega.
        rewrite Zlength_app. rep_omega.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        rep_omega. rep_omega. reflexivity.
  - rewrite In_map_snd_iff in H1; destruct H1.
    rewrite filter_In in H1; destruct H1; simpl in H2.
    rewrite In_map_snd_iff.
    exists x.
    rewrite filter_In; split; trivial. clear H2.
    rewrite <- (sublist_same 0 (Zlength (l1 ++ l2)) (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))).
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))).
    5,3: rewrite (Zlength_correct (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2)))));
      rewrite nat_inc_list_length;
      rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.
    all: try rep_omega.
    rewrite combine_app.
    2: { repeat rewrite <- ZtoNat_Zlength. f_equal.
         rewrite Zlength_sublist. omega.
         pose proof (Zlength_nonneg l1); omega.
         rewrite Zlength_app.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id; omega.
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
         omega.
         rewrite Zlength_sublist.
         rewrite Zlength_app. omega.
         rewrite Zlength_app.
         pose proof (Zlength_nonneg l2).
         rep_omega.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id. reflexivity.
         omega.
    }
    rewrite Znth_combine in *.
    2: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; omega.
    3: rewrite Zlength_sublist, Zlength_app; [|rewrite Zlength_app|]; try rep_omega;
      repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; omega.
    2, 3: rewrite combine_same_length in H1; [rep_omega|].
    2, 3: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; omega.
    inversion H2.
    rewrite (nat_inc_list_app (Zlength l1) _ (Zlength (l1 ++ l2))) in H5.
    rewrite Z.sub_cancel_r in H5.
    rewrite Zlength_app at 1.
    rewrite H5. reflexivity.
    rewrite combine_same_length in H1. omega.
    repeat rewrite Zlength_correct.
    rewrite nat_inc_list_length.
    rewrite Z2Nat.id. reflexivity.
    omega. rep_omega.
    rewrite Zlength_app. rep_omega.
Qed.

Lemma get_popped_meaning:
  forall l i,
    0 <= i < Zlength l ->
    In i (get_popped l) <-> Znth i l = inf + 1.
Proof.
  intros. generalize dependent i.
  induction l; intros.
  1: rewrite Zlength_nil in H; omega.
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
           rewrite Z2Nat.id; omega.
      }
      rewrite nat_inc_list_hd in H0 by omega.
      simpl in H0. destruct H0.
      * inversion H0. rewrite Z.eqb_eq in H1.
        rewrite <- inf_eq. rep_omega.
      * pose proof (in_combine_r _ _ _ _ H0).
        exfalso.
        apply in_tl_nat_inc_list in H2.
        omega.
    + unfold get_popped.
      rewrite (behead_list (nat_inc_list (Z.to_nat (Zlength (a :: l))))).
      2: { rewrite Zlength_correct.
           rewrite nat_inc_list_length.
           rewrite Z2Nat.id; omega.
      }
      rewrite nat_inc_list_hd by omega.
      simpl.
      destruct (a =? 1879048193) eqn:?.
      simpl; left; trivial.
      rewrite Z.eqb_neq in Heqb.
      exfalso; apply Heqb.
      rewrite Znth_0_cons in H0.
      rewrite <- inf_eq in H0. omega.
  - rewrite Znth_pos_cons by omega.
    rewrite Zlength_cons in H.
    assert (0 <= (i-1) < Zlength l) by omega.
    assert (Zlength [a] = 1) by reflexivity.
    change (a :: l) with ([a] ++ l).
    rewrite in_get_popped by omega. apply IHl; omega.
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
  repeat rewrite get_popped_meaning; [| rewrite upd_Znth_Zlength; omega | omega].
  rewrite upd_Znth_diff; trivial; reflexivity.
Qed.

Lemma get_popped_range:
  forall n l,
    In n (get_popped l) ->
    0 <= n < Zlength l.
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
     SEP (data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) v_pq;
          data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) (pointer_val_val prev);
          data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) (pointer_val_val dist);
          graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
  - unfold SIZE. rep_omega.
  - unfold data_at, data_at_, field_at_, SIZE; entailer!.
  - forward. forward.
    forward_call (v_pq, i, inf, (list_repeat (Z.to_nat i) (Vint (Int.repr inf)) ++
             list_repeat (Z.to_nat (SIZE - i)) Vundef)).
    replace 8 with SIZE by (unfold SIZE; rep_omega).
    rewrite inf_eq2.
    assert ((upd_Znth i
                      (list_repeat (Z.to_nat i) (Vint (Int.repr inf)) ++
                                   list_repeat (Z.to_nat (SIZE - i)) Vundef) (Vint (Int.repr inf))) =
            (list_repeat (Z.to_nat (i + 1)) (Vint (Int.repr inf)) ++ list_repeat (Z.to_nat (SIZE - (i + 1))) Vundef)). {
      rewrite upd_Znth_app2 by (repeat rewrite Zlength_list_repeat by omega; omega).
      rewrite Zlength_list_repeat by omega.
      replace (i-i) with 0 by omega.
      rewrite <- list_repeat_app' by omega.
      rewrite app_assoc_reverse; f_equal.
      rewrite upd_Znth0_old. 2: rewrite Zlength_list_repeat; omega.
      rewrite Zlength_list_repeat by omega.
      rewrite sublist_list_repeat by omega.
      replace (SIZE - (i + 1)) with (SIZE - i - 1) by omega.
      replace (list_repeat (Z.to_nat 1) (Vint (Int.repr inf))) with ([Vint (Int.repr inf)]) by reflexivity. easy.
    }
    rewrite H5. entailer!.
  - (* At this point we are done with the
       first for loop. The arrays are all set to INF. *)
    replace (SIZE - SIZE) with 0 by omega; rewrite list_repeat_0, <- (app_nil_end).
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
           (* Information about the ranges
              of the three arrays *)
           inrange_prev prev_contents;
           inrange_dist dist_contents;
           inrange_priq priq_contents)
       LOCAL (temp _dist (pointer_val_val dist);
              temp _prev (pointer_val_val prev);
              temp _src (Vint (Int.repr src));
              lvar _pq (tarray tint SIZE) v_pq;
              temp _graph (pointer_val_val arr))
       SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) v_pq;
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
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
       SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) v_pq);
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
    + Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) src).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat SIZE) inf) = SIZE). {
        rewrite Zlength_list_repeat; omega. }
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
          rewrite new. rewrite <- inf_eq. omega.
        }
        split3; [| |split3; [| |split]];
         try apply inrange_upd_Znth;
         try rewrite upd_Znth_same; try omega; trivial.
        all: rewrite <- inf_eq; unfold SIZE in *; omega.
      }
      (* And now we must show dijkstra_correct for the initial arrays *)
      (* First, worth noting that _nothing_ has been popped so far *)
      assert (get_popped (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) = []).
      { apply get_popped_empty. rewrite Forall_forall; intros.
        rewrite upd_Znth_unfold in H15. 2: omega.
        apply in_app_or in H15.
        destruct H15; [| apply in_inv in H15; destruct H15].
        1,3: rewrite sublist_list_repeat in H15 by omega;
          apply in_list_repeat in H15; omega.
        rewrite <- H15. compute; omega.
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
          rewrite upd_Znth_diff in H17; try omega.
          rewrite Znth_list_repeat_inrange in H17; omega.
        }
        subst dst. left; trivial.
      * split; trivial.
        assert (0 <= dst < SIZE) by
            (rewrite <- (vvalid_range g dst); trivial).
        rewrite upd_Znth_diff; try omega.
        rewrite Znth_list_repeat_inrange. trivial. omega.
        intro. subst dst. rewrite upd_Znth_same in H17.
        inversion H17. omega.
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
            rewrite H15 in H14; simpl in H14;
              now inversion H14.
        }
        clear H14.
        forward_call (v_pq, priq_contents). Intros u.
        (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

        (* We prove a few useful facts about u: *)
        assert (0 <= u < Zlength priq_contents). {
          rewrite H14.
          apply find_range.
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H11.
          inversion H11. simpl. left; trivial.
        }
        rewrite Znth_0_hd, <- H14 by omega.
        do 2 rewrite upd_Znth_map.
        assert (~ (In u (get_popped priq_contents))). {
          intro.
          rewrite get_popped_meaning in H17 by omega.
          rewrite <- isEmpty_in' in H15.
          destruct H15 as [? [? ?]].
          rewrite H14 in H17.
          rewrite Znth_find in H17.
          2: {
            rewrite <- Znth_0_hd by (unfold SIZE in *; omega).
            apply min_in_list; [ apply incl_refl | apply Znth_In; unfold SIZE in *; omega].
          }
          pose proof (fold_min _ _ H15).
          omega.
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
               forall dst, inv_popped g src prev_contents' priq_contents' dist_contents' dst;
              (* inv_unpopped is restored for those vertices
                 that the for loop has scanned and repaired *)
               forall dst,
                 0 <= dst < i ->
                 inv_unpopped g src prev_contents' priq_contents' dist_contents' dst;
                 
                 (* a weaker version of inv_popped is
                    true for those vertices that the
                    for loop has not yet scanned *)
                 forall dst,
                   i <= dst < SIZE ->
                   Znth dst priq_contents' < inf ->
                   let mom := Znth dst prev_contents' in
                   exists p2mom,
                     path_correct g prev_contents' dist_contents' src mom p2mom /\
                     (forall step,
                         In_path g step p2mom ->
                         In step (get_popped priq_contents') /\
                         step <> u) /\
                     path_globally_optimal g src mom p2mom /\
                     elabel g (mom, dst) < inf /\
                     (path_cost g p2mom) + (Znth dst (Znth mom (graph_to_mat g))) < inf /\
                     Znth dst dist_contents' = Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) /\
                     forall mom' p2mom',
                       path_correct g prev_contents' dist_contents' src mom' p2mom' ->
                       (forall step',
                           In_path g step' p2mom' ->
                           In step' (get_popped priq_contents') /\
                           step' <> u) ->
                       path_globally_optimal g src mom' p2mom' ->
                       path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) <= careful_add (path_cost g p2mom') (Znth dst (Znth mom' (graph_to_mat g)));
                       
                       (* similarly for inv_unseen,
                          the invariant has been
                       restored until i:
                       u has been taken into account *)
                                   forall dst,
                                     0 <= dst < i ->
                                     inv_unseen prev_contents' priq_contents' dist_contents' dst;

                                     (* and a weaker version of inv_unseen is
                   true for those vertices that the
                   for loop has not yet scanned *)
                                     forall dst,
                                       i <= dst < SIZE ->
                                       Znth dst priq_contents' = inf ->
                                       Znth dst dist_contents' = inf /\
                                       Znth dst prev_contents' = inf;
                                       (* further, some useful facts
                                          about src... *)
                                         Znth src dist_contents' = 0;
                                         Znth src prev_contents' = src;
                                         Znth src priq_contents' <> inf;

                                         (* a useful fact about u *)
                                         In u (get_popped priq_contents');

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
                SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents')) (pointer_val_val prev);
                     data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents')) v_pq;
                     data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents')) (pointer_val_val dist);
                     graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
        -- unfold SIZE; rep_omega.
        -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
          (* We must prove the for loop's invariants for i = 0 *)
          Exists prev_contents.
          Exists priq_contents_popped.
          Exists dist_contents.
          repeat rewrite <- upd_Znth_map.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u. 
          split3; [| | split3; [| |split3]].
          ++ (* We must show inv_popped for all
                 dst that are in range. *)
            unfold inv_popped. intros.
            pose proof (get_popped_range _ _ H14).
            rewrite upd_Znth_Zlength in H31 by omega.
            rewrite H11 in H31.
            rewrite <- (vvalid_range g) in H31.
            destruct (H4 dst H31) as [? [? ?]].
            unfold inv_popped in H32.
            (* now we must distinguish between those
                 vertices that were already popped
                 and u, which was just popped
             *)
            destruct (Z.eq_dec dst u).
            **  (* show that u is a valid entrant *)
              subst dst.
              unfold inv_unpopped in H33.
              assert (Znth u priq_contents < inf).
              { apply find_min_lt_inf; auto. unfold SIZE in H11. omega. }
              specialize (H33 H35).
              destruct H33.
              1: { (* src is being popped *)
                rewrite H33 in *.
                exists (u, []); split3.
                - split3; [| | split3]; trivial.
                  + simpl. destruct H2 as [? [? [? ?]]].
                    red in H2. rewrite H2. omega.
                  + split; trivial.
                  + unfold path_cost. simpl. rewrite <- inf_eq. omega.
                  + rewrite Forall_forall; intros.
                    simpl in H36. omega.
                - intros. destruct H36.
                  + simpl in H36. rewrite H36, H33; trivial.
                  + destruct H36 as [? [? ?]].
                    simpl in H36; omega.
                - unfold path_globally_optimal; intros.
                  unfold path_cost at 1; simpl.
                  apply path_cost_pos; trivial.
              }
              destruct H33 as [? [p2mom [? [? [? [? [? [? ?]]]]]]]].
              unfold VType in *.
              remember (Znth u prev_contents) as mom.
              assert (vvalid g mom). {
                destruct H36 as [? [? _]].
                apply (valid_path_valid g p2mom); trivial.
                destruct H43.
                apply pfoot_in; trivial.
              }
              (* this the best path to u:
                    go, optimally, to mom, and then take one step
               *)
              exists (fst p2mom, snd p2mom +:: (mom, u)).
              split3; trivial.
              --- destruct H36 as [? [? [? [? ?]]]].
                  assert (path_cost g p2mom + elabel g (mom, u) < inf).
                  { rewrite elabel_Znth_graph_to_mat; trivial; simpl. 
                    apply vvalid2_evalid; trivial.
                  }
                  split3; [| | split3].
                  +++
                    destruct H44.
                    apply valid_path_app_cons; trivial;
                      try rewrite <- surjective_pairing; trivial.
                    apply vvalid2_evalid; trivial.
                    
                  +++
                    rewrite (surjective_pairing p2mom) in *.
                    simpl.
                    replace (fst p2mom) with src in *.
                    apply path_ends_app_cons; trivial.
                    destruct H44. simpl in H44; omega.
                  +++ 
                    rewrite path_cost_app_cons; trivial.
                    *** unfold VType in *. omega.
                    *** apply vvalid2_evalid; trivial.
                  +++
                    rewrite path_cost_app_cons; trivial.
                    rewrite elabel_Znth_graph_to_mat; simpl; try omega; trivial.
                    apply vvalid2_evalid; trivial.
                    unfold VType in *. omega.
                    apply vvalid2_evalid; trivial.
                  +++ unfold VType in *.
                      rewrite Forall_forall. intros.
                      rewrite Forall_forall in H47.
                      apply in_app_or in H49.
                      destruct H49.
                      *** specialize (H47 _ H49). trivial.
                      *** simpl in H49.
                          destruct H49; [| omega].
                          rewrite (surjective_pairing x) in *.
                          inversion H49.
                          simpl.
                          rewrite <- H51, <- H52.
                          omega.
              --- intros.
                  destruct H36 as [_ [? _]].
                  apply (in_path_app_cons _ _ _ src) in H44; trivial.
                  destruct H44.
                  +++ specialize (H37 _ H44).
                      rewrite <- get_popped_irrel_upd; try omega; trivial.
                      apply get_popped_range in H37; omega.
                      intro. rewrite H45 in H37.
                      apply H17; trivial.
                  +++ rewrite H44.
                      rewrite get_popped_meaning.
                      rewrite upd_Znth_same; omega.
                      rewrite upd_Znth_Zlength; omega.
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
                unfold path_globally_optimal in H38.
                destruct H36 as [? [? [? [? ?]]]].
                assert (evalid g (mom, u)) by
                    (apply vvalid2_evalid; trivial).
                rewrite path_cost_app_cons; trivial.
                2: rewrite elabel_Znth_graph_to_mat; simpl; trivial; omega.
                rewrite elabel_Znth_graph_to_mat; trivial.
                simpl.
                destruct (Z_le_gt_dec
                            (path_cost g p2mom + Znth u (Znth mom (graph_to_mat g)))
                            (path_cost g p')); auto.
                apply Z.gt_lt in g0.
                destruct (zlt (path_cost g p') inf).
                2: unfold VType in *; omega.
                
                exfalso.
                unfold VType in *.   
                assert (exists p1 mom' child' p2,
                           path_glue p1 (path_glue (mom', [(mom',child')]) p2) = p' /\
                           valid_path g p1 /\
                           valid_path g p2 /\
                           path_ends g p1 src mom' /\
                           path_ends g p2 child' u /\
                           In mom' (get_popped priq_contents) /\
                           path_cost g p1 < inf /\
                           path_cost g p2 < inf /\
                           Znth child' (Znth mom' (graph_to_mat g)) < inf /\
                           path_cost g p2 + Znth child' (Znth mom' (graph_to_mat g)) < inf /\
                           evalid g (mom', child')                          
                       (* etc *)) by admit.
                
                destruct H51 as [p1 [mom' [child' [p2 [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]].

                rewrite <- H51 in g0.
                
                (* new g0: path_cost p'1 + (label mom' child') + path_cost p'2 < path_cost g p2mom + ... *)

                
 
                assert (0 <= path_cost g (mom', [(mom', child')]) < inf). {
                  rewrite one_step_path_Znth; trivial.
                  red in H1.
                  destruct H2 as [? [? _]].
                  red in H2, H62.
                  rewrite H62 in H61.
                  destruct H61.
                  rewrite H2 in H61, H63.
                  rewrite graph_to_mat_Zlength in H1.
                  specialize (H1 _ _ H63 H61).
                  destruct H1.
                  2: unfold VType in *; omega.
                  unfold VType in *.
                  split; [destruct H1; omega|].
                  apply Z.le_lt_trans with (m := Int.max_signed / SIZE).
                  apply H1.
                  compute; trivial.
                }
                unfold VType in *.
                do 2 rewrite path_cost_path_glue in g0; trivial.
                2: omega.

                rewrite careful_add_clean in g0; trivial; try omega; try apply path_cost_pos; trivial.
                rewrite careful_add_clean in g0; trivial; try omega; try apply path_cost_pos; trivial.
                2: {
  (* path_cost g (mom', [(mom', child')]) + path_cost g p2 < inf *)
                  unfold path_cost at 1. simpl.
                     rewrite careful_add_comm, careful_add_id.
                     rewrite elabel_Znth_graph_to_mat; trivial; simpl.
                     omega.
                }
                2: {
  (* 0 <= careful_add (path_cost g (mom', [(mom', child')])) (path_cost g p2) *)
                  apply careful_add_pos; apply path_cost_pos; trivial.
                     simpl.
                     red in H2. destruct H2 as [? [? [? ?]]].
                     unfold strong_evalid.
                     rewrite H64, H65; simpl.
                     split3; [| | split]; trivial;
                       apply H63 in H61; destruct H61; trivial.
                }
                2: {
  (* path_cost g p1 +
  careful_add (path_cost g (mom', [(mom', child')])) (path_cost g p2) < inf
   *)
                  rewrite <- H51 in l.
                  rewrite path_cost_path_glue in l; trivial.
                  assert (valid_path g (path_glue (mom', [(mom', child')]) p2)). {
                    Opaque valid_path.
                    unfold path_glue. simpl.
                    rewrite valid_path_cons_iff.
                    red in H2. destruct H2 as [? [? [? ?]]].
                    unfold strong_evalid.
                    rewrite H64, H65. simpl.
                    split3; trivial.
                    - split3; trivial.
                      + apply (valid_path_valid _ p1); trivial.
                        destruct H54. apply pfoot_in; trivial.
                      + apply (valid_path_valid _ p2); trivial.
                        destruct H55.
                        rewrite (surjective_pairing p2) in *.
                        simpl in H55. rewrite H55 in *.
                        unfold In_path. left. simpl; trivial.
                    - rewrite (surjective_pairing p2) in *.
                      simpl. replace (fst p2) with child' in H53; trivial.
                      destruct H55. simpl in H55. omega.
                      Transparent valid_path.
                  }

                  rewrite careful_add_clean in l; try apply path_cost_pos; trivial.
                  2: apply careful_add_inf_clean; trivial;
                    apply path_cost_pos; trivial.
                  rewrite path_cost_path_glue in l; trivial.
                  rewrite one_step_path_Znth; trivial.
                }
                  

                (* and now just a little cleanup...  *)
                unfold path_cost at 2 in g0. simpl in g0.
                rewrite careful_add_clean in g0.
                2: omega.
                2: { rewrite elabel_Znth_graph_to_mat; simpl; trivial.
                     rewrite one_step_path_Znth in H62; trivial.
                     omega.
                }
                2: { rewrite elabel_Znth_graph_to_mat; simpl; trivial. }

                rewrite Z.add_0_l in g0.
                rewrite elabel_Znth_graph_to_mat in g0 by assumption.
                simpl in g0.
                rewrite Z.add_assoc in g0. 


                (* from global optimal within dark green, you know that there exists a 
   path p2mom', the global minimum from src to mom' *)
                assert (vvalid g mom'). {
                  destruct H2 as [_ [? _]].
                  red in H2. rewrite H2 in H61.
                  destruct H61; trivial.
                }
                destruct (H4 mom' H63) as [? _].
                unfold inv_popped in H64.
                destruct (H64 H56) as [p2mom' [? [? ?]]].

                (* and path_cost of p2mom' will be <= that of p1 *)
                specialize (H67 p1 H52 H54). 
                
                (* assert by transitivity that
     path_cost (p2mom' +++ (mom', child') +++ p2) < path_cost p2mom +++ ...   *) 
                
                assert (path_cost g p2mom' + Znth child' (Znth mom' (graph_to_mat g)) + path_cost g p2 <
                        path_cost g p2mom + Znth u (Znth mom (graph_to_mat g))). {     
                  apply (Z.le_lt_trans _ (path_cost g p1 + Znth child' (Znth mom' (graph_to_mat g)) + path_cost g p2) _); trivial.
                  do 2 rewrite <- Z.add_assoc.
                  apply Zplus_le_compat_r; trivial.
                }
                
                (* assert that child' <> u 
   because then LHS is x + c + ? and RHS is x + c *)
                assert (child' <> u). {
                  intro; subst child'.
                  pose proof (path_cost_pos g p2 H2 H53 H1).
                  admit.
                }
                

                (* now we know that child' is not minimal, and thus x + c >= p2mom +++ u *)
                (* thus we have both x + c >= p2mom +++ u     and
                       x + c + ? < p2mom +++ u *)


                admit.
                
            ** (* Here we must show that the
                    vertices that were popped earlier
                    are not affected by the addition of
                    u to the popped set.

                    As expected, this is significantly easier.
                *)
              rewrite <- get_popped_irrel_upd in H14; try omega.
              2: { replace (Zlength priq_contents) with SIZE by omega.
                   apply (vvalid_range g dst); trivial.
              }
              specialize (H32 H14).
              destruct H32 as [? [? [? ?]]].
              exists x. split3; trivial.
              intros.
              specialize (H35 _ H37).
              destruct H32.
              rewrite <- get_popped_irrel_upd; try omega; trivial.
              apply get_popped_range in H35; omega.
              intro contra. rewrite contra in H35.
              apply H17; trivial.
            ** trivial.
          ++ (* No vertex has been repaired yet... *)
            intros; omega.
          ++ (* ... in fact, any vertex that is
                 "seen but not popped"
                 is that way without the benefit of u.

                 We will be asked to provide a locally optimal
                 path to such a dst, and we will simply provide the
                 old one best-known path
              *)
            intros.
            destruct (Z.eq_dec dst u).
            1: subst dst; rewrite upd_Znth_same in H31; omega.
            rewrite upd_Znth_diff in H31 by omega.
            rewrite <- (vvalid_range g) in H14.
            destruct (H4 dst H14) as [_ [? _]].
            unfold inv_unpopped in H32.
            specialize (H32 H31).
            destruct H32.
            1: {
              subst dst.
              rewrite H6.
              exists (src, []); split3; [| | split3; [| | split3]].
              - split3; [| | split3]; trivial.
                + split; trivial.
                + unfold path_cost. simpl. rewrite <- inf_eq. omega.
                + rewrite Forall_forall; intros.
                  simpl in H32. omega.
              - intros. destruct H32.
                + simpl in H32.
                  rewrite H32; split; trivial.
                  rewrite <- get_popped_irrel_upd; try omega; trivial.
                  assert (Znth u priq_contents < inf). {
                    apply find_min_lt_inf; auto. unfold SIZE in H11. omega. }
                  rewrite H11 in H16.
                  rewrite <- (vvalid_range g) in H16; trivial.
                  destruct (H4 _ H16) as [_ [? _]].
                  destruct (H34 H33). 1: exfalso; now apply n.
                  destruct H35 as [? [p2mom [? [? _]]]]. apply H37.
                  left. destruct H36 as [_ [[? _] _]]. destruct p2mom.
                  now simpl in H36 |- *.
                + destruct H32 as [? [? ?]].
                  simpl in H32; omega.
              - unfold path_globally_optimal; intros.
                unfold path_cost at 1; simpl.
                apply path_cost_pos; trivial.
              - rewrite elabel_Znth_graph_to_mat; try omega; trivial.
                simpl; rewrite H3. compute; trivial.
                trivial.
                apply vvalid2_evalid; trivial.
              - rewrite H3; trivial; unfold path_cost; simpl.
                compute; trivial.
              - rewrite H3; simpl; trivial.
              - intros.
                rewrite H3; trivial. unfold path_cost at 1; simpl.
                apply careful_add_pos.
                apply path_cost_pos; trivial.
                destruct H32; trivial.
                red in H1. 
                rewrite graph_to_mat_Zlength in H1.
                destruct H32 as [? [? _]].
                destruct H35.
                apply pfoot_in in H36.
                pose proof (valid_path_valid _ _ _ H32 H36).
                rewrite vvalid_range in H14, H37; trivial.
                specialize (H1 _ _ H14 H37). destruct H1.
                + omega.
                + rewrite H1. compute; inversion 1.
            }                    
            destruct H32 as [? [p2mom [? [? ?]]]].
            unfold VType in *.
            remember (Znth dst prev_contents) as mom.
            destruct H35 as [? [? [? [? ?]]]].
            (* We have retrieved the old path to mom,
                and we will now provide it.

                Several of the proof obligations
                fall away easily, and those that remain
                boil down to showing that
                u was not involved in this
                locally optimal path.
             *)
            exists p2mom. split3; [| |split3; [| |split3]]; trivial.
            ** intros.
               specialize (H34 _ H40).
               assert (step <> u). {
                 intro.
                 unfold VType in *. rewrite H41 in H34.
                 apply H17; trivial.
               }
               split; trivial.
               rewrite <- get_popped_irrel_upd; try omega; trivial.
               apply get_popped_range in H34; omega.
            ** intros.
               apply H39; trivial.
               intros.
               specialize (H41 _ H43). destruct H41.
               rewrite <- get_popped_irrel_upd in H41; try omega; trivial.
               apply get_popped_range in H41.
               rewrite upd_Znth_Zlength in H41; try omega; trivial.
            ** trivial.
          ++ (* no unseen vertices have been repaired yet *)
            intros. omega.
          ++ intros.
             destruct (Z.eq_dec dst u).
             1: { rewrite e in H31.
                  rewrite upd_Znth_same in H31 by omega.
                  inversion H31.
             }
             rewrite upd_Znth_diff in H31 by omega.
             rewrite <- (vvalid_range g) in H14; trivial.
             destruct (H4 dst H14) as [_ [_ ?]].
             unfold inv_unseen in H32.
             specialize (H32 H31).
             destruct H32.
             split; trivial.
          ++ destruct (Z.eq_dec src u).
             1: subst src; rewrite upd_Znth_same; omega.
             rewrite upd_Znth_diff; omega.
          ++ split.
             ** apply get_popped_meaning.
                rewrite upd_Znth_Zlength; omega.
                rewrite upd_Znth_same; omega.
             ** apply inrange_upd_Znth; trivial;
                  rewrite <- inf_eq; rep_omega.
        -- (* We now begin with the for loop's body *)
          assert (0 <= u < Zlength (graph_to_mat g)). {
            unfold graph_to_mat.
            repeat rewrite Zlength_map.
            rewrite nat_inc_list_Zlength.
            rep_omega.
          }
          assert (Zlength (Znth u (graph_to_mat g)) = SIZE). {
            rewrite Forall_forall in H0. apply H0. apply Znth_In. omega.
          }
          freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
          rewrite (graph_unfold _ _ _ u) by omega.
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
            1: rewrite offset_offset_val; simpl; f_equal; rep_omega.
            destruct H36 as [? [? [? [? ?]]]].
            unfold field_compatible; split3; [| | split3]; auto.
            unfold legal_nested_field; split; [auto | simpl; omega].
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
               replace 8 with SIZE in H38.
               assert (0 <= i < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; omega).
               assert (0 <= u < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; omega).
               specialize (H1 i u H39 H40).
               rewrite inf_eq2 in H38.
               rewrite Heqcost in *.
               rewrite Int.signed_repr in H38.
               2: { destruct H1.
                    - unfold VType in *.
                      replace SIZE with 8 in H1.
                      destruct H1.
                      pose proof (Int.min_signed_neg).
                      assert (Int.max_signed / 8 <= Int.max_signed). {
                        compute.
                        intro. inversion H43.
                      }
                      split; try omega.
                    - rewrite H1.
                      rewrite <- inf_eq.
                      compute; split; inversion 1.
               }
               rewrite Int.signed_repr in H38.
               2: rewrite <- inf_eq; compute; split; inversion 1.
               destruct H1; omega.
             }
             assert (0 <= Znth u dist_contents' <= inf). {
               assert (0 <= u < Zlength dist_contents') by omega.
               apply (Forall_Znth _ _ _ H40) in H32.
               assumption.
             }
             assert (0 <= Znth i dist_contents' <= inf). {
               assert (0 <= i < Zlength dist_contents') by omega.
               apply (Forall_Znth _ _ _ H41) in H32.
               assumption.
             }
             assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
               split; [omega|].
               unfold inf in *. rep_omega.
             }
             forward. forward. forward_if.
             ** rewrite Int.signed_repr in H43
                 by (unfold inf in *; rep_omega).
                (* At this point we know that we are definitely
        going to make edits in the arrays:
        we have found a better path to i, via u *)
                assert (~ In i (get_popped priq_contents')). {
                  (* This useful fact is true because
          the cost to i was just improved.
          This is impossible for popped items.
                   *)
                  intro.
                  unfold inv_popped in H21.
                  destruct (H21 _ H44) as [p2i [? [? ?]]].
                  destruct (H21 _ H29) as [p2u [? [? ?]]].
                  unfold path_globally_optimal in H47.
                  specialize (H47 (fst p2u, snd p2u +:: (u,i))).
                  rewrite Heqcost in H43.
                  destruct H48 as [? [? [? [? ?]]]].
                  destruct H45 as [? [? [? [? ?]]]].
                  rewrite H57, H53 in H43.
                  apply Zlt_not_le in H43.
                  unfold VType in *.
                  apply H43.
                  rewrite path_cost_app_cons in H47; trivial.
                  2: { rewrite elabel_Znth_graph_to_mat; trivial.
                       2: { apply vvalid2_evalid; 
                            try apply vvalid_range;
                            trivial.
                       }
                       simpl. omega.
                  }
                  rewrite elabel_Znth_graph_to_mat in H47; trivial.
                  2: { apply vvalid2_evalid; 
                            try apply vvalid_range;
                            trivial.
                       }
                  simpl fst in H47.
                  simpl snd in H47.
                  apply H47. 
                  - destruct H51.
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
                    destruct H51. simpl in H51; omega.
                  - apply vvalid2_evalid;
                      try apply vvalid_range; trivial.
                }
                assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
                    (repeat rewrite Zlength_map; omega).
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
                assert (u <> i) by (intro; subst; omega).
                split3; [| | split3; [| | split3; [| | split3]]].
                --- 
                  intros. pose proof (H21 dst).
                  unfold inv_popped in H58.
                  unfold inv_popped.
                  intros.
                  destruct (Z.eq_dec dst i).
                  +++ subst dst.
                      rewrite get_popped_meaning, upd_Znth_same in H59.
                      3: rewrite upd_Znth_Zlength.
                      all: omega.
                  +++ pose proof (get_popped_range _ _ H59).
                      rewrite upd_Znth_Zlength in H60 by omega.
                      rewrite <- get_popped_irrel_upd in H59; try omega.
                      specialize (H58 H59).
                      destruct H58 as [p2dst [? [? ?]]].
                      exists p2dst; split3; trivial.
                      *** destruct H58 as [? [? [? [? ?]]]].
                          split3; [| | split3]; trivial.
                          1: rewrite upd_Znth_diff; omega.
                          rewrite Forall_forall; intros.
                          assert (In_path g (snd x) p2dst). {
                            unfold In_path. right.
                            exists x. split; trivial.
                            destruct H2 as [? [? [? ?]]].
                            red in H70; rewrite H70.
                            right; trivial.
                          }
                          specialize (H61 _ H68).
                          rewrite Forall_forall in H66.
                          specialize (H66 _ H67).
                          assert (snd x <> i). {
                            intro contra.
                            unfold VType in *.
                            rewrite contra in H61.
                            apply H44. trivial.
                          }
                          unfold VType in *.
                          rewrite upd_Znth_diff; try omega.
                          apply get_popped_range in H61; omega.
                      *** intros.
                          specialize (H61 _ H63).
                          rewrite <- get_popped_irrel_upd; try omega; trivial.
                          apply get_popped_range in H61; omega.
                          intro contra. rewrite contra in H61.
                          apply H44. trivial.
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
                        unfold inv_popped in H21.
                        destruct (H21 _ H29) as [p2u [? [? ?]]].
                        unfold VType in *.
                        rewrite upd_Znth_same by omega.
                        right.
                        split.
                        1: { intro. assert (In_path g src p2u). {
                               left. destruct H60 as [_ [[? _] _]].
                               destruct p2u. now simpl in H60 |- *. }
                             specialize (H61 _ H64).
                             now subst. }
                        exists p2u.
                        split3; [| |split3; [| |split3]]; trivial.
                        *** destruct H60 as [? [? [? [? ?]]]].
                            split3; [ | | split3]; trivial.
                            ---- rewrite upd_Znth_diff by omega.
                                 trivial.
                            ---- rewrite Forall_forall; intros.
                                 assert (In_path g (snd x) p2u). {
                                   unfold In_path. right.
                                   exists x. split; trivial.
                                   destruct H2 as [? [? [? ?]]].
                                   unfold dst_edge in H70.
                                   rewrite H70. right; trivial.
                                 }
                                 specialize (H61 _ H68).
                                 rewrite Forall_forall in H66.
                                 specialize (H66 _ H67).
                                 unfold VType in *.
                                 rewrite upd_Znth_diff; try omega; trivial.
                                 apply get_popped_range in H61; omega.
                                 intro. rewrite H69 in H61.
                                 apply H44. trivial.
                        *** intros.
                            specialize (H61 _ H63).
                            rewrite <- get_popped_irrel_upd; try omega; trivial.
                            apply get_popped_range in H61; omega.
                            intro; rewrite H64 in H61. apply H44; trivial.
                        *** rewrite elabel_Znth_graph_to_mat;
                              simpl; trivial; try omega.
                            apply vvalid2_evalid;
                              try apply vvalid_range; trivial.
                        *** rewrite upd_Znth_same in H59 by omega.
                            destruct H60 as [_ [_ [_ [? _]]]].
                            rewrite <- H60. omega.
                        *** rewrite upd_Znth_same by omega.
                            destruct H60 as [_ [_ [_ [? _]]]].
                            omega.
                        *** intros. 
                            rewrite upd_Znth_same in H59 by omega.
 (* This is another key point in the proof:
    we must show that the path via u is
    better than all other paths via
    other popped verices *)
                            (*
                            destruct (Z.eq_dec mom' u).
                            1: {
                              subst mom'.
                              (* use path_globally_optimal
                                 of u to prove that first
                                 is le first. then done.
                               *)
                              unfold path_globally_optimal in H62.
                              specialize (H62 _ H63 H66).
                              rewrite careful_add_clean.
                              1: omega.
                              1: apply path_cost_pos; trivial.
                              2: {
                                rewrite upd_Znth_same in H59 by omega.
                                remember (path_cost g p2mom') as pc.
                                rewrite upd_Znth_diff in H68 by omega.
                                unfold VType in *.
                                omega.
                              } 
                              red in H1.
                              rewrite graph_to_mat_Zlength in H1.
                              replace (Zlength priq_contents) with SIZE in H16.
                              specialize (H1 _ _ H18 H16).
                              destruct H1; omega.
                            }
                             *)
                            (*
                            assert (In_path g mom' p2mom'). {
                              destruct H63 as [_ [? _]].
                              destruct H63.
                              apply pfoot_in in H66. trivial.
                            }
                             *)
                            (*
                            specialize (H64 _ H66).
                            rewrite <- get_popped_irrel_upd in H64;
                              try omega; trivial.
                            2: { replace (Zlength priq_contents') with SIZE by omega.
                                 destruct H63.
                                 apply (vvalid_range g); trivial.
                                 apply (valid_path_valid g p2mom'); trivial.
                            }
                            2: { intro. subst mom'.
                                 rewrite get_popped_meaning in H64.
                                 rewrite upd_Znth_same in H64; omega.
                                 rewrite upd_Znth_Zlength; omega.
                            }
                             *)
                              
  (* see H43: Znth u dist_contents' + Znth i (Znth u (graph_to_mat g)) < Znth i dist_contents'
     further, we know that for all popped items like mom', 
     Znth i dist_contents' < Znth mom' dist_contents' + (mom', i).
   *)
                            (*
                            destruct path_corr as [_ [_ [_ [? _]]]].
                            rewrite upd_Znth_diff in H74.
                            2: { replace (Zlength dist_contents') with SIZE by omega.
                                 destruct H2 as [? _].
                                 red in H2.
                                 rewrite <- H2.
                                 apply (valid_path_valid g p2mom'); trivial.
                            }
                            2: omega.
                            2: { intro.
                                 rewrite H75 in H64.
                                 rewrite get_popped_meaning in H64. omega. omega.
                            }
                            rewrite <- H74.
                            
                            assert (Znth i dist_contents' <= careful_add (Znth mom' dist_contents') (Znth i (Znth mom' (graph_to_mat g)))) by admit. (* invariant *)
                            unfold VType in *. 
                            omega.
                             *)
                            (*
                            ----  (* now we know that i was
                          seen, but unpopped *)
                              assert (Znth i priq_contents' < inf). {
                                assert (0 <= i < Zlength priq_contents') by omega.
                                pose proof (Forall_Znth _ priq_contents' i H70 H31).
                                Opaque inf. simpl in H71. Transparent inf.
                                rewrite get_popped_meaning in H44.
                                omega. omega.
                              }
                              *)

(*
Denote the old dist[i] as old-shortest-to-i.
So the known conditions are:

H43: dist[u] + graph[u][i] < old-shortest-to-i

H44: i is an unpopped vertex.

Now we prove for any other path p' which is from s to i
and composed by popped vertices (including u),
dist[u] + graph[u][i] <= path_cost p'.

There are two cases about p': In u p' \/ ~ In u p'
 *)
                            destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).
                            ++++ (* Yes, the path p2mom' goes via u *) 
                              (*
  1. In u p': p' is the path from s to i.
  Consider the vertex k which is
  just before i. Again, there are two cases:
  k = u \/ ~ k = u.
                                 *)
                              destruct (Z.eq_dec mom' u).
                              1: {
                                (*
        1.1 k = u: path_cost p' = path_cost [s to u] + graph[u][i].
        As we know, u is just popped, dist[u] is the
        global optimal, so dist[u] <= path_cost [s to u],
        so dist[u] + graph[u][i] <= path_cost p'.
        DONE
                                 *)
                                subst mom'.
                                unfold path_globally_optimal in H62.
                                destruct H63 as [? [? [? [? ?]]]].
                                specialize (H62 _ H63 H66).
                                rewrite careful_add_clean; try omega; trivial.
                                1: apply path_cost_pos; trivial.
                                rewrite upd_Znth_diff in H68 by omega.
                                rewrite <- H68; omega.
                              }
                              
                              
                              apply in_path_eq_epath_to_vpath in i0.
                              2: destruct H63; trivial.

(*
  1.2 ~ k = u: 
  
  p' can conceptually be split up as:
  path s to u ++ path u to k + edge k i.
 *) 
                                                                    
(*
  Since p' is composed by popped vertex
  (including u) only, k must be a popped
  vertex. Then it satisfies NewInv1, which means
  dist[k] <= path_cost [s to u] + path_cost [u to k]
  and the global optimal path from s to k is
  composed by popped vertices only. 
 *)
                              
                              assert (In_path g mom' p2mom'). {
                                destruct H63 as [_ [[_ ?] _]].
                                apply pfoot_in in H63.
                                trivial.
                              }
                              assert (mom' <> i). {
                                intro.
                                specialize (H64 _ H66).
                                rewrite H67 in H64.
                                rewrite get_popped_meaning, upd_Znth_same in H64; [| | rewrite upd_Znth_Zlength]; omega.
                              }
                              assert (vvalid g mom'). {
                                destruct H63.
                                apply (valid_path_valid g p2mom'); trivial.
                              }
                              assert (In mom' (get_popped priq_contents')). {
                                specialize (H64 _ H66).
                                rewrite <- get_popped_irrel_upd in H64; auto; try omega.
                                replace (Zlength priq_contents') with SIZE by omega.
                                apply (vvalid_range g); trivial.
                              }
                              assert (vvalid g i). {
                                destruct H2 as [? _].
                                red in H2; rewrite H2; trivial.
                              }
                              destruct H63 as [? [? [? [? ?]]]].
                              rewrite upd_Znth_diff in H73; trivial.
                              2,3: replace (Zlength dist_contents') with SIZE by omega; apply (vvalid_range g); trivial.

 (*   dist[k] <= path_cost [s to u] + path_cost [u to k]
  and the global optimal path from s to k is
  composed by popped vertices only. 
  DONE
  *)

                                  
  (*
    Thus dist[k] + len(edge k i) <= path_cost (path s to u ++ path u to k) + len (edge k i)
                                  = path_cost p'.
   *)
                              (* done, just proved equal in
                                 goal. can throw away the 
                                 careful_add easily.
                               *)
                                  
 
(*
  Since dist[k] only contains popped vertices, this path
  having dist[k] + edge k i also only contains popped vertices. 
  Thus we have old-shortest-to-i <= dist[k] + len(edge k i) because of Inv2.
 *)
(*
assert (i <= i < SIZE) by omega.
destruct (H23 _ H78 H70) as [p2ioldmom [? [? [? [? [? [? ?]]]]]]].
remember (Znth i prev_contents') as ioldmom.
rewrite <- H84 in H85.
assert (forall step' : Z,
           In_path g step' optimalp2mom' ->
           In step' (get_popped priq_contents') /\ step' <> u) by....

specialize (H85 mom' optimalp2mom' H74 H86 H76rem).
 *)

(* Said another way... the best-known path to i via popped vertices is 
   already logged in dist[i]. 
   So dist[i] <= p2any_popped_person + (person, i).
   In this case, that person is k.


Add to invariants? This is actually true of all vertices, 
no matter what class of poppedness they're in!
 *)
                              assert (Znth i dist_contents' <= careful_add (path_cost g p2mom') (Znth i (Znth mom' (graph_to_mat g)))) by admit.
                              (* this should come from an inv
                                 but is not possible rn *)
                              (* need to try and remove step <> u
                                 from inv_unpopped_weak
                               *)

                              (*
                              
                              {
                                    assert (i <= i < SIZE) by omega.
                                    destruct (H23 _ H77 H70)
                                    as [x [? [? [? [? [? [? ?]]]]]]].
                                    rewrite <- H83 in H84.
                                    apply H84; trivial.
                                    - split3; [| |split3]; trivial.
                                      destruct path_corr as [_ [_ [_ [? _]]]].
                                      rewrite upd_Znth_diff in H85; trivial.
                                      admit. omega.
                                      intro.
                                      rewrite H86 in H72.
                                      rewrite get_popped_meaning in H72.
                                      omega.
                                      omega.
                                      rewrite Forall_forall.
                                      intros.
                                      rewrite Forall_forall in H69.
                                      specialize (H69 _ H85).
                                      rewrite upd_Znth_diff in H69; trivial.
                                      replace (Zlength prev_contents') with SIZE by omega.
                                      apply (step_in_range2 g p2mom' x0); trivial.
                                      omega.
                                      intro.
                                      admit. (* easy *)
                                    - admi
}
*)
 
(*
  So we still have 
  dist[u] + graph[u][i] <=
  old-shortest-to-i <=
  dist[k] + len(edge k i) <=
  path_cost p'.
 *)
                              unfold VType in *.
                              destruct H60 as [_ [_ [_ [? _]]]].
                              omega.
                              ++++

                                (*
  2. ~ In u p': This means p' is totally composed by
  old popped vertices. According to Inv2,
  old-shortest-to-i <= path_cost p'.
  According to Cond:
  dist[u] + graph[u][i] < old-shortest-to-i, we have
  dist[u] + graph[u][i] <= path_cost p'.
                                 *)

                                admit.

                                (*
                                

                                

                                

                                  

                                

                                assert (Znth i dist_contents' <= careful_add (path_cost g p2mom') (Znth i (Znth mom' (graph_to_mat g)))). {
                                  assert (i <= i < SIZE) by omega.
                                  destruct (H23 i H66 H70) as [x [? [? [? [? [? [? ?]]]]]]].
                                  rewrite <- H77 in H78.
                                  apply H78; trivial.
                                  - unfold path_correct.
                                    split3; trivial; split3; trivial.
                                    + rewrite upd_Znth_diff in H68; trivial.
                                      * replace (Zlength dist_contents') with SIZE by omega.
                                        destruct H2 as [? _].
                                        red in H2. rewrite <- H2.
                                        apply (valid_path_valid g p2mom'); trivial.
                                        destruct H66.
                                        apply pfoot_in; trivial.
                                      * omega.
                                      * intro.
                                        assert (In_path g mom' p2mom'). {
                                        destruct H66.
                                        apply pfoot_in; trivial.
                                        }
                                        specialize (H64 _ H80).
                                        rewrite get_popped_meaning in H64.
                                        rewrite H79 in *.
                                        rewrite upd_Znth_same in H64.
                                        omega.
                                        omega.
                                        rewrite upd_Znth_Zlength.
                                        omega. omega.
                                    + rewrite Forall_forall. intros.
                                      rewrite Forall_forall in H69.
                                      specialize (H69 _ H79).
                                      rewrite upd_Znth_diff in H69; trivial.
                                      * unfold VType in *.
                                        replace (Zlength prev_contents') with SIZE by omega.
                                        red in H2.
                                        destruct H2 as [? [? [? ?]]].
                                        red in H2. rewrite <- H2.
                                        apply (valid_path_valid g p2mom'); trivial.
                                        unfold In_path. right.
                                        exists x0. split; trivial.
                                        rewrite H81, H82. right; trivial.
                                      * unfold VType in *. omega.
                                      * intro.
                                        assert (In_path g (snd x0) p2mom'). {
                                          unfold In_path. right.
                                          exists x0. split; trivial.
                                          red in H2. destruct H2 as [? [? [? ?]]].
                                          rewrite H82, H83. right; trivial.
                                        }
                                        specialize (H64 _ H81).
                                        rewrite get_popped_meaning in H64.
                                        rewrite H80 in *.
                                        rewrite upd_Znth_same in H64.
                                        omega.
                                        omega.
                                        rewrite upd_Znth_Zlength.
                                        omega. omega.
                                  - intros.
                                    assert (Hrem := H64).
                                    specialize (H64 _ H79).
                                    rewrite <- get_popped_irrel_upd in H64.
                                    + split; trivial.
                                      intro. rewrite H80 in H79.
                                      rewrite <- in_path_eq_epath_to_vpath in H79. exfalso.
                                      unfold VType in *.
                                      apply n0; trivial.
                                      trivial.
                                    + replace (Zlength priq_contents') with SIZE by omega.
                                      red in H2. destruct H2 as [? [? [? ?]]].
                                      red in H2.
                                      rewrite <- H2.
                                      apply (valid_path_valid g p2mom'); trivial.
                                    + omega.
                                    + intro.
                                      specialize (Hrem _ H79).
                                      subst step'.
                                      rewrite get_popped_meaning in Hrem.
                                      rewrite upd_Znth_same in Hrem.
                                      omega.
                                      omega.
                                      rewrite upd_Znth_Zlength; omega.
                                }
                                apply Z.le_trans with (m := Znth i dist_contents'); trivial.
                                destruct H60 as [_ [_ [_ [? _]]]].
                                rewrite <- H60; omega. *)
                    +++ assert (0 <= dst < i) by omega.
                        (* We will proceed using the
                old best-known path for dst *)
                        specialize (H22 _ H59).
                        unfold inv_unpopped in *.
                        intros.
                        rewrite upd_Znth_diff in H60 by omega.
                        specialize (H22 H60). destruct H22.
                        1: left; trivial.
                        destruct H22 as [? [p2mom [? [? [? [? [? [? ]]]]]]]].
                        unfold VType in *.
                        remember (Znth dst prev_contents') as mom. right.
                        split; trivial.


                        exists p2mom. split3; [| |split3; [| |split3]]; trivial.
                        *** destruct H61 as [? [? [? [? ?]]]].
                            split3; [| | split3]; trivial.
                            ---- rewrite upd_Znth_diff by omega;
                                   rewrite <- Heqmom; trivial.
                            ---- rewrite (upd_Znth_diff dst i) by omega.
                                 assert ((Znth dst prev_contents') <> i). {
                                   (* the path could not have gone
                           through i, since i is unpopped *)
                                   intro.
                                   apply H44.
                                   rewrite <- Heqmom in *.
                                   rewrite <- H72. apply H62.
                                   apply pfoot_in. now destruct H68.
                                 }
                                 rewrite upd_Znth_diff; try omega.
                                 2: {
                                   rewrite <- Heqmom.
                                   rewrite H36.
                                   destruct H2.
                                   unfold vertex_valid in H2.
                                   rewrite <- H2.
                                   apply (valid_path_valid g p2mom); trivial.
                                   destruct H68.
                                   apply pfoot_in; trivial.
                                 }
                                 rewrite <- Heqmom.
                                 trivial.
                            ---- rewrite Forall_forall; intros.
                                 rewrite Forall_forall in H71.
                                 specialize (H71 _ H72).
                                 rewrite upd_Znth_diff; try omega.
                                 1: unfold VType in *; rewrite H35;
                                   apply (step_in_range2 g p2mom); trivial.
                                 1: unfold VType in *; omega.
                                 intro contra. apply H44. apply H62. right. exists x.
                                 split; auto. right. destruct H2 as [_ [_ [_ ?]]]. red in H2.
                                 now rewrite H2.
                        *** intros.
                            specialize (H62 _ H68).
                            repeat rewrite <- get_popped_irrel_upd; try omega; trivial.
                            apply get_popped_range in H62; omega.
                            intro; rewrite H69 in H62; apply H44; trivial.
                        *** rewrite upd_Znth_diff by omega.
                            rewrite <- Heqmom; trivial.
                        *** rewrite upd_Znth_diff by omega.
                            rewrite <- Heqmom in *. trivial.
                        *** rewrite upd_Znth_diff by omega.
                            rewrite <- Heqmom in *. trivial.
                        *** rewrite upd_Znth_diff by omega.
                            rewrite upd_Znth_diff by omega.
                            rewrite <- Heqmom in *. trivial.
                        *** intros.
                            rewrite upd_Znth_diff by omega.
                            rewrite <- Heqmom.
                            apply H67; trivial.
                            ---- destruct H68 as [? [? [? [? ?]]]].
                                 split3; [| |split3]; trivial.
                                 ++++ assert (In mom' (get_popped priq_contents')). {
                                        assert (In_path g mom' p2mom'). {
                                          apply pfoot_in. now destruct H71. }
                                        specialize (H69 _ H75).
                                        rewrite get_popped_unchanged in H69; auto.
                                        - now rewrite H34.
                                        - omega.
                                        - intro. apply H44.
                                          rewrite get_popped_meaning; auto.
                                          now rewrite H34. }
                                      rewrite upd_Znth_diff in H73; try omega.
                                      **** rewrite H36. rewrite <- H34.
                                           now apply get_popped_range.
                                      **** intro. apply H44. now rewrite <- H76.
                                 ++++ rewrite Forall_forall; intros.
                                      rewrite Forall_forall in H74.
                                      specialize (H74 _ H75).
                                      unfold VType in *.
                                      rewrite upd_Znth_diff in H74;
                                        try omega.
                                      rewrite H35.
                                      apply (step_in_range2 g p2mom');
                                        trivial.
                                      intro. assert (In_path g i p2mom'). {
                                        right. exists x. split; auto.
                                        right. destruct H2 as [_ [_ [_ ?]]]. red in H2.
                                        now rewrite H2. } specialize (H69 _ H77).
                                      rewrite get_popped_meaning in H69.
                                      **** rewrite upd_Znth_same in H69. omega.
                                           now rewrite H34.
                                      **** rewrite upd_Znth_Zlength; now rewrite H34.
                            ---- intros.
                                 specialize (H69 _ H71).
                                 rewrite <- get_popped_irrel_upd in H69; try omega; trivial.
                                 apply get_popped_range in H69;
                                   rewrite upd_Znth_Zlength in H69; omega.
                                 intro. rewrite H72 in H69.
                                 rewrite get_popped_meaning in H69.
                                 rewrite upd_Znth_same in H69; omega.
                                 rewrite upd_Znth_Zlength; omega.
                --- intros.
                    assert (i <= dst < SIZE) by omega.
                    destruct (Z.eq_dec dst i).
                    1: subst dst; omega.
                    rewrite upd_Znth_diff in H59 by omega.
                    destruct (H23 _ H60 H59) as [p2mom [? [? ?]]].
                    unfold VType in *.
                    remember (Znth dst prev_contents') as mom.
                    rewrite upd_Znth_diff by omega.
                    exists p2mom.
                    destruct H63 as [? [? [? [? ?]]]].
                    split3; [| | split3; [| | split3]]; trivial.
                    +++ destruct H61 as [? [? [? [? ?]]]].
                        split3; [| | split3]; trivial.
                        *** rewrite <- Heqmom. trivial.
                        *** rewrite <- Heqmom.
                            ---- assert (In mom (get_popped priq_contents')). {
                                   assert (In_path g mom p2mom). {
                                     apply pfoot_in. now destruct H68. }
                                   specialize (H62 _ H72). now destruct H62. }
                                 rewrite upd_Znth_diff; try omega; trivial.
                                 ++++ rewrite H36, <- H34. now apply get_popped_range.
                                 ++++ intro. apply H44. now rewrite <- H73.
                        *** rewrite Forall_forall; intros.
                            rewrite Forall_forall in H71.
                            specialize (H71 _ H72).
                            unfold VType in *.
                            rewrite upd_Znth_diff; try omega; trivial.
                            ---- rewrite H35.
                                 apply (step_in_range2 g p2mom); trivial.
                            ---- intro. assert (In_path g i p2mom). {
                                   right. exists x. split; auto. right.
                                   destruct H2 as [_ [_ [_ ?]]]. now rewrite H2. }
                                 specialize (H62 _ H74). now destruct H62.
                    +++ intros.
                        specialize (H62 _ H68).
                        destruct H62.
                        split; trivial.
                        rewrite <- get_popped_irrel_upd;
                          try omega; trivial.
                        *** apply get_popped_range in H62; omega.
                        *** intro contra. rewrite contra in H62.
                            apply H44; trivial.
                    +++ intros. rewrite <- Heqmom; trivial.
                    +++ rewrite <- Heqmom; trivial.
                    +++ rewrite <- Heqmom. trivial.
                    +++ rewrite <- Heqmom. rewrite upd_Znth_diff; omega.
                    +++ intros. rewrite <- Heqmom.
                        apply H67.
                        *** destruct H68 as [? [? [? [? ?]]]].
                            split3; [| |split3]; trivial.
                            ---- assert (In mom' (get_popped priq_contents')). {
                                   assert (In_path g mom' p2mom'). {
                                     apply pfoot_in. now destruct H71. }
                                   specialize (H69 _ H75). destruct H69.
                                   rewrite get_popped_unchanged in H69; auto.
                                   - now rewrite H34.
                                   - omega.
                                   - intro. apply H44.
                                     rewrite get_popped_meaning; auto.
                                     now rewrite H34. }
                                 rewrite upd_Znth_diff in H73; try omega.
                                 ++++ rewrite H36. rewrite <- H34.
                                      now apply get_popped_range.
                                 ++++ intro. apply H44. now rewrite <- H76.
                            ---- rewrite Forall_forall; intros.
                                 rewrite Forall_forall in H74.
                                 specialize (H74 _ H75).
                                 unfold VType in *.
                                 ++++ assert (In_path g (snd x) p2mom'). {
                                        right. exists x. split; auto. right.
                                        destruct H2 as [_ [_ [_ ?]]]. now rewrite H2. }
                                      specialize (H69 _ H76). destruct H69.
                                      assert (In (snd x) (get_popped priq_contents')). {
                                        rewrite get_popped_unchanged in H69; auto.
                                        - now rewrite H34.
                                        - omega.
                                        - intro. apply H44.
                                          rewrite get_popped_meaning; auto.
                                          now rewrite H34. }
                                      rewrite upd_Znth_diff in H74; try omega.
                                      **** rewrite H35. rewrite <- H34.
                                           now apply get_popped_range.
                                      **** intro. rewrite H79 in *.
                                           rewrite get_popped_meaning in H69.
                                           ----- rewrite upd_Znth_same in H69. 1: omega.
                                           rewrite H34; auto.
                                           ----- rewrite upd_Znth_Zlength; now rewrite H34.
                        *** intros.
                            specialize (H69 _ H71).
                            destruct H69.
                            rewrite <- get_popped_irrel_upd in H69; try omega; trivial.
                            split; trivial.
                            ---- apply get_popped_range in H69.
                                 rewrite upd_Znth_Zlength in H69; omega.
                            ---- intro contra. rewrite contra in H69.
                                 rewrite get_popped_meaning in H69.
                                 rewrite upd_Znth_same in H69; omega.
                                 rewrite upd_Znth_Zlength; omega.
                        *** trivial.
                --- unfold inv_unseen; intros.
                    assert (dst <> i). {
                      intro. subst dst. rewrite upd_Znth_same in H59; omega.
                    }
                    assert (0 <= dst < i) by omega.
                    pose proof (H24 dst H61).
                    rewrite upd_Znth_diff in H59; try omega.
                    rewrite upd_Znth_diff; try omega.
                    rewrite upd_Znth_diff; try omega.
                    unfold inv_unseen in H62.
                    specialize (H62 H59).
                    destruct H62.
                    split; trivial.
                --- intros.
                    assert (dst <> i) by omega.
                    rewrite upd_Znth_diff in H59 by omega.
                    repeat rewrite upd_Znth_diff by omega.
                    assert (i <= dst < SIZE) by omega.
                    destruct (H25 _ H61 H59).
                    split; trivial.
                --- rewrite upd_Znth_diff; try omega.
                    intro. subst src; omega.
                --- rewrite upd_Znth_diff; try omega.
                    intro. subst src; omega.
                --- rewrite upd_Znth_diff; try omega.
                    intro. subst src; omega.
                --- split.
                    +++ apply get_popped_irrel_upd; try omega; trivial.
                    +++ split3; apply inrange_upd_Znth; trivial; try omega. 
             ** rewrite Int.signed_repr in H43
                 by (unfold inf in *; rep_omega).
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
                    2: apply H22; omega.
                    (* things get interesting when dst = i
            We must show that i is better off
            not going via u *)
                    subst dst.
                    (* i already obeys the weaker inv_unpopped,
            ie inv_unpopped without going via u.
            Now I must show that it actually satisfies
            inv_unpopped proper
                     *)
                    unfold inv_unpopped; intros.
                    assert (i <= i < SIZE) by omega.
                    destruct (H23 i H57 H56) as [p2mom [? [? [? [? [? [? ?]]]]]]].
                    unfold VType in *.
                    remember (Znth i prev_contents') as mom.
                    destruct (Z.eq_dec i src); [left | right]; trivial.
                    split; trivial.
                    exists p2mom; split3; [| |split3; [| |split3]]; trivial.
                    +++ intros.
                        specialize (H59 _ H65).
                        destruct H59. trivial.
                    +++ intros.
                        assert (Hrem := H65).

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
                        destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).

                        *** destruct H65 as [? [? [? [? ?]]]].
                            apply in_path_eq_epath_to_vpath in i0; trivial.
                            (*
1. In u p': p' is from s to i, consider the
vertex k which is just before i.
                             *)
                            destruct (Z.eq_dec mom' u).
                            ----
                              (*
1.1 k = u: dist[u] is global optimal. We have
dist [i] < dist[u] + graph[u][i] ......(H43)
         <= path_cost [s to u of p'] + graph[u][i]
         = path_cost p'
                               *)
                              subst mom'.
                              specialize (H66 _ i0).
                              rename p2mom' into p2u.
                              unfold path_globally_optimal in H67.
                              apply Z.ge_le in H43.

                              destruct (zlt (path_cost g p2u + Znth i (Znth u (graph_to_mat g))) inf).
                              ++++ rewrite careful_add_clean; try omega; trivial.
                              ++++ rewrite careful_add_dirty; trivial.
                                   omega.
                                   replace 8 with SIZE in H38 by omega.
                                   rewrite inf_eq2 in H38.
                                   rewrite Int.signed_repr in H38.
                                   2: rep_omega.
                                   rewrite Int.signed_repr in H38.
                                   2: { rewrite <- inf_eq.
                                        unfold VType in *.
                                        unfold Int.min_signed, Int.max_signed.
                                        unfold Int.half_modulus.
                                        simpl. omega.
                                   }
                                   omega.
                            ----
                              (*
1.2 ~ k = u: p' = s to u + u to k + edge k i.
Since p' is composed by popped vertex (including u) only,
k must be a popped vertex.
Then it satisfies NewInv1, which means
dist[k] <= path_cost [s to u] + path_cost [u to k]
and the global optimal path from s to k is composed by
popped vertices only.
Thus dist[k] + len(edge k i) <= path_cost p'.
Since dist[k] only contains popped vertices, this path
having dist[k] + edge k i also only contains popped
vertices. Thus we have dist[i] <= dist[k] + len(edge k i)
because of Inv2. So we have:
dist[i] <= dist[k] + len(edge k i) <= path_cost p'.

                               *) 
                              admit.
                        ***

                          (* 2. ~ In u p': This is an easy case.
   dist[i] < path_cost p' because of Inv2.
                           *)
                          apply H64; trivial.
                          intros.
                          specialize (H66 _ H68).
                          split; trivial.
                          destruct H65.
                          rewrite in_path_eq_epath_to_vpath in n0; trivial.
                          intro. rewrite H70 in H68.
                          apply n0; trivial.
                --- intros. destruct (Z.eq_dec dst i).
                    +++ subst dst. omega.
                    +++ apply H23; omega.
                --- unfold inv_unseen; intros.
                    destruct (Z.eq_dec dst i).
                    2: apply H24; omega.
                    subst dst.
                    assert (i <= i < SIZE) by omega.
                    destruct (H25 _ H57 H56).
                    split; trivial.
                --- intros.
                    assert (i <= dst < SIZE) by omega.
                    apply H25; trivial.
          ++  (* i was not a neighbor of u.
                 prove the for loop's invariant holds *)
            replace 8 with SIZE in H38 by omega.
            rewrite inf_eq2 in H38.
            forward.
            Exists prev_contents' priq_contents' dist_contents'.
            entailer!.
            remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
            assert (Znth i (Znth u (graph_to_mat g)) = inf). {
              assert (0 <= i < SIZE) by omega.
              assert (0 <= u < SIZE) by omega.
              assert (Int.max_signed / SIZE < inf) by now compute. 
              unfold inrange_graph in H1;
                destruct (H1 _ _ H14 H51); trivial.
              rewrite Int.signed_repr in H38.
              2: { unfold VType in *. replace SIZE with 8 in H53, H52.
                   unfold Int.min_signed, Int.max_signed, Int.half_modulus in *.
                   simpl. simpl in H53, H52.
                   assert (2147483647 / 8 < 2147483647) by now compute.
                   omega.
              }
              rewrite Int.signed_repr in H38.
              2: rewrite <- inf_eq; rep_omega.
              omega.
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
                   assert (i <= i < SIZE) by omega.
                   destruct (H23 i H53 H52) as [p2mom [? [? [? [? [? ?]]]]]].
                   unfold VType in *.
                   remember (Znth i prev_contents') as mom.
                   right. split.
                   1: {
                     assert (In src (get_popped priq_contents')). {
                       assert (In_path g src p2mom). {
                         left. destruct H54 as [_ [[? _] _]].
                         destruct p2mom. 
                         now simpl in H54 |- *. }
                       specialize (H55 _ H60).
                       now subst. }
                     intro contra. rewrite <- contra in H60.
                     rewrite get_popped_meaning in H60.
                     omega. omega.
                   }
                   exists p2mom; split3; [| |split3; [| |split3]]; trivial.
                   +++ intros.
                       specialize (H55 _ H60).
                       destruct H55. trivial.
                   +++ intros. apply H59; trivial.
                   +++ intros. apply H59; trivial.
                       intros. specialize (H61 _ H63).
                       split; trivial. 
                       admit.
                       (* check invariants re: step <> u *)
               --- apply H22; omega.
            ** destruct (Z.eq_dec dst i).
               --- omega. 
               --- apply H23; omega.
            ** destruct (Z.eq_dec dst i).
               2: apply H24; omega.
               subst dst.
               assert (i <= i < SIZE) by omega.
               unfold inv_unseen; intros.
               destruct (H25 _ H52 H53).
               split; trivial.
            ** apply H25; omega.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
          unfold dijkstra_correct.
          split3; trivial;
            [apply H19 | apply H21];
            rewrite <- (vvalid_range g); trivial.
      * (* After breaking, the while loop,
           prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H15 in H14; simpl in H14; now inversion H14.
        }
        clear H14.
        forward. Exists prev_contents priq_contents dist_contents.
        entailer!. apply (isEmptyMeansInf _ H15).
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents.
      forward. Exists prev_contents dist_contents priq_contents. entailer!.
Abort.
