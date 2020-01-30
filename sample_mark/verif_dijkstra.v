Require Import VST.msl.iter_sepcon.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

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

Definition inrange_graph grph_contents :=
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    (i <> j ->
     0 < Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
     Znth i (Znth j grph_contents) = inf) /\
    (i = j ->
     Znth i (Znth j grph_contents) = inf).

Lemma inrange_upd_Znth: forall (l: list Z) i new F,
    0 <= i < Zlength l ->
    Forall F l -> F new ->
    Forall F (upd_Znth i l new).
Proof.
  intros. rewrite Forall_forall in *. intros.
  destruct (eq_dec x new); [rewrite e; trivial|].
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2; [omega|].
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Definition isEmpty_Prop (pq_contents : list Z) :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then False else acc) True pq_contents.

Definition isEmpty (pq_contents : list Z) : val :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then Vzero else acc) Vone pq_contents.

Lemma isEmpty_prop_val: forall l,
    isEmpty_Prop l <-> isEmpty l = Vone.
Proof.
  intros. induction l; simpl in *. split; intro; trivial. 
  destruct (Z_lt_dec a inf); trivial. split; inversion 1.
Qed.

Lemma isEmpty_in': forall l,
    (exists i, In i l /\ i < inf) <-> isEmpty l = Vzero.
Proof.
  split; intros.
  - destruct H as [? [? ?]]. induction l. 
    1: exfalso; apply (in_nil H).
    unfold isEmpty. rewrite fold_right_cons.
    destruct (Z_lt_dec a inf); trivial.
    simpl in H; simpl; destruct H.
    1: rewrite H in n; exfalso. omega.
    clear n a. specialize (IHl H).
    unfold isEmpty in IHl. trivial.
  - induction l.
    1: inversion H.
    simpl in H.
    destruct (Z_lt_dec a inf).
    + exists a. split; simpl; [left|]; trivial.
    + destruct (IHl H) as [? [? ?]].
      exists x. split; [apply in_cons|]; assumption.
Qed.

Lemma isEmpty_in: forall l target,
    In target l -> target < inf -> isEmpty l = Vzero.
Proof.
  intros. induction l.
  1: exfalso; apply (in_nil H).
  unfold isEmpty. rewrite fold_right_cons.
  destruct (Z_lt_dec a inf); trivial.
  simpl in H; simpl; destruct H.
  1: rewrite H in n; exfalso; omega.
  clear n a. specialize (IHl H).
  unfold isEmpty in IHl. trivial.
Qed.

Lemma isEmptyTwoCases: forall l,
    isEmpty l = Vone \/ isEmpty l = Vzero.
Proof.
  intros. induction l. 1: simpl; left; trivial.
  destruct IHl; simpl; destruct (Z_lt_dec a inf);
  (try now left); now right.
Qed.

Lemma isEmptyMeansInf: forall l,
    isEmpty l = Vone -> Forall (fun x => x >= inf) l.
Proof.
  intros. induction l; trivial. simpl in H.
  destruct (Z_lt_dec a inf); [inversion H|].
  specialize (IHl H). apply Forall_cons; trivial.
Qed.

Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
  induction al; intros. 1: inversion H.
  destruct H.
  1: subst a; simpl; apply Z.le_min_l.
  simpl. rewrite Z.le_min_r. apply IHal, H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof. intros. apply fold_min_general, H. Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
 intros. induction H0.
 simpl. auto. simpl. unfold Z.min at 1.
 destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
 intros. revert x; induction al; simpl; intros.
 apply Z.min_comm. rewrite <- Z.min_assoc. f_equal. apply IHal.
Qed.

Lemma min_not_in_prev i l :
  Znth i l < fold_right Z.min (Znth 0 l) (sublist 0 i l) ->
  ~ In (Znth i l) (sublist 0 i l).
Proof.
  intros. intro.
  pose proof (fold_min_general (sublist 0 i l) (Znth i l) H0(Znth 0 l)). omega.
Qed.

Fixpoint find (l : list Z) (n : Z) (ans : Z) :=
  match l with
  | [] => ans
  | h :: t => if eq_dec h n
              then ans
              else (find t n (1 + ans))
  end.

Lemma find_index_gen: forall l i ans,
  0 <= i < Zlength l ->
  ~ In (Znth i l) (sublist 0 i l) ->
  find l (Znth i l) ans = i + ans.
Proof.
  intros. generalize dependent i.
  generalize dependent ans. induction l.
  1: intros; rewrite Zlength_nil in H; exfalso; omega.
  unfold find.
  intros.
  destruct (eq_dec a (Znth i (a :: l))).
  - rewrite <- e in H0. clear - H H0.
    destruct (Z.eq_dec 0 i). 1: omega. 
    destruct H. assert (0 < i) by omega.
    exfalso. apply H0.
    unfold sublist. replace (i-0) with i by omega.
    simpl. replace (Z.to_nat i) with (Z.to_nat (Z.succ (i-1))) by rep_omega.
    rewrite Z2Nat.inj_succ by omega.
    rewrite firstn_cons. apply in_eq.
  - destruct (Z.eq_dec 0 i).
    1: rewrite <- e in n; rewrite Znth_0_cons in n;
      exfalso; omega.
    assert (0 <= i - 1 < Zlength l) by 
        (rewrite Zlength_cons in H; rep_omega).
    assert (~ In (Znth (i - 1) l) (sublist 0 (i - 1) l)). { 
        rewrite <- (Znth_pos_cons i l a) by omega.
        rewrite <- (sublist_1_cons l a i).
        intro. apply H0.
        apply (sublist_In 1 i).
        rewrite sublist_sublist0 by omega. assumption.
      }
    pose proof (IHl (1 + ans) (i - 1) H1 H2).
    replace (i - 1 + (1 + ans)) with (i + ans) in H3 by omega.
    replace (Znth i (a :: l)) with (Znth (i - 1) l).
    2: { symmetry. apply Znth_pos_cons; omega. }
    rewrite <- H3.
    unfold find. trivial.
Qed.

Lemma find_index: forall l i,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) 0 = i.
Proof.
  intros. replace i with (i + 0) at 2 by omega.
  apply find_index_gen; trivial.
Qed.

Lemma find_range_gen: forall l target ans,
    In target l ->
    0 <= ans ->
    ans <= find l target ans < Zlength l + ans.
Proof.
  intros. generalize dependent target.
  generalize dependent ans.
  induction l.
  1: intros; simpl; now rewrite Zlength_nil. 
  intros. apply in_inv in H. destruct H.
  - subst a. unfold find.
    destruct (eq_dec target target).
    rewrite Zlength_cons. split; rep_omega.
    exfalso; omega.
  - unfold find. destruct (eq_dec a target).
    1: rewrite Zlength_cons; split; rep_omega.
    assert (0 <= 1 + ans) by omega.
    pose proof (IHl (1+ans) H1 target H).
    clear -H2. unfold find in H2.
    rewrite Zlength_cons. rep_omega.
Qed.

Lemma find_range: forall l target,
    In target l ->
    0 <= find l target 0 < Zlength l.
Proof.
  intros. replace (Zlength l) with (Zlength l + 0) by omega.
  apply find_range_gen; trivial; omega.
Qed.

Lemma Znth_find_gen:
  forall l target ans,
    0 <= ans ->
    In target l ->
    Znth ((find l target ans)-ans) l = target.
Proof.
  intros. generalize dependent ans.
  induction l. 1: inversion H0.
  intros.
  destruct H0.
  - subst target. simpl.
    destruct (initial_world.EqDec_Z a a).
    + replace (ans-ans) with 0 by omega.
      rewrite Znth_0_cons; auto.
    + exfalso; omega.
  - specialize (IHl H0).
    simpl.
    destruct (initial_world.EqDec_Z a target).
    + replace (ans-ans) with 0 by omega.
      rewrite Znth_0_cons; auto.
    + assert (0 <= 1 + ans) by omega.
      specialize (IHl (1+ans) H1).
      rewrite Znth_pos_cons.
      replace (1+ans) with (ans+1) in IHl at 2 by omega.
      rewrite Z.sub_add_distr in IHl.
      assumption.
      destruct (find_range_gen l target (1+ans) H0 H1) as [? _].
      omega.
Qed.

Lemma Znth_find:
  forall l target,
    In target l ->
    Znth (find l target 0) l = target.
Proof.
  intros.
  replace (find l target 0) with (find l target 0 - 0) by omega.
  apply Znth_find_gen; [omega | assumption].
Qed.  

Lemma min_in_list : forall l1 l2 starter,
    incl l1 l2 ->
    In starter l2 ->
    In (fold_right Z.min starter l1) l2.
Proof.
  intros. induction l1; trivial. simpl.
  destruct (Z.min_dec a (fold_right Z.min starter l1));
    rewrite e; clear e.
  - apply H, in_eq.
  - apply IHl1, (incl_cons_inv H).
Qed.  

Lemma Znth_0_hd:
  forall list, Zlength list > 0 -> Znth 0 list = hd 0 list.
Proof.
  intros. induction list; inversion H.
  rewrite Znth_0_cons. trivial.
Qed.

Lemma min_picks_first:
  forall num mono start,
    start <= mono ->
    fold_right Z.min start (list_repeat num mono) = start.
Proof.
  intros. induction num; trivial.
  simpl. rewrite IHnum. rewrite Z.min_r; omega.
Qed.
  
Lemma find_src: forall src,
    0 <= src < Zlength (list_repeat (Z.to_nat SIZE) inf) ->
    find (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)
               (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0))
                           (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)) 0 = src.
Proof.
  intros.
  remember (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength; trivial.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l by omega.
    rewrite sublist_list_repeat.
    2: omega.
    2: rewrite Zlength_list_repeat in H; [|unfold SIZE]; rep_omega.
    replace (src - 0) with (src) by omega.
    intro.
    apply in_list_repeat in H0.
    inversion H0.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_list_repeat; try omega.
    2: rewrite Zlength_list_repeat in H; [|unfold SIZE]; omega.
    2: { split. omega. unfold SIZE in *; rewrite Zlength_list_repeat; omega. }
    repeat rewrite Zlength_list_repeat by omega.
    replace (src - 0) with (src) by omega.
    rewrite <- Znth_0_hd.
    2: { unfold SIZE in *; rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_list_repeat; omega. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same. simpl.
      compute; trivial. omega.
    + rewrite upd_Znth_diff by omega.
      rewrite Znth_list_repeat_inrange by (unfold SIZE in *; omega).
      rewrite Zlength_list_repeat.
      simpl. rewrite Z.min_l.
      1,2: rewrite min_picks_first.
      all: try rewrite <- inf_eq; try unfold SIZE; omega.
Qed.

Definition get_popped pq : list VType :=
  map snd (filter (fun x => (fst x) =? (inf+1))
                  (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))).

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

Lemma filter_app:
  forall l1 l2 (F: Z*Z -> bool),
    filter F (l1 ++ l2) = (filter F l1) ++ (filter F l2).
Proof.
  intros. induction l1.
  1: simpl; repeat rewrite app_nil_l; reflexivity.
  simpl. destruct (F a); [rewrite IHl1|]; easy.
Qed.

Lemma sublist_nil: forall lo hi A,
    sublist lo hi (@nil A) = (@nil A).
Proof.
  intros. unfold sublist, skipn.
  destruct (Z.to_nat lo); destruct (Z.to_nat (hi - lo)); reflexivity.
Qed.

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
    sublist lo (Zlength (a :: l)) (a::l) =
    sublist (lo - 1) (Zlength (a :: l) - 1) l.
Proof.
  intros.
  unfold sublist.
  destruct (Z.to_nat lo) eqn:?.
  - exfalso.
    unfold Z.to_nat in Heqn.
    destruct lo; try inversion H.
    pose proof (Pos2Nat.is_pos p); omega.
  - simpl. replace (Zlength (a :: l) - 1 - (lo - 1)) with 
               (Zlength (a :: l) - lo) by omega.
    f_equal. replace (Z.to_nat (lo - 1)) with n.
    reflexivity. apply juicy_mem_lemmas.nat_of_Z_lem1. omega.
Qed.

Lemma combine_sublist_0:
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    combine (sublist 0 (Zlength l1) l1) (sublist 0 (Zlength l2) l2) =
    sublist 0 (Zlength (combine l1 l2)) (combine l1 l2).
Proof. 
  intros. generalize dependent l2. induction l1. 
  - intros. simpl. rewrite sublist_nil. reflexivity.
  - intros.
    assert (1 <= Zlength l2). {
      rewrite Zlength_cons in H. rep_omega. }
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite (sublist_one 0 1) by omega.
    rewrite <- semax_lemmas.cons_app.
    rewrite sublist_same by omega.
    rewrite sublist_same by omega.
    rewrite (sublist_same 0 (Zlength (combine (a :: l1) (Znth 0 l2 :: sublist 1 (Zlength l2) l2))))  by omega.
    simpl. f_equal. 
Qed.

Lemma combine_sublist_gen:
  forall (l1 l2 : list Z) lo,
    0 <= lo < Zlength l1 + 1 ->
    Zlength l1 = Zlength l2 ->
    combine (sublist lo (Zlength l1) l1) (sublist lo (Zlength l2) l2) =
    sublist lo (Zlength (combine l1 l2)) (combine l1 l2).
Proof. 
  intros.
  generalize dependent l2.
  generalize dependent lo.
  induction l1. 
  1: intros; rewrite sublist_nil; simpl;
    rewrite sublist_nil; reflexivity.
  intros. destruct (Z.eq_dec 0 lo).
  1: subst lo; apply combine_sublist_0; omega.
  rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
  assert (1 <= Zlength l2). {
    rewrite Zlength_cons in H0.
    rewrite <- Z.add_1_l in H0. rewrite <- H0.
    pose proof (Zlength_nonneg l1). omega. }
  rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
  rewrite (sublist_one 0 1); try omega.
  rewrite <- semax_lemmas.cons_app.
  simpl.
  repeat rewrite sublist_skip by omega.
  replace (Zlength (a :: l1) - 1) with (Zlength l1)
    by (rewrite Zlength_cons; omega).
  replace (Zlength (Znth 0 l2 :: sublist 1 (Zlength l2) l2) - 1) with (Zlength (sublist 1 (Zlength l2) l2)) by
      (rewrite Zlength_cons, Zlength_sublist; rep_omega).
    replace (Zlength ((a, Znth 0 l2) :: combine l1 (sublist 1 (Zlength l2) l2)) - 1)
      with (Zlength (combine l1 (sublist 1 (Zlength l2) l2))) by
      (rewrite Zlength_cons; rep_omega).
    apply IHl1.
    rewrite Zlength_cons in H; omega.
    rewrite Zlength_cons in H0.
    rewrite Zlength_sublist; omega.
Qed.

Lemma combine_sublist_specific:
  forall (l1 l2: list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (sublist 0 i l1) (sublist 0 i l2) = sublist 0 i (combine l1 l2).
Proof.
  intros.
  generalize dependent i.
  generalize dependent l2. induction l1. 
  - intros. simpl. repeat rewrite sublist_nil. reflexivity.
  - intros.
    assert (1 <= Zlength l2). {
      rewrite Zlength_cons in H. rep_omega. }
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite (sublist_one 0 1) by omega.
    rewrite <- semax_lemmas.cons_app.
    destruct (Z.eq_dec i 0).
    + subst i; repeat rewrite sublist.sublist_nil; reflexivity.
    + repeat rewrite sublist_cons.
      simpl. rewrite sublist_cons'.
      f_equal. apply IHl1.
      all: try rewrite Zlength_cons in *.
      3: rewrite combine_same_length.
      1,4,5: rewrite Zlength_sublist.
      all: omega.
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
  unfold upd_Znth.
  rewrite combine_app.
  2: { repeat rewrite <- ZtoNat_Zlength.
       f_equal. repeat rewrite Zlength_sublist; omega. }
  f_equal. 
  1: apply combine_sublist_specific; assumption.
  rewrite (sublist_split i (i+1) (Zlength l2) l2) by omega.
  rewrite sublist_len_1 by omega.
  rewrite <- semax_lemmas.cons_app.
  simpl combine. f_equal.
  apply combine_sublist_gen.  omega. omega.
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
    rewrite <- semax_lemmas.cons_app.
    simpl. destruct (Z.eq_dec i 0).
    1: subst i; repeat rewrite Znth_0_cons; reflexivity.
    repeat rewrite Znth_pos_cons by omega.
    apply IHl1.
    rewrite Zlength_sublist by omega.
    rewrite Zlength_cons in H; rep_omega.
    rewrite Zlength_cons in H0; rep_omega.
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
  unfold upd_Znth.
  rewrite <- (sublist_same 0 (Zlength (combine l l2)) (combine l l2)) at 4 by reflexivity.
  rewrite (sublist_split 0 i (Zlength (combine l l2))
                         (combine l l2)) by omega.
  do 2 rewrite filter_app.
  f_equal. rewrite H3.
  rewrite (sublist_split i (i+1) (Zlength l)) by omega.
  rewrite (sublist_one i (i+1) (combine l l2)) by omega.
  rewrite semax_lemmas.cons_app.
  do 2 rewrite filter_app.
  f_equal. simpl.
  destruct (F (new, Znth i l2)) eqn:?; rewrite HeqF in Heqb; simpl in Heqb.
  - exfalso. apply H1. rewrite <- inf_eq.
    simpl. rewrite Z.eqb_eq in Heqb. rewrite <- inf_eq in *.
    omega.
  - destruct (F (Znth i (combine l l2))) eqn:?; trivial.
    rewrite HeqF, Znth_combine, Z.eqb_eq in Heqb0 by omega.
    simpl in Heqb0. exfalso. apply H1. rewrite <- inf_eq. omega.
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
    rewrite semax_lemmas.cons_app.
    assert (Zlength [a] = 1) by reflexivity.
    rewrite in_get_popped by omega.
    apply IHl; omega.
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

Definition path_correct (g: LGraph) prev dist src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost g p <> inf /\
  Znth dst dist = path_cost g p /\
  Forall (fun x => Znth (snd x) prev = fst x) (snd p).

Definition path_globally_optimal (g: LGraph) src dst p : Prop :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost g p <= path_cost g p'.

Definition inv_popped g src prev priq dist dst :=
    In dst (get_popped priq) ->
    exists path,
      path_correct g prev dist src dst path /\
      (forall step, step <> src ->
                    In_path g step path ->
                    In step (get_popped priq)) /\
      path_globally_optimal g src dst path.

Definition inv_unpopped g src prev priq dist dst :=
  Znth dst priq < inf ->
  let mom := Znth dst prev in
  exists p2mom,
    path_correct g prev dist src mom p2mom /\
    (forall step, step <> src ->
                  In_path g step p2mom ->
                  In step (get_popped priq)) /\
    path_globally_optimal g src mom p2mom /\
    elabel g (mom, dst) <> inf /\
    Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) <> inf /\ 
    Znth dst dist = path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) /\
    forall mom' p2mom',
      path_correct g prev dist src mom' p2mom' ->
      (forall step', step' <> src ->
                     In_path g step' p2mom' ->
                     In step' (get_popped priq)) ->
      path_globally_optimal g src mom' p2mom' ->
      path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) <= path_cost g p2mom' + Znth dst (Znth mom' (graph_to_mat g)).

Definition inv_unseen prev priq dist dst :=
  Znth dst priq = inf ->
  Znth dst dist = inf /\
  Znth dst prev = inf.

Definition dijkstra_correct g (src : VType) (prev priq dist: list VType) : Prop :=
  forall dst,
    0 <= dst < SIZE ->
    (* src <> dst -> *)
    inv_popped g src prev priq dist dst /\
    inv_unpopped g src prev priq dist dst /\
    inv_unseen prev priq dist dst.

(* SPECS *)
Definition pq_emp_spec :=
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP (inrange_priq priq_contents)
    LOCAL (temp _pq pq)
    SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
    POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (isEmpty priq_contents))
    SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq).

Definition popMin_spec :=
 DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP  (inrange_priq priq_contents;
         isEmpty priq_contents = Vzero)
    LOCAL (temp _pq pq)
    SEP   (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
    EX rt : Z,
    PROP (rt = find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
    LOCAL (temp ret_temp  (Vint (Int.repr rt)))
    SEP   (data_at Tsh (tarray tint SIZE) (upd_Znth
       (find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
       (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: Graph, arr : pointer_val,
       dist : pointer_val, prev : pointer_val, src : Z
  PRE [_graph OF (tptr (tarray tint SIZE)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
    PROP (0 <= src < SIZE;
          Forall (fun list => Zlength list = SIZE) (graph_to_mat g);
          inrange_graph (graph_to_mat g);
          sound_dijk_graph g;
          forall i, 0 <= i < SIZE ->
                    Znth i (Znth i (graph_to_mat g)) = inf)
    LOCAL (temp _graph (pointer_val_val arr);
         temp _src (Vint (Int.repr src));
         temp _dist (pointer_val_val dist);
         temp _prev (pointer_val_val prev))
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val dist);
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val prev))
  POST [tvoid]
    EX prev_contents : list Z,
    EX dist_contents : list Z,
    EX priq_contents : list Z,
    PROP (dijkstra_correct g src prev_contents priq_contents dist_contents)
    LOCAL ()
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
         data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
         data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist)).
    
Definition Gprog : funspecs := ltac:(with_library prog [pq_emp_spec; popMin_spec; dijkstra_spec]).

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP (isEmpty_Prop (sublist 0 i priq_contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_omega.
  - unfold SIZE; rep_omega.
  - entailer!.
  - simpl.
    assert_PROP (Zlength priq_contents = SIZE). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)).
      trivial. 
      apply Znth_In; omega.
      rewrite <- H1 in H0.
      pose proof (Forall_Znth _ _ i H0 H).
      rewrite Int.signed_repr in H3.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3; trivial.
      simpl in H7. rep_omega.
    + rewrite (sublist_split 0 i (i+1)); try omega.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      rewrite sublist_one; try omega. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) inf).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3.
      do 2 rewrite Int.signed_repr in H3. 
      rep_omega.
      1: compute; split; inversion 1. 
      1,2: rewrite <- H1 in H0; apply (Forall_Znth _ _ i H0) in H; simpl in H; rep_omega.  
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: { symmetry; repeat rewrite Zlength_map in H2.
         unfold SIZE. simpl in H2. omega. }
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry. apply isEmpty_prop_val; trivial. 
Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = SIZE). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)) by
      (rewrite Zlength_map; rewrite H1; unfold SIZE; omega).
  assert (0 <= 0 < Zlength priq_contents) by 
      (rewrite H1; unfold SIZE; omega).
  forward. forward.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
            temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0))); 
            temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_omega.
  - entailer!. simpl. rewrite find_index.
    trivial. omega. simpl. unfold not. omega.
  - forward.
    assert (0 <= i < Zlength priq_contents) by omega.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      pose proof (Forall_Znth _ _ x0 H6 H).
      simpl in H8. rep_omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      apply (Forall_sublist _ 0 i _) in H.
      apply (Forall_Znth _ _ _ H6) in H.
      simpl in H. rep_omega.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (Forall_Znth _ _ _ H5) in H; simpl in H; rep_omega. }
    forward_if.
    + forward. forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by omega.
      rewrite (sublist_one i (i+1) priq_contents) by omega.
      rewrite fold_min_another.
      rewrite Z.min_r; [|omega]. 
      split; trivial. f_equal. 
      rewrite find_index; trivial.
      apply min_not_in_prev; trivial.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by omega.
      rewrite (sublist_one i (i+1) priq_contents) by omega.
      rewrite fold_min_another.
      rewrite Z.min_l; [|omega]. split; trivial.
  - forward. 
    + entailer!. rewrite <- H1.
      apply find_range. 
      rewrite sublist_same; [|omega..].
      apply min_in_list; [apply incl_refl | apply Znth_In; omega]. 
    + forward. 
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 SIZE priq_contents)) 0).
      rewrite sublist_same by omega. entailer!.
      destruct priq_contents; simpl; auto.
Qed.

Definition cost_was_improved_if_possible g me dst dist : Prop :=
  let cost := Znth dst (Znth me (graph_to_mat g)) in
  (* cost from me to dst *)
  cost < inf -> (* is dst my neighbor? if yes... *)
  Znth dst dist <= Znth me dist + cost.
(* by the time we're done, the cost to the dst is either better 
or the same as the cost via me *)

Lemma valid_path_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    0 <= u < SIZE ->
    0 <= i < SIZE ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  destruct H as [? [? [? ?]]].
  simpl; split.
  + rewrite H5; simpl.
    assumption.  
  + unfold strong_evalid.
    unfold edge_valid in H4.
    unfold vertex_valid in H.
    rewrite H4, H5, H6, H, H; simpl.
    split; split; assumption.
Qed.

Lemma path_ends_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.                    
  split.
  + destruct H0; apply H0.
  + rewrite pfoot_last.
    destruct H as [_ [_ [_ ?]]].
    rewrite H; reflexivity.
Qed.

Lemma link_evalid:
  forall g a b,
    sound_dijk_graph g ->
    0 <= a < SIZE ->
    0 <= b < SIZE ->
    evalid g (a,b).
Proof.
  intros.
  destruct H as [? [? _]].
  unfold edge_valid in H2.
  unfold vertex_valid in H.
  rewrite H2; split; simpl; [rewrite H|]; assumption.
Qed.
  
Lemma path_cost_app_not_inf:
  forall g p mom u,
    sound_dijk_graph g ->
    0 <= mom < SIZE ->
    0 <= u < SIZE -> 
    path_cost g p <> inf ->  
    elabel g (mom, u) <> inf ->
    path_cost g p + Znth u (Znth mom (graph_to_mat g)) <> inf ->
    path_cost g (fst p, snd p +:: (mom, u)) <> inf.    
Proof.
  intros.
  rewrite path_cost_app_cons; trivial.
  rewrite elabel_Znth_graph_to_mat; simpl;
    try omega; trivial.
  apply link_evalid; trivial.
Qed.

(*
Lemma cant_improve_further:
  forall i u src g priq prev dist,
    sound_dijk_graph g ->
    dijkstra_correct g src prev priq dist ->
    Zlength (graph_to_mat g) = SIZE ->
    Zlength priq = SIZE ->
    In i (get_popped priq) ->
    In u (get_popped priq) ->
    inrange_graph (graph_to_mat g) ->
    Znth i dist <= Znth u dist + Znth i (Znth u (graph_to_mat g)).
Proof.
  intros.
  unfold dijkstra_correct in H0.
  destruct (H0 i) as [? _].
  destruct (H0 u) as [? _].
  unfold inv_popped in H6, H7.
  destruct (H6 H3) as [p2i [? ?]].
  destruct (H7 H4) as [p2u [? ?]].
  clear H0 H6 H7. 
  unfold path_globally_optimal in H9. 
  destruct H8 as [? [? [? [? ?]]]].
  destruct H10 as [? [? [? [? ?]]]].  
  specialize (H10 (fst p2u, snd p2u ++ [(u,i)])).
  apply get_popped_range in H3.
  apply get_popped_range in H4.
  unfold VType in *. rewrite H2 in H3, H4.
  rewrite <- path_cost_app_cons in H9 by assumption.
  rewrite H15, H8. apply H9. 
  - destruct p2u; simpl. 
    destruct H13.
    apply valid_path_app_cons; assumption.
  - destruct p2u; simpl.
    replace z with src in *.
    apply path_ends_app_cons; assumption.
    destruct H13; simpl in H13; omega.
Qed.
*)

Lemma path_end_in_popped:
  forall g src mom priq prev dist p2mom,
    sound_dijk_graph g ->
    In src (get_popped priq) ->
    path_correct g prev dist src mom p2mom ->
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq) /\
         In (snd x) (get_popped priq)) (snd p2mom) ->
    In mom (get_popped priq).
Proof.
  intros.
  rewrite Forall_forall in H2. assert (Hrem := H1).
  destruct H1 as [_ [? _]].  
  destruct H1.
  pose proof (pfoot_in _ _ _ H3).
  unfold In_path in H4.
  destruct H4.
  - destruct p2mom. simpl in H4.
    unfold phead in H1; simpl in H1.
    rewrite H1 in H4. rewrite H4.
    trivial.
  - destruct H4 as [? [? ?]].
    specialize (H2 _ H4).
    destruct H2.
    destruct H as [? [? [? ?]]].
    destruct H5.
    + rewrite H8 in H5. 
      unfold VType in *.
      rewrite <- H5 in H2; trivial.
    + rewrite H9 in H5.
      unfold VType in *.
      rewrite <- H5 in H6; trivial.
Qed.

Lemma graph_to_mat_Zlength: forall g, Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; auto. now vm_compute.
Qed.

Lemma inrange_graph_cost_pos: forall g e,
    sound_dijk_graph g -> inrange_graph (graph_to_mat g) ->
    evalid g e -> 0 <= elabel g e.
Proof.
  intros. rewrite elabel_Znth_graph_to_mat; auto. destruct H as [? [? _]].
  red in H, H2. rewrite H2, H in H1. destruct H1. red in H0.
  rewrite <- (graph_to_mat_Zlength g) in H1, H3. specialize (H0 _ _ H3 H1).
  destruct H0.
  destruct (Z.eq_dec (snd e) (fst e)).
  - rewrite (H4 e0). omega.
  - destruct (H0 n).
    + destruct H5; omega.
    + rewrite H5. rewrite <- inf_eq. omega.
Qed.

Lemma acc_pos: forall (g: LGraph) l z,
    (forall e : EType, In e l -> 0 <= elabel g e) -> 0 <= z ->
    0 <= fold_left careful_add (map (elabel g) l) z.
Proof.
  intro. induction l; intros; simpl; auto. apply IHl.
  - intros. apply H. now apply in_cons.
  - unfold careful_add. destruct ((z =? inf) || (elabel g a =? inf))%bool.
    + now vm_compute.
    + apply Z.add_nonneg_nonneg; auto. apply H, in_eq.
Qed.

Lemma path_cost_pos:
  forall g p,
    sound_dijk_graph g ->
    valid_path g p ->
    inrange_graph (graph_to_mat g) ->
    0 <= path_cost g p.
Proof.
  intros.
  destruct p as [src links]. unfold path_cost. simpl.
  assert (forall e, In e links -> evalid g e). {
    intros. eapply valid_path_evalid; eauto. }
  assert (forall e, In e links -> 0 <= elabel g e). {
    intros. apply inrange_graph_cost_pos; auto. }
  apply acc_pos; auto. easy.
Qed.

Lemma entirely_in_subgraph_upd:
  forall u priq_contents links2mom mom,
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq_contents) /\
         In (snd x) (get_popped priq_contents)) links2mom ->
            0 <= u < Zlength priq_contents ->
Znth u priq_contents <> inf + 1           ->
In mom (get_popped priq_contents) ->
 Forall
    (fun x : Z * Z =>
     In (fst x) (get_popped (upd_Znth u priq_contents (inf + 1))) /\
     In (snd x) (get_popped (upd_Znth u priq_contents (inf + 1)))) (links2mom +:: (mom, u)).
Proof.
  intros.
  rewrite Forall_forall; intros.
  rewrite Forall_forall in H.
  simpl in H3. apply in_app_or in H3.
  destruct H3. 
  - specialize (H _ H3).
    destruct H. 
    pose proof (get_popped_range _ _ H). 
    pose proof (get_popped_range _ _ H4).
    split; rewrite <- get_popped_irrel_upd;
      trivial; intro; apply H1;
        rewrite H7 in *; apply get_popped_meaning; trivial.
  - simpl in H3. destruct H3; [|omega].
    rewrite surjective_pairing in H3.
    inversion H3.
    unfold VType in *.
    rewrite <- H5, <- H6. split.
    + apply get_popped_irrel_upd; trivial.
      apply get_popped_range; trivial.
      intro. apply H1. rewrite H4 in *.
      apply get_popped_meaning; trivial.
    + rewrite get_popped_meaning.
      rewrite upd_Znth_same; trivial.
      rewrite upd_Znth_Zlength; trivial.
Qed.

Lemma step_in_range: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [? _]]].
  unfold vertex_valid in H.
  unfold src_edge in H2.
  assert (In_path g (fst x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| left]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. omega.
Qed.

Lemma step_in_range2: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [_ ?]]].
  unfold vertex_valid in H.
  unfold dst_edge in H2.
  assert (In_path g (snd x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| right]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. omega.
Qed.

Set Nested Proofs Allowed.

Lemma in_path_app_cons:
  forall g step p2a src a b,
     sound_dijk_graph g ->
    path_ends g p2a src a ->
    In_path g step (fst p2a, snd p2a +:: (a, b)) ->
    In_path g step p2a \/ step = b.
Proof.
  intros. destruct H1; simpl in H1.
  - left. unfold In_path. left; trivial.
  - destruct H1 as [? [? ?]].
    apply in_app_or in H1.
    destruct H as [? [? [? ?]]].
    unfold src_edge in H4. unfold dst_edge in H5.
    rewrite H4, H5 in H2.
    destruct H1.
    + left. unfold In_path. right.
      exists x. rewrite H4, H5. split; trivial.
    + simpl in H1. destruct H1; [|omega].
      rewrite (surjective_pairing x) in *.
      inversion H1. simpl in H2.
      destruct H2.
      * left. destruct H0.
        apply pfoot_in in H6. rewrite H7, <- H2 in H6.
        trivial.
      * right; trivial.
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
  - unfold data_at, data_at_, field_at_; entailer!.
  - forward. forward. forward.
    entailer!.
    replace 8 with SIZE by (unfold SIZE; rep_omega).
    rewrite inf_eq2.
    replace (upd_Znth i
       (list_repeat (Z.to_nat i) (Vint (Int.repr inf)) ++
                    list_repeat (Z.to_nat (SIZE - i)) Vundef) (Vint (Int.repr inf))) with
        (list_repeat (Z.to_nat (i + 1)) (Vint (Int.repr inf)) ++ list_repeat (Z.to_nat (SIZE - (i + 1))) Vundef).
    1: entailer!.
    rewrite upd_Znth_app2 by (repeat rewrite Zlength_list_repeat by omega; omega).
    rewrite Zlength_list_repeat by omega.
    replace (i-i) with 0 by omega.
    rewrite <- list_repeat_app' by omega.
    rewrite app_assoc_reverse; f_equal.
    rewrite upd_Znth0.
    rewrite Zlength_list_repeat by omega.
    rewrite sublist_list_repeat by omega.
    replace (SIZE - (i + 1)) with (SIZE - i - 1) by omega.
    replace (list_repeat (Z.to_nat 1) (Vint (Int.repr inf))) with ([Vint (Int.repr inf)]) by reflexivity.
    rewrite <- semax_lemmas.cons_app. reflexivity.
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
        unfold upd_Znth in H15.
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
          destruct (Z.eq_dec src dst); trivial.
          rewrite upd_Znth_diff in H17 by omega.
          rewrite Znth_list_repeat_inrange in H17; omega.
        }
        subst dst.
        exists (src, []).
        split3; [| |split3; [| |split3]].
        -- split3; [| | split3].
           ++ simpl. destruct H2 as [? [? [? ?]]].
              unfold vertex_valid in H2.
              rewrite H2. omega.
           ++ rewrite upd_Znth_same by omega.
              unfold path_ends; simpl; omega.
           ++ unfold path_cost; simpl.
              rewrite <- inf_eq. omega.
           ++ repeat rewrite upd_Znth_same by omega.
              unfold path_cost; simpl; omega.
           ++ simpl snd. apply Forall_nil.
        -- intros. destruct H19.
           ++ simpl in H19. omega.
           ++ destruct H19 as [? [? ?]]. simpl in H19. omega.
        -- intros. rewrite upd_Znth_same by omega.
           unfold path_globally_optimal. intros.
           unfold path_cost at 1; simpl.
           apply path_cost_pos; trivial.
        -- intros. repeat rewrite upd_Znth_same by omega.
           rewrite elabel_Znth_graph_to_mat; trivial.
           simpl. rewrite H3. rewrite <- inf_eq. omega.
           omega. apply link_evalid; trivial.
        -- unfold path_cost at 1.
           rewrite upd_Znth_same by omega.
           rewrite H3 by omega. simpl.
           rewrite <- inf_eq. omega.
        -- repeat rewrite upd_Znth_same by omega.
           unfold path_cost at 1; simpl.
           rewrite H3 by omega. 
           omega.
        -- intros. repeat rewrite upd_Znth_same by omega.
           unfold path_cost at 1; simpl.
           rewrite H3 by omega. 
           assert (0 <= src < Zlength (graph_to_mat g)). {
             rewrite graph_to_mat_Zlength. omega.
           }
           assert (0 <= mom' < Zlength (graph_to_mat g)). {
             rewrite graph_to_mat_Zlength.
             destruct H18 as [? [? [? [? ?]]]].
             assert (In_path g mom' p2mom'). {
               destruct H22.
               apply pfoot_in; trivial.
             }
             destruct H2. unfold vertex_valid in H2.
             rewrite <- H2.
             apply (valid_path_valid g p2mom'); trivial.
           }
           pose proof (H1 src mom' H21 H22).
           destruct H18.
           pose proof (path_cost_pos g p2mom' H2 H18 H1).
           unfold VType in *.
           destruct H23.
           destruct (Z.eq_dec src mom').
           ++ rewrite (H26 e). omega.
           ++ destruct (H23 n).
              ** omega.
              ** rewrite H27.
                 rewrite <- inf_eq. omega.
      * split; trivial.
        rewrite upd_Znth_diff; try omega.
        rewrite Znth_list_repeat_inrange; omega.
        intro. rewrite H18 in H17.
        rewrite upd_Znth_same in H17.
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
                  (forall step, step <> src ->
                                In_path g step p2mom ->
                                In step (get_popped priq_contents') /\
                                step <> u) /\
                  path_globally_optimal g src mom p2mom /\
                  elabel g (mom, dst) <> inf /\
                  Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) <> inf /\
                  Znth dst dist_contents' = Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) /\ 
                  forall mom' p2mom',
                    path_correct g prev_contents' dist_contents' src mom' p2mom' ->
                    (forall step', step' <> src ->
                                   In_path g step' p2mom' ->
                                   In step' (get_popped priq_contents') /\
                                   step' <> u) ->
                    path_globally_optimal g src mom' p2mom' ->
                    path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) <= path_cost g p2mom' + Znth dst (Znth mom' (graph_to_mat g));

                    (* and inv_unseen remains true *)
                    forall dst,
                      0 <= dst < SIZE ->
                      inv_unseen prev_contents' priq_contents' dist_contents' dst;

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
              destruct (Z.eq_dec src dst).
              1: { (* separately handling a trivial case 
                      may now be able to remove this?      
                    *)
                subst dst.
                exists (src, []); split3.
                - split3; [| | split3].
                  + simpl. destruct H2 as [? [? [? ?]]].
                    unfold vertex_valid in H2.
                    rewrite H2. omega.
                  + unfold path_ends; simpl; omega.
                  + unfold path_cost; simpl.
                    rewrite <- inf_eq. omega.
                  + unfold path_cost; simpl. trivial.
                  + simpl. apply Forall_nil.
                - intros. destruct H33; simpl in H33.
                  + omega.
                  + destruct H33 as [? [? ?]]. omega.
                - unfold path_globally_optimal.
                  intros.
                  unfold path_cost at 1; simpl.
                  apply path_cost_pos; trivial.
              }
              destruct (H4 dst H31) as [? [? ?]].
              unfold inv_popped in H32.
              (* now we must distinguish between those
                 vertices that were already popped
                 and
                 u, which was just popped
               *)
              destruct (Z.eq_dec dst u).
              **  (* show that u is a valid entrant *)
                subst dst.
                unfold inv_unpopped in H33.
                assert (Znth u priq_contents < inf).
                {
                  rewrite <- isEmpty_in' in H15.
                   destruct H15 as [? [? ?]].
                   rewrite Hequ.
                   rewrite Znth_find.
                   2: { apply min_in_list.
                        apply incl_refl.
                        rewrite <- Znth_0_hd by (unfold SIZE in *; omega).
                        apply Znth_In; omega.
                   }
                   pose proof (fold_min _ _ H15). omega.
                 }
                 specialize (H33 H35).
                 destruct H33 as [p2mom [? [? [? [? [? [? ?]]]]]]].
                 unfold VType in *.
                 remember (Znth u prev_contents) as mom.
                 assert (0 <= mom < SIZE). {
                   destruct H33 as [? [? _]].              
                   assert (In_path g mom p2mom). {
                     destruct H42.
                     apply pfoot_in; trivial.
                   }
                   destruct H2. unfold vertex_valid in H2.
                   rewrite <- H2.
                   apply (valid_path_valid g p2mom); trivial.
                 }
                 (* this the best path to u:
                    go, optimally, to mom, and then take one step 
                  *)
                 exists (fst p2mom, snd p2mom +:: (mom, u)).
                 split3; trivial.
                 --- destruct H33 as [? [? [? [? ?]]]].
                     split3; [| | split3].
                     +++
                       destruct H43.
                       apply valid_path_app_cons; trivial;
                         try rewrite <- surjective_pairing; trivial.
                     +++ rewrite (surjective_pairing p2mom) in *.
                         simpl.
                         replace (fst p2mom) with src in *.
                         apply path_ends_app_cons; trivial.
                         destruct H43. simpl in H43; omega.
                     +++ apply path_cost_app_not_inf; trivial.
                     +++ rewrite path_cost_app_cons; trivial.
                         rewrite elabel_Znth_graph_to_mat; simpl; try omega; trivial.
                         apply link_evalid; trivial. 
                     +++ unfold VType in *.
                         rewrite Forall_forall. intros.
                         rewrite Forall_forall in H46.
                         apply in_app_or in H47.
                         destruct H47.
                         *** specialize (H46 _ H47). trivial.
                         *** simpl in H47.
                             destruct H47; [| omega].
                             rewrite (surjective_pairing x) in *.
                             inversion H47.
                             simpl.
                             rewrite <- H49, <- H50.
                             omega.
                 --- intros.
                     destruct H33 as [_ [? _]].
                     apply (in_path_app_cons _ _ _ src) in H44; trivial.
                     destruct H44.
                     +++ specialize (H36 _ H43 H44).
                         rewrite <- get_popped_irrel_upd; try omega; trivial.
                         apply get_popped_range in H36; omega.
                         intro. rewrite H45 in H36.
                         apply H17; trivial.
                     +++ rewrite H44.
                         rewrite get_popped_meaning.
                         rewrite upd_Znth_same; omega.
                         rewrite upd_Znth_Zlength; omega.
                 --- (* This is a key juncture --
                        we must show that the locally optimal path via mom
                        is actually the globally optimal path to u *)
(* tricky admit #1 *)
                   admit.
                   (*
                   unfold path_globally_optimal; intros.
                   unfold path_globally_optimal in H38.
                   destruct H36 as [? [? [? [? ?]]]].
                   rewrite path_cost_app_cons; trivial.
                   rewrite elabel_Znth_graph_to_mat;
                     trivial.
                   2: apply link_evalid; trivial.
                   simpl.
                   assert (forall x : Z * Z,
  {In (fst x) (get_popped priq_contents) /\ In (snd x) (get_popped priq_contents)} +
  {~
     (In (fst x) (get_popped priq_contents) /\ In (snd x) (get_popped priq_contents))}).
                   {
                     intros.
                     destruct (in_dec (ZIndexed.eq) (fst x)
                                      (get_popped priq_contents));
                     destruct (in_dec (ZIndexed.eq) (snd x)
                                      (get_popped priq_contents)).
                     - left; split; trivial.
                     - right. intro. destruct H50.
                       apply n0; trivial.
                     - right. intro. destruct H50.
                       apply n0; trivial.
                     - right. intro. destruct H50.
                       apply n0; trivial.
                   }
                   
                   destruct (Forall_dec (fun x : Z * Z =>
                                           In (fst x) (get_popped priq_contents) /\
                                           In (snd x) (get_popped priq_contents)) H50 (snd p')).
                   +++  (* impossible *)
                   +++ apply neg_Forall_Exists_neg in n0.
                       rewrite Exists_exists in n0.
                       destruct n0 as [? [? ?]].
                       apply Classical_Prop.not_and_or in H52.
                       assert (In_path g x p').
                       epath_to_vpath

                       
                       in_path_split:
                       
                       
                       
                       
                       n



                   (fun x : Z * Z =>
                      In (fst x) (get_popped priq_contents) /\
                      In (snd x) (get_popped priq_contents))
  ).
                                        
                   

                   
                   (* apply Znot_gt_le. intro. *)
                   destruct (H4 u) as [_ [? _]]; trivial.
                   unfold inv_unpopped in H50.
                   specialize (H50 H35).
                   
                 *)

              ** (* Here we must show that the 
                    vertices that were popped earlier
                    are not affected by the addition of
                    u to the popped set.

                    As expected, this is significantly easier.      
                  *)
                rewrite <- get_popped_irrel_upd in H14 by omega.
                 specialize (H32 H14).
                 destruct H32 as [? [? [? ?]]].
                 exists x. split3; trivial.
                 intros.
                 specialize (H35 _ H37 H38).
                 destruct H32.
                 rewrite <- get_popped_irrel_upd; try omega; trivial.
                 apply get_popped_range in H35; omega.
                 intro contra. rewrite contra in H35.
                     apply H17. trivial.
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
             destruct (Z.eq_dec src dst).
             1: { (* This trivial case can be handled separately 
                     Maybe I can now remove this? *)
               subst dst.
               replace (Znth src prev_contents) with src. 
               exists (src, []).
               split3; [| |split3; [| |split3]]; trivial.
               - split3; [| | split3].
                 + simpl. destruct H2. unfold vertex_valid in H2. rewrite H2. omega.
                 + split; trivial.
                 + unfold path_cost. simpl.
                   rewrite <- inf_eq. omega.
                 + unfold path_cost. simpl.
                   trivial.
                 + rewrite Forall_forall; intros.
                   simpl in H32; omega.
               - intros. destruct H33; simpl in H33.
                 omega. destruct H33 as [? [? ?]]. omega.
               - unfold path_globally_optimal; intros.
                 unfold path_cost at 1; simpl.
                 apply path_cost_pos; trivial.
               - rewrite elabel_Znth_graph_to_mat; simpl.
                 rewrite H3. rewrite <- inf_eq. omega.
                 omega. trivial. apply link_evalid; trivial.
               - unfold path_cost; simpl.
                 rewrite H3 by omega.
                 rewrite <- inf_eq; omega.
               - unfold path_cost; simpl.
                 rewrite H3 by omega.
                 omega.
               - intros.
                 unfold path_cost at 1; simpl.
                 rewrite H3 by omega.
                 destruct H32.
                 pose proof (path_cost_pos g p2mom' H2 H32 H1).
                   unfold inrange_graph in H1.
                   pose proof (H1 src mom').
                   assert (0 <= src < Zlength (graph_to_mat g)). {
                     rewrite graph_to_mat_Zlength. omega. }
                   assert ( 0 <= mom' < Zlength (graph_to_mat g)). {
                     rewrite graph_to_mat_Zlength.
                   destruct H35. destruct H35.
                   destruct H2.
                   unfold vertex_valid in H2.
                   rewrite <- H2.
                   apply (valid_path_valid _ p2mom'); trivial.
                   apply pfoot_in; trivial.
                 }
                   specialize (H37 H38 H39).
                   destruct H37.
                   destruct (Z.eq_dec src mom').
                 + rewrite (H40 e). omega.
                 + destruct (H37 n0).
                   * omega.
                   * rewrite H41. rewrite <- inf_eq. omega.
             }
             destruct (H4 dst H14) as [_ [? _]].
             unfold inv_unpopped in H32.
             specialize (H32 H31).
             destruct H32 as [p2mom [? [? ?]]].
             unfold VType in *.
             remember (Znth dst prev_contents) as mom.
             destruct H34 as [? [? [? [? ?]]]].
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
                specialize (H33 _ H39 H40).
                assert (step <> u). {
                  intro. 
                  unfold VType in *. rewrite H41 in H33.
                  apply H17; trivial.
                }
                split; trivial.
                rewrite <- get_popped_irrel_upd; try omega; trivial.
                apply get_popped_range in H33; omega.
             ** intros.
                apply H38; trivial.
                intros. admit.
                (* tricky *)
           ++ (* now we show that all is well for the 
                 vertices that have not yet been seen *)
             unfold inv_unseen; intros.
             destruct (Z.eq_dec dst u).
             1: { rewrite e in H31.
                  rewrite upd_Znth_same in H31; omega. }
             rewrite upd_Znth_diff in H31 by omega.
             destruct (H4 dst H14) as [_ [_ ?]].
             unfold inv_unseen in H32.
             specialize (H32 H31); trivial.
           ++ destruct (Z.eq_dec src u).
              1: subst src; rewrite upd_Znth_same; omega.
              rewrite upd_Znth_diff; omega.             
           ++ apply get_popped_meaning.
              rewrite upd_Znth_Zlength; omega.
              rewrite upd_Znth_same; omega.
           ++ apply inrange_upd_Znth; trivial;
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
             destruct H35 as [? [? [? [? ?]]]].
      unfold field_compatible; split3; [| | split3]; auto.
      unfold legal_nested_field; split; [auto | simpl; omega].
           }
           forward. thaw FR2. 
           gather_SEP 0 3 1.
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
               replace 8 with SIZE in H37.
               assert (0 <= i < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; omega).
               assert (0 <= u < Zlength (graph_to_mat g)) by
                   (rewrite graph_to_mat_Zlength; omega).
               specialize (H1 i u H38 H39).
               rewrite inf_eq2 in H37.
               rewrite Heqcost in *.
               rewrite Int.signed_repr in H37.
               2: {
                 destruct H1.
                 destruct (Z.eq_dec i u).
                 - rewrite (H40 e). rep_omega.
                 - destruct (H1 n).
                   unfold VType in *.
                   replace SIZE with 8 in H41.
                   destruct H41. 
                   pose proof (Int.min_signed_neg).
                   assert (Int.max_signed / 8 <= Int.max_signed). {
                        compute. inversion 1.
                   }
                   split; try omega.
                   rewrite H41.
                   rewrite <- inf_eq. 
                   compute; split; inversion 1.
               }
               rewrite Int.signed_repr in H37.
               2: rewrite <- inf_eq; compute; split; inversion 1.
               destruct H1.
               destruct (Z.eq_dec i u).
               - rewrite (H40 e). compute; split; inversion 1.
               - destruct (H1 n).
                 + omega.
                 + rewrite H41. omega.
             }
             assert (0 <= Znth u dist_contents' <= inf). {
               assert (0 <= u < Zlength dist_contents') by omega.
               apply (Forall_Znth _ _ _ H39) in H31.
               assumption. 
             } 
              assert (0 <= Znth i dist_contents' <= inf). {
                assert (0 <= i < Zlength dist_contents') by omega.
                apply (Forall_Znth _ _ _ H40) in H31.
                assumption. 
              }
              assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
                split; [omega|].
                unfold inf in *. rep_omega.
                }
              forward. forward. forward_if.
  ** rewrite Int.signed_repr in H42
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
       destruct (H21 _ H43) as [p2i [? [? ?]]].
       destruct (H21 _ H28) as [p2u [? [? ?]]].
       unfold path_globally_optimal in H46.
       specialize (H46 (fst p2u, snd p2u +:: (u,i))).
       rewrite Heqcost in H42.
       destruct H47 as [? [? [? [? ?]]]].
       destruct H44 as [? [? [? [? ?]]]].
       rewrite H56, H52 in H42.
       apply Zlt_not_le in H42.
       unfold VType in *.
       apply H42.
       rewrite path_cost_app_cons in H46; trivial. 
       2: { rewrite elabel_Znth_graph_to_mat; trivial.
            2: apply link_evalid; trivial.
            simpl. omega.
       }
       rewrite elabel_Znth_graph_to_mat in H46; trivial.
       2: apply link_evalid; trivial.
       simpl fst in H46.
       simpl snd in H46.
       apply H46.
       - apply valid_path_app_cons; trivial;
         rewrite <- surjective_pairing; 
         destruct H50; trivial.
       - rewrite (surjective_pairing p2u) in *.
           simpl.
           replace (fst p2u) with src in *.
           apply path_ends_app_cons; trivial.
           destruct H50. simpl in H50; omega.
     }
     assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
         (repeat rewrite Zlength_map; omega).
     forward. forward. forward.
     forward; rewrite upd_Znth_same; trivial.
     (* The above "forward" commands are tweaking the 
        three arrays! *)
     1: entailer!. 
     forward.

     (* Now we must show that the for loop's invariant
        holds if we take another step, 
        ie when i increments *)

     (* We will provide the arrays as they stand now:
        with the i'th cell updated in all three arrays, 
        to log a new improved path via u *)
     Exists (upd_Znth i prev_contents' u).
     Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
     Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)). 
     repeat rewrite <- upd_Znth_map; entailer!.
     remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
     assert (u <> i) by (intro; subst; omega).
     split3; [| | split3; [| | split3; [| | split3]]].
     ---
       intros. pose proof (H21 dst).
       unfold inv_popped in H57.
       unfold inv_popped.
       intros.
       destruct (Z.eq_dec dst i).
       +++ subst dst.
           rewrite get_popped_meaning, upd_Znth_same in H58.
           3: rewrite upd_Znth_Zlength.
           all: omega.
       +++ pose proof (get_popped_range _ _ H58).
           rewrite upd_Znth_Zlength in H59 by omega.
           rewrite <- get_popped_irrel_upd in H58; try omega.
           specialize (H57 H58).
           destruct H57 as [p2dst [? [? ?]]].
           exists p2dst; split3; trivial.
           *** destruct H57 as [? [? [? [? ?]]]].
               split3; [| | split3]; trivial.
               1: rewrite upd_Znth_diff; omega.
               rewrite Forall_forall; intros.
               assert ((snd x) <> src). {
                 admit.
               (* The "to" vertex of the link
                  would never be src. *)
                 (* Shengyi, could you prove this for me?

                  Also, please note how I use this 
                  technique to specialise H60
                  and get that (snd x) is in popped.

                  Later there are some places where
                  I have left easy admits for you to 
                  do the same for me. 
*)
               }
               assert (In_path g (snd x) p2dst). {
                 unfold In_path. right.
                 exists x. split; trivial.
                 destruct H2 as [? [? [? ?]]].
                 unfold dst_edge in H70.
                 rewrite H70. right; trivial.
               }
               specialize (H60 _ H67 H68).
               rewrite Forall_forall in H65.
               specialize (H65 _ H66).
               assert (snd x <> i). {
                 intro contra.
                 unfold VType in *.
                 rewrite contra in H60.
                 apply H43. trivial.
               }
               unfold VType in *.
               rewrite upd_Znth_diff; try omega.
               apply get_popped_range in H60; omega.
           *** intros.
               specialize (H60 _ H62 H63).
               rewrite <- get_popped_irrel_upd; try omega; trivial.
               apply get_popped_range in H60; omega.
               intro contra. rewrite contra in H60.
               apply H43. trivial.
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
             destruct (H21 _ H28) as [p2u [? [? ?]]].
             unfold VType in *.
             rewrite upd_Znth_same by omega.
             exists p2u.
             split3; [| |split3; [| |split3]]; trivial.
             *** destruct H59 as [? [? [? [? ?]]]].
                 split3; [ | | split3]; trivial.
                 ---- rewrite upd_Znth_diff by omega.
                      trivial.
                 ---- rewrite Forall_forall; intros.
                      assert ((snd x) <> src). {
                        admit.
                      (* The "to" vertex of the link
                         would never be src. *)
                        (* Shengyi? *)
                      }
                      assert (In_path g (snd x) p2u). {
                        unfold In_path. right.
                        exists x. split; trivial.
                        destruct H2 as [? [? [? ?]]].
                        unfold dst_edge in H70.
                        rewrite H70. right; trivial.
                      }
                      specialize (H60 _ H67 H68).
                      rewrite Forall_forall in H65.
                      specialize (H65 _ H66).
                      unfold VType in *.
                      rewrite upd_Znth_diff; try omega; trivial.
                      apply get_popped_range in H60; omega.
                      intro. rewrite H69 in H60.
                      apply H43. trivial.
             *** intros.
                 specialize (H60 _ H62 H63).
                 rewrite <- get_popped_irrel_upd; try omega; trivial.
                 apply get_popped_range in H60; omega.
                 intro; rewrite H64 in H60. apply H43; trivial.
             *** rewrite elabel_Znth_graph_to_mat;
                   simpl; trivial; try omega.
                 apply link_evalid; trivial.
             *** rewrite upd_Znth_same in H58 by omega.
                 destruct H59 as [_ [_ [_ [? _]]]].
                 rewrite <- H59. omega.
             *** rewrite upd_Znth_same by omega.
                 destruct H59 as [_ [_ [_ [? _]]]].
                 omega.
             *** intros.
                 (* This is another key point in the proof:
                    we must show that the path via u is 
                    better than all other paths via
                    other popped verices *)
                 destruct H62 as [? [? [? [? ?]]]].
                 admit.
                 (*       This is tricky admit #2 *) 
                 (*
                 destruct (in_dec (ZIndexed.eq) u (epath_to_vpath g p2mom')).
                 ---- (* Yes, the path p2mom' goes via u *)
                   apply in_path_eq_epath_to_vpath in i0; trivial.
                   destruct i0.
                   ++++ (* u is the source itself, 
                           meaning that this dst is 
                           just one hop from src *)
                 (* This also means that mom' has to be
                    src -- if the minimally-chosen vertex
                    is the source itself, that means
                    that means that the while loop
                    is on its first run.
                  *)
                     destruct H66.
                     replace (fst p2mom') with src in * by omega.
                     replace mom' with src in * by admit.
                     rewrite H70 in *.
                     destruct H59 as [? [? [? [? ?]]]].
                     rewrite <- H74.
                     destruct (Z.eq_dec src i).
                     **** rewrite e in H68.
                          rewrite upd_Znth_same in H68.
                          rewrite <- H68. rewrite e.
                          rewrite <- e.
                          rewrite H25, H3; omega.
                          omega.
                     **** rewrite upd_Znth_diff in H68 by omega.
                          rewrite <- H68. omega.
                   ++++ (* u is in the links of the path *)
                     destruct H70 as [? [? ?]].
                     destruct H2 as [? [? [? ?]]].
                     unfold src_edge in H73.
                     unfold dst_edge in H74.
                     rewrite H73, H74 in H71.
                     destruct (Z.eq_dec mom' u).
                     1: { rewrite e in *.
                          unfold path_globally_optimal in H61.
                          specialize (H61 _ H63 H66).
                          omega.
                     }
                     (* so the path p2mom' goes 
                        src --> u --> mom'
                        and then takes one hop to i
                      *)
                     rewrite Forall_forall in H64.
                     destruct (H64 _ H70).
                     rewrite <- get_popped_irrel_upd in H62; try omega; trivial.
                     2: apply get_popped_range in H62; rewrite upd_Znth_Zlength in H62; omega.
                     2: { intro. rewrite H77 in H62.
                          rewrite get_popped_meaning in H62.
                          rewrite upd_Znth_same in H62; omega.
                          rewrite upd_Znth_Zlength; omega.
                     }
                     destruct (H21 _ H62) as [? [? [? ?]]].

                     admit.
                 ---- (* p2mom' was composed entirely of
                         old popped vertices --
                         we can apply inv_unpopped for i
                       *)
                   assert (i <= i < SIZE) by omega.
                   destruct (Z.eq_dec (Znth i priq_contents') inf).
                   ++++ admit.
                   ++++ assert (Znth i priq_contents' < inf). {
                          rewrite get_popped_meaning in H43.
                          admit.
                          (* easy *)
                          omega.
                        }
                        assert (0 <= i < SIZE) by omega.
                        unfold inv_unpopped in H23.
                        specialize (H23 i H70 H71).
                        destruct H23 as [? [? [? [? [? [? [? [? ?]]]]]]]].
                        admit.
*)
         +++ assert (0 <= dst < i) by omega.
             (* We will proceed using the 
                old best-known path for dst *)
             specialize (H22 _ H58).
             unfold inv_unpopped in *.
             intros.
             rewrite upd_Znth_diff in H59 by omega.
             destruct (H22 H59) as [p2mom [? [? [? [? [? [? ]]]]]]].
             unfold VType in *.
             remember (Znth dst prev_contents') as mom.
             exists p2mom. split3; [| |split3; [| |split3]]; trivial. 
             *** destruct H60 as [? [? [? [? ?]]]].
                 split3; [| | split3]; trivial.
                 ---- rewrite upd_Znth_diff by omega;
                        rewrite <- Heqmom; trivial.
                 ---- rewrite (upd_Znth_diff dst i) by omega.
                      assert ((Znth dst prev_contents') <> i). {
                        (* the path could not have gone 
                           through i, since i is unpopped *)
                        intro.
                        apply H43.
                        rewrite <- Heqmom in *.
                        rewrite <- H71. trivial.
                        (* can get from 
                           H71 : mom = i
                           H67 : path_ends g p2mom src mom
                           H61 : forall step : Z,
                           step <> src -> In_path g step p2mom -> In step (get_popped priq_contents')
                         *)
                        (* Shengyi? *)
                        admit.
                      }
                      rewrite upd_Znth_diff; try omega.
                      2: {
                        rewrite <- Heqmom.
                        rewrite H35.
                        destruct H2.
                        unfold vertex_valid in H2.
                        rewrite <- H2.
                        apply (valid_path_valid g p2mom); trivial.
                        destruct H67.
                        apply pfoot_in; trivial.
                      }
                      rewrite <- Heqmom.
                      trivial.
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H70.
                      specialize (H70 _ H71).
                      rewrite upd_Znth_diff; try omega.
                      1: unfold VType in *; rewrite H34;
                        apply (step_in_range2 g p2mom); trivial.
                      1: unfold VType in *; omega.
                      intro contra.
                      (* 
                         Shengyi? 

                         can specialise 
                          H61 : forall step : Z,
        step <> src -> In_path g step p2mom -> In step (get_popped priq_contents')
                          using step = (snd x)

                          Will need
                          H67 : path_ends g p2mom src mom

                          Then rewrite snd x = i.

                          there is a contradiction thanks to 
                          H43 : ~ In i (get_popped priq_contents')
                       *)
                      admit.

             *** intros.
                 specialize (H61 _ H67 H68).
                 repeat rewrite <- get_popped_irrel_upd; try omega; trivial.
                 apply get_popped_range in H61; omega.
                 intro; rewrite H69 in H61; apply H43; trivial.
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
                 apply H66; trivial.
                 ---- destruct H67 as [? [? [? [? ?]]]].
                      split3; [| |split3]; trivial.
                      ++++ rewrite upd_Znth_diff in H72; try omega.
                           (* specialise H68. 
                              1. use get_popped_range. done.
                              2. intro contra. 
                              rewrite contra in H68.
                           rewrite get_popped_meaning in H68.
                           rewrite upd_Znth_same in H68; omega.
                            *)
                           (* Shengyi? *)
                           (* Below I give you an example *)
                           admit.
                           admit.
                      ++++ rewrite Forall_forall; intros.
                           rewrite Forall_forall in H73.
                           specialize (H73 _ H74).
                           unfold VType in *.
                           rewrite upd_Znth_diff in H73;
                             try omega.
                           rewrite H34.
                           apply (step_in_range2 g p2mom');
                             trivial.
                           intro.
                           (* similar to above *)
                           (* Shengyi? *)
                           admit.
                 ---- intros.
                      specialize (H68 _ H70 H71).
                      rewrite <- get_popped_irrel_upd in H68; try omega; trivial.
                      apply get_popped_range in H68;
                        rewrite upd_Znth_Zlength in H68; omega.
                      (* Example for Shengyi *)
                      intro. rewrite H72 in H68.
                      rewrite get_popped_meaning in H68.
                      rewrite upd_Znth_same in H68; omega.
                      rewrite upd_Znth_Zlength; omega.
     --- intros.
         assert (i <= dst < SIZE) by omega.
         destruct (Z.eq_dec dst i).
         1: subst dst; omega.
         rewrite upd_Znth_diff in H58 by omega.
         destruct (H23 _ H59 H58) as [p2mom [? [? ?]]].
         unfold VType in *.
         remember (Znth dst prev_contents') as mom.
         rewrite upd_Znth_diff by omega.
         exists p2mom.
         destruct H62 as [? [? [? [? ?]]]].
         split3; [| | split3; [| | split3]]; trivial.
         +++ destruct H60 as [? [? [? [? ?]]]].
             split3; [| | split3]; trivial.
             *** rewrite <- Heqmom. trivial.
             *** rewrite <- Heqmom.
                 rewrite upd_Znth_diff; try omega; trivial.
                 (* can show that mom is in popped.
                    then can use get_popped_range, 
                    and for the contra can intro, 
                    rewrite in H61, and then get a contra
                    from H43 

                    Shengyi?
                  *)
                 admit.
                 admit.
             *** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H70.
                 specialize (H70 _ H71).
                 unfold VType in *.
                 rewrite upd_Znth_diff; try omega; trivial.
                 ---- rewrite H34.
                      apply (step_in_range2 g p2mom); trivial.
                 ---- (* can specialize H61 and then
                         use contra 

                         Shengyi?
*)
                   admit.
         +++ intros.
             specialize (H61 _ H67 H68).
             destruct H61.
             split; trivial.
             rewrite <- get_popped_irrel_upd;
             try omega; trivial.
             *** apply get_popped_range in H61; omega.
             *** intro contra. rewrite contra in H61.
                 apply H43; trivial.
         +++ intros. rewrite <- Heqmom; trivial.
         +++ rewrite <- Heqmom; trivial.
         +++ rewrite <- Heqmom. trivial.
         +++ rewrite <- Heqmom. rewrite upd_Znth_diff; omega.
         +++ intros. rewrite <- Heqmom.
             apply H66. 
             *** destruct H67 as [? [? [? [? ?]]]].
                 split3; [| |split3]; trivial.
                 ---- rewrite upd_Znth_diff in H72;
                        try omega; trivial.
                      (* Shengyi? *)
                      (* first please help me 
                         specialize H68.
                         
                         then...
                      apply get_popped_range in H68.
                      rewrite upd_Znth_Zlength in H68;
                        omega.
                      intro. rewrite H70 in H68.
                      rewrite get_popped_meaning in H68.
                      rewrite upd_Znth_same in H68; omega.
                      
                      rewrite upd_Znth_Zlength; omega.
                       *)
                      admit.
                      admit.
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H73.
                      specialize (H73 _ H74).
                      unfold VType in *.
                      rewrite upd_Znth_diff in H73; try omega; trivial.
                      (* Shengyi? *)
                      (* same story. need to specialize
                       H68 and then proceed *)

                      (*rewrite get_popped_meaning in H68.
                      rewrite upd_Znth_same in H68; omega.
                      rewrite upd_Znth_Zlength; omega.
                       *)
                      admit.
                      admit.

             *** intros.
                 specialize (H68 _ H70 H71).
                 destruct H68.
                 rewrite <- get_popped_irrel_upd in H68; try omega; trivial.
                 split; trivial.
                 ---- apply get_popped_range in H68.
                      rewrite upd_Znth_Zlength in H68; omega.
                 ---- intro contra. rewrite contra in H68.
                      rewrite get_popped_meaning in H68.
                      rewrite upd_Znth_same in H68; omega.
                      rewrite upd_Znth_Zlength; omega.
             *** trivial.
     --- intros.
         pose proof (H24 dst H57).
         unfold inv_unseen in H58.
         unfold inv_unseen; intros.
         assert (dst <> i). {
           intro. subst dst. rewrite upd_Znth_same in H59; omega.
           }
         rewrite upd_Znth_diff in H59; try omega.
         specialize (H58 H59).
         repeat rewrite upd_Znth_diff; try omega.
     --- rewrite upd_Znth_diff; try omega.
         intro. subst src; omega.
     --- rewrite upd_Znth_diff; try omega.
         intro. subst src; omega.
     --- rewrite upd_Znth_diff; try omega.
         intro. subst src; omega.
     --- apply get_popped_irrel_upd; try omega; trivial.
     --- split3; apply inrange_upd_Znth; trivial; try omega.
  ** rewrite Int.signed_repr in H42
      by (unfold inf in *; rep_omega).
     (* This is the branch where I didn't
        make a change to the i'th vertex. *)
     forward.
     (* The old arrays are just fine. *)
     Exists prev_contents' priq_contents' dist_contents'.
     entailer!.
     remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
     split.
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
         destruct (H23 i H56 H55) as [p2mom [? [? [? [? [? [? ?]]]]]]].
         unfold VType in *.
         remember (Znth i prev_contents') as mom.
         (* now I must show that the same path
            is actually still okay *)
         exists p2mom; split3; [| |split3; [| |split3]]; trivial.
         +++ intros.
             specialize (H58 _ H64 H65).
             destruct H58. trivial.
         +++ intros.
             apply H63; trivial. intros.
             specialize (H65 _ H67 H68).
             split; trivial.
             admit.
             (* Another interesting case *)
     --- intros. destruct (Z.eq_dec dst i).
         +++ subst dst. omega.
         +++ apply H23; omega.
          ++ (* i was not a neighbor of u. 
                 prove the for loop's invariant holds *)
             replace 8 with SIZE in H37 by omega.
             rewrite inf_eq2 in H37.
             forward.
             Exists prev_contents' priq_contents' dist_contents'.
             entailer!.
             remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
             split; intros.
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
                    destruct (H23 i H51 H50) as [p2mom [? [? [? [? [? ?]]]]]].
                    unfold VType in *.
                    remember (Znth i prev_contents') as mom.
                    exists p2mom; split3; [| |split3; [| |split3]]; trivial.
                    +++ intros.
                        specialize (H53 _ H58 H59).
                        destruct H53. trivial.
                    +++ intros. apply H57; trivial.
                    +++ intros. apply H57; trivial.
                        unfold VType in *. intros.    
                        specialize (H59 _ H61 H62).
                        split; trivial.
                        admit.
                        (* interesting case -- 
                           show that the path neednt'
                           go through u *)
                --- apply H22; omega.
             ** destruct (Z.eq_dec dst i).
                --- omega. 
                --- apply H23; omega.
        -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
              
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
          unfold dijkstra_correct. 
          split3; trivial.
          apply H19; trivial.
          apply H21; trivial.
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
