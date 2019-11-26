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
(* Require Import RamifyCoq.msl_application.DijkstraGraph. *)
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
(* Definition inf := Int.max_signed - Int.max_signed/SIZE. *)

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
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE.

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

(* During refactoring, merge the two that follow *)
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

(* Find a way to hint that the inhabitant of 
   Z*Z is (0,0). 
   Then merge the two below 
 *)
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
         (* rewrite Zlength_correct at 1. *)
         (* rewrite Zlength_correct at 1. *)
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

Definition dijkstra_correct g (src : VType) (prev priq dist: list VType) : Prop :=
  forall dst,  
    (In dst (get_popped priq) -> (* globally optimized *)
     exists path, 
       path_correct g prev dist src dst path /\
       path_globally_optimal g src dst path /\
       (* Znth dst dist = path_cost g path /\ *)
       (* moved the above into path_correct. *)
       Forall (fun x => In (fst x) (get_popped priq) /\
                        In (snd x) (get_popped priq))
              (snd path)) /\
    (0 <= dst < Zlength priq ->
     Znth dst priq < inf  -> (* have been seen *)
     let mom := (Znth dst prev) in 
     (* In mom (get_popped priq) /\ *) (* redundant *)
     exists p2mom,
       path_correct g prev dist src mom p2mom /\
       path_globally_optimal g src mom p2mom /\
       Forall (fun x => In (fst x) (get_popped priq) /\
                        In (snd x) (get_popped priq))
              (snd p2mom) /\
       let p2dst := (fst p2mom, snd p2mom +:: (mom, dst)) in 
       path_correct g prev dist src dst p2dst /\
       forall mom' p2mom',
         path_correct g prev dist src mom' p2mom' ->
         path_globally_optimal g src mom' p2mom' ->
         Forall (fun x => In (fst x) (get_popped priq) /\
                          In (snd x) (get_popped priq))
                (snd p2mom') ->
         path_cost g p2dst <=
         path_cost g (fst p2mom', snd p2mom' +:: (mom', dst))) /\
    (0 <= dst < Zlength priq ->
     Znth dst priq = inf  -> (* have not been seen *)
     forall u p2u,
       In u (get_popped priq) ->
       path_correct g prev dist src u p2u ->
       Forall (fun x => In (fst x) (get_popped priq) /\
                        In (snd x) (get_popped priq))
              (snd p2u) ->
       path_cost g (fst p2u, snd p2u +:: (u, dst)) = inf).

(*
Lemma dijkstra_correct_priq_irrel:
  forall g src prev priq dist i new,
    Zlength priq = SIZE ->
    0 <= i < Zlength priq ->
    Znth i priq < inf ->
    new < inf ->
    dijkstra_correct g src prev priq dist ->
    dijkstra_correct g src prev (upd_Znth i priq new) dist.
Proof.
  unfold SIZE.
  unfold dijkstra_correct. intros.
  assert (new <> inf + 1) by omega.
  assert (Znth i priq <> inf + 1) by omega.
  rewrite get_popped_unchanged in * by assumption. 
  split; intros. 
  - apply H3; trivial.
  - mit.
    (*rewrite upd_Znth_Zlength in H7 by assumption.
    apply H3; trivial.       
    destruct (Z.eq_dec dst i).  
    + rewrite e. assumption.
    + rewrite upd_Znth_diff in H8; assumption. *)
mited. *)
(* Qed. *)

(* Even if I state this functionally, 
   it doesn't matter if prev[i] has been changed.
   This is because we only look at _those_
   cells of prev for which the vertices 
   have been popped. 
   We have a proof that i has not been popped.
 *)
Lemma dijkstra_correct_prev_irrel:
  forall g src prev priq dist i new,
    0 <= i < Zlength priq ->
    new <> inf + 1 ->
    dijkstra_correct g src prev priq dist ->
    dijkstra_correct g src (upd_Znth i prev new) priq dist.
Proof.
  intros. unfold dijkstra_correct in *. intros.
  split; intros.
  (* apply H1. assumption. *)
Abort. (* may now be impossible to show like this *)

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
                    Znth i (Znth i (graph_to_mat g)) = 0)
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
        (* and add a statement that the items that are in PQ but are not inf+1 are known to be unreachable *) 
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
  cost < inf -> (* is dst my neighbor? *)
  Znth dst dist <= Znth me dist + cost.
(* by the time we're done, the cost to the dst is either better 
or the same as the cost via me *)

Lemma valid_path_app_cons: (* drag out *)
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    0 <= u < SIZE ->
    0 <= i < SIZE ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.  (* another lemma *)
  split; [assumption|].
  destruct H as [? [? [? ?]]].
  simpl; split.
  + rewrite H5; simpl. (* sound_dijk *)
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

Lemma path_cost_app_cons:
  forall g p2u u i,
    inrange_graph (graph_to_mat g) ->
    sound_dijk_graph g ->
    Zlength (graph_to_mat g) = SIZE ->
    0 <= u < SIZE ->
    0 <= i < SIZE ->
    path_cost g p2u <> inf ->
    path_cost g p2u + Znth i (Znth u (graph_to_mat g)) =
    path_cost g (fst p2u, snd p2u +:: (u, i)).
Proof.
  intros.
  rewrite path_cost_app_cons.
  - rewrite elabel_Znth_graph_to_mat; simpl.
    omega. assumption.
    destruct H0 as [? [? [_ _]]].
    unfold edge_valid in H5.
    unfold vertex_valid in H0.
    rewrite H5; split; simpl; [rewrite H0|]; assumption.
  - rewrite elabel_Znth_graph_to_mat; simpl.
    + intro. unfold inrange_graph in H.
      rewrite <- H1 in H2, H3.
      specialize (H _ _ H3 H2).
      rewrite H5 in H.
      compute in H; destruct H.
      apply H6; reflexivity.
    + assumption.
    + destruct H0 as [? [? [_ _]]].
      unfold edge_valid in H5.
      unfold vertex_valid in H0.
      rewrite H5; split; simpl; [rewrite H0|]; assumption.
  - assumption.
Qed.

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
  destruct (H6 H3) as [p2i [? [? ?]]].
  destruct (H7 H4) as [p2u [? [? ?]]].
  clear H0 H6 H7. 
  unfold path_globally_optimal in H9. 
  destruct H8 as [? [? [? [? ?]]]].
  destruct H11 as [? [? [? [? ?]]]].  
  specialize (H9 (fst p2u, snd p2u ++ [(u,i)])).
  apply get_popped_range in H3.
  apply get_popped_range in H4.
  unfold VType in *. rewrite H2 in H3, H4.
  rewrite <- path_cost_app_cons in H9 by assumption.
  rewrite H17, H8. apply H9. 
  - destruct p2u; simpl. 
    destruct H15.
    apply valid_path_app_cons; assumption.
  - destruct p2u; simpl.
    replace z with src in *.
    apply path_ends_app_cons; assumption.
    destruct H15; simpl in H15; omega.
Qed.

(* Pretty sure I can prove this without using 
   In src (get_popped priq)
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
    trivial. (* here *)
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

Lemma path_end_in_popped':
  forall g src mom priq prev dist p2mom,
    sound_dijk_graph g ->
    snd p2mom <> [] ->
    path_correct g prev dist src mom p2mom ->
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq) /\
         In (snd x) (get_popped priq)) (snd p2mom) ->
    In mom (get_popped priq).
Proof. Abort.
(*
  intros. rewrite Forall_forall in H1.
  destruct H0 as [? [? [? [? ?]]]].
  destruct H2.
  pose proof (pfoot_in _ _ _ H6).
  unfold In_path in H7.
  destruct H7.
  - destruct p2mom. simpl in H7. subst v.
    

    
    unfold phead in H1; simpl in H1.
    rewrite H1 in H4. rewrite H4.
    trivial. (* here *)
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
Qed. *)

Lemma path_cost_pos_gen:
  forall g links starter,
    inrange_graph (graph_to_mat g) ->
    0 <= starter ->
    0 <= fold_left careful_add (map (elabel g) links) starter.
Proof.
  intros. generalize dependent starter.
  induction links.
  - intros. simpl; trivial.
  - intros. simpl. apply IHlinks.
    rewrite elabel_Znth_graph_to_mat.
    rewrite careful_add_clean.
    unfold inrange_graph in H.
    specialize (H (fst a) (snd a)).
    (* okie, we're gonna be fine after adding those on *)  
Admitted.


Lemma path_cost_pos:
  forall g p,
    inrange_graph (graph_to_mat g) ->
    (* valid_path g p -> *)
    0 <= path_cost g p.
Proof.
  intros.
  destruct p as [src links].
  unfold path_cost. simpl.
  apply path_cost_pos_gen. trivial. reflexivity.
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
  - (* done with the first forloop *)
    replace (SIZE - SIZE) with 0 by omega; rewrite list_repeat_0, <- (app_nil_end).
    forward. forward. forward. 
    forward_loop
      (EX prev_contents : list Z,
       EX priq_contents : list Z,
       EX dist_contents : list Z,
       PROP (
           dijkstra_correct g src prev_contents priq_contents dist_contents;
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
       PROP (Forall (fun x => x >= inf) priq_contents;
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
        split3; try apply inrange_upd_Znth; trivial.     
        left; unfold SIZE; simpl.
        2,3: rewrite <- inf_eq. all: unfold SIZE in *; omega.
      }
      assert (get_popped (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) = []).
      { apply get_popped_empty. rewrite Forall_forall; intros.
        unfold upd_Znth in H15.
        apply in_app_or in H15.
        destruct H15; [| apply in_inv in H15; destruct H15].
        1,3: rewrite sublist_list_repeat in H15 by omega;
          apply in_list_repeat in H15; omega.
        rewrite <- H15. compute; omega.
      } 
      (* math stuff *)
      unfold dijkstra_correct; rewrite H15. split3; intros.
      * inversion H16.
      * destruct (Z.eq_dec src dst). 
        -- subst dst.
           exists (src, []).
           split3; [| | split3].    
           ++ split3; [| | split3]; try repeat rewrite upd_Znth_same.
              3,6,7: rewrite Zlength_list_repeat; omega.
              3,4: unfold path_cost; simpl; compute; omega.
              ** simpl. destruct H2 as [? [? [? ?]]].
                 unfold vertex_valid in H2.
                 rewrite H2. omega.
              ** split; simpl; trivial.
              ** rewrite Forall_forall; intros.
                 simpl in H18. inversion H18.
           ++ unfold path_globally_optimal; intros.
              unfold path_cost at 1; simpl.
              apply path_cost_pos; trivial.
           ++ rewrite Forall_forall; intros. inversion H18.
           ++ split3; [| | split3]; try repeat rewrite upd_Znth_same; try rewrite Zlength_list_repeat; try omega.
              ** simpl. destruct H2 as [? [? [? ?]]].
                 unfold strong_evalid.
                 unfold vertex_valid in H2;
                   unfold edge_valid in H18.
                 rewrite H18, H2, H2, H2, H20, H19; simpl.
                 omega.
              ** simpl. split; simpl; trivial.
                 destruct H2 as [? [? [? ?]]].
                 rewrite H20. trivial.
              ** simpl. unfold path_cost.
                 simpl. rewrite elabel_Znth_graph_to_mat.
                 simpl. rewrite H3 by omega.
                 unfold careful_add. simpl. compute; omega.
                 trivial.
                 destruct H2 as [? [? [? ?]]].
                 unfold edge_valid in H18.
                 unfold vertex_valid in H2.
                 rewrite H18, H2; simpl; omega.
              ** simpl. unfold path_cost. simpl.
                 rewrite elabel_Znth_graph_to_mat.
                 simpl. rewrite H3 by omega.
                 unfold careful_add. simpl. compute; omega.
                 trivial.
                 destruct H2 as [? [? [? ?]]].
                 unfold edge_valid in H18.
                 unfold vertex_valid in H2.
                 rewrite H18, H2; simpl; omega.
              ** rewrite Forall_forall; intros.
                 simpl in H18.
                 destruct H18; [|omega].
                 rewrite (surjective_pairing x) in *.
                 inversion H18. simpl snd.
                 rewrite upd_Znth_same; trivial.
                 rewrite Zlength_list_repeat; omega.
           ++ intros. simpl fst. simpl snd.
              rewrite upd_Znth_same.
              2: rewrite Zlength_list_repeat; omega.
              simpl. unfold path_cost at 1. simpl.
              rewrite elabel_Znth_graph_to_mat.
              2: trivial.
              2: { destruct H2 as [? [? [? ?]]].
                   unfold edge_valid in H21.
                   unfold vertex_valid in H2.
                   rewrite H21, H2; simpl; omega. }
              simpl. rewrite H3 by omega.
              unfold careful_add; simpl.
              apply path_cost_pos; trivial.
        -- exfalso.
           rewrite upd_Znth_Zlength, Zlength_list_repeat in H16; try omega.
           rewrite upd_Znth_diff, Znth_list_repeat_inrange in H17; try omega.
           all: rewrite Zlength_list_repeat; omega.
      * inversion H18.
    + Intros prev_contents priq_contents dist_contents.
      assert_PROP (Zlength priq_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength prev_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength dist_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      forward_call (v_pq, priq_contents). 
      forward_if.
      * assert (isEmpty priq_contents = Vzero). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H12 in H11; simpl in H11;
              now inversion H11.
        }
        clear H11.
        forward_call (v_pq, priq_contents). Intros u.
        assert (0 <= u < Zlength priq_contents).
        { rewrite H11. 
          apply find_range.  
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H8.
          inversion H8. simpl. left; trivial. }
        rewrite Znth_0_hd, <- H11 by omega.
        do 2 rewrite upd_Znth_map.
        remember (upd_Znth u priq_contents (inf+1)) as priq_contents_popped.
        forward_for_simple_bound
          SIZE
          (EX i : Z,
           EX prev_contents' : list Z,
           EX priq_contents' : list Z,
           EX dist_contents' : list Z,
           PROP (
               In u (get_popped priq_contents');
               forall dst, (* time to rethink this...*)
                 0 <= dst < i ->
                 cost_was_improved_if_possible g u dst dist_contents';
                 dijkstra_correct g src prev_contents' priq_contents' dist_contents';
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
        -- Exists prev_contents. 
           Exists priq_contents_popped.
           Exists dist_contents.
           repeat rewrite <- upd_Znth_map.
           entailer!. (* here *)
           remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u. 
           split. 
           1: { apply get_popped_meaning.
                rewrite upd_Znth_Zlength; omega.
                rewrite upd_Znth_same; omega. } 
           split3; [intros; omega | |
                    apply inrange_upd_Znth; trivial;
                    rewrite <- inf_eq; rep_omega].  
           assert (Znth u priq_contents <> inf + 1). {
             (* maybe lemma *)
 (* comes from the fact that priq_contents is not empty, 
    and that u was found to be the min *) 
             clear -H12 Hequ H8.
             rewrite <- isEmpty_in' in H12.
             destruct H12 as [? [? ?]].
             apply fold_min in H.
             remember (fold_right Z.min (hd 0 priq_contents) priq_contents).
             subst u. intro.
             rewrite Znth_find in H1. omega.
             subst z.
             rewrite <- Znth_0_hd by (unfold SIZE in *; omega).
             apply min_in_list; [ apply incl_refl | apply Znth_In; unfold SIZE in *; omega].
           }
           (* math stuff *)
           unfold dijkstra_correct. intros. 
           destruct (Z.eq_dec dst u).
           (* ie, are you the new entrant or an old-timer? *) 
 ++ (* the new entrant *)  
   subst dst; split3; intros. 
    ** (* there is actually work to do here:
          u is not in popped, 
          but dst is in the new popped. 
          so we're deadling with exactly the new entrant. 
          we must show that it is worthy. *)
       (* Solution: find the path to mom, u's prev.
          the path we need is p2mom +:: mom2u *)
       assert (Znth u priq_contents < inf). {
         assert (Znth u priq_contents <> inf). {
           intro.
           rewrite <- isEmpty_in' in H12.
           destruct H12 as [? [? ?]].
           pose proof (fold_min _ _ H12).
           rewrite Hequ in H28.
           rewrite Znth_find in H28. omega.
           unfold VType in *.   
           rewrite <- Znth_0_hd by omega.
           apply min_in_list; [apply incl_refl | apply Znth_In; omega].
           }
         pose proof (Forall_Znth _ _ _ H13 H7).
         Opaque inf.
         simpl in H29.
         Transparent inf.
         rep_omega.
       }
       unfold dijkstra_correct in H4.
       destruct (H4 u) as [_ [? _]].   
       specialize (H29 H13 H28).  
       destruct H29 as [p2mom [? [? [? [? ?]]]]].
       unfold VType in *.
       remember (Znth u prev_contents) as mom.
       assert (In mom (get_popped priq_contents)). {
       assert (In src (get_popped priq_contents))
          (* add to invariant? *)
           by admit.
       apply (path_end_in_popped _ _ _ _ _ _ _ H2 H34 H29 H31). }
       exists (fst p2mom, snd p2mom +:: (mom, u)).
       split3; trivial.
       --- unfold path_globally_optimal; intros.
    (* this alternate path either went through
       the subgraph to some mom' + one step, or not. *)
    (* if yes, then we can use H33 *)
    (* if no, then it loses by default because
       the cost to go to mom' > cost to u anyway! *) 
           admit.
       (* why is this path _globally_ optimal? *)
       --- rewrite Forall_forall; intros.
           rewrite Forall_forall in H31.
           simpl in H35. apply in_app_or in H35.
           destruct H35. 
           +++ specialize (H31 _ H35).
               destruct H31. 
               pose proof (get_popped_range _ _ H31). 
               pose proof (get_popped_range _ _ H36).
               split; rewrite <- get_popped_irrel_upd;
                 trivial; intro; apply H11.
               *** rewrite H39 in H31, H37.
                   apply get_popped_meaning; trivial.
               *** rewrite H39 in H36, H38.
                   apply get_popped_meaning; trivial.
           +++ simpl in H35. destruct H35; [|omega].
               rewrite surjective_pairing in H35.
               inversion H35.
               unfold VType in *.
               rewrite <- H37, <- H38. split.
               *** apply get_popped_irrel_upd; trivial.
                   apply get_popped_range; trivial.
                   intro. apply H11. rewrite H36 in *.
                   apply get_popped_meaning; trivial.
               *** rewrite get_popped_meaning.
                   rewrite upd_Znth_same; trivial.
                   rewrite upd_Znth_Zlength; trivial.
    ** exfalso.
       rewrite upd_Znth_same in H28. omega.
       rewrite upd_Znth_Zlength in H27; trivial.
    ** rewrite upd_Znth_same in H28. omega.
       rewrite upd_Znth_Zlength in H27; trivial.
 ++ (* now prove the whole thing for a dst that's not u.
       ie, we're talking about an old-timer.
       This old-timer could have been in subgraph or
       in fringe, so we'll have to deal with both cases *)
   split3; intros.  
   ** (* dst is in subgraph. 
         show that adding u didn't mess anything up *)
     assert (0 <= dst < Zlength priq_contents).
       { apply get_popped_range in H27.
         rewrite upd_Znth_Zlength in H27; trivial. }
       apply get_popped_irrel_upd in H27; try assumption.
       unfold dijkstra_correct in H4.
       destruct (H4 dst) as [? _]. 
       destruct (H29 H27) as [p2dst [? [? ?]]].
       exists p2dst.
       split3; trivial.
       rewrite Forall_forall; intros.
       rewrite Forall_forall in H32.
       specialize (H32 _ H33).
       destruct H32. 
       pose proof (get_popped_range _ _ H32). 
       pose proof (get_popped_range _ _ H34).
       split; rewrite <- get_popped_irrel_upd;
         trivial; intro; apply H11.
       (* Both these cases are impossible for 
          an interesting reason:
          - x is in p2dst, a legal path.
          - so snd x and fst x are in get_popped
          - but u is not in get_popped. *)
       --- rewrite H37 in H32, H35.
           apply get_popped_meaning; trivial.
       --- rewrite H37 in H34, H36.
           apply get_popped_meaning; trivial.
   ** (* dst is in fringe. show that moving 
         u from the fringe to the subgraph won't
         screw anything up *)
     (* the main point is that it's possible to reach
        dst via some subgraph-internal path + one hop.
        plan: use the same path as before this tweak. *)
     rewrite upd_Znth_Zlength in H27 by trivial.
     rewrite upd_Znth_diff in H28 by trivial.
     unfold dijkstra_correct in H4.
     destruct (H4 dst) as [_ [? _]].
     specialize (H29 H27 H28).
     destruct H29 as [p2mom [? [? [? [? ?]]]]]. 
     exists p2mom. 
     remember (Znth dst prev_contents) as mom.
     unfold VType in *. rewrite <- Heqmom in *.
     split3; [| | split3]; trivial. 
     --- assert (In mom (get_popped priq_contents)). {
           assert (In src (get_popped priq_contents)).
           admit.
         apply (path_end_in_popped _ _ _ _ _ _ _ H2 H34 H29 H31). }
         assert (mom <> u). { 
           intro. apply H11. rewrite <- H35.
           apply get_popped_meaning;
             [apply get_popped_range|]; trivial. }
         rewrite Forall_forall; intros.
         rewrite Forall_forall in H31. 
         destruct (H31 _ H36).
         pose proof (get_popped_range _ _ H37).
         pose proof (get_popped_range _ _ H38).
         split; apply get_popped_irrel_upd;
           trivial; intro; apply H11.
         +++ rewrite H41 in H37, H39.
             apply get_popped_meaning; trivial.
         +++ rewrite H41 in H38, H40.
             apply get_popped_meaning; trivial.
     --- intros.        
         apply H33; trivial.
         rewrite Forall_forall; intros.
         rewrite Forall_forall in H36. 
         destruct (H36 _ H37).
         pose proof (get_popped_range _ _ H39).
         pose proof (get_popped_range _ _ H38).
         rewrite upd_Znth_Zlength in H41, H40; trivial.
         apply get_popped_irrel_upd in H39; trivial.
         apply get_popped_irrel_upd in H38; trivial.
         split; trivial.
         (* well this makes sense --
            u is now gone from the fringe, 
            so if there was a path link on the way to 
            dst that passed through u, then...?

            good news: the path could not have
            passed through u, since u was not in 
            the subgraph! gonna be fine...

          *)
         admit. admit. (* not sure... *)
(*

       --- unfold dijkstra_correct in H4.
           destruct (H4 dst) as [_ ?].
           specialize (H32 H27 H28 H29).
           destruct H32 as [? [p2mom [? [? ?]]]].
           unfold VType in *.
           rewrite <- Heqmom in *.
           exists p2mom; split3; trivial.
           intros.  
           assert (mom' <> u). { 
             intro. 
             subst mom'.
             (* use mom' in H4 to get that
                u must be in get_popped
                and therefore H11 will fail *)
              
}


             rewrite H38 in H36.
             apply get_popped_meaning in H36; trivial.
             

             apply H11. rewrite <- H38.
             pose proof (get_popped_range _ _ H36).
             apply get_popped_meaning in H36; trivial.
             
             
             
             
           specialize (H35 _ _ H3


           
           +++ unfold path_correct in *.
               destruct H32 as [? [? [? ?]]]. 
               split3; [| | split]. 
               *** apply valid_path_app_cons; trivial;
                     [| destruct H36 | omega];
                     rewrite <- surjective_pairing; trivial.
               *** destruct p2mom; simpl.
                   replace src with v in *.
                   apply path_ends_app_cons; trivial.
                   destruct H36 as [? _].
                   simpl in H36. rewrite H36. trivial.
               *** destruct (H4 dst) as [_ ?].
                   specialize (H39 H27 H28 H29). 
                   destruct H39 as [? [? [? [? ?]]]].

                 rewrite H8 in H28.
                   rewrite <- path_cost_app_cons; trivial.
                   *)
          
           (* hm so here I specialized for mom.
              but maybe I should have specialized for dst *)
           (*
           destruct (H4 mom) as [? _]. 
           specialize (H32 H30). 
           destruct H32 as [p2mom [? [? [? ?]]]].
           exists p2mom; split3; trivial.
           +++ unfold path_correct in *.
               destruct H32 as [? [? [? ?]]]. 
               split3; [| | split]. 
               *** apply valid_path_app_cons; trivial;
                     [| destruct H36 | omega];
                     rewrite <- surjective_pairing; trivial.
               *** destruct p2mom; simpl.
                   replace src with v in *.
                   apply path_ends_app_cons; trivial.
                   destruct H36 as [? _].
                   simpl in H36. rewrite H36. trivial.
               *** destruct (H4 dst) as [_ ?].
                   specialize (H39 H27 H28 H29). 
                   destruct H39 as [? [? [? [? ?]]]].

                 rewrite H8 in H28.
                   rewrite <- path_cost_app_cons; trivial.
                   *) 
                (* work to do. 
                    I don't quite understand right now. *)
               (*  it. *)
                 (* REMNANTS: *)
(*        apply H28.
        apply (get_popped_irrel_upd _ _ u (inf + 1)).
        1: apply get_popped_range in H27;
          rewrite upd_Znth_Zlength in H27.
        all: try omega; assumption.*)

  (* ++ there is one new guy in get_popped: u *)
          (* subst dst. 
              remember (Znth u prev_contents) as mom.
              assert (In mom (get_popped priq_contents)).
              mit.
              (* should be okay...
                 if mom were not in get_popped,
                 then the cost to go to mom
                 would exceed the cost to go to me
                 (by minimality of find_min)
                 and then from mom to me would be > 0 *)
              
              unfold dijkstra_correct in H4.
              pose proof (H4 _ H28).
              destruct H29 as [p2mom [? ?]].
              exists (fst p2mom, snd p2mom +:: (mom, u)).
              split. 
              ** unfold path_is_optimal.
                 unfold path_is_optimal in H29. 
                 destruct H29 as [? [? [? ?]]]. 
                 split3; [ | |split].
                 mit.
                 (* all easy. see example below *)
                 (* let's consider the interesting case: *)
                 --- intros.
                     rewrite path_cost_app_cons.
                     rewrite elabel_Znth_graph_to_mat.
                     simpl.
                     unfold path_is_optimal in H4.
                     rewrite <- H30.

                     clear -H4 H34 H35.
 (* p' has an alternate mom' 
    - if mom' is not in subgraph, dead. 
    because cost to go to mom' >= cost to go to me. and then    
    from mom' to me is > 0.
    - if mom' is in subgraph...
    ADD THIS TO DIJK_CORRECT?

           *)        *)
   ** destruct (H4 dst) as [_ [_ ?]].
      apply H32; trivial.
      2: rewrite upd_Znth_diff in H28; trivial. 
      3: rewrite <- get_popped_irrel_upd in H29; trivial.
      1,2: rewrite upd_Znth_Zlength in H27; trivial.
      apply get_popped_range in H29.
      rewrite upd_Znth_Zlength in H29; trivial.      
      admit. (* not sure... *)
      rewrite Forall_forall; intros.
      rewrite Forall_forall in H31.
      destruct (H31 _ H33).
      rewrite <- get_popped_irrel_upd in H34; try omega.
      rewrite <- get_popped_irrel_upd in H35; try omega.
      split; trivial.
      apply get_popped_range in H35. rewrite upd_Znth_Zlength in H35; trivial.
      2: apply get_popped_range in H34; rewrite upd_Znth_Zlength in H34; trivial.
      admit. admit. (* not sure. similar to earlier.
                       how to show that it could not 
                       have gone through u? *)
     (* dst was unseen. show that moving u from 
         fringe to subgraph won't change anything *)
        (* new goo from adding third case. inverstigate asap *)
        -- assert (0 <= u < Zlength (graph_to_mat g)). {
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
             destruct H26 as [? [? [? [? ?]]]].
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
           assert (0 <= cost <= Int.max_signed / SIZE) by
               (rewrite Heqcost; apply H1; omega). 
           forward_if.
           ++ assert (0 <= Znth u dist_contents' <= inf). {
                assert (0 <= u < Zlength dist_contents') by omega.
                apply (Forall_Znth _ _ _ H30) in H22.
                assumption. 
              } 
              assert (0 <= Znth i dist_contents' <= inf). {
                assert (0 <= i < Zlength dist_contents') by omega.
                apply (Forall_Znth _ _ _ H31) in H22.
                assumption. 
              }               
              assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
                split; [omega|].
                unfold inf in *. rep_omega.
                }
              forward. forward. forward_if.
  ** rewrite Int.signed_repr in H33
      by (unfold inf in *; rep_omega).
     assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
         (repeat rewrite Zlength_map; omega).
     assert (Znth i priq_contents' <> inf + 1). {
       intro. apply Zlt_not_le in H33. apply H33.
       rewrite <- get_popped_meaning in H35 by omega.
       rewrite H8 in H13.  
       rewrite Heqcost.
       apply (cant_improve_further _ _ src _ priq_contents' prev_contents'); assumption.
     }
     forward. forward. forward.
     forward; rewrite upd_Znth_same; trivial.
     1: entailer!.
     forward.
     Exists (upd_Znth i prev_contents' u).
     Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
     Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)).
     repeat rewrite <- upd_Znth_map; entailer!. 
     split3; [| |split].
     --- remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
         assert (u <> i) by (intro; subst; omega).
         apply get_popped_irrel_upd; try omega; assumption.
     --- intros.
         unfold cost_was_improved_if_possible. intros.
         remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
         assert (0 <= dst < i \/ dst = i) by omega.
         unfold cost_was_improved_if_possible in H19.
         destruct H49; [assert (dst <> i) by omega|]; destruct (Z.eq_dec u i).
         +++ rewrite <- e, upd_Znth_same, upd_Znth_diff; try rep_omega.
             rewrite (H3 u) by trivial.
             rewrite Z.add_0_r. apply H18; trivial.
         +++ repeat rewrite upd_Znth_diff; try rep_omega.
             apply H18; trivial.
         +++ rewrite H49, <- e.
             repeat rewrite upd_Znth_same.
             rewrite (H3 u) by trivial.
             omega. rep_omega.
         +++ rewrite H49, upd_Znth_same, upd_Znth_diff; [reflexivity | rep_omega..].
     ---  (* Important Spot #2: 
            We just "saw" a better way to get to i: via u.
            The three arrays have all changed in response.
          *)
       remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
       intro.
       (* plan: 
           if dst is i
            if dst is in subgraph -- impossible!
            else if in fringe -- show all is well, 
                 using {path to u +:: (u,i)}.
           else if dst <> i
            if dst is in subgraph -- completely unaffected
            else if dst is a different fringe item -- 
                                     completely unaffected *)
       destruct (Z.eq_dec dst i). 
       (* the interesting case is when dst = i *)
       +++ subst dst; split3.  
           *** intros.
               (* we can't be here -- 
                  i was not popped before, 
                  and the changes we just made 
                  do not constitute a pop *)
               exfalso.
               rewrite get_popped_meaning in H11.
               2: rewrite upd_Znth_Zlength; omega.
               rewrite upd_Znth_same in H11 by omega.
               rewrite H11 in H33.
               repeat rewrite Zlength_map in H34.
               pose proof (Forall_Znth _ _ i H34 H22).
               simpl in H48. omega.
           *** intros.    
               (* "mom" is just u
                  we're going to pass it 
                  the path to u and show that
                  nothing got screwed up
                *)
               unfold VType in *.
               subst mom. rewrite upd_Znth_same by omega.
               destruct (H19 u) as [? _]. 
               specialize (H49 H17).               
               destruct H49 as [p2u [? [? ?]]].
               exists p2u.  
               split3; [| | split3]; trivial.    
 ---- unfold path_correct in *.
      destruct H49 as [? [? [? [? ?]]]].
      split3; [| | split3]; trivial.
      ++++ rewrite upd_Znth_diff; try omega.
           intro. apply H35. subst i.
           apply get_popped_meaning; omega.
      ++++ unfold VType in *.
           rewrite Forall_forall. intros.
           rewrite Forall_forall in H55, H51.
           specialize (H55 _ H56).
           specialize (H51 _ H56); destruct H51.
           pose proof (get_popped_range _ _ H57).
           rewrite upd_Znth_diff; try omega.
           intro. apply H35.
           rewrite H59 in H57, H58.
           apply get_popped_meaning; trivial.
 ---- unfold VType in *.
      rewrite Forall_forall; intros.
      rewrite Forall_forall in H51. specialize (H51 _ H52).
      destruct H51.
      pose proof (get_popped_range _ _ H51).
      pose proof (get_popped_range _ _ H53).
      split; apply get_popped_irrel_upd; trivial; try omega; intro; apply H35.
      rewrite H56 in H51, H54.
      apply get_popped_meaning; trivial.
      rewrite H56 in H53, H55.
      apply get_popped_meaning; trivial.
 ---- unfold VType in *.
      unfold path_correct in *.
      destruct H49 as [? [? [? [? ?]]]].
      split3; [ | | split3].
      ++++ destruct H52.
           apply valid_path_app_cons; trivial;
             rewrite <- surjective_pairing; trivial.
      ++++ rewrite (surjective_pairing p2u) in *.
           simpl.
           replace (fst p2u) with src in *.
           apply path_ends_app_cons; trivial.
           destruct H52. simpl in H52; omega.
      ++++ rewrite <- path_cost_app_cons; trivial.
           rewrite <- H54.
           omega.
      ++++ rewrite <- path_cost_app_cons; trivial.
           rewrite upd_Znth_same by omega.
           rewrite <- H54. omega.
      ++++ unfold VType in *.
           rewrite Forall_forall. intros.
           rewrite Forall_forall in H55, H51.
           apply in_app_or in H56. destruct H56.
           **** specialize (H55 _ H56).
                specialize (H51 _ H56).
                destruct H51.
                pose proof (get_popped_range _ _ H57).
                rewrite upd_Znth_diff; try omega.
                intro. apply H35.
                rewrite H59 in H57, H58.
                apply get_popped_meaning; trivial.
           **** simpl in H56. destruct H56; [| omega].
                rewrite (surjective_pairing x) in *.
                simpl. inversion H56.
                rewrite upd_Znth_same; trivial.
                omega.
 ---- intros.
      assert (In mom' (get_popped priq_contents')) by admit.
      (* potentially bad... *)
      unfold VType in *.  
      destruct H49 as [? [? [? [? ?]]]].
      destruct H52 as [? [? [? [? ?]]]]. 
      rewrite <- path_cost_app_cons; trivial; try omega.
      rewrite <- H58.
      apply (Z.le_trans _ (Znth i dist_contents') _).
      1: omega.
      destruct (Z.eq_dec (Znth i priq_contents') inf).
      ++++ destruct (H19 i) as [_ [_ ?]].  
           assert (0 <= i < Zlength priq_contents') by 
             omega.  
           specialize (H64 H65 e).
           rewrite H64; trivial; try omega.
           split3; [| | split3]; trivial.
           rewrite <- H62.
           rewrite upd_Znth_diff; trivial; try omega.
           replace (Zlength dist_contents') with (Zlength priq_contents') by omega. 
           apply get_popped_range; trivial.
           intro.
           apply H35. rewrite <- H66. 
           apply get_popped_meaning; trivial.
           apply get_popped_range; trivial.
           rewrite Forall_forall; intros. 
           rewrite Forall_forall in H63, H54. 
           specialize (H63 _ H66). rewrite <- H63.
           specialize (H54 _ H66). destruct H54.
           unfold VType in *.
           rewrite upd_Znth_diff; trivial; try omega.
           pose proof (get_popped_range _ _ H67).
           rewrite upd_Znth_Zlength in H68. omega.
           omega.
           pose proof (get_popped_range _ _ H67).
           intro. rewrite get_popped_meaning in H67.
           rewrite H69 in H67.
           rewrite upd_Znth_same in H67.
           omega. trivial. omega.
           rewrite Forall_forall; intros.
           rewrite Forall_forall in H54.
           specialize (H54 _ H66); destruct H54.
           rewrite <- get_popped_irrel_upd in H54, H67;
             trivial; try omega.
           split; trivial.
           apply get_popped_range in H67.
           rewrite upd_Znth_Zlength in H67; trivial.
           2: apply get_popped_range in H54;
               rewrite upd_Znth_Zlength in H54; trivial.
           intro. rewrite H68 in H67.
           rewrite get_popped_meaning in H67.
           rewrite upd_Znth_same in H67; omega.
           omega.
           intro. rewrite H68 in H54.
           rewrite get_popped_meaning in H54.
           rewrite upd_Znth_same in H54; omega.
           omega.
      ++++ destruct (H19 i) as [_ [? _]].
           assert (0 <= i < Zlength priq_contents') by omega. 
           assert (Znth i priq_contents' < inf). { 
             pose proof (Forall_Znth _ _ _ H65 H21).
             Opaque inf. simpl in H66. omega. }
           specialize (H64 H65 H66).
           destruct H64 as [? [? [? [? [? ?]]]]].
           destruct H69 as [? [? [? [? ?]]]].
           rewrite H73.
           apply H70; trivial.
           split3; [| | split3]; trivial.
           **** rewrite <- H62. rewrite upd_Znth_diff; try omega.
                replace (Zlength dist_contents') with (Zlength priq_contents') by omega.  
                apply get_popped_range; trivial.
                intro.
                apply H35. rewrite <- H75.
                apply get_popped_meaning; trivial.
                apply get_popped_range; trivial. 
           **** rewrite Forall_forall; intros.
                rewrite Forall_forall in H63. 
                pose proof (H63 _ H75). rewrite <- H76.
                rewrite Forall_forall in H54.
                destruct (H54 _ H75). 
                pose proof (get_popped_range _ _ H78).
                rewrite upd_Znth_Zlength in H79; trivial.
                unfold VType in *.
                rewrite upd_Znth_diff; trivial; try omega.
                intro. rewrite H80 in H78. rewrite get_popped_meaning in H78.
                rewrite upd_Znth_same in H78.
                omega. trivial. rewrite upd_Znth_Zlength.
                assumption.
                assumption.
           **** rewrite Forall_forall; intros.
                rewrite Forall_forall in H63. 
                pose proof (H63 _ H75).
                rewrite Forall_forall in H54.
                destruct (H54 _ H75). 
                pose proof (get_popped_range _ _ H77).
                pose proof (get_popped_range _ _ H78).
                rewrite upd_Znth_Zlength in H79, H80; trivial.
                unfold VType in *.
                rewrite <- get_popped_irrel_upd in H77; try omega.
                rewrite <- get_popped_irrel_upd in H78; try omega.
                split; trivial.
                ----- intro.
                rewrite H81 in H78.
                rewrite get_popped_meaning in H78 by omega.
                rewrite upd_Znth_same in H78 by omega.
                omega.
                ----- intro.
                rewrite H81 in H77.
                rewrite get_popped_meaning in H77 by omega.
                rewrite upd_Znth_same in H77 by omega.
                omega.
           *** intros. rewrite upd_Znth_same in H48.
               destruct (H19 i) as [_ [_ ?]].
               apply H52; trivial; try omega.
               repeat rewrite upd_Znth_Zlength in H34.
               unfold VType in *.
               omega.
       +++ (* the "easier" case: dst <> i *) 
         split3; intros.     
         *** (* when dst was in the subgraph *)
           assert (0 <= dst < Zlength priq_contents). {
             apply get_popped_range in H11.
             rewrite upd_Znth_Zlength in H11; omega. }
           rewrite <- get_popped_irrel_upd in H11 by omega.
           destruct (H19 dst) as [? _].
           destruct (H49 H11) as [p2dst [? [? ?]]].
           exists p2dst. split3; trivial.   
 ---- destruct H50 as [? [? [? [? ?]]]].
      split3; [| | split3]; trivial.
      ++++ rewrite upd_Znth_diff; trivial; omega.
      ++++ unfold VType in *.
           rewrite Forall_forall; intros.
           rewrite Forall_forall in H56, H52. 
           specialize (H56 _ H57).
           specialize (H52 _ H57); destruct H52.
           pose proof (get_popped_range _ _ H58).
           rewrite upd_Znth_diff; trivial; try omega.
           intro. apply H35.
           rewrite H60 in H58, H59.
           apply get_popped_meaning; trivial.
 ---- unfold VType in *.
      rewrite Forall_forall; intros.
      rewrite Forall_forall in H52.
      specialize (H52 _ H53); destruct H52.
      pose proof (get_popped_range _ _ H52).
      pose proof (get_popped_range _ _ H54).
      split; apply get_popped_irrel_upd; trivial;
        try omega; intro; apply H35.
      rewrite H57 in H52, H55.
      apply get_popped_meaning; trivial.
      rewrite H57 in H54, H56.
      apply get_popped_meaning; trivial.
         *** (* when dst was in the fringe *)
           unfold VType in *.
           subst mom;
             remember (Znth dst (upd_Znth i prev_contents' u)) as mom.
           rewrite upd_Znth_Zlength in H11.
           rewrite upd_Znth_diff in Heqmom, H48; try omega.
           2: rewrite H24; trivial.
           destruct (H19 dst) as [_ [? _]].
           specialize (H49 H11 H48). unfold VType in *.
           destruct H49 as [p2mom [? [? [? [? ?]]]]].
           rewrite <- Heqmom in *. 
           assert (In mom (get_popped priq_contents')). {
             assert (In src (get_popped priq_contents')) by admit.
             apply (path_end_in_popped _ _ _ _ _ _ _ H2 H54 H49 H51). }
           exists p2mom; split3; [| | split3]; trivial.   
 ---- unfold path_correct in *.
      destruct H49 as [? [? [? [? ?]]]].
      split3; [| | split3]; trivial.
      ++++ pose proof (get_popped_range _ _ H54).
           rewrite upd_Znth_diff; trivial; try omega.
           intro. apply H35. rewrite H60 in H54, H59.
           apply get_popped_meaning; trivial.
      ++++ unfold VType in *.
           rewrite Forall_forall; intros.
           rewrite Forall_forall in H58, H51.
           specialize (H58 _ H59).
           specialize (H51 _ H59). destruct H51.
           pose proof (get_popped_range _ _ H60).
           rewrite upd_Znth_diff; trivial; try omega.
           intro.
           apply H35.
           rewrite H62 in H61, H60.
           apply get_popped_meaning; trivial.
 ---- rewrite Forall_forall; intros.
      rewrite Forall_forall in H51. 
      specialize (H51 _ H55). destruct H51.
      pose proof (get_popped_range _ _ H51).
      pose proof (get_popped_range _ _ H56).
      split; apply get_popped_irrel_upd; trivial;
        try omega; intro; apply H35.
      rewrite H59 in H57, H51.
      apply get_popped_meaning; trivial.
      rewrite H59 in H58, H56.
      apply get_popped_meaning; trivial.
 ---- unfold path_correct.
      unfold path_correct in H52.
      destruct H52 as [? [? [? [? ?]]]].
      split3; [ | | split3]; trivial.
      ++++ rewrite upd_Znth_diff; trivial; try omega.
      ++++ unfold VType in *.
           rewrite Forall_forall; intros.
           rewrite Forall_forall in H58, H51.
           simpl in H58, H59.
           rewrite upd_Znth_diff; trivial; try omega.
           apply H58; trivial.
           apply in_app_or in H59. destruct H59. 
           **** destruct (H51 _ H59) as [_ ?].
                apply get_popped_range in H60.
                omega.
           **** simpl in H59. destruct H59; [|omega].
                rewrite (surjective_pairing x) in *.
                simpl. inversion H59.
                omega.
           **** intro. apply in_app_or in H59.
                destruct H59.
                ----- destruct (H51 _ H59) as [_ ?].
                rewrite H60 in H61.
                apply H35.
                pose proof (get_popped_range _ _ H61).
                apply get_popped_meaning; trivial.
                ----- simpl in H59. destruct H59; [|omega].
                rewrite (surjective_pairing x) in *.
                inversion H59. simpl in H60. omega.
 ---- intros.
      (* path cost of (p2mom + mom2me) <=
              cost of (p2mom' + mom'2me)
       *)
      admit.      
      (* show that they're a pair. *)
      (* then see how much of the below can be used *)
      (*
      rewrite elabel_Znth_graph_to_mat; simpl.
      rewrite <- H55. mit. (* unclear *)
      assumption.
      unfold edge_valid in H60;
        unfold vertex_valid in H2;
        rewrite H60, H2; simpl; split; mit. (* easy ranges *)
      rewrite elabel_Znth_graph_to_mat; simpl.
      unfold DijkstraArrayGraph.inf.
      intro.
      clear -H1 H63. mit. (* gonna be okay *)
      assumption.
      unfold edge_valid in H60;
        unfold vertex_valid in H2;
        rewrite H60, H2; simpl; split; mit. (* easy ranges *)
      assumption. *)
         *** rewrite upd_Znth_Zlength in H11. 
           destruct (H19 dst) as [_ [_ ?]]. 
             apply H52; trivial; try omega.
             rewrite upd_Znth_diff in H48; trivial.
             2: rewrite <- get_popped_irrel_upd in H49; trivial.
             2: apply get_popped_range in H49;
                  rewrite upd_Znth_Zlength in H49; trivial.
             4: intro; rewrite H53 in H49;
               rewrite get_popped_meaning in H49.
             4: rewrite upd_Znth_same in H49; omega.
             4: rewrite upd_Znth_Zlength.
             all: unfold VType in *; try omega.
             clear H52; unfold path_correct in *.
             destruct H50 as [? [? [? [? ?]]]].
             split3; [| | split3]; trivial; try omega. 
             ---- rewrite <- H54.
                  rewrite upd_Znth_diff; trivial; try omega.
                  apply get_popped_range in H49.
                  rewrite upd_Znth_Zlength in H49; omega.
                  intro. rewrite H56 in H49.
                  rewrite get_popped_meaning in H49.
                  rewrite upd_Znth_same in H49. omega.
                  omega. rewrite upd_Znth_Zlength.
                  unfold VType in *. omega. omega.
             ---- rewrite Forall_forall; intros. 
                  rewrite Forall_forall in H55.
                  rewrite <- H55; trivial.
                  rewrite Forall_forall in H51.
                  specialize (H51 _ H56); destruct H51.
                  unfold VType in *. 
                  rewrite upd_Znth_diff; trivial.
                  apply get_popped_range in H57.
                  rewrite upd_Znth_Zlength in H57; try omega.
                  omega.
                  intro. rewrite H58 in H57.
                  rewrite get_popped_meaning in H57.
                  rewrite upd_Znth_same in H57. omega.
                  omega.
                  apply get_popped_range; trivial.
             ---- rewrite Forall_forall; intros.
                  rewrite Forall_forall in H51.
                  destruct (H51 _ H53).
                  rewrite <- get_popped_irrel_upd in H54, H55; trivial; try omega.
                  split; trivial.
                  apply get_popped_range in H55.
                  rewrite upd_Znth_Zlength in H55; omega.
                  2: apply get_popped_range in H54;
                    rewrite upd_Znth_Zlength in H54; omega.
                  intro. rewrite H56 in H55.
                  rewrite get_popped_meaning in H55.
                  rewrite upd_Znth_same in H55; omega.
                  apply get_popped_range; trivial.
                  intro. rewrite H56 in H54.
                  rewrite get_popped_meaning in H54.
                  rewrite upd_Znth_same in H54; omega.
                  apply get_popped_range; trivial.
     --- repeat rewrite Zlength_map in H34.
         split3; apply inrange_upd_Znth;
           trivial; try omega.
  ** rewrite Int.signed_repr in H33.
     2: { assert (0 <= i < Zlength dist_contents') by omega.
          apply (Forall_Znth _ _ _ H34) in H22.
          simpl in H22.
          Transparent inf.
          unfold inf in H22.
          rep_omega. }
     forward.
     Exists prev_contents' priq_contents' dist_contents'.
     entailer!.
     unfold cost_was_improved_if_possible in *. intros.
     assert (0 <= dst < i \/ dst = i) by omega.
     remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
     destruct H47; [apply H18; trivial|].
     subst dst. omega.
           ++ (* ...prove the for loop's invariant holds *)
             forward.
             Exists prev_contents' priq_contents' dist_contents'.
             entailer!. unfold cost_was_improved_if_possible in *. intros.
             assert (0 <= dst < i \/ dst = i) by omega.
             destruct H43; [apply H18; trivial|].
             subst dst. exfalso. unfold inf in H42.
             replace 8 with SIZE in H29 by (unfold SIZE; rep_omega).
             rewrite inf_eq2 in H29.
             do 2 rewrite Int.signed_repr in H29. 
             unfold inf in H29. rep_omega.
             compute; split; inversion 1.
             all: rep_omega.
        -- (* from the for loop's inv, prove the while loop's inv *)
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!. 
      * (* after breaking, prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H12 in H11; simpl in H11; now inversion H11.
        }
        clear H11.
        forward. Exists prev_contents priq_contents dist_contents.
        entailer!. apply (isEmptyMeansInf _ H12).
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents.
      forward. Exists prev_contents dist_contents priq_contents. entailer!. 
Abort.