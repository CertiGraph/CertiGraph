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
Require Import RamifyCoq.msl_application.DijkstraGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Definition inf := Int.max_signed - 1.

Lemma inf_eq: 2147483647 - 1 = inf.
Proof. unfold inf. rep_omega. Qed.

(* Ranges for different arrays *)
Definition inrange_prev prev_contents :=
  Forall (fun x => 0 <= x <= SIZE-1 \/ x = inf) prev_contents.

Definition inrange_priq priq_contents :=
  Forall (fun x => 0 <= x <= inf+1) priq_contents.

Definition inrange_dist dist_contents :=
  Forall (fun x => 0 <= x <= inf - (inf / SIZE)
                                     \/ x = inf) dist_contents. 

Definition inrange_graph grph_contents :=
  Forall (fun list => Forall (fun cost => 0 <= cost <= inf / SIZE) list) grph_contents.
  
Lemma inrange_priq_zoom_in:
  forall priq_contents i,
    0 <= i < Zlength priq_contents ->
    inrange_priq priq_contents ->
    0 <= Znth i priq_contents <= Int.max_signed.
Proof.
  intros. unfold inrange_priq in H0. rewrite Forall_forall in H0.
  pose proof (Znth_In i priq_contents H).
  specialize (H0 (Znth i priq_contents) H1).
  unfold inf in H0. omega.
Qed.

Lemma inrange_dist_zoom_in:
  forall dist_contents i,
    0 <= i < Zlength dist_contents ->
    inrange_dist dist_contents ->
    (0 <= Znth i dist_contents <= inf - inf/SIZE
     \/ Znth i dist_contents = inf).
Proof.
  intros. unfold inrange_dist in H0. rewrite Forall_forall in H0.
  pose proof (Znth_In i dist_contents H).
  specialize (H0 (Znth i dist_contents) H1).
  destruct H0; omega.
Qed.

Lemma inrange_priq_sublist:
  forall priq_contents i,
    0 <= i < Zlength priq_contents ->
    inrange_priq priq_contents ->
    inrange_priq (sublist 0 i priq_contents).
Proof.
  intros. unfold inrange_priq in *.
  apply Forall_sublist; trivial.
Qed.
  
Lemma signed_repr_same_priq: forall priq_contents i,
    0 <= i < Zlength priq_contents ->
    inrange_priq priq_contents ->
    Int.signed (Int.repr (Znth i priq_contents)) =
    Znth i priq_contents.
Proof.
  intros. rewrite Int.signed_repr; trivial.
  apply (inrange_priq_zoom_in _ i) in H0; trivial.
  rep_omega.
Qed.

Lemma signed_repr_same_dist: forall dist_contents i,
    0 <= i < Zlength dist_contents ->
    inrange_dist dist_contents ->
    Int.signed (Int.repr (Znth i dist_contents)) =
    Znth i dist_contents.
Proof.
  intros. rewrite Int.signed_repr; trivial.
  apply (inrange_dist_zoom_in _ i) in H0; trivial.
  simpl in *. destruct H0; [|unfold inf in *]; rep_omega. 
Qed.

Lemma inrange_upd_Znth_dist: forall l i new,
    0 <= i < Zlength l ->
    inrange_dist l ->
    (0 <= new <= inf - inf/SIZE \/ new = inf) ->
    inrange_dist (upd_Znth i l new).
Proof.
  intros. unfold inrange_dist in *.
  rewrite Forall_forall in *. intros.
  destruct (eq_dec x new). 1: omega.
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2.
    1: exfalso; omega.
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Lemma inrange_upd_Znth_prev: forall l i new,
    0 <= i < Zlength l ->
    inrange_prev l ->
    (0 <= new <= SIZE - 1 \/ new = inf) ->
    inrange_prev (upd_Znth i l new).
Proof.
  intros. unfold inrange_prev in *.
  rewrite Forall_forall in *. intros.
  destruct (eq_dec x new). 1: omega.
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2.
    1: exfalso; omega.
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Lemma inrange_upd_Znth_priq: forall l i new,
    0 <= i < Zlength l ->
    inrange_priq l ->
    (0 <= new <= inf+1) ->
    inrange_priq (upd_Znth i l new).
Proof.
  intros. unfold inrange_priq in *.
  rewrite Forall_forall in *. intros.
  destruct (eq_dec x new). 1: omega.
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2.
    1: exfalso; omega.
    apply sublist_In in H2. apply (H0 x H2).
Qed.


(* 
 * If it's a valid situation, it will return the 
 * path.
 * If not, it will return an empty list.
 *)
Fixpoint create_path_inner (src dst : VType) (prev : list VType) (ans : list VType) (n : nat) : list VType :=
  match n with
  | O => []
  | S n' => if Z_le_gt_dec dst SIZE
            then if Z.eq_dec src dst
                 then src :: ans
                 else create_path_inner src (Znth dst prev) prev (dst :: ans) n'
            else []
  end.

Definition create_path src dst prev :=
  create_path_inner src dst prev [] (Z.to_nat (Zlength prev)).

Compute (create_path 0 3 [0; 0; 1; inf]).

(* can probably collapse these two together *)
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
    0 <= find l target ans < Zlength l + ans.
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
  forall list,
    Zlength list > 0 ->
    Znth 0 list = hd 0 list.
Proof.
  intros. induction list; inversion H.
  rewrite Znth_0_cons. trivial.
Qed.

Lemma min_picks_first:
  forall num mono start,
    start <= mono ->
    fold_right Z.min start (list_repeat num mono) = start.
Proof.
  intros.
  induction num; trivial.
  simpl. rewrite IHnum. rewrite Z.min_r; omega.
Qed.
  
Lemma find_src: forall src,
    0 <= src < Zlength (list_repeat (Z.to_nat 8) inf) ->
    find (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0)
               (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0))
                           (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0)) 0 = src.
Proof.
  intros.
  remember (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength; trivial.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l by omega.
    rewrite sublist_list_repeat.
    2: omega.
    2: rewrite Zlength_list_repeat in H; omega.
    replace (src - 0) with (src) by omega.
    intro.
    apply in_list_repeat in H0.
    inversion H0.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_list_repeat; try omega.
    2: rewrite Zlength_list_repeat in H by omega; omega.
    2: { split. omega. rewrite Zlength_list_repeat; omega. }
    repeat rewrite Zlength_list_repeat by omega.
    replace (src - 0) with (src) by omega.
    rewrite <- Znth_0_hd.
    2: { rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_list_repeat; omega. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same. simpl.
      compute; trivial. omega.
    + rewrite upd_Znth_diff by omega.
      rewrite Znth_list_repeat_inrange by omega.
      replace (fold_right Z.min inf (list_repeat (Z.to_nat (8 - (src + 1))) inf)) with inf.
      simpl. rewrite Z.min_l.
      symmetry. apply min_picks_first.
      1,2: rewrite <- inf_eq; rep_omega.
      symmetry. apply min_picks_first. reflexivity.
Qed.

Definition optimal_path (g: Graph) src dst p : Prop  :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost g p' <= path_cost g p ->
             p = p'.

(* will add more facts to this *)
Definition valid_prev prev src : Prop :=
  inrange_prev prev /\
  Znth src prev = src.

(* reachable and optimal *)
Definition dijkstra_pair_correct (g: Graph) src dst prev : Prop :=
  dst = src \/  (* Maybe I can massage away this conjunct *)
  (let p := (src, create_path src dst prev) in (* This is in VST *)
   optimal_path g src dst p).
(* this has to be in Graph land *)

Definition dijkstra_correct (g: Graph) (src : VType) (prev: list VType) (priq: list VType) : Prop :=
  forall dst,
    valid_prev prev src ->
    0 <= dst < SIZE ->
    isEmpty_Prop priq ->
    (Znth dst priq = inf + 1 -> (* if popped *)
     dijkstra_pair_correct g src dst prev).
    (* /\ *) (* can add this on later... *)
    (* (Znth dst priq = inf -> *)
     (* Znth dst prev = inf). *)

(* SPECS *)

Definition pq_emp_spec :=
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP (inrange_priq priq_contents)
    LOCAL (temp _pq pq)
    SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) pq)
    POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (isEmpty priq_contents))
    SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) pq).

Definition popMin_spec :=
 DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP  (inrange_priq priq_contents;
         isEmpty priq_contents = Vzero)
    LOCAL (temp _pq pq)
    SEP   (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
    EX rt : Z,
    PROP (rt = find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
    LOCAL (temp ret_temp  (Vint (Int.repr rt)))
    SEP   (data_at Tsh (tarray tint 8) (upd_Znth
       (find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
       (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: Graph, arr : pointer_val,
       dist : pointer_val, prev : pointer_val, src : Z
  PRE [_graph OF (tptr (tarray tint 8)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
    PROP (0 <= src < 8;
          Forall (fun list => Zlength list = 8) (graph_to_mat g);
       inrange_graph (graph_to_mat g))
    LOCAL (temp _graph (pointer_val_val arr);
         temp _src (Vint (Int.repr src));
         temp _dist (pointer_val_val dist);
         temp _prev (pointer_val_val prev))
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
       data_at_ Tsh (tarray tint 8) (pointer_val_val dist);
       data_at_ Tsh (tarray tint 8) (pointer_val_val prev))
  POST [tvoid]
    EX prev_contents : list Z,
    EX dist_contents : list Z,
    EX priq_contents : list Z,
    PROP (dijkstra_correct g src prev_contents priq_contents)
    LOCAL ()
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
         data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
         data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist)).
    
Definition Gprog : funspecs := ltac:(with_library prog [pq_emp_spec; popMin_spec; dijkstra_spec]).

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function.
  forward_for_simple_bound
    8
    (EX i : Z,
     PROP (isEmpty_Prop (sublist 0 i priq_contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) pq)).
  - entailer!.
  - simpl.
    assert_PROP (Zlength priq_contents = 8). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)).
      trivial. 
      apply Znth_In; omega.
      rewrite signed_repr_same_priq in H3; trivial; omega.
    + rewrite (sublist_split 0 i (i+1)); try omega.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      rewrite sublist_one; try omega. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) inf).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso.
      rewrite signed_repr_same_priq in H3 by (trivial; omega).
      unfold inf in l. rep_omega.
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: repeat rewrite Zlength_map in H2; omega.
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry. apply isEmpty_prop_val; trivial. 
Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = 8). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  forward. forward.
  forward_for_simple_bound
    8
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
            temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0))); 
            temp _pq pq)
     SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) pq)).
  - entailer!. simpl. rewrite find_index.
    trivial. omega. simpl. unfold not. omega.
  - forward.
    assert (0 <= i < Zlength priq_contents) by omega.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H4.
      destruct H4 as [? [? ?]]. rewrite <- H5.
      apply (inrange_priq_zoom_in _ x0) in H; trivial.
      rep_omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H4.
      destruct H4 as [? [? ?]]. rewrite <- H5.
      apply (inrange_priq_sublist _ _ H3) in H.
      pose proof (inrange_priq_zoom_in (sublist 0 i priq_contents) x0 H4 H).
      rep_omega.
    }
    forward_if; rewrite signed_repr_same_priq in H5; trivial.
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
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 8 priq_contents)) 0).
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

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    8
    (EX i : Z, 
     PROP (inrange_graph (graph_to_mat g))
     LOCAL (temp _dist (pointer_val_val dist);
            temp _prev (pointer_val_val prev);
            temp _src (Vint (Int.repr src));
            lvar _pq (tarray tint 8) v_pq;
            temp _graph (pointer_val_val arr))
     SEP (data_at Tsh (tarray tint 8) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (8-i)) Vundef)) v_pq;
          data_at Tsh (tarray tint 8) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (8-i)) Vundef)) (pointer_val_val prev);
          data_at Tsh (tarray tint 8) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (8-i)) Vundef)) (pointer_val_val dist);
          graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
  - unfold data_at, data_at_, field_at_; entailer!.
  - forward. forward. forward.
    entailer!. rewrite inf_eq. 
    replace (upd_Znth i
       (list_repeat (Z.to_nat i) (Vint (Int.repr inf)) ++
                    list_repeat (Z.to_nat (8 - i)) Vundef) (Vint (Int.repr inf))) with
        (list_repeat (Z.to_nat (i + 1)) (Vint (Int.repr inf)) ++ list_repeat (Z.to_nat (8 - (i + 1))) Vundef).
    1: entailer!.
    rewrite upd_Znth_app2 by (repeat rewrite Zlength_list_repeat by omega; omega).
    rewrite Z2Nat.inj_add by omega.
    rewrite <- list_repeat_app, app_assoc_reverse. f_equal.
    rewrite Zlength_list_repeat by omega.
    replace (i-i) with 0 by omega. rewrite upd_Znth0.
    rewrite Zlength_list_repeat by omega.
    rewrite sublist_list_repeat by omega.
    replace (8 - (i + 1)) with (8 - i - 1) by omega.
    replace (list_repeat (Z.to_nat 1) (Vint (Int.repr inf))) with ([Vint (Int.repr inf)]) by reflexivity.
    rewrite <- semax_lemmas.cons_app. reflexivity.
  - (* done with the first forloop *)
    replace (8-8) with 0 by omega; rewrite list_repeat_0, <- (app_nil_end).
    forward. forward. forward. 
    forward_loop
      (EX prev_contents : list Z,
       EX priq_contents : list Z,
       EX dist_contents : list Z,
       PROP (
           forall dst,
             isEmpty priq_contents = Vzero ->
             0 <= dst < Zlength priq_contents ->
             dst = find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0 ->
             dijkstra_pair_correct g src dst prev_contents;
             (* forall dst, *)
             (* 0 <= dst < Zlength priq_contents -> *)
             (* Znth dst priq_contents > inf -> (* if popped *) *)
             (* dijkstra_pair_correct g src dst prev_contents; (* optimal *) *)
             inrange_prev prev_contents;
             inrange_dist dist_contents;
             inrange_priq priq_contents)
       LOCAL (temp _dist (pointer_val_val dist);
              temp _prev (pointer_val_val prev);
              temp _src (Vint (Int.repr src));
              lvar _pq (tarray tint 8) v_pq;
              temp _graph (pointer_val_val arr))
       SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) v_pq;
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))) 
      break:
      (EX prev_contents: list Z,
       EX priq_contents: list Z,
       EX dist_contents: list Z,                                    
       PROP (Forall (fun x => x >= inf) priq_contents;
             dijkstra_correct g src prev_contents priq_contents)
       LOCAL (lvar _pq (tarray tint 8) v_pq)
       SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            (data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents)) v_pq);
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
    + Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) src).
      Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0).
      Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat 8) inf) = 8). {
        rewrite Zlength_list_repeat; omega. }
      split.
      2: {
        assert (inrange_prev (list_repeat (Z.to_nat 8) inf)). {
          unfold inrange_prev. rewrite Forall_forall.
          intros. apply in_list_repeat in H13. right; trivial.
        }
        assert (inrange_dist (list_repeat (Z.to_nat 8) inf)). {
          unfold inrange_dist. rewrite Forall_forall.
          intros. apply in_list_repeat in H14. right; trivial.
        }
        assert (inrange_priq (list_repeat (Z.to_nat 8) inf)). {
          unfold inrange_priq. rewrite Forall_forall.
          intros. apply in_list_repeat in H15.
          rewrite H15. rewrite <- inf_eq. omega.
        }          
        split3; [apply inrange_upd_Znth_prev | apply inrange_upd_Znth_dist | apply inrange_upd_Znth_priq].        
        3,6: left.
        3,4: unfold SIZE; simpl.
        9: rewrite <- inf_eq.
        all: try rep_omega; trivial.
      }
      intros.
      replace (find (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0)
          (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0))
                      (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0)) 0) with src in H15.
      unfold dijkstra_pair_correct. left; trivial.
      rewrite find_src; trivial.
    + Intros prev_contents priq_contents dist_contents.
      assert_PROP (Zlength priq_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength prev_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength dist_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in *. }
      forward_call (v_pq, priq_contents).
      forward_if.
      * assert (isEmpty priq_contents = Vzero). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H10 in H9; simpl in H9; now inversion H9.
        }
        clear H9.
        forward_call (v_pq, priq_contents). Intros u.
        assert (0 <= u < Zlength priq_contents).
        { rewrite H9.
          apply find_range.  
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H6.
          inversion H6. simpl. left; trivial. }
        specialize (H2 u H10 H11 H9).
        (* good! The u we popped was minimal *)
        forward_for_simple_bound
          8
          (EX i : Z,
           EX prev_contents' : list Z,
           EX priq_contents' : list Z,
           EX dist_contents' : list Z,
           PROP (forall dst,
                 0 <= dst < i ->
                 cost_was_improved_if_possible g u dst dist_contents';  
                 inrange_prev prev_contents';
                 inrange_priq priq_contents';
                 inrange_dist dist_contents')
           LOCAL (temp _u (Vint (Int.repr u));
                  temp _dist (pointer_val_val dist);
                  temp _prev (pointer_val_val prev);
                  temp _src (Vint (Int.repr src));
                  lvar _pq (tarray tint 8) v_pq;
                  temp _graph (pointer_val_val arr))
           SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents')) (pointer_val_val prev);
                data_at Tsh (tarray tint 8) (map Vint (map Int.repr priq_contents')) v_pq;
                data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents')) (pointer_val_val dist);
                graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
        -- rewrite Znth_0_hd, <- H9 by omega.
           Exists prev_contents.
           Exists (upd_Znth u priq_contents (inf+1)).
           Exists dist_contents.
           repeat rewrite <- upd_Znth_map.
           entailer!.
           split; [intros; exfalso; omega|].
           apply inrange_upd_Znth_priq; trivial.
           unfold inf. rep_omega.
        -- Fail forward.
           assert (0 <= u < Zlength (graph_to_mat g)). {
             unfold graph_to_mat.
             repeat rewrite Zlength_map.
             rewrite Z_inc_list_length.
             unfold SIZE. rep_omega.
           }
           assert (Zlength (Znth u (graph_to_mat g)) = 8). {
             rewrite Forall_forall in H0. apply H0. apply Znth_In. omega.
           }
           freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
           rewrite (graph_unfold _ _ _ u) by omega.
           Intros.
           freeze FR2 :=
             (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                          (sublist 0 u (Z_inc_list (Z.to_nat (Zlength (graph_to_mat g))))))
                                                                                            (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                                                                                                         (sublist (u + 1) (Zlength (graph_to_mat g))
                                                                                                                  (Z_inc_list (Z.to_nat (Zlength (graph_to_mat g)))))). 
           unfold list_rep.
           Fail forward.
           assert_PROP (force_val
                          (sem_add_ptr_int tint Signed
                                           (force_val (sem_add_ptr_int (tarray tint 8) Signed (pointer_val_val arr) (Vint (Int.repr u))))
                                           (Vint (Int.repr i))) = field_address (tarray tint 8) [ArraySubsc i] (list_address (pointer_val_val arr) u SIZE)). {
             entailer!.
             unfold list_address. simpl.
             rewrite field_address_offset.
             1: rewrite offset_offset_val; simpl; f_equal; rep_omega.
             unfold field_compatible in H22. destruct H22 as [? [? [? [? ?]]]].
      unfold field_compatible; split3; [| | split3]; auto.
      unfold legal_nested_field; split; [auto | simpl; omega].
           }
           forward. thaw FR2. 
           gather_SEP 0 3 1.
           rewrite <- graph_unfold; trivial. thaw FR.
           remember (Znth i (Znth u (graph_to_mat g))) as cost.
           assert_PROP (Zlength priq_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength prev_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength dist_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }    
           assert_PROP (Zlength (graph_to_mat g) = 8) by entailer!.
           assert (0 <= cost <= inf / SIZE). {
             unfold inrange_graph in H1.
             rewrite Forall_forall in H1.
             specialize (H1 (Znth u (graph_to_mat g))).
             pose proof (Znth_In u (graph_to_mat g) H13).
             specialize (H1 H24).
             unfold inrange_graph in H1. rewrite Forall_forall in H1.
             apply (H1 cost). rewrite Heqcost.
             apply Znth_In. omega.
           } 
           forward_if.
           ++ assert (0 <= Znth u dist_contents' <= inf - inf / SIZE). {
                assert (0 <= u < Zlength dist_contents') by omega.
                pose proof (inrange_dist_zoom_in _ _ H26 H18).
                destruct H27; [omega | exfalso].
                unfold cost_was_improved_if_possible in H15.
                admit.
                (* need to show that it's not inf
                   because it came via popping *)
              } 
              assert (cost < inf). {
                rewrite inf_eq in H25.
                unfold inf,SIZE in H24.
                rewrite Int.signed_repr in H25. rep_omega.
                clear -H24.
                destruct H24; split; try rep_omega.
                apply (Z.le_trans cost ((Int.max_signed - 1)/ 8) Int.max_signed); trivial.
                compute. inversion 1.
              }
              assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
                split; [omega|].
                destruct H26. destruct H24.
                clear -H28 H29.
                unfold inf in *.
                rep_omega.
                }
              forward. forward. forward_if.
              ** rewrite signed_repr_same_dist in H29; trivial; try rep_omega.
                 assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))).
                 { repeat rewrite Zlength_map. omega. }
                 forward. forward. forward.
                 forward; rewrite upd_Znth_same; trivial.
                 1: entailer!.
                 forward.
                 Exists (upd_Znth i prev_contents' u).
                 Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
                 Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)).
                 repeat rewrite <- upd_Znth_map; entailer!.
                 split.
                 2: { repeat rewrite Zlength_map in H30.
                      split3; [apply inrange_upd_Znth_prev |
                               apply inrange_upd_Znth_priq |
                               apply inrange_upd_Znth_dist];
                      trivial; try omega.
                      - left.
                        replace SIZE with (Zlength priq_contents).
                        rewrite Z.sub_1_r.
                        rewrite <- (Z.lt_succ_r _ (Z.pred (Zlength priq_contents))).
                        rewrite Z.succ_pred.
                        apply find_range.
                        apply min_in_list.
                        apply incl_refl.
                        rewrite <- Znth_0_hd by omega.
                        apply Znth_In; omega.
                      - pose proof (inrange_dist_zoom_in dist_contents' i H30 H18). 
                        clear -H29 H9.
                        destruct H9.
                        + admit. (* easy *)
                        + (* hmm, time to rethink the dist_range? *) admit.
                 }
                 intros.
                 unfold cost_was_improved_if_possible. intros.
                 remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                 assert (0 <= dst < i \/ dst = i) by omega.
                 unfold cost_was_improved_if_possible in H15.
                 destruct H44; [assert (dst <> i) by omega|]; destruct (Z.eq_dec u i).
                 --- rewrite <- e, upd_Znth_same, upd_Znth_diff; try rep_omega.
                     rewrite graph_to_mat_diagonal by omega.
                     rewrite Z.add_0_r. apply H15; trivial.           
                 --- repeat rewrite upd_Znth_diff; try rep_omega.
                     apply H15; trivial.
                 --- rewrite H44, <- e.
                     repeat rewrite upd_Znth_same.
                     rewrite graph_to_mat_diagonal by omega.
                     omega. rep_omega.
                 --- rewrite H44, upd_Znth_same, upd_Znth_diff; try rep_omega.
              ** rewrite signed_repr_same_dist in H29 by (trivial; omega).
                 forward.
                 Exists prev_contents' priq_contents' dist_contents'.
                 entailer!.
                 unfold cost_was_improved_if_possible in *. intros.
                 assert (0 <= dst < i \/ dst = i) by omega.
                 remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
                 destruct H43; [apply H15; trivial|].
                 subst dst. omega.
           ++ forward. Exists prev_contents' priq_contents' dist_contents'.
              entailer!. unfold cost_was_improved_if_possible in *. intros.
              assert (0 <= dst < i \/ dst = i) by omega.
              destruct H39; [apply H15; trivial|].
              (* clear -H25 H38 H39.  *)
              subst dst. exfalso. unfold inf in H38.
              rewrite Int.signed_repr in H25; rep_omega.
        -- (* from the for loop's inv, prove the while loop's inv *)
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!. 
          unfold dijkstra_pair_correct.
          admit. (* Hmm I need some way to link up the 
                    prev and prev' arrays *)
      * (* after breaking, prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H10 in H9; simpl in H9; now inversion H9.
        }
        clear H9.
        (* I may need some way to separate things that are inf in the PQ from things that have been popped from the PQ *)
        (* Then I will know for sure which items have been optimized. *)
        forward. Exists prev_contents priq_contents dist_contents.
        entailer!. split; [apply (isEmptyMeansInf _ H10)|].
        unfold dijkstra_correct. intros.
        (* need some sort of compatibility condition 
           on the three different arrays *)
        (* being inf+1 in the PQ should _mean_ 
           something in the other arrays, etc etc *)
        unfold dijkstra_pair_correct.
        
        admit. (* hmmmm *)
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents.
      forward. Exists prev_contents dist_contents priq_contents. entailer!. 
Abort.