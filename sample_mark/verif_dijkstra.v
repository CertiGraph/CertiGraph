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
Definition inf := Int.max_signed/2.

Lemma inf_eq : 1073741823 = inf.
Proof. unfold inf, Int.max_signed; auto. Qed.

Lemma inf_gt_0: 0 <= inf.
Proof. unfold inf, Int.max_signed; simpl. apply Z.div_pos; omega. Qed.

Lemma inf_div_2: inf < Int.max_signed.
Proof. apply (Z_div_lt Int.max_signed 2); rep_omega. Qed.

Lemma inf_div_eq:
  (Int.divs (Int.repr 2147483647) (Int.repr 2)) = Int.repr inf.
Proof.
  unfold Int.divs. repeat rewrite Int.signed_repr by rep_omega.
  rewrite Zquot.Zquot_Zdiv_pos by rep_omega.
  unfold inf, Int.max_signed; simpl. trivial.
Qed.

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map Vint (map Int.repr mylist)) (list_address l index size).

Definition graph_rep sh contents_graph gaddr : mpred :=
  iter_sepcon (list_rep sh SIZE gaddr contents_graph)
              (Z_inc_list (Z.to_nat (Zlength contents_graph))).

Lemma Z_inc_list_length: forall n, Zlength (Z_inc_list n) = Z.of_nat n.
Proof.
  intros. induction n. trivial.
  simpl Z_inc_list. rewrite Zlength_app. rewrite IHn.
  rewrite Nat2Z.inj_succ. unfold Zlength. simpl. omega.
Qed.

Lemma Z_inc_list_eq: forall i len,
    0 <= i < (Z.of_nat len) ->
    i = Znth i (Z_inc_list len).
Proof.
  intros. generalize dependent i. induction len.
  1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; omega.
  intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
  apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
  - rewrite app_Znth1. apply IHlen. omega. now rewrite Z_inc_list_length.
  - rewrite app_Znth2 by (rewrite Z_inc_list_length; omega).
    rewrite H0 at 2. rewrite Z_inc_list_length. simpl.
    replace (Z.of_nat len - Z.of_nat len) with 0 by omega.
    rewrite Znth_0_cons; trivial.
Qed.

Definition inrange l :=
  Forall (fun x => 0 <= x <= inf) l.

Lemma inrange_upd_Znth: forall l i new,
    0 <= i < Zlength l ->
    inrange l ->
    0 <= new <= inf ->
    inrange (upd_Znth i l new).
Proof.
  intros. unfold inrange in *.
  rewrite Forall_forall in *. intros.
  destruct (eq_dec x new). 1: omega.
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2.
    1: exfalso; omega.
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Lemma inrange_Znth: forall l i,
    0 <= i < Zlength l ->
    inrange l ->
    Int.min_signed <= Znth i l <= Int.max_signed.
Proof.
  intros. unfold inrange in H0. rewrite Forall_forall in H0.
  assert (In (Znth i l) l) by (apply Znth_In; omega).
  specialize (H0 (Znth i l) H1). split; destruct H0; try rep_omega.
  pose proof inf_div_2. omega.
Qed.

Lemma graph_unfold: forall sh contents ptr i,
    0 <= i < (Zlength contents) ->
    graph_rep sh contents ptr =
    iter_sepcon (list_rep sh SIZE ptr contents)
            (sublist 0 i (Z_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh SIZE ptr contents i *
           iter_sepcon (list_rep sh SIZE ptr contents)
             (sublist (i + 1) (Zlength contents) (Z_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros. unfold graph_rep.
  replace (Z_inc_list (Z.to_nat (Zlength contents))) with
      (sublist 0 (Zlength contents) (Z_inc_list (Z.to_nat (Zlength contents)))) at 1.
  2: { rewrite sublist_same; trivial.
       rewrite Z_inc_list_length, Z2Nat_id', Z.max_r; trivial.
       apply Zlength_nonneg.
  }
  rewrite (sublist_split 0 i (Zlength contents)),
  (sublist_split i (i+1) (Zlength contents)), (sublist_one i); try omega.
  2, 3, 4: rewrite Z_inc_list_length; rewrite Z2Nat.id; omega.
  rewrite <- (Z_inc_list_eq i (Z.to_nat (Zlength contents))).
  2: rewrite Z2Nat_id', Z.max_r; trivial; apply Zlength_nonneg. 
  repeat rewrite iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.

Fixpoint create_path (src dst : VType) (prev : list VType) (ans : list VType) (n : nat) : list VType :=
  match n with
  | O => ans
  | S n' => if Z.eq_dec src dst
            then src :: ans
            else create_path src (Znth dst prev) prev (dst :: ans) n'
  end.

(*
Fixpoint isEmpty' (l : list Z) : val :=
  match l with
  | [] => Vone
  | h :: t => if (Z_lt_dec h inf) then Vzero else isEmpty' t
  end.
*)

Definition isEmpty_Prop (l : list Z) :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then False else acc) True l.

Definition isEmpty (l : list Z) : val :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then Vzero else acc) Vone l.

Lemma isEmpty_prop_val: forall l,
    isEmpty_Prop l -> isEmpty l = Vone.
Proof.
  intros. induction l.
  1: reflexivity.
  simpl in *. destruct (Z_lt_dec a inf).
  inversion H.
  apply (IHl H).
Qed.

Lemma isEmpty_in: forall l target,
    In target l ->
    target < inf ->
    isEmpty l = Vzero.
Proof.
  intros. induction l.
  1: exfalso; apply (in_nil H).
  unfold isEmpty.
  rewrite fold_right_cons.
  destruct (Z_lt_dec a inf); trivial.
  simpl in H; simpl; destruct H.
  1: rewrite H in n; exfalso; omega.
  clear n a. specialize (IHl H).
  unfold isEmpty in IHl. trivial.
Qed.

Lemma isEmptyTwoCases: forall l,
    isEmpty l = Vone \/ isEmpty l = Vzero.
Proof.
  intros. induction l.
  1: simpl; left; trivial.
  destruct IHl.
  - simpl. destruct (Z_lt_dec a inf). 1: right; trivial.
    left; trivial.
  - simpl. destruct (Z_lt_dec a inf). 1: right; trivial.
    right; trivial.
Qed.

Lemma isEmptyMeansInf: forall l,
    isEmpty l = Vone -> Forall (fun x => x >= inf) l.
Proof.
  intros. induction l; trivial. simpl in H.
  destruct (Z_lt_dec a inf); [inversion H|].
  specialize (IHl H). apply Forall_cons; trivial.
Qed.

Definition pq_emp_spec :=
  DECLARE _pq_emp
  WITH pq: val, contents: list Z
  PRE [_pq OF tptr tint]
  PROP (inrange contents)
    LOCAL (temp _pq pq)
    SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr contents)) pq)
    POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (isEmpty contents))
    SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr contents)) pq).

Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
induction al; intros.
inversion H.
destruct H.
subst a.
simpl.
apply Z.le_min_l.
simpl. rewrite Z.le_min_r.
apply IHal.
apply H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof.
intros.
apply fold_min_general.
apply H.
Qed.

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
 intros.
 revert x; induction al; simpl; intros.
 apply Z.min_comm.
 rewrite <- Z.min_assoc. f_equal.
 apply IHal.
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

Lemma find_index l i ans :
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

Lemma find_range: forall l target ans,
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

Lemma min_in_list : forall l1 l2 starter,
    incl l1 l2 ->
    In starter l2 ->
    In (fold_right Z.min starter l1) l2.
Proof.
  intros. induction l1.
  - assumption.
  - simpl.
    destruct (Z.min_dec a (fold_right Z.min starter l1)); rewrite e; clear e.
    + apply H. apply in_eq.
    + apply IHl1. apply (incl_cons_inv H).
Qed.

Definition popMin_spec :=
 DECLARE _popMin
  WITH pq: val, contents: list Z
  PRE [_pq OF tptr tint]
  PROP  (inrange contents;
           isEmpty contents = Vzero)
    LOCAL (temp _pq pq)
    SEP   (data_at Tsh (tarray tint 8) (map Vint (map Int.repr contents)) pq)
    POST [ tint ]
    EX rt : Z,
    PROP (rt = find contents (fold_right Z.min (hd 0 contents) contents) 0)
    LOCAL (temp ret_temp  (Vint (Int.repr rt)))
    SEP   (data_at Tsh (tarray tint 8) (upd_Znth
       (find contents (fold_right Z.min (Znth 0 contents) contents) 0)
       (map Vint (map Int.repr contents)) (Vint (Int.repr inf))) pq).

(*
sample prev array, where src = 3, dst = 8.
[inf;  3 ; inf;  3 ;  5 ;  1 ;  1 ; inf;  6 ]
  0    1    2    3    4    5    6    7    8     <- indices

prev[3] = 3, which indicates that 3 is the source.

The above function create_path will work only if 
the prev array has been generated perfectly. ie, 
(1) There needs to be some cell such that its value is the same as its index. 
(2) There need to be no loops. 
a(3) If I query any cell, its value needs to be either 
   (a) inf (meaning the cell was unreachable)
  or
   (b) it needs to point to another cell such that that cellb will lead me closer to the source.

orIf all these guarantees are set up, then I can find you the 
source.  *)

Definition dijkstra_correct (g: Graph) (src : VType) (prev: list VType) : Prop :=
  forall dst,
    (Znth dst prev) = inf \/ (* unreachable *)
    let p := (src, create_path src dst prev [] 8) in
    valid_path g p ->
    path_ends g p src dst ->
    forall p', valid_path g p' ->
               path_ends g p' src dst ->
               Nat.lt (path_cost g p') (path_cost g p) ->
               p = p'.

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: Graph, arr : pointer_val,
       dist : pointer_val, prev : pointer_val, src : Z
  PRE [_graph OF (tptr (tarray tint 8)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
    PROP (0 <= src < 8;
          Forall (fun list => Zlength list = 8) (graph_to_mat g);
       Forall (fun list => inrange list) (graph_to_mat g))
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
    PROP (dijkstra_correct g src prev_contents)
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
            PROP (isEmpty_Prop (sublist 0 i contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr contents)) pq)).
  - entailer!.
  - simpl.
    assert_PROP (Zlength contents = 8). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    } 
    forward. forward_if.
    + forward. entailer!. 
      rewrite (isEmpty_in contents (Znth i contents)).
      unfold Vzero; trivial.
      apply Znth_In; omega.
      rewrite Int.signed_repr in H3; trivial.
      apply inrange_Znth; trivial; omega.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)); try omega.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      rewrite sublist_one; try omega. simpl.
      destruct (Z_lt_dec (Znth i contents) inf).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso. rewrite inf_div_eq in H3.
      rewrite Int.signed_repr in H3. auto.
      apply inrange_Znth; trivial.
      repeat rewrite Zlength_map in H5; rep_omega. 
  - forward. entailer!.
    rewrite sublist_same in H0.
    2: omega.
    2: repeat rewrite Zlength_map in H2; omega.
    rewrite isEmpty_prop_val; [unfold Vone; f_equal | assumption].
Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength contents = 8). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  forward. forward.
  forward_for_simple_bound
    8
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 contents) (sublist 0 i contents))));
            temp _minVertex (Vint (Int.repr (find contents (fold_right Z.min (Znth 0 contents) (sublist 0 i contents)) 0))); 
            temp _pq pq)
     SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr contents)) pq)).
  - entailer!. simpl. rewrite find_index.
    trivial. omega. simpl. unfold not. omega.
  - forward.
    assert (Int.min_signed <= Znth i contents <= Int.max_signed) by
        (apply inrange_Znth; trivial; omega).
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 contents) (sublist 0 i contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H4.
      destruct H4 as [? [? ?]]. rewrite <- H5.
      apply inrange_Znth; trivial. apply Forall_sublist; auto.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H4.
      destruct H4 as [? [? ?]]. rewrite <- H5. apply inrange_Znth; trivial.
    }
    forward_if.
    + forward. forward.
      entailer!.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) contents) by omega.
    rewrite fold_min_another.
    rewrite Z.min_r; [| omega].
    split; trivial. f_equal. 
    rewrite find_index.
    replace (i+0) with i by omega. trivial. omega.
    apply min_not_in_prev. assumption.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by omega.
      rewrite (sublist_one i (i+1) contents) by omega.
      rewrite fold_min_another.
      rewrite Z.min_l; [|omega]. split; trivial.
  - forward. entailer!.
    + rewrite <- H1. replace (Zlength contents) with (Zlength contents + 0) by omega.
      apply find_range. 2: reflexivity.
      rewrite sublist_same; [|omega..].
      apply min_in_list; [apply incl_refl | apply Znth_In; omega]. 
    + forward. 
      Exists (find contents (fold_right Z.min (hd 0 contents) (sublist 0 8 contents)) 0).
      rewrite sublist_same by omega. entailer!.
      destruct contents; simpl; auto.
Qed.

Definition compatible (prev pq dist : list Z) : Prop :=
  True.
(* This is where I will make a claim about how the three lists
interact with each other during the working of the inner loop *)

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    8
    (EX i : Z, 
     PROP (Forall (fun list => inrange list) (graph_to_mat g))
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
    rewrite inf_div_eq in *.
    (* rewrite inf_eq in *. *)
    entailer!. 
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
    replace (8-8) with 0 by omega; rewrite list_repeat_0.
    rewrite <- (app_nil_end).
    forward. forward. forward.  
    forward_loop
      (EX prev_contents : list Z,
       EX pq_contents : list Z,
       EX dist_contents : list Z,
       PROP (inrange pq_contents;
             inrange prev_contents;
             inrange dist_contents)
       LOCAL (temp _dist (pointer_val_val dist);
              temp _prev (pointer_val_val prev);
              temp _src (Vint (Int.repr src));
              lvar _pq (tarray tint 8) v_pq;
              temp _graph (pointer_val_val arr))
       SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr pq_contents)) v_pq;
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist); graph_rep sh (graph_to_mat g) (pointer_val_val arr))) 
      break:
      (EX prev_contents: list Z,
       EX pq_contents: list Z,
       EX dist_contents: list Z,                                    
       PROP (Forall (fun x => x >= inf) pq_contents)
       LOCAL (lvar _pq (tarray tint 8) v_pq)
       SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            (data_at Tsh (tarray tint 8) (map Vint (map Int.repr pq_contents)) v_pq);
            data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist); graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
 (* ie, the PQ is all inf --> is empty *)
    + Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) src).
      Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0).
      Exists (upd_Znth src (list_repeat (Z.to_nat 8) inf) 0).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (0 <= inf <= inf).
      { pose proof inf_gt_0. omega. }
      assert (inrange (list_repeat (Z.to_nat 8) inf)).
      { unfold inrange. rewrite Forall_forall; intros.
        apply in_list_repeat in H13. rewrite H13. assumption. }
      split3; apply inrange_upd_Znth; trivial; try rep_omega.
      clear -H; unfold inf. unfold Int.max_signed; simpl.
      assert (8 < 2147483647) by omega. destruct H.
      pose proof (Z.lt_trans src 8 (2147483647 / 2) H1 H0). omega.
    + Intros prev_contents pq_contents dist_contents.
      assert_PROP (Zlength pq_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in H12. }
      assert_PROP (Zlength prev_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in H10. }
      assert_PROP (Zlength dist_contents = 8).
      { entailer!. now repeat rewrite Zlength_map in H17. }
      forward_call (v_pq, pq_contents).
      forward_if.
      * forward_call (v_pq, pq_contents).
        assert (isEmpty pq_contents = Vzero). {
          destruct (isEmptyTwoCases pq_contents);
            rewrite H9 in H8; simpl in H8; now inversion H8.
        }
        clear H8. split; trivial.
        Intros u.
        assert (0 <= u < 8).
        { rewrite <- H5, H9.
          replace (Zlength pq_contents)
            with (Zlength pq_contents + 0) by omega.
          apply find_range; [|reflexivity]. 
          apply min_in_list. apply incl_refl.
          destruct pq_contents. rewrite Zlength_nil in H5.
          inversion H5. simpl. left; trivial.
        }
        forward_for_simple_bound
          8
          (EX i : Z,
           EX prev_contents' : list Z,
           EX pq_contents' : list Z,
           EX dist_contents' : list Z,
           PROP (inrange prev_contents';
                 inrange pq_contents';
                 inrange dist_contents')
           LOCAL (temp _u (Vint (Int.repr u));
                  temp _dist (pointer_val_val dist);
                  temp _prev (pointer_val_val prev);
                  temp _src (Vint (Int.repr src));
                  lvar _pq (tarray tint 8) v_pq;
                  temp _graph (pointer_val_val arr))
           SEP (data_at Tsh (tarray tint 8) (map Vint (map Int.repr prev_contents')) (pointer_val_val prev);
                data_at Tsh (tarray tint 8) (map Vint (map Int.repr pq_contents')) v_pq;
                data_at Tsh (tarray tint 8) (map Vint (map Int.repr dist_contents')) (pointer_val_val dist);
                graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
        -- Exists prev_contents.
           Exists (upd_Znth
            (find pq_contents (fold_right Z.min (Znth 0 pq_contents) pq_contents) 0)
            pq_contents inf).
           Exists dist_contents.
           repeat rewrite <- upd_Znth_map.
           entailer!. pose proof inf_div_2.
           apply inrange_upd_Znth; trivial.
           2: { pose proof inf_gt_0. omega. }
           replace (Zlength pq_contents) with (Zlength pq_contents + 0) by omega.
           apply find_range; [|reflexivity].
           apply min_in_list; [apply incl_refl | apply Znth_In; omega].
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
             unfold field_compatible in H20. destruct H20 as [? [? [? [? ?]]]].
      unfold field_compatible; split3; [| | split3]; auto.
      unfold legal_nested_field; split; [auto | simpl; omega].
           }
           forward. thaw FR2. 
           gather_SEP 0 3 1.
           rewrite <- graph_unfold; trivial. thaw FR.
           remember (Znth i (Znth u (graph_to_mat g))) as cost.
           remember (find pq_contents (fold_right Z.min (hd 0 pq_contents) pq_contents) 0) as min_ind.
           assert_PROP (Zlength pq_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength prev_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength dist_contents' = 8). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }    
           assert_PROP (Zlength (graph_to_mat g) = 8) by 
               entailer!.
           assert (0 <= cost <= inf). {
             rewrite Forall_forall in H1.
             specialize (H1 (Znth u (graph_to_mat g))).
             pose proof (Znth_In u (graph_to_mat g) H10).
             specialize (H1 H22).
             unfold inrange in H1. rewrite Forall_forall in H1.
             apply (H1 cost).
             rewrite Heqcost.
             apply Znth_In. omega.
           } 
           forward_if; rewrite inf_div_eq in H23.
           2: {
             forward. 
             Exists prev_contents' pq_contents' dist_contents'. 

             entailer!. } 
           forward. forward.
           assert (0 <= Znth u dist_contents' <= inf). {
             unfold inrange in H16.
             rewrite Forall_forall in H16. unfold inf.
             apply H16; apply Znth_In; omega. }
           assert (0 <= Znth i dist_contents' <= inf). {
             unfold inrange in H16.
             rewrite Forall_forall in H16. unfold inf.
             apply H16; apply Znth_In; omega. }
           assert (0 <= Znth i (Znth u (graph_to_mat g)) <= inf). {
             rewrite Forall_forall in H1.
             pose proof (Znth_In u (graph_to_mat g) H12).
             specialize (H1 (Znth u (graph_to_mat g)) H26).
             unfold inrange in H1. rewrite Forall_forall in H1.
             apply H1. apply Znth_In. rep_omega. }
             assert (0 <=
                   Znth (find pq_contents (fold_right Z.min (hd 0 pq_contents) pq_contents) 0)
                        dist_contents' +
                   Znth i
                        (Znth (find pq_contents (fold_right Z.min (hd 0 pq_contents) pq_contents) 0)
                              (graph_to_mat g)) <= Int.max_signed). {
             rewrite <- Heqmin_ind. rewrite <- H9.
             clear -H24 H26. split; [omega|].
             assert (Z.mul 2 inf < Int.max_signed) by
                 (unfold inf, Int.max_signed; simpl; reflexivity). 
             destruct H24 as [_ ?]; destruct H26 as [_ ?]. omega.
           }
           forward_if.
           2: forward;
             Exists prev_contents' pq_contents' dist_contents';
             entailer!.
           rewrite Int.signed_repr in H28.
           2: { subst u cost min_ind. rep_omega. }
           rewrite Int.signed_repr in H28.
           2: { clear -H25. pose proof inf_div_2. rep_omega. }
           forward. forward.
           forward. forward.
           entailer!.
           1: { rewrite upd_Znth_same by (repeat rewrite Zlength_map; omega). 
                trivial. }
           forward. entailer!. rewrite upd_Znth_same.
           2: repeat rewrite Zlength_map; omega. 
           remember (find pq_contents (fold_right Z.min (hd 0 pq_contents) pq_contents) 0) as min_ind.
           Exists (upd_Znth i prev_contents' min_ind).
           Exists
             (upd_Znth i pq_contents'
                       (Znth min_ind dist_contents' + Znth i (Znth min_ind (graph_to_mat g)))).
           Exists
             (upd_Znth i dist_contents'
                       (Znth min_ind dist_contents' + Znth i (Znth min_ind (graph_to_mat g)))).
           repeat rewrite <- upd_Znth_map; entailer!.
           split3; apply inrange_upd_Znth; try rep_omega; try assumption.
           clear -H10. assert (8 <= inf). {
             unfold inf, Int.max_signed in *; simpl in *.
             replace 8 with (8 * 2 / 2). apply Z_div_le; omega.
             apply Z_div_mult; omega. }
           rep_omega.
        -- Intros a b c. Exists a b c. entailer!.
      * assert (isEmpty pq_contents = Vone). {
          destruct (isEmptyTwoCases pq_contents);
            rewrite H9 in H8; simpl in H8; now inversion H8.
        }
        forward. Exists prev_contents pq_contents dist_contents.
        entailer!. apply (isEmptyMeansInf _ H9).
    + Intros prev_contents pq_contents dist_contents.
      forward. Exists prev_contents dist_contents.
      entailer!. admit.
Abort.