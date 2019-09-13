Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.DijkstraGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Definition inf := 2147483647.

Definition whole_graph sh g x := (@graph_rep_spatial mpred pointer_val (SDAG_VST sh) g x).

Fixpoint create_path (src dst : VType) (prev : list VType) (ans : list VType) (n : nat) : list VType :=
  match n with
  | O => ans
  | S n' => if Z.eq_dec src dst
            then src :: ans
            else create_path src (Znth dst prev) prev (dst :: ans) n'
  end.

Definition empty (l : list Z) : val :=
  if (eq_dec (list_repeat (Z.to_nat (Zlength l)) inf) l)
  then Vone else Vzero.
  
Definition pq_emp_spec :=
  DECLARE _pq_emp
  WITH pq: val, contents: list Z
  PRE [_pq OF tptr tint]
  PROP (Forall repable_signed contents)
    LOCAL (temp _pq pq)
    SEP (data_at Ews (tarray tint 8) (map Vint (map Int.repr contents)) pq)
    POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (empty contents))
    SEP (data_at Ews (tarray tint 8) (map Vint (map Int.repr contents)) pq).

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
  PROP  (Forall repable_signed contents;
           list_repeat (Z.to_nat (Zlength contents)) inf <>
            contents) (* not an empty pq *)
    LOCAL (temp _pq pq)
    SEP   (data_at Ews (tarray tint 8) (map Vint (map Int.repr contents)) pq)
    POST [ tint ]
    EX rt : Z,
    PROP (rt = find contents (fold_right Z.min (hd 0 contents) contents) 0)
    LOCAL (temp ret_temp  (Vint (Int.repr rt)))
    SEP   (data_at Ews (tarray tint 8) (upd_Znth
       (find contents (fold_right Z.min (Znth 0 contents) (sublist 0 8 contents)) 0)
       (map Vint (map Int.repr contents)) (Vint (Int.repr 2147483647))) pq).
    
Definition Gprog : funspecs := ltac:(with_library prog [pq_emp_spec; popMin_spec]).

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function.
  forward_for_simple_bound
    8
    (EX i : Z,
     PROP (sublist 0 i contents = list_repeat (Z.to_nat i) inf)
     LOCAL (temp _pq pq)
     SEP (data_at Ews (tarray tint 8) (map Vint (map Int.repr contents)) pq)).
  - entailer!.
  - simpl.
    assert_PROP (Zlength contents = 8). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward. forward_if.
    + forward. entailer!. unfold empty, inf.
      replace (Zlength contents - 0) with (Zlength contents) by omega.
      destruct eq_dec; trivial. exfalso.
      assert (Int.signed (Int.repr (Znth i contents)) = 2147483647). {
        rewrite <- e.
        rewrite Znth_list_repeat_inrange by rep_omega.
        simpl. apply Int.signed_repr. rep_omega.
      }
      clear -H3 H7. omega.
    + forward. entailer!.
      rewrite sublist_last_1 by rep_omega. rewrite H2.
      Open Scope nat_scope.
      replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1).
      Close Scope nat_scope.
      2: { rewrite Z2Nat.inj_add by easy. simpl; trivial. }
      rewrite <- (list_repeat_app Z (Z.to_nat i) 1 inf).
      f_equal. simpl. f_equal.
      assert (0 <= i < Zlength contents) by rep_omega.
      pose proof (Forall_Znth repable_signed contents i H7 H).
      destruct H8. rewrite Int.signed_repr in H3 by easy. 
      replace (Int.max_signed) with inf in * by auto.
      unfold inf in *. rep_omega.
  - forward. entailer!.
    assert (0 = 0) by omega. symmetry in H2.
    repeat rewrite Zlength_map in H2.
    rewrite (sublist_same 0 8 contents H4 H2) in H0.
    rewrite H0. unfold empty. simpl. auto.
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
     SEP (data_at Ews (tarray tint 8) (map Vint (map Int.repr contents)) pq)).
  - entailer!. simpl. rewrite find_index.
    trivial. omega. simpl. unfold not. omega.
  - forward. 
    assert (repable_signed (Znth i contents))
      by (apply Forall_Znth; auto; omega).
    assert (repable_signed (fold_right Z.min (Znth 0 contents) (sublist 0 i contents)))
      by (apply Forall_fold_min;
       [apply Forall_Znth; auto; omega
       |apply Forall_sublist; auto]).
    autorewrite with sublist.
    subst POSTCONDITION; unfold abbreviate.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) contents) by omega.
    rewrite fold_min_another.
    forward_if.
    + forward. forward.
      entailer!. rewrite Z.min_r; [|omega]. split; trivial.
      rewrite find_index.
      replace (i+0) with i by omega. trivial. omega.
      apply min_not_in_prev. assumption.
    + forward. entailer!.
      rewrite Z.min_l; [|omega]. split; trivial.
  - forward. entailer!.
    + rewrite <- H1. replace (Zlength contents) with (Zlength contents + 0) by omega.
      apply find_range. 2: reflexivity.
      rewrite sublist_same; [|omega..].
      apply min_in_list; [apply incl_refl | apply Znth_In; omega]. 
    + forward. 
      Exists (find contents (fold_right Z.min (hd 0 contents) (sublist 0 8 contents)) 0).
      entailer!.
      * rewrite sublist_same by rep_omega. split; trivial.
        destruct contents; simpl; auto.
Qed.
      
(*
sample prev array, where src = 3, dst = 8.
[inf;  3 ; inf;  3 ;  5 ;  1 ;  1 ; inf;  6 ]
  0    1    2    3    4    5    6    7    8     <- indices

prev[3] = 3, which indicates that 3 is the source.

The above function create_path will work only if 
the prev array has been generated perfectly. ie, 
(1) There needs to be some cell such that its value is the same as its index. 
(2) There need to be no loops. 
(3) If I query any cell, its value needs to be either 
   (a) inf (meaning the cell was unreachable)
  or
   (b) it needs to point to another cell such that that cell will lead me closer to the source.

If all these guarantees are set up, then I can find you the 
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
                                                                                    (* here, I can put a list of Z and tie that to dist and prev *)
  PRE [_graph OF (tptr (tarray tint 8)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
    PROP (0 <= src < 8)
    LOCAL (temp _graph (pointer_val_val arr);
         temp _src (Vint (Int.repr src));
         temp _dist (pointer_val_val dist);
         temp _prev (pointer_val_val prev))
    SEP (whole_graph sh g arr; (* make them specific list of Z *)
       data_at Tsh (tarray tint 8) (pointer_val_val dist);
       data_at Tsh (tarray tint 8) (pointer_val_val prev))
  POST [tvoid]
    EX prev : list Z, (* should probably go away *)
    PROP (dijkstra_correct g src prev)
    LOCAL ()
    SEP (whole_graph sh g arr).







Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function.  
  forward_for_simple_bound
    8
    (EX i : Z, 
     PROP ()
          LOCAL (temp _dist (pointer_val_val dist);
                 temp _prev (pointer_val_val prev);
                 temp _src (Vint (Int.repr src));
                 lvar _pq (tarray tint 8) v_pq)
     (* ; lvar _prev (tarray tint 8) _prev; *) 
            (* lvar _dist (tarray tint 8) _dist; *)
            (* temp _src (Vint (Int.repr src))) *)
           (* temp _j (Vint (Int.repr j))) *)
     SEP (data_at_ Tsh (tarray tint 8) v_pq;
          whole_graph sh g arr; (* make these concrete *)
          data_at Tsh (tarray tint 8) (pointer_val_val dist);
          data_at Tsh (tarray tint 8) (pointer_val_val prev))).
          (* data_at Tsh (tarray tint 8) (map Vint (map Int.repr pq_contents)) v_pq)). *)
  - entailer!. 
  - forward. forward. forward.
    + entailer!. rewrite upd_Znth_same; easy.
    + Compute (reptype (tarray tint 8)).


      forward. entailer!.
  - (* done with the first forloop *)
    forward. forward. forward.











    forward_for_simple_bound
      8
      (EX j : Z,
              PROP ()
                   LOCAL (lvar _pq (tarray tint 8) v_pq)
                   SEP (data_at Tsh (tarray tint 8)
         (upd_Znth src (default_val (tarray tint 8)) (Vint (Int.repr 0))) v_pq;
  whole_graph sh g arr;
  data_at Tsh (tarray tint 8)
    (upd_Znth src (default_val (tarray tint 8)) (Vint (Int.repr 0)))
    (pointer_val_val dist);
  data_at Tsh (tarray tint 8)
    (upd_Znth src (default_val (tarray tint 8)) (Vint (Int.repr src)))
    (pointer_val_val prev))).
    + entailer!.
    + forward_call (v_pq).
      * unfold whole_graph. unfold graph_rep_spatial.

        entailer!.

      forward.
    
    

    Intros. do 3 forward. 2: forward; entailer!. 
    entailer!.
    rewrite upd_Znth_Zlength in H5.
    rewrite <- H5 in H1.
    rewrite upd_Znth_same. 2, 3: assumption.
    apply is_int_I32_Vint.
  - Intros. forward. forward.
    forward_loop
      (
        EX j : Z,
        PROP ()
        LOCAL (lvar _pq (tarray tint 8) v_pq; temp _j (Vint (Int.repr j)))
        SEP (data_at Tsh (tarray tint 8)
            (upd_Znth src (default_val (tarray tint 8)) (Vint (Int.repr 0))) v_pq;
     data_at_ Tsh (tarray tint 8) v_prev;
     data_at Tsh (tarray tint 8)
       (upd_Znth src (default_val (tarray tint 8)) (Vint (Int.repr 0))) v_dist;
     whole_graph sh g arr)
      )
      break:
      (
        PROP ()
        LOCAL ()
        SEP ()
      ).
    + forward. entailer!.










      
      admit.
      admit.
    + forward_if.
      * admit.
      * forward. admit.
    + unfold POSTCONDITION. unfold abbreviate.
      admit.
Admitted.