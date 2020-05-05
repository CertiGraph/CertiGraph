Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import RamifyCoq.sample_mark.priq_utils.
Require Import RamifyCoq.sample_mark.priorityqueue.
Require Import RamifyCoq.sample_mark.dijkstra.

Local Open Scope Z_scope.

Definition get_popped pq : list VType :=
  map snd (filter (fun x => (fst x) =? (inf+1))
                  (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))).

Definition path_correct (g: LGraph) prev dist src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost g p < inf /\
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
    (forall step, In_path g step path ->
                  In step (get_popped priq)) /\
    path_globally_optimal g src dst path.

Definition inv_unpopped g src prev priq dist dst :=
  Znth dst priq < inf ->
  dst = src \/
  (dst <> src /\
   let mom := Znth dst prev in
   In mom (get_popped priq) /\
   elabel g (mom, dst) < inf /\
   (Znth mom dist) + (Znth dst (Znth mom (graph_to_mat g))) < inf /\
   Znth dst dist = Znth mom dist + Znth dst (Znth mom (graph_to_mat g)) /\
   forall mom',
     In mom' (get_popped priq) ->
     Znth dst dist <= careful_add (Znth mom' dist) (Znth dst (Znth mom' (graph_to_mat g)))).

Definition inv_unpopped_weak g src prev priq dist dst u :=
  Znth dst priq < inf ->
  dst = src \/
  dst <> src /\
  (let mom := Znth dst prev in
   mom <> u /\
   In mom (get_popped priq) /\
   elabel g (mom, dst) < inf /\
   Znth mom dist + (Znth dst (Znth mom (graph_to_mat g))) < inf /\
   Znth dst dist = Z.add (Znth mom dist) (Znth dst (Znth mom (graph_to_mat g))) /\
   forall mom',
     mom' <> u ->
     In mom' (get_popped priq) ->
     Znth dst dist <=
     careful_add (Znth mom' dist) (Znth dst (Znth mom' (graph_to_mat g)))).
  
Definition inv_unseen g prev priq dist dst :=
  Znth dst priq = inf ->
  Znth dst dist = inf /\
  Znth dst prev = inf /\
  forall m, In m (get_popped priq) ->
            careful_add 
              (Znth m dist)
              (Znth dst (Znth m (graph_to_mat g))) = inf.

Definition inv_unseen_weak g prev priq dist dst u :=
  Znth dst priq = inf ->
  Znth dst dist = inf /\
  Znth dst prev = inf /\
  forall mom, In mom (get_popped priq) ->
              mom <> u ->
              careful_add
                (Znth mom dist)
                (Znth dst (Znth mom (graph_to_mat g))) = inf.
                                                           
Definition dijkstra_correct (g: LGraph) (src : VType) (prev priq dist: list VType) : Prop :=
  forall dst,
    vvalid g dst ->
    inv_popped g src prev priq dist dst /\
    inv_unpopped g src prev priq dist dst /\
    inv_unseen g prev priq dist dst.

Definition push_spec :=
  DECLARE _push
  WITH pq: val, vertex : Z, weight : Z, priq_contents_val: list val
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr weight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) priq_contents_val pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                         priq_contents_val (Vint (Int.repr weight))) pq).
    
Definition pq_emp_spec := 
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents)
   PARAMS (pq)
   GLOBALS ()
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (isEmpty priq_contents))
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq).

Definition adjustWeight_spec :=
  DECLARE _adjustWeight
  WITH pq: val, vertex : Z, newWeight : Z, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr newWeight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                  (map Vint (map Int.repr priq_contents)) (Vint (Int.repr newWeight))) pq).

Definition popMin_spec :=
  DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents;
        isEmpty priq_contents = Vzero)
   PARAMS (pq)
   GLOBALS ()
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
  PRE [tptr (tarray tint SIZE), tint, tptr tint, tptr tint]
   PROP (0 <= src < SIZE;
        Forall (fun list => Zlength list = SIZE) (graph_to_mat g);
        inrange_graph (graph_to_mat g);
        sound_dijk_graph g;
        forall i, vvalid g i ->
                  Znth i (Znth i (graph_to_mat g)) = 0)
   PARAMS (pointer_val_val arr;
          Vint (Int.repr src);
          pointer_val_val dist;
          pointer_val_val prev)
   GLOBALS ()
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


Definition Gprog : funspecs := ltac:(with_library prog
                                                  [push_spec;
                                                  pq_emp_spec;
                                                  adjustWeight_spec;
                                                  popMin_spec;
                                                  dijkstra_spec]).
