(* A separate file with the underlying PQ spec-ed out *)
Require Import RamifyCoq.priq.priq_arr_specs.

(* Dijkstra-specific stuff *)
Require Import RamifyCoq.dijkstra.env_dijkstra_arr.
Require Import RamifyCoq.dijkstra.MathDijkGraph.
Require Import RamifyCoq.dijkstra.SpaceDijkGraph.
Require Import RamifyCoq.dijkstra.path_cost.

Local Open Scope Z_scope.

(*
Definition get_popped pq : list VType :=
  map snd (filter (fun x => (fst x) =? (inf + 1))
                  (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))).
 *)

Definition path_correct (g : DijkstraGeneralGraph) (prev dist: list VType) src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost g p < inf /\ 
  Znth dst dist = path_cost g p /\
  Forall (fun x => Znth (snd x) prev = fst x) (snd p).

Definition path_globally_optimal (g : DijkstraGeneralGraph) src dst p : Prop :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost g p <= path_cost g p'.

Definition path_in_popped (g : DijkstraGeneralGraph) popped dist path :=
  forall step, In_path g step path ->
               In step popped /\ Znth step dist < inf.

Definition inv_popped (g : DijkstraGeneralGraph) src (popped prev dist : list VType) dst :=
  In dst popped ->
  (Znth dst dist = inf /\
   (forall m,
     vvalid g m -> 
     (careful_add
       (Znth m dist)
       (Znth dst (Znth m (graph_to_mat g))) = inf) /\
     (~ In m popped -> Znth m dist = inf)))
  \/
  (exists path,
      path_correct g prev dist src dst path /\
      path_in_popped g popped dist path /\
      path_globally_optimal g src dst path).

Definition inv_unpopped (g : DijkstraGeneralGraph) src (popped prev dist: list VType) (dst: VType) :=
  ~ In dst popped ->
  Znth dst dist < inf ->
  dst = src \/
  (dst <> src /\
   let mom := Znth dst prev in
   vvalid g mom /\
   In mom popped /\
   elabel g (mom, dst) < inf /\
   (Znth mom dist) + (Znth dst (Znth mom (graph_to_mat g))) < inf /\
   Znth dst dist = Znth mom dist + Znth dst (Znth mom (graph_to_mat g)) /\
   forall mom',
     vvalid g mom' ->
     In mom' popped ->
     Znth dst dist <= careful_add (Znth mom' dist) (Znth dst (Znth mom' (graph_to_mat g)))).

Definition inv_unpopped_weak (g : DijkstraGeneralGraph) (src: VType) (popped prev dist : list VType) (dst u : VType) :=
  ~ In dst popped ->
  Znth dst dist < inf ->
  dst = src \/
  dst <> src /\
  (let mom := Znth dst prev in
   mom <> u /\
   vvalid g mom /\
   In mom popped /\
   elabel g (mom, dst) < inf /\
   Znth mom dist + (Znth dst (Znth mom (graph_to_mat g))) < inf /\
   Znth dst dist = Z.add (Znth mom dist) (Znth dst (Znth mom (graph_to_mat g))) /\
   forall mom',
     mom' <> u ->
     vvalid g mom' ->
     In mom' popped ->
     Znth dst dist <=
     careful_add (Znth mom' dist) (Znth dst (Znth mom' (graph_to_mat g)))).
  
Definition inv_unseen (g : DijkstraGeneralGraph) (popped dist: list VType) (dst : VType) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m, vvalid g m ->
            In m popped ->
            careful_add 
              (Znth m dist)
              (Znth dst (Znth m (graph_to_mat g))) = inf.

Definition inv_unseen_weak (g : DijkstraGeneralGraph) (popped dist: list VType) (dst u : VType) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m, vvalid g m ->
            In m popped ->
            m <> u ->
            careful_add
              (Znth m dist)
              (Znth dst (Znth m (graph_to_mat g))) = inf.
                                                           
Definition dijkstra_correct (g : DijkstraGeneralGraph) src popped prev dist : Prop :=
  forall dst,
    vvalid g dst ->
    inv_popped g src popped prev dist dst /\
    inv_unpopped g src popped prev dist dst /\
    inv_unseen g popped dist dst.

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: DijkstraGeneralGraph, arr : pointer_val,
                                   dist : pointer_val, prev : pointer_val, src : VType
  PRE [tptr (tarray tint SIZE), tint, tptr tint, tptr tint]
   PROP (0 <= src < SIZE;
        Forall (fun list => Zlength list = SIZE) (graph_to_mat g);
        inrange_graph g;
        sound_dijk_graph g;
        forall i, vvalid g i ->
                  Znth i (Znth i (graph_to_mat g)) = 0)
   PARAMS (pointer_val_val arr;
          Vint (Int.repr src);
          pointer_val_val dist;
          pointer_val_val prev)
   GLOBALS ()
   SEP (DijkGraph sh g (pointer_val_val arr);
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val dist);
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val prev))
  POST [tvoid]
   EX prev_contents : list VType,
   EX dist_contents : list VType,
   EX popped_verts: list VType,                             
   PROP (dijkstra_correct g src popped_verts prev_contents dist_contents)
   LOCAL ()
   SEP (DijkGraph sh g (pointer_val_val arr);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist)).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     adjustWeight_spec;
                     popMin_spec;
                     dijkstra_spec]).
