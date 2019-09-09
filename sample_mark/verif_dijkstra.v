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
  PRE [_graph OF (tptr (tarray tint 8)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
  PROP (0 <= src < 8)
  LOCAL (temp _graph (pointer_val_val arr);
         temp _src (Vint (Int.repr src));
         temp _dist (pointer_val_val dist);
         temp _prev (pointer_val_val prev))
  SEP (whole_graph sh g arr;
       data_at_ Tsh (tarray tint 8) (pointer_val_val dist);
       data_at_ Tsh (tarray tint 8) (pointer_val_val prev))
  POST [tvoid]
      EX prev : list Z, (* should probably go away *)
      PROP (dijkstra_correct g src prev)
      LOCAL ()
      SEP (whole_graph sh g arr).

Definition Gprog : funspecs := ltac:(with_library prog [dijkstra_spec]).

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    8
    (EX i : Z,
     PROP ()
     LOCAL (lvar _pq (tarray tint 8) v_pq; lvar _prev (tarray tint 8) v_prev;
            lvar _dist (tarray tint 8) v_dist;
            temp _src (Vint (Int.repr src));
           temp _j (Vint (Int.repr j)))
     SEP (data_at_ Tsh (tarray tint 8) v_pq *
          data_at_ Tsh (tarray tint 8) (pointer_val_val prev) *
          data_at_ Tsh (tarray tint 8) (v_prev) *
          data_at_ Tsh (tarray tint 8) (pointer_val_val dist) *
          data_at_ Tsh (tarray tint 8) (v_dist) *
          whole_graph sh g arr)).
  - entailer!.
  - Intros. do 3 forward. 2: forward; entailer!. 
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