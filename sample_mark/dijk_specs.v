(** SPECS **)
Require Import VST.floyd.proofauto.
Require Import CertiGraph.sample_mark.priorityqueue.
Require Import CertiGraph.sample_mark.dijkstra.

Require Import CertiGraph.sample_mark.priq_utils.
Require Import CertiGraph.sample_mark.dijk_pq_arr_macros.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.msl_application.DijkstraArrayGraph.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.


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
        forall i, 0 <= i < SIZE ->
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

Definition Gprog : funspecs := ltac:(with_library prog [pq_emp_spec; popMin_spec; dijkstra_spec]).
