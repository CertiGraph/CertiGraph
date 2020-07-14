Require Import VST.floyd.proofauto.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.prim.spatial_undirected_matrix.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope Z_scope.

Definition init_matrix_spec :=
  DECLARE _initialise_matrix
  WITH sh: wshare, arr : pointer_val, old_contents: list (list Z)
  PRE [tptr (tarray tint SIZE)]
     PROP ()
     PARAMS ( pointer_val_val arr )
     GLOBALS ()
     SEP (undirected_matrix sh (old_contents) (pointer_val_val arr))
  POST [ tvoid ]
     EX g: MatrixUGraph,
     PROP ()
     LOCAL ()
     SEP (undirected_matrix sh (graph_to_mat g) (pointer_val_val arr)
         ).
