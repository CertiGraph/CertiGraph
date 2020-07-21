Require Import VST.floyd.proofauto.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.prim.spatial_undirected_matrix.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope Z_scope.

Definition init_list_spec :=
  DECLARE _initialise_list
  WITH sh: share, arr : pointer_val, old_list: list val
  PRE [tptr tint]
     PROP (Zlength old_list = SIZE (*<--I'm not sure if this is derivable from SEP*)
          )
     PARAMS ( pointer_val_val arr )
     GLOBALS ()
     SEP (data_at sh (tarray tint SIZE) (old_list) (pointer_val_val arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (pointer_val_val arr)
         ).

Definition init_matrix_spec :=
  DECLARE _initialise_matrix
  WITH sh: wshare, arr : pointer_val, old_contents: list (list Z)
  PRE [tptr (tarray tint SIZE)]
     PROP ( Zlength old_contents = SIZE;
            forall row, In row old_contents -> Zlength row = SIZE
          )
     PARAMS ( pointer_val_val arr )
     GLOBALS ()
     SEP (undirected_matrix sh (old_contents) (pointer_val_val arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (undirected_matrix sh (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) inf)) (pointer_val_val arr)
         ).

Definition prim_spec :=
  DECLARE _prim
  WITH sh: wshare, g: MatrixUGraph, gptr : pointer_val, r: Z, mstptr : pointer_val
  PRE [tptr (tarray tint SIZE), tint, tptr (tarray tint SIZE)]
     PROP (sound_undirected_matrix_graph g;
            connected_graph g; (*prim's can only work on a connected graph with no disjoint components*)
            vvalid g r
          )
     PARAMS ( pointer_val_val gptr; (Vint (Int.repr r)); pointer_val_val mstptr)
     GLOBALS ()
     SEP (undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
          undirected_matrix sh (graph_to_symm_mat (edgeless_graph SIZE)) (pointer_val_val mstptr)
         )
  POST [ tvoid ]
     EX mst: MatrixUGraph,
     PROP ( minimum_spanning_forest mst g;
            connected_graph mst
          )
     LOCAL ()
     SEP (undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
          undirected_matrix sh (graph_to_symm_mat mst) (pointer_val_val mstptr)
         ).

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [init_list_spec; init_matrix_spec; prim_spec
  ]).
