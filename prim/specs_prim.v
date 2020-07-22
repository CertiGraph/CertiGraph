Require Import VST.floyd.proofauto.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.graph.AdjMatGraph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.prim.spatial_undirected_matrix.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope Z_scope.

Definition init_list_spec :=
  DECLARE _initialise_list
  WITH sh: share, arr : val, old_list: list val, a: Z
  PRE [tptr tint, tint]
     PROP ( writable_share sh;
            Zlength old_list = SIZE; (*<--I'm not sure if this is derivable from SEP*)
            repable_signed a
          )
     PARAMS ( arr; Vint (Int.repr a) )
     GLOBALS ()
     SEP (data_at sh (tarray tint SIZE) (old_list) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr a))) arr
         ).

Definition init_matrix_spec :=
  DECLARE _initialise_matrix
  WITH sh: share, arr : val, old_contents: list (list Z), a: Z
  PRE [tptr (tarray tint SIZE), tint]
     PROP ( writable_share sh;
            Zlength old_contents = SIZE;
            forall row, In row old_contents -> Zlength row = SIZE;
            repable_signed a
          )
     PARAMS ( arr ; Vint (Int.repr a) )
     GLOBALS ()
     SEP (undirected_matrix sh (old_contents) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (undirected_matrix sh (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) a)) arr
         ).

Definition prim_spec :=
  DECLARE _prim
  WITH sh: wshare, g: G, gptr : pointer_val, r: Z, mstptr : pointer_val
  PRE [tptr (tarray tint SIZE), tint, tptr (tarray tint SIZE)]
     PROP ( connected_graph g; (*prim's can only work on a connected graph with no disjoint components*)
            vvalid g r
          )
     PARAMS ( pointer_val_val gptr; (Vint (Int.repr r)); pointer_val_val mstptr)
     GLOBALS ()
     SEP (undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
          undirected_matrix sh (graph_to_symm_mat (@edgeless_graph inf SIZE SIZE_rep)) (pointer_val_val mstptr)
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
