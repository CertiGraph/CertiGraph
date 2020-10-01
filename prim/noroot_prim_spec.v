Require Import CertiGraph.floyd_ext.share.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.priq.priq_arr_specs.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.lib.List_ext.

Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.prim.noroot_prim.
Require Import CertiGraph.prim.spatial_undirected_matrix.

Local Open Scope Z_scope.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition getCell_spec :=
  DECLARE _getCell
  WITH sh: wshare,
       g: G,
       graph_ptr: pointer_val,
       addresses: list val,
       u: V,
       i : V
  PRE [tptr (tarray tint SIZE), tint, tint]
    PROP (0 <= i < SIZE;
          0 <= u < SIZE)
    PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
    GLOBALS ()
    SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh (graph_to_symm_mat g) (pointer_val_val graph_ptr))
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_symm_mat g))))) 
    SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh (graph_to_symm_mat g) (pointer_val_val graph_ptr)).    

Definition initialise_list_spec :=
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

Definition initialise_matrix_spec :=
  DECLARE _initialise_matrix
  WITH sh: wshare, arr : val, old_contents: list (list Z), a: Z
  PRE [tptr (tarray tint SIZE), tint]
     PROP ( writable_share sh;
            Zlength old_contents = SIZE;
            forall row, In row old_contents -> Zlength row = SIZE;
            repable_signed a
          )
     PARAMS ( arr ; Vint (Int.repr a) )
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh old_contents arr)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) a)) arr).

Definition prim_spec :=
  DECLARE _prim
  WITH sh: wshare, g: G, garbage: list V, gptr : pointer_val, parent_ptr : pointer_val
  PRE [tptr (tarray tint SIZE), tptr tint]
     PROP ( writable_share sh
          )
     PARAMS ( pointer_val_val gptr; pointer_val_val parent_ptr)
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh (graph_to_symm_mat g) (pointer_val_val gptr);
          data_at sh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) garbage) (pointer_val_val parent_ptr)
         )
  POST [ tint ]
     EX mst: G,
     EX fmst: FiniteGraph mst,
     EX parents: list V,
     PROP ( (*connected_graph mst;*)
            minimum_spanning_forest mst g;
            Permutation (EList mst) (map (fun v => eformat (v, Znth v parents))
              (filter (fun v => Znth v parents <? SIZE) (nat_inc_list (Z.to_nat SIZE))))
          )
     RETURN (Vint (Int.repr 0))
     SEP (@SpaceAdjMatGraph' SIZE CompSpecs sh (graph_to_symm_mat g) (pointer_val_val gptr);
          data_at sh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr)
         ).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     popMin_spec;
                     adjustWeight_spec;
                     getCell_spec;
                     initialise_list_spec;
                     initialise_matrix_spec;
                     prim_spec
       ]).
