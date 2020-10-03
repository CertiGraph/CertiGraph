Require Import CertiGraph.floyd_ext.share.
Require Export CertiGraph.priq_malloc.priq_arr_specs.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.prim.MatrixUGraph.
Require Export CertiGraph.prim.prim3.
Require Import CertiGraph.prim.prim_constants.
Require Import CertiGraph.prim.spatial_undirected_matrix3.
Require Import CertiGraph.lib.List_ext.

Local Open Scope Z_scope.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section PrimSpec.


Definition getCell_spec :=
  DECLARE _getCell
  WITH g: G,
       graph_ptr: pointer_val,
       addresses: list val,
       u: V,
       i : V
  PRE [tptr (tarray tint size), tint, tint]
    PROP (0 <= i < size;
          0 <= u < size)
    PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
    GLOBALS ()
    SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (graph_to_symm_mat g) (pointer_val_val graph_ptr))
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr (Znth i (Znth u (graph_to_symm_mat g))))) 
    SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (graph_to_symm_mat g) (pointer_val_val graph_ptr)).    

Definition initialise_list_spec :=
  DECLARE _initialise_list
  WITH arr : val, old_list: list val, a: Z
  PRE [tptr tint, tint]
     PROP ( writable_share Tsh;
            repable_signed a
          )
     PARAMS ( arr; Vint (Int.repr a) )
     GLOBALS ()
     SEP (data_at Tsh (tarray tint size) (old_list) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at Tsh (tarray tint size) (list_repeat (Z.to_nat size) (Vint (Int.repr a))) arr
         ).

Definition initialise_matrix_spec :=
  DECLARE _initialise_matrix
  WITH arr : val, old_contents: list (list Z), a: Z
  PRE [tptr (tarray tint size), tint]
     PROP ( writable_share Tsh;
            Zlength old_contents = size;
            forall row, In row old_contents -> Zlength row = size;
            repable_signed a
          )
     PARAMS ( arr ; Vint (Int.repr a) )
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh old_contents arr)

     (* (undirected_matrix sh (old_contents) (arr)) *)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (list_repeat (Z.to_nat size) (list_repeat (Z.to_nat size) a)) arr).

     (* (undirected_matrix sh (list_repeat (Z.to_nat size) (list_repeat (Z.to_nat size) a)) arr *)

Definition prim_spec :=
  DECLARE _prim
  WITH g: G, garbage: list V, gptr : pointer_val, r: Z, parent_ptr : pointer_val
  PRE [tptr (tarray tint size), tint, tptr tint]
     PROP ( writable_share Tsh;
            vvalid g r
          )
     PARAMS ( pointer_val_val gptr; (Vint (Int.repr r)); pointer_val_val parent_ptr)
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (graph_to_symm_mat g) (pointer_val_val gptr); 

       (* undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr); *)
          data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) garbage) (pointer_val_val parent_ptr)
         )
  POST [ tvoid ]
     EX mst: G,
     EX fmst: FiniteGraph mst,
     EX parents: list V,
     PROP ( (*connected_graph mst;*)
            (@minimum_spanning_forest size inf mst g);
            Permutation (EList mst) (map (fun v => eformat (v, Znth v parents))
              (filter (fun v => Znth v parents <? size) (nat_inc_list (Z.to_nat size))))
          )
     RETURN ()
     SEP ((@SpaceAdjMatGraph' size CompSpecs Tsh (graph_to_symm_mat g) (pointer_val_val gptr));

       (* undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr); *)
          data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr)
         ).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [(@push_spec size inf _);
                     (@pq_emp_spec size inf _);
                     (@popMin_spec size inf _);
                     (@adjustWeight_spec size inf _);
                     (@init_spec size _);
                     freePQ_spec;
                     getCell_spec;
                     initialise_list_spec;
                     initialise_matrix_spec;
                     prim_spec
       ]).

End PrimSpec.
