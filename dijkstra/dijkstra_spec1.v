Require Import CertiGraph.graph.SpaceAdjMatGraph1.
Require Import CertiGraph.dijkstra.dijkstra_env.

(* A separate file with the underlying PQ spec-ed out *)
Require Export CertiGraph.binheap.binary_heap_malloc_spec.
Require Export CertiGraph.binheap.spec_binary_heap_pro.

(* Dijkstra-specific imports *)
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Export CertiGraph.dijkstra.dijkstra_spec_pure.

(* The first moment we become implementation-specific *)
Require Export CertiGraph.dijkstra.dijkstra1.

Local Open Scope Z_scope.

Section DijkstraSpec.

  Context {size : Z}.
  Context {inf : Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.

  Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.
  Global Existing Instance CompSpecs.

  (*
  Definition freeN_spec {CS: compspecs} :=
    DECLARE _freeN
    WITH sh: share, p: pointer_val, n: Z, contents: list Z
    PRE [tptr tvoid]
    PROP ()
    PARAMS (pointer_val_val p)
    GLOBALS ()
    SEP (data_at sh (tarray tint n)
                 (map Vint (map Int.repr contents))
                 (pointer_val_val p) *
        free_tok (pointer_val_val p) (sizeof tint * n))
  POST [tvoid]
    PROP () LOCAL () SEP (emp).
   *)
  
  Definition getCell_spec :=
    DECLARE _getCell
    WITH sh: wshare,
         g: @DijkGG size inf,
         graph_ptr: pointer_val,
         addresses: list val,
         u: V,
         i : V
    PRE [tptr (tptr tint), tint, tint]
      PROP (0 <= i < size;
            0 <= u < size)
      PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
      GLOBALS ()
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g 
                             (pointer_val_val graph_ptr) addresses)
    POST [tint]
      PROP ()
      RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_mat size g id))))) 
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g 
                             (pointer_val_val graph_ptr) addresses).    
  
  Definition dijkstra_spec :=
    DECLARE _dijkstra
    WITH sh: wshare,
         g: DijkGG,
         graph_ptr : pointer_val,
         addresses : list val,
         dist_ptr : pointer_val,
         prev_ptr : pointer_val,
         src : V
    PRE [tptr (tptr tint), tint, tptr tint, tptr tint, tint, tint]
      PROP (0 <= src < size;
           Forall (fun list => Zlength list = size) (@graph_to_mat size g id);
           12 * size <= Int.max_unsigned)
      PARAMS (pointer_val_val graph_ptr;
             Vint (Int.repr src);
             pointer_val_val dist_ptr;
             pointer_val_val prev_ptr;
             Vint (Int.repr size);
             Vint (Int.repr inf))
      GLOBALS ()
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g 
                             (pointer_val_val graph_ptr) addresses;
          data_at_ Tsh (tarray tint size) (pointer_val_val dist_ptr);
          data_at_ Tsh (tarray tint size) (pointer_val_val prev_ptr))
    POST [tvoid]
      EX prev: list V,
      EX dist: list V,
      EX popped: list V,                             
      PROP (forall dst,
               vvalid g dst ->
               @inv_popped size inf g src popped prev dist dst)
      LOCAL ()
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g 
                             (pointer_val_val graph_ptr) addresses;
          data_at Tsh (tarray tint size) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
          data_at Tsh (tarray tint size) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr)).

  Definition Gprog : funspecs :=
    ltac:(with_library prog [
                       getCell_spec;
                       dijkstra_spec;
                       mallocN_spec;
                       freeN_spec;
                       pq_remove_min_nc_spec;
                       pq_insert_nc_spec; 
                       pq_size_spec;
                       pq_make_spec;
                       pq_edit_priority_spec;
                       pq_free_spec]).



End DijkstraSpec.
