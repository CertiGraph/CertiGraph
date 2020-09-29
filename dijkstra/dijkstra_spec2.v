(* A separate file with the underlying PQ spec-ed out *)
Require Import CertiGraph.priq_malloc.priq_arr_specs.

(* Dijkstra-specific stuff *)
Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.SpaceDijkGraph2.
Require Import CertiGraph.dijkstra.path_cost.
Require Import CertiGraph.dijkstra.dijkstra_spec_pure.


(* The first moment we become implementation-specific *)
Require Export CertiGraph.dijkstra.dijkstra2.
Require Import CertiGraph.dijkstra.dijkstra_constants.

Local Open Scope Z_scope.

Section DijkstraSpec.
  
  Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.
  Global Existing Instance CompSpecs.

  Definition getCell_spec :=
    DECLARE _getCell
    WITH sh: wshare,
         g: @DijkGG size inf,
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
      SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size addresses)
    POST [tint]
      PROP ()
      RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_mat size g id))))) 
      SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size addresses).    
  
  Definition dijkstra_spec :=
    DECLARE _dijkstra
    WITH sh: wshare,
         g: DijkGG,
         graph_ptr : pointer_val,
         addresses : list val,
         dist_ptr : pointer_val,
         prev_ptr : pointer_val,
         src : V
    PRE [tptr (tarray tint size), tint, tptr tint, tptr tint]
    
      PROP (0 <= src < size;
           Forall (fun list => Zlength list = size) (@graph_to_mat size g id))
      PARAMS (pointer_val_val graph_ptr;
             Vint (Int.repr src);
             pointer_val_val dist_ptr;
             pointer_val_val prev_ptr)
      GLOBALS ()
      SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size addresses;
          data_at_ Tsh (tarray tint size) (pointer_val_val dist_ptr);
          data_at_ Tsh (tarray tint size) (pointer_val_val prev_ptr))
    POST [tvoid]
      EX prev: list V,
      EX dist: list V,
      EX priq: list V,
      EX priq_ptr: pointer_val,
      EX popped: list V,                             
      PROP (forall dst,
               vvalid g dst ->
               @inv_popped size inf g src popped prev dist dst)
      LOCAL ()
      SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size addresses;
          data_at Tsh (tarray tint size) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
          data_at Tsh (tarray tint size) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr);
          data_at Tsh (tarray tint size) (map Vint (map Int.repr priq)) (pointer_val_val priq_ptr)).
  
  Definition mallocN_spec :=
    DECLARE _mallocN
    WITH sh:wshare, n: Z
    PRE [tint]
      PROP (4 <= n <= Int.max_unsigned)
      PARAMS (Vint (Int.repr n))
      GLOBALS ()
      SEP ()
    POST [ tptr tvoid ]
      EX v: pointer_val,
      PROP (malloc_compatible n (pointer_val_val v))
      LOCAL (temp ret_temp (pointer_val_val v))
      SEP (data_at_ Tsh (tarray tint (n / sizeof tint)) (pointer_val_val v)).

  (*Definition freeN_spec :=
  DECLARE _freeN
  WITH sh: share, p: pointer_val, n: Z, contents: list Z
    PRE [tptr tvoid]
    PROP ()
    PARAMS (pointer_val_val p)
    GLOBALS ()
    SEP (data_at sh (tarray tint n)
                 (map Vint (map Int.repr contents))
                 (pointer_val_val p))
  POST [tvoid]
    PROP () LOCAL () SEP (emp).
   *)

  Definition Gprog : funspecs :=
    ltac:(with_library prog
                       [push_spec;
                       pq_emp_spec;
                       adjustWeight_spec;
                       popMin_spec;
                       mallocN_spec;
                       (* freeN_spec; *)
                       getCell_spec;
                       dijkstra_spec]).

End DijkstraSpec.
