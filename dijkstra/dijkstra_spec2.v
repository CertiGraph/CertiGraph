Require Import CertiGraph.graph.SpaceAdjMatGraph2.
Require Import CertiGraph.dijkstra.dijkstra_env.

(* A separate file with the underlying PQ spec-ed out *)
Require Export CertiGraph.priq.priq_arr_specs.

(* Dijkstra-specific imports *)
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Export CertiGraph.dijkstra.dijkstra_spec_pure.

(* The first moment we become implementation-specific *)
Require Export CertiGraph.dijkstra.dijkstra2.
Require Import CertiGraph.dijkstra.dijkstra_constants.

Local Open Scope Z_scope.

Section DijkstraSpec.

  Context {Z_EqDec : EquivDec.EqDec Z eq}.
  
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
    PRE [tptr tint, tint, tint]
      PROP (0 <= i < size;
           0 <= u < size;
           Forall (fun list => Zlength list = size) (@graph_to_mat size g id);
           (size * size <= Int.max_signed))
      PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
      GLOBALS ()
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g (pointer_val_val graph_ptr))
    POST [tint]
      PROP ()
      RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_mat size g id))))) 
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g (pointer_val_val graph_ptr)).
  
  Definition dijkstra_spec :=
    DECLARE _dijkstra
    WITH sh: wshare,
         g: DijkGG,
         graph_ptr : pointer_val,
         addresses : list val,
         dist_ptr : pointer_val,
         prev_ptr : pointer_val,
         src : V
    PRE [tptr tint, tint, tptr tint, tptr tint]
    
      PROP (0 <= src < size;
           Forall (fun list => Zlength list = size) (@graph_to_mat size g id);
           (size * size <= Int.max_signed))
      PARAMS (pointer_val_val graph_ptr;
             Vint (Int.repr src);
             pointer_val_val dist_ptr;
             pointer_val_val prev_ptr)
      GLOBALS ()
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g (pointer_val_val graph_ptr);
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
      SEP (@SpaceAdjMatGraph size CompSpecs sh id g (pointer_val_val graph_ptr);
          data_at Tsh (tarray tint size) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
          data_at Tsh (tarray tint size) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr)).
  
  Definition Gprog : funspecs :=
    ltac:(with_library prog
                       [(@init_spec size _);
                       (@push_spec size inf _);
                       (@pq_emp_spec size inf _);
                       (@adjustWeight_spec size inf _);
                       (@popMin_spec size inf Z_EqDec _);
                       freePQ_spec;
                       getCell_spec;
                       dijkstra_spec]).

End DijkstraSpec.
