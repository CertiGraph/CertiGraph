(* A separate file with the underlying PQ spec-ed out *)
Require Import CertiGraph.priq.priq_arr_specs.

(* Dijkstra-specific stuff *)
Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.SpaceDijkGraph.
Require Import CertiGraph.dijkstra.path_cost.

Local Open Scope Z_scope.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition path_correct (g : DijkGG) (prev dist: list V) src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost g p < inf /\ 
  Znth dst dist = path_cost g p /\
  Forall (fun x => Znth (snd x) prev = fst x) (snd p).

Definition path_globally_optimal (g : DijkGG) src dst p : Prop :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost g p <= path_cost g p'.

Definition path_in_popped (g : DijkGG) popped p :=
  forall step, In_path g step p ->
               In step popped.

Definition inv_popped (g : DijkGG) src (popped prev dist : list V) dst :=
  In dst popped ->
  (Znth dst dist = inf /\ (* if I'm unreachable *)
   (forall p, (* I'm unreachable via all paths *)
       valid_path g p ->
       path_ends g p src dst ->
       path_cost g p >= inf))
  \/
  (exists p, (* else, I'm optimal *)
      path_correct g prev dist src dst p /\
      path_in_popped g popped p /\
      path_globally_optimal g src dst p).

Definition inv_unpopped (g : DijkGG) src (popped prev dist: list V) (dst: V) :=
  ~ In dst popped ->
  Znth dst dist < inf ->
  dst = src \/
  (dst <> src /\
   let mom := Znth dst prev in
   vvalid g mom /\
   In mom popped /\
   elabel g (mom, dst) < inf /\
   Znth mom dist + elabel g (mom, dst) < inf /\
   Znth dst dist = Znth mom dist + elabel g (mom, dst) /\
   forall mom',
     vvalid g mom' ->
     In mom' popped ->
     Znth dst dist <= Znth mom' dist + elabel g (mom', dst)).

Definition inv_unpopped_weak (g : DijkGG) (src: V) (popped prev dist : list V) (dst u : V) :=
  ~ In dst popped ->
  Znth dst dist < inf ->
  dst = src \/
  dst <> src /\
  (let mom := Znth dst prev in
   mom <> u /\
   vvalid g mom /\
   In mom popped /\
   (elabel g (mom, dst)) < inf /\
   Znth mom dist + elabel g (mom, dst) < inf /\
   Znth dst dist = Znth mom dist + (elabel g (mom, dst))) /\
  forall mom',
    mom' <> u ->
    vvalid g mom' ->
    In mom' popped ->
    Znth dst dist <= Znth mom' dist + elabel g (mom', dst).
  
Definition inv_unseen (g : DijkGG) (src: V) (popped prev dist: list V) (dst : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m p2m,
    vvalid g m ->
    In m popped ->
    path_correct g prev dist src m p2m ->
    path_cost g (path_glue p2m (m, [(m, dst)])) >= inf.

Definition inv_unseen_weak (g : DijkGG) (src: V) (popped prev dist: list V) (dst u : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m p2m,
    vvalid g m ->
    In m popped ->
    m <> u ->
    path_correct g prev dist src m p2m ->
    path_cost g (path_glue p2m (m, [(m, dst)])) >= inf.
                                                           
Definition dijkstra_correct (g : DijkGG) src popped prev dist : Prop :=
  forall dst,
    vvalid g dst ->
    inv_popped g src popped prev dist dst /\
    inv_unpopped g src popped prev dist dst /\
    inv_unseen g src popped prev dist dst.

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare,
       g: DijkGG,
       graph_ptr : pointer_val,
       dist_ptr : pointer_val,
       prev_ptr : pointer_val,
       src : V
  PRE [tptr (tarray tint SIZE), tint, tptr tint, tptr tint]
  PROP (0 <= src < SIZE;
       Forall (fun list => Zlength list = SIZE) (@graph_to_mat SIZE g id))
  PARAMS (pointer_val_val graph_ptr;
         Vint (Int.repr src);
         pointer_val_val dist_ptr;
         pointer_val_val prev_ptr)
  GLOBALS ()
  SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr);
      data_at_ Tsh (tarray tint SIZE) (pointer_val_val dist_ptr);
      data_at_ Tsh (tarray tint SIZE) (pointer_val_val prev_ptr))
  POST [tvoid]
   EX prev: list V,
   EX dist : list V,
   EX popped : list V,                             
   PROP (forall dst,
            vvalid g dst ->
            inv_popped g src popped prev dist dst)
   LOCAL ()
   SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr)).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     adjustWeight_spec;
                     popMin_spec;
                     dijkstra_spec]).
