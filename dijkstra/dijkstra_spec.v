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

Definition path_correct inf size (g : (DijkGG inf size)) (prev dist: list V) src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost inf size g p < inf /\ 
  Znth dst dist = path_cost inf size g p /\
  Forall (fun x => Znth (snd x) prev = fst x) (snd p).

Definition path_globally_optimal inf size (g : (DijkGG inf size)) src dst p : Prop :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost inf size g p <= path_cost inf size g p'.

Definition path_in_popped inf size (g : (DijkGG inf size)) popped p :=
  forall step, In_path g step p ->
               In step popped.

Definition inv_popped inf size (g : (DijkGG inf size)) src (popped prev dist : list V) dst :=
  In dst popped ->
  (Znth dst dist = inf /\ (* if I'm unreachable *)
   (forall p, (* I'm unreachable via all paths *)
       valid_path g p ->
       path_ends g p src dst ->
       path_cost inf size g p >= inf))
  \/
  (exists p, (* else, I'm optimal *)
      path_correct inf size g prev dist src dst p /\
      path_in_popped inf size g popped p /\
      path_globally_optimal inf size g src dst p).

Definition inv_unpopped inf size (g : (DijkGG inf size)) src (popped prev dist: list V) (dst: V) :=
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

Definition inv_unpopped_weak inf size (g : (DijkGG inf size)) (src: V) (popped prev dist : list V) (dst u : V) :=
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
  
Definition inv_unseen inf size (g : (DijkGG inf size)) (src: V) (popped prev dist: list V) (dst : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m p2m,
    vvalid g m ->
    In m popped ->
    path_correct inf size g prev dist src m p2m ->
    path_cost inf size g (path_glue p2m (m, [(m, dst)])) >= inf.

Definition inv_unseen_weak inf size (g : (DijkGG inf size)) (src: V) (popped prev dist: list V) (dst u : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m p2m,
    vvalid g m ->
    In m popped ->
    m <> u ->
    path_correct inf size g prev dist src m p2m ->
    path_cost inf size g (path_glue p2m (m, [(m, dst)])) >= inf.
                                                           
Definition dijkstra_correct inf size (g : (DijkGG inf size)) src popped prev dist : Prop :=
  forall dst,
    vvalid g dst ->
    inv_popped inf size g src popped prev dist dst /\
    inv_unpopped inf size g src popped prev dist dst /\
    inv_unseen inf size g src popped prev dist dst.

Definition getCell_spec inf size :=
  DECLARE _getCell
  WITH sh: wshare,
       g: (DijkGG inf size),
       graph_ptr: pointer_val,
       u: V,
       i : V
  PRE [tptr (tptr tint), tint, tint]
  PROP (0 <= i < size;
       0 <= u < size)
  PARAMS (pointer_val_val graph_ptr;
         Vint (Int.repr u);
         Vint (Int.repr i))
  GLOBALS ()
  SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size)
  POST [tint]
  PROP ()
  RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_mat size g id))))) 
  SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size).    

Definition dijkstra_spec inf size :=
  DECLARE _dijkstra
  WITH sh: wshare,
       g: (DijkGG inf size),
       graph_ptr : pointer_val,
       dist_ptr : pointer_val,
       prev_ptr : pointer_val,
       src : V
  PRE [tptr (tptr tint), tint, tptr tint, tptr tint, tint, tint]
  PROP (0 <= src < size;
       Forall (fun list => Zlength list = size) (@graph_to_mat size g id))
  PARAMS (pointer_val_val graph_ptr;
         Vint (Int.repr src);
         pointer_val_val dist_ptr;
         pointer_val_val prev_ptr;
         Vint (Int.repr size);
         Vint (Int.repr inf))
  GLOBALS ()
  SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size;
      data_at_ Tsh (tarray tint size) (pointer_val_val dist_ptr);
      data_at_ Tsh (tarray tint size) (pointer_val_val prev_ptr))
  POST [tvoid]
   EX prev: list V,
   EX dist : list V,
   EX popped : list V,                             
   PROP (forall dst,
            vvalid g dst ->
            inv_popped inf size g src popped prev dist dst)
   LOCAL ()
   SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr) size;
       data_at Tsh (tarray tint size) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
       data_at Tsh (tarray tint size) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr)).

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
     (* SEP (memory_block sh n (pointer_val_val v)). *)

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

Definition Gprog inf size : funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     adjustWeight_spec;
                     popMin_spec;
                     mallocN_spec;
                     (* freeN_spec; *)
                     getCell_spec inf size;
                     dijkstra_spec inf size]).
