(* A separate file with the underlying PQ spec-ed out *)
(* Require Import CertiGraph.priq.priq_arr_specs. *)

(* Dijkstra-specific stuff *)
Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.SpaceDijkGraph.
Require Import CertiGraph.dijkstra.path_cost.

Local Open Scope Z_scope.

(*
Definition get_popped pq : list VType :=
  map snd (filter (fun x => (fst x) =? (inf + 1))
                  (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))).
 *)

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

Definition path_in_popped (g : DijkGG) popped dist path :=
  forall step, In_path g step path ->
               In step popped /\ Znth step dist < inf.

Definition inv_popped (g : DijkGG) src (popped prev dist : list V) dst :=
  In dst popped ->
  ((* the first unreachable vertex has been popped.
      the invariant is unaware of this, but this 
      means that we will break *)   
    Znth dst dist = inf /\     
   (forall m,
     vvalid g m -> 
     (Znth m dist + elabel g (m, dst) >= inf) /\
     (~ In m popped -> Znth m dist = inf)))
  \/
  (exists path,
      path_correct g prev dist src dst path /\
      path_in_popped g popped dist path /\
      path_globally_optimal g src dst path).

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
  
Definition inv_unseen (g : DijkGG) (popped dist: list V) (dst : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m, vvalid g m ->
            In m popped ->
            Znth m dist + elabel g (m, dst) >= inf.

Definition inv_unseen_weak (g : DijkGG) (popped dist: list V) (dst u : V) :=
  ~ In dst popped ->
  Znth dst dist = inf ->
  forall m, vvalid g m ->
            In m popped ->
            m <> u ->
            Znth m dist + elabel g (m, dst) >= inf.
                                                           
Definition dijkstra_correct (g : DijkGG) src popped prev dist : Prop :=
  forall dst,
    vvalid g dst ->
    inv_popped g src popped prev dist dst /\
    inv_unpopped g src popped prev dist dst /\
    inv_unseen g popped dist dst.

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
   PROP (dijkstra_correct g src popped prev dist)
   LOCAL ()
   SEP (DijkGraph sh CompSpecs g (pointer_val_val graph_ptr);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev)) (pointer_val_val prev_ptr);
       data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist)) (pointer_val_val dist_ptr)).

Definition push_spec push :=
  DECLARE push
  WITH pq: val, vertex : Z, weight : Z, priq_contents_val: list val
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE;
       weight_inrange_priq weight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr weight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) priq_contents_val pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                         priq_contents_val (Vint (Int.repr weight))) pq).
    
Definition pq_emp_spec pq_emp := 
  DECLARE pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents)
   PARAMS (pq)
   GLOBALS ()
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (isEmpty priq_contents))
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq).

Definition adjustWeight_spec adjustWeight :=
  DECLARE adjustWeight
  WITH pq: val, vertex : Z, newWeight : Z, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE;
       weight_inrange_priq newWeight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr newWeight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                  (map Vint (map Int.repr priq_contents)) (Vint (Int.repr newWeight))) pq).

Definition popMin_spec popMin :=
  DECLARE popMin
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents;
        isEmpty priq_contents = Vzero)
   PARAMS (pq)
   GLOBALS ()
   SEP   (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   EX rt : Z,
   PROP (rt = priq_arr_utils.find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
   LOCAL (temp ret_temp  (Vint (Int.repr rt)))
   SEP   (data_at Tsh (tarray tint SIZE) (upd_Znth
                                            (priq_arr_utils.find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
                                            (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec _push;
                     pq_emp_spec _pq_emp;
                     adjustWeight_spec _adjustWeight;
                     popMin_spec _popMin;
                     dijkstra_spec]).
