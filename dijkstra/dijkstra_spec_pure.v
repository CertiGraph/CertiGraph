Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.path_cost.

Local Open Scope Z_scope.

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
