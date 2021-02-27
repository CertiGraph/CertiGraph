Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.

Local Open Scope Z_scope.

Section DijkstraSpecPure.

  Context {size : Z}.
  Context {inf : Z}.
  Context {V_EqDec : EquivDec.EqDec V eq}. 
  Context {E_EqDec : EquivDec.EqDec E eq}. 

  Definition acyclic_path (g: @DijkGG size inf) p := NoDup (epath_to_vpath g p).

  Lemma NoDup_one: forall A (n: A), NoDup [n].
  Proof.
    intros. apply NoDup_cons. 
    inversion 1. apply NoDup_nil.
  Qed.
        
  Lemma acyclic_nil_path:
    forall g p, acyclic_path g (p, []).
  Proof.
    intros. unfold acyclic_path. simpl.
    apply NoDup_one.
  Qed.

  Definition connected_dir (g: @DijkGG size inf) src :=
    forall v,
      vvalid g v ->
      exists p, path_ends g p src v /\ valid_path g p /\ path_cost g p < inf.
    
  Definition path_correct (g: @DijkGG size inf)
             (popped prev: list V) (dist: list Z) src dst p : Prop  :=
    valid_path g p /\
    (* I. II. add acyclic p here? 
       or... p's cost is bounded somehow
     *)
    path_ends g p src dst /\
    path_cost g p <= (Zlength popped - 1) * (Int.max_signed / size) /\ 
    Znth dst dist = path_cost g p /\
    Forall (fun (x: E) => Znth (snd x) prev = fst x) (snd p) /\
    acyclic_path g p.

  Definition path_globally_optimal (g: @DijkGG size inf) src dst p : Prop :=
    forall p', valid_path g p' ->
               path_ends g p' src dst ->
               path_cost g p <= path_cost g p'.

  Definition path_in_popped (g: @DijkGG size inf) popped p :=
    forall step, In_path g step p ->
                 In step popped.

  Definition inv_popped (g: DijkGG) src (popped prev: list V) (dist: list Z) dst :=
    In dst popped ->
    (Znth dst dist = inf /\ (* if I'm unreachable *)
     (forall p, (* no valid path connects src to me *)
         path_ends g p src dst ->
         ~ valid_path g p))
    \/
    (exists p, (* else, I'm optimal *)
        path_correct g popped prev dist src dst p /\
        path_in_popped g popped p /\
        path_globally_optimal g src dst p).

  Definition inv_unpopped (g : @DijkGG size inf) src
             (popped prev: list V) (dist: list Z) (dst: V) :=
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

  Definition inv_unpopped_weak (g : @DijkGG size inf) (src: V)
             (popped prev: list V) (dist: list Z) (dst u : V) :=
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
  
  Definition inv_unseen (g : DijkGG) (src: V)
             (popped prev: list V) (dist: list Z) (dst : V) :=
    ~ In dst popped ->
    Znth dst dist = inf ->
    forall m p2m,
      vvalid g m ->
      (* I. acyclic p2m -> *)
      In m popped ->
      path_correct g popped prev dist src m p2m ->
      ~ valid_path g (path_glue p2m (m, [(m, dst)])).
  (* II. path_cost (path_glue p2m (m, [(m, dst)])) >= inf *)

  (* p2m has size-2 edges at most
     (path_glue p2m (m, [(m, dst)])) has size-1 at most *)
  (* every path has an acyclic subpath that still connects src to dst *)
  

  Definition inv_unseen_weak (g : DijkGG) (src: V)
             (popped prev: list V) (dist: list Z) (dst u : V) :=
    ~ In dst popped ->
    Znth dst dist = inf ->
    forall m p2m,
      vvalid g m ->
      In m popped ->
      m <> u ->
      path_correct g popped prev dist src m p2m ->
      ~ valid_path g (path_glue p2m (m, [(m, dst)])). 

  Definition dijkstra_correct (g : DijkGG) src popped prev dist : Prop :=
    forall dst,
      vvalid g dst ->
      inv_popped g src popped prev dist dst /\
      inv_unpopped g src popped prev dist dst /\
      inv_unseen g src popped prev dist dst.

End DijkstraSpecPure.
