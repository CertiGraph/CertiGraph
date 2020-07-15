Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.dijkstra.env_dijkstra_arr.
Require Import RamifyCoq.dijkstra.MathDijkGraph.
Require Import RamifyCoq.graph.AdjMatGraph.

Local Open Scope logic.

(* Would be good to generalize these further and move them to AdjMatGraph. *)
Lemma graph_to_mat_Zlength_gen:
  forall g size,
    0 <= size ->
    Zlength (graph_to_mat_gen g size) = size.
Proof.
  intros. unfold graph_to_mat_gen.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; trivial.
Qed.

Lemma elabel_Znth_graph_to_mat_gen:
  forall (g: LabeledGraph VType EType LV LE LG) src dst size,
    0 <= size ->
    0 <= src < size ->
    0 <= dst < size ->
    elabel g (src, dst) =
    Znth dst (Znth src (graph_to_mat_gen g size)).
Proof.
  intros. 
  unfold graph_to_mat_gen.
  rewrite Znth_map, nat_inc_list_i.
  unfold vert_to_list. rewrite Znth_map.
  rewrite Znth_map. rewrite nat_inc_list_i.
  reflexivity.
  3: rewrite Zlength_map.
  2, 3, 5: rewrite nat_inc_list_Zlength.
  all: rewrite Z2Nat.id; trivial.
Qed.

Definition inrange_graph_gen g size :=
  let grph_contents := (graph_to_mat_gen g size) in
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / size \/
    Znth i (Znth j grph_contents) = inf.



(* Truly spatial stuff *)

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map Vint (map Int.repr mylist)) (list_address l index size).

Definition DijkGraph sh contents_graph gaddr : mpred :=
  iter_sepcon (list_rep sh SIZE gaddr contents_graph)
              (nat_inc_list (Z.to_nat (Zlength contents_graph))).

Lemma DijkGraph_unfold: forall sh contents ptr i,
    0 <= i < (Zlength contents) ->
    DijkGraph sh contents ptr =
    iter_sepcon (list_rep sh SIZE ptr contents)
                            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh SIZE ptr contents i *
     iter_sepcon (list_rep sh SIZE ptr contents)
                             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros. unfold DijkGraph.
  replace (nat_inc_list (Z.to_nat (Zlength contents))) with
      (sublist 0 (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents)))) at 1.
  2: { rewrite sublist_same; trivial.
       rewrite nat_inc_list_Zlength, Z2Nat_id', Z.max_r; trivial.
       apply Zlength_nonneg.
  }
  rewrite (sublist_split 0 i (Zlength contents)),
  (sublist_split i (i+1) (Zlength contents)), (sublist_one i); try lia.
  2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
  rewrite nat_inc_list_i.
  2: rewrite Z2Nat_id', Z.max_r; trivial; apply Zlength_nonneg. 
  repeat rewrite iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.


(* sugared version so as not to break Dijk *)
Definition graph_to_mat
           (g: LabeledGraph VType EType LV LE LG) : list (list LE) :=
  map (vert_to_list g SIZE) (nat_inc_list (Z.to_nat SIZE)).

Definition graph_to_list
           (g: LabeledGraph VType EType LV LE LG) : list LE :=
  (concat (graph_to_mat g)).

(* sugared version so as not to break Dijk *)
Definition inrange_graph g :=
  let grph_contents := (graph_to_mat g) in
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
    Znth i (Znth j grph_contents) = inf.

(* sugared version so as not to break Dijk *)
Lemma graph_to_mat_Zlength:
  forall g,
    Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; trivial.
  unfold SIZE; lia.
Qed.

(* sugared version so as not to break Dijk *)
 Lemma elabel_Znth_graph_to_mat:
   forall (g: DijkstraGeneralGraph) src dst,
     sound_dijk_graph g ->
     evalid g (src, dst) ->
     elabel g (src, dst) =
     Znth dst (Znth src (graph_to_mat (lg_gg g))).
 Proof.
   intros.
   destruct H as [? [? _]].
   red in H, H1. rewrite H1, H, H in H0. destruct H0.
   apply elabel_Znth_graph_to_mat_gen; trivial. lia.
 Qed.
 
 (* sugared version so as not to break Dijk *)
 Lemma inrange_graph_cost_pos: forall g e,
     sound_dijk_graph g ->
     inrange_graph g ->
     evalid g e ->
     0 <= elabel g e.
Proof.
  intros. rewrite (surjective_pairing e) in *.
  rewrite elabel_Znth_graph_to_mat; auto. destruct H as [? [? _]].
  red in H, H2.
  rewrite (surjective_pairing e) in H1.
  rewrite H2 in H1. red in H0.
  rewrite (graph_to_mat_Zlength g) in H0.
  simpl in H1. destruct H1. rewrite H in H1, H3.
  specialize (H0 _ _ H3 H1). destruct H0.
  1: destruct H0; lia.
  rewrite H0. compute; inversion 1. 
Qed.
