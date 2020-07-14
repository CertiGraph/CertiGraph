Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.dijkstra.env_dijkstra_arr.
Require Import RamifyCoq.dijkstra.MathDijkGraph.

Local Open Scope logic.

(* Specific to Adjacency Matrix representation *)

Class SpaceDijkGraph (Addr: Type) (Pred: Type) :=
  abstract_data_at: Addr -> list Z -> Pred.

Context {Pred: Type}.
Context {Addr: Type}.
Context {SDG : SpaceDijkGraph Addr Pred}.

(* Assumption: 
   For any vertex v,
       (v,0), (v,1) ... (v, SIZE-1)
   are edges.

   What it does: 
   Makes a list containing each edge's elabel.
 *)
Definition vert_to_list (g : DijkstraGeneralGraph) (v : VType) : list Z :=
  map (elabel g) (map (fun x => (v,x)) (nat_inc_list (Z.to_nat SIZE))).


(* Assumptions: 
   1. 0, 1, ... (SIZE-1) are vertices
   2. for any vertex v,
          (v,0), (v,1) ... (v, SIZE-1)
      are edges.

      What it does: 
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
 *)
Definition graph_to_mat (g : DijkstraGeneralGraph) : list (list Z) :=
  map (vert_to_list g) (nat_inc_list (Z.to_nat SIZE)).

Definition graph_to_list (g : DijkstraGeneralGraph) : list Z :=
  (concat (graph_to_mat g)).

(* Assumptions: 
   See above

   What it does: 
   Flattens the list of lists into one list, and then uses
    abstract_data_at to create a spatial representation.

   This is not currently used by SpaceDijkGraph because iter_sepcon 
   is cleaner. However, just keep it around because it is a general model.
 *)
Definition graph_rep (g : DijkstraGeneralGraph) (a : Addr)  :=
  abstract_data_at a (graph_to_list g).

                   
(* Helpers *)

Lemma graph_to_mat_Zlength: forall g, Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; auto. now vm_compute.
Qed.

Lemma elabel_Znth_graph_to_mat:
  forall g src dst,
    sound_dijk_graph g ->
    evalid g (src, dst) ->
    elabel g (src, dst) =
    Znth dst (Znth src (graph_to_mat g)).
Proof.
  intros. 
  unfold graph_to_mat.
  destruct H as [? [? _]].
  red in H, H1.
  rewrite H1 in H0; destruct H0. 
  rewrite H in H0, H2.
  rewrite Znth_map, nat_inc_list_i.
  unfold vert_to_list. rewrite Znth_map.
  rewrite Znth_map. rewrite nat_inc_list_i.
  reflexivity.
  3: rewrite Zlength_map.
  2, 3, 5: rewrite nat_inc_list_Zlength.
  all: rewrite Z2Nat.id; lia.
Qed.

Definition inrange_graph g :=
  let grph_contents := (graph_to_mat g) in
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
    Znth i (Znth j grph_contents) = inf.

Lemma inrange_graph_cost_pos: forall g e,
    sound_dijk_graph g -> inrange_graph g ->
    evalid g e -> 0 <= elabel g e.
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
