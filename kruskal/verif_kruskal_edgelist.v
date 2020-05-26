Require Import VST.floyd.proofauto.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
(*are these needed?*)
Require Import RamifyCoq.graph.path_lemmas. (*yes, because ufgraph relies on it*)
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
(*for unionfind*)
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
(*edgelist*)
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
(*spanning tree definition*)
Require Import RamifyCoq.kruskal.mst.
Require Import RamifyCoq.kruskal.kruskal_uf_specs.
(*Require Import RamifyCoq.graph.spanning_tree.*)

Local Open Scope Z_scope.

(*I guess we ought to throw these in a specs_kruskal.v
Also, thinking of we can combine env and spatial*)

Lemma numE_pos: forall g, 0 <= numE g.
Proof.
  intros. unfold numE. apply Zlength_nonneg.
Qed.

Lemma g2wedgelist_numE:
  forall g,
    Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist.
  rewrite Zlength_map. trivial.
Qed.

Lemma numE_range:
  forall g,
    numE g <= MAX_EDGES ->
    Int.min_signed <= numE g <= Int.max_signed.
Proof.
  intros.
  pose proof (numE_pos g).
  unfold MAX_EDGES in H.
  assert (Int.min_signed <= 0) by now compute.
  assert (8 <= Int.max_signed) by now compute.
  lia.
Qed.

Lemma numE_pred_range:
  forall g,
    numE g <= MAX_EDGES ->
    Int.min_signed <= numE g - 1 <= Int.max_signed.
Proof.
  intros.
  pose proof (numE_pos g).
  unfold MAX_EDGES in H.
  assert (Int.min_signed <= -1) by now compute.
  assert (7 <= Int.max_signed) by now compute.
  lia.
Qed.

Lemma body_init_empty_graph: semax_body Vprog Gprog f_init_empty_graph init_empty_graph_spec.
Proof.
start_function.
forward_call (sh, sizeof t_wedgearray_graph).
set (j := Int.max_unsigned) in *; compute in j; subst j. simpl; lia.
Intros gptr.
assert (memory_block sh (sizeof t_wedgearray_graph) (pointer_val_val gptr) =
        data_at_ sh (t_wedgearray_graph) (pointer_val_val gptr)). {
  rewrite <- memory_block_data_at_; auto.
} rewrite H0. clear H0.
assert (data_at_ sh t_wedgearray_graph (pointer_val_val gptr) =
        data_at sh t_wedgearray_graph (Vundef,(Vundef,Vundef)) (pointer_val_val gptr)). {
  unfold data_at_, field_at_, data_at.
  assert (default_val (nested_field_type t_wedgearray_graph []) = (Vundef,(Vundef,Vundef))) by reflexivity.
  rewrite H0. auto.
} rewrite H0. clear H0. (*that was easier than I thought :]*)
forward.
forward_call (sh, MAX_EDGES*(sizeof t_struct_edge)).
set (j := Int.max_unsigned) in *; compute in j; subst j. simpl; lia.
Intros eptr.
assert (memory_block sh (MAX_EDGES * (sizeof t_struct_edge)) (pointer_val_val eptr) = data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr)). {
  assert (memory_block sh (MAX_EDGES*(sizeof t_struct_edge)) (pointer_val_val eptr) = memory_block sh (sizeof (tarray t_struct_edge MAX_EDGES)) (pointer_val_val eptr)). {
    simpl. auto.
  } rewrite <- memory_block_data_at_; auto.
} rewrite H1. clear H1.
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr) = data_at sh (tarray t_struct_edge MAX_EDGES) (list_repeat (Z.to_nat MAX_EDGES) (Vundef, (Vundef, Vundef))) (pointer_val_val eptr)). {
  unfold data_at_, field_at_, data_at. assert (default_val (nested_field_type (tarray t_struct_edge MAX_EDGES) []) = list_repeat (Z.to_nat MAX_EDGES) (Vundef, (Vundef, Vundef))) by reflexivity.
  rewrite H1. auto.
} rewrite H1. clear H1.
forward.
forward.
forward.
forward.
forward.
Exists gptr eptr.
unfold wedgearray_graph_rep.
rewrite empty_WEdgeListGraph_numV. rewrite empty_WEdgeListGraph_numE.
simpl. rewrite data_at_zero_array_eq. entailer!.
reflexivity. apply H4. rewrite empty_WEdgeListGraph_graph_to_wedgelist. simpl. reflexivity.
Qed.

Lemma body_kruskal: semax_body Vprog Gprog f_kruskal kruskal_spec.
Proof.
  start_function.
  unfold wedgearray_graph_rep. Intros.
  forward. forward. 
  forward_call (sh, (numV g)).
  Intros subsets.
  forward_call (gv, sh).
  Intros mst.
  destruct subsets as [subsetsGraph subsetsPtr].
  destruct mst as [gptr eptr].
  simpl fst in *. simpl snd in *.
  unfold wedgearray_graph_rep. Intros.
  forward.
  forward.
  forward_call ((wshare_share sh), 
                pointer_val_val orig_eptr,
                (Int.repr 0),
                (Int.repr ((numE g) - 1)),
                (@nil wedgerep),
                (map wedge_to_cdata (graph_to_wedgelist g)),
                (@nil wedgerep)).
  - rewrite Int.signed_repr.
    2: apply numE_range; trivial.
    rewrite Int.signed_repr.
    2: compute; split; inversion 1.
    apply numE_pred_range; trivial.
  - rewrite app_nil_r, app_nil_l, Zlength_map, g2wedgelist_numE.
    entailer!.
  - split3; [| |split3]; trivial.
    + rewrite app_nil_r, app_nil_l, Zlength_map.
      rewrite g2wedgelist_numE.
      apply numE_range; trivial.
    + destruct (zlt (Int.signed (Int.repr 0)) (Int.signed (Int.repr (numE g - 1)))).
      * split3; trivial.
        -- rewrite app_nil_r, app_nil_l, Zlength_map, g2wedgelist_numE.
           rewrite Int.signed_repr.
           2: apply numE_pred_range; trivial.
           rewrite Zlength_nil. lia.
        -- rewrite Zlength_map.
           rewrite g2wedgelist_numE.
           rewrite Int.signed_repr.
           2: apply numE_pred_range; trivial.
           rewrite Int.signed_repr.
           2: compute; split; inversion 1.
           lia.
      * admit.
        (* something is wrong... from g0 I can show that 
           numE is 0 or 1. But that's not enough to 
           prove the goal. 
         *)
    + rewrite Forall_forall. intros.
      apply list_in_map_inv in H3.
      destruct H3 as [? [? _]].
      unfold wedge_to_cdata in H3.
      unfold def_wedgerep.
      exists (Int.repr (fst x0)),
      (Int.repr (fst (snd x0))),
      (Int.repr (snd (snd x0))).
      split; trivial.
      split3; apply Int.signed_range.
  - Intros sorted.
Abort.



(*
Idea of proof:
int graph_V = graph->V;
int graph_E = graph->E;
struct subset *subsets = makeSet(graph_V); (*ufgraph with V vertices all distinct*)
struct graph *mst = init_empty_graph();

mst->V = graph_V; <-- mst is now a graph with V vertices and 0 edges

sort_edges(graph->edge_list,0,graph_E-1);

    //invariant: is_partial_graph mst orig_graph /\ uforest mst
    //   connected ufgraph u v <-> connected in mst (also connected ufgraph u v -> connected graph u v)
    // showing forest is a problem... need an easy-to-work-with definition
    // and something about minimum weight...
    //precon: mst has no edges, is a trivial subset, trivial forest. subsets are all disjoint
    for (int i = 0; i < graph_E; ++i) {

        int u = graph->edge_list[i].u;
        int v = graph->edge_list[i].v;

        int ufind = find(subsets, u);		//returned g' is: uf_root g' i rt
        int vfind = find(subsets, v);

        //need a join postcon?
        //ufind != vfind <-> not connected in mst
        //not_connected -> add edge -> no cycle <-- Need a lemma in undirected_graph.v
        //also show that edge here: minimum of all (u,v) edges
        if (ufind != vfind) {
            mst->edge_list[mst->E].u = u;
            mst->edge_list[mst->E].v = v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            mst->E += 1;
            Union(subsets, u, v);

            //mst = mst + (u,v), thus u,v are connected
            //ifcon (loopcon): is_partial_graph (mst + (u,v)) orig
            //mst is still uforest (using the needed lemma above)
            //same_subset(u,v) /\ u,v connected (*trivially <->*)
        }
        //need an elsecon?
        //uf_root p u -> reachable g u p -> connected p u (reachable_implies_connected)
        //connected p u -> connected p v -> connected u v (connected_trans)
    }
    //postcon

    //before free, need to prove that same_subset(u,v) <-> connected orig u v
    //from invariant, same_subset(u,v) <-> connected in mst
    //thus, connected in mst <-> connected in orig: spanning definition

    free(subsets);

    //worried about proving minimum
    return mst;

*)
