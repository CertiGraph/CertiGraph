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

Require Import RamifyCoq.kruskal.undirected_graph.

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

Lemma Permutation_Zlength:
  forall (A : Type) (l l' : list A),
    Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros.
  rewrite Zlength_length; [| apply Zlength_nonneg].
  rewrite Zlength_correct, Nat2Z.id.
  apply Permutation_length; trivial.
Qed.

Lemma def_wedgerep_map_w2c:
  forall g,
    Forall def_wedgerep (map wedge_to_cdata (graph_to_wedgelist g)).
Proof.
  intros.
  rewrite Forall_forall; intros.
  apply list_in_map_inv in H.
  destruct H as [? [? _]].
  unfold wedge_to_cdata in H.
  unfold def_wedgerep.
  rewrite (surjective_pairing x) in *.
  inversion H; clear H.
  destruct x.
  rewrite (surjective_pairing c) in *.
  simpl fst in *; simpl snd in *.
  inversion H2; clear H2.
  rewrite H1, H0, H3. split3; trivial.
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

Lemma Forall_permutation: forall {A: Type} (al bl: list A) f, Forall f al -> Permutation al bl -> Forall f bl.
Proof.
intros. rewrite Forall_forall in *; intros.
apply H. apply (Permutation_in (l:=bl) (l':=al) x). apply Permutation_sym. apply H0. apply H1.
Qed.

Lemma body_kruskal: semax_body Vprog Gprog f_kruskal kruskal_spec.
Proof.
  start_function.
  unfold wedgearray_graph_rep. Intros.
  forward.
  forward.
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
  assert (Hdef_g: Forall def_wedgerep (map wedge_to_cdata (graph_to_wedgelist g))) by (apply def_wedgerep_map_w2c).
  (******************************SORT******************************) 
  forward_call ((wshare_share sh), 
                pointer_val_val orig_eptr,
                (map wedge_to_cdata (graph_to_wedgelist g))).
  - rewrite Zlength_map, g2wedgelist_numE. entailer!.
  - rewrite Zlength_map, g2wedgelist_numE. entailer!.
  - split3; [| |split]; trivial.
    rewrite Zlength_map, g2wedgelist_numE.
      split; [ apply numE_pos | apply numE_range; trivial].
  - Intros sorted.
    (* a little cleanup... *)
    rewrite empty_WEdgeListGraph_numE.
    rewrite <- Z2Nat.inj_sub, Z.sub_0_r. 2: lia.
    rewrite Z.mul_0_l.
    assert_PROP (isptr (pointer_val_val eptr)) by
        (rewrite (data_at_isptr sh); entailer!).
    rename H5 into H_eptr_isptr.
    rewrite isptr_offset_val_zero. 2: auto.
    rewrite data_at_zero_array_eq. 2: trivial. 2: auto.
    2: rewrite empty_WEdgeListGraph_graph_to_wedgelist; trivial.
    assert (Hdef_sorted: Forall def_wedgerep sorted).
      apply (Forall_permutation _ _ _ Hdef_g H3).
    (*clear Hdef_g.*)
    assert (HZlength_sorted: Zlength sorted = numE g).
      rewrite <- (Permutation_Zlength _ _ _ H3).
      rewrite Zlength_map. apply g2wedgelist_numE.
    (* done with cleanup. *)
    (******************************THE BIG NASTY LOOP******************************) 
     forward_for_simple_bound
    (numE g)
    (EX i : Z,
     EX msf' : FiniteWEdgeListGraph,
     EX subsetsGraph' : UFGraph,                      
     PROP (numV msf' = numV g; (*which combined with below should give vvalid msf' v <-> vvalid g v, see if we need it later*)
           is_partial_graph msf' g;
           uforest msf';
           True; (* something about min wt *)
           forall u v, connected subsetsGraph' u v -> connected g u v; (*uf represents components of graph*)
           forall u v, connected subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           uf_equiv subsetsGraph subsetsGraph')
     LOCAL (temp _graph_E (Vint (Int.repr (numE g)));
            temp _graph__1 (pointer_val_val orig_gptr);
            temp _subsets (pointer_val_val subsetsPtr);
            temp _mst (pointer_val_val gptr))
     SEP (
          (*the irritating global haha*)
          data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
          (*orig graph with sorted edgelist*)
          data_at sh (tarray t_struct_edge (Zlength sorted)) sorted (pointer_val_val orig_eptr);
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (list_repeat (Z.to_nat MAX_EDGES - Z.to_nat (numE g)) (Vundef, (Vundef, Vundef))) (offset_val (numE g * sizeof t_struct_edge) (pointer_val_val orig_eptr));
          (*msf'. fold this into wedgearray_graph_rep?*)
          data_at sh (tarray t_struct_edge (numE msf')) (map wedge_to_cdata (graph_to_wedgelist msf')) (pointer_val_val eptr);
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE msf')) (list_repeat (Z.to_nat MAX_EDGES - Z.to_nat (numE g)) (Vundef, (Vundef, Vundef))) (offset_val (numE msf' * sizeof t_struct_edge) (pointer_val_val orig_eptr));
          (*ufgraph*)
          whole_graph sh subsetsGraph' subsetsPtr
    ))%assert.
    + apply numE_range; trivial.
    + (******PRECON******)
      (* pure obligations *)
      (*Exists edgeless graph with V vertices*)
      admit.
      (* any SEP obligatins will also appear here, 
         as a separate goal after the entailer!. 
         currently there are none because I just 
         added an overapproximation of SEPs to the 
         invariant 
       *)
    + (******LOOP BODY******)
      Intros.
      assert (Hdef_i: def_wedgerep (Znth i sorted)). {
        rewrite Forall_forall in Hdef_sorted. apply Hdef_sorted. apply Znth_In. lia. }
      forward. forward.
      * entailer!.
        rewrite (surjective_pairing (Znth i sorted)).
        rewrite (surjective_pairing (snd (Znth i sorted))).
        apply Hdef_i.
      * (* inside the for loop *) 
 forward. forward.
 1: { entailer!.
      rewrite (surjective_pairing (Znth i sorted)).
      rewrite (surjective_pairing (snd (Znth i sorted))).
      apply Hdef_i.
 }
 rewrite (surjective_pairing (Znth i sorted)).
 rewrite (surjective_pairing (snd (Znth i sorted))).
 
 forward_call (sh,
               subsetsGraph',
               subsetsPtr,
               (force_signed_int
                  (fst (snd (Znth i sorted))))).
 ++
  entailer!. simpl.
  clear - Hdef_i.
  destruct Hdef_i as [_ [? _]].
  apply is_int_e in H.
  destruct H as [? [? _]].
  unfold wedgerep_inhabitant in *.
  replace ((fst (snd (Znth i sorted)))) with (Vint x).
  simpl.
  rewrite Int.repr_signed. trivial.
 ++
  destruct H11 as [? _].
  rewrite <- H11.
  apply H2.
  destruct Hdef_i as [_ [? _]].
  apply is_int_e in H12.
  destruct H12 as [? [? _]].
  rewrite H12. simpl.
  admit.  (* leaving for WX *)
 ++
  Intros u_root.
  destruct u_root as [subsetsGraph_u u_root].
  (* 1. the UFGraph after finding u
     2. u's root 
   *)
  simpl fst.
  forward_call (sh,
                subsetsGraph_u,
                subsetsPtr,
                (force_signed_int
                   (snd (snd (Znth i sorted))))).
  **
   entailer!.
   simpl.
   clear - Hdef_i.
   destruct Hdef_i as [_ [_ ?]].
   apply is_int_e in H.
   destruct H as [? [? _]].
   unfold wedgerep_inhabitant in *.
   replace ((snd (snd (Znth i sorted)))) with (Vint x).
   simpl.
   rewrite Int.repr_signed. trivial.
  **
   simpl fst in H12.
   destruct H12 as [? _].
   destruct H11 as [? _].
   rewrite <- H12, <- H11.
   apply H2.
   destruct Hdef_i as [_ [_ ?]].
   apply is_int_e in H14.
   destruct H14 as [? [? _]].
   rewrite H14. simpl.
  admit. (* leaving for WX *)
  **
   Intros v_root.
   destruct v_root as [subsetsGraph_uv v_root].
   simpl fst in *. simpl snd in *.
   forward_if.
   --- (* yes, add this edge.
          the bulk of the proof *)
    admit.
   --- (* no, don't add this edge *)
    forward. entailer!.
    (* the variables are uncertain but here's a guess: *)
    Exists msf' subsetsGraph_uv.
    assert (uf_equiv subsetsGraph_uv subsetsGraph') by admit.
    entailer!.

    Set Nested Proofs Allowed.
    Lemma uf_equiv_connected:
      forall {g1 g2 u v},
        uf_equiv g1 g2 ->
        connected g1 u v <->
        connected g2 u v.
    Proof.
      (* does this look reasonable to you?? *)
    Admitted.
    Unset Nested Proofs Allowed.
    
    split3; intros.
    +++
     apply H9.
     apply (uf_equiv_connected H39); trivial.
    +++
      rewrite <- H10.
      apply uf_equiv_connected; trivial.
    +++
      (* probably can make this work with u
         uf_equiv_trans
       *)
     admit.
    + Intros mst.
       Intros subsetsGraph'.
      forward_call ((pointer_val_val subsetsPtr)).
      forward.
      admit.
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
