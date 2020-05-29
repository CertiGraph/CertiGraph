Require Import VST.floyd.proofauto.
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope logic.

Definition wedge_to_cdata (wedge : LE*EType) : reptype t_struct_edge :=
  (Vint (Int.repr (fst wedge)),
    (Vint (Int.repr (fst (snd wedge))),
      Vint (Int.repr (snd (snd wedge)))
    )
  ).

Lemma wedge_to_cdata_wedgerep:
  forall w, Int.min_signed <= Int.signed (Int.repr (fst w)) <= Int.max_signed ->
            Int.min_signed <= Int.signed (Int.repr (fst (snd w))) <= Int.max_signed ->
            Int.min_signed <= Int.signed (Int.repr (snd (snd w))) <= Int.max_signed ->
            def_wedgerep (wedge_to_cdata w).
Proof.
  intros. unfold wedge_to_cdata; unfold def_wedgerep; simpl. lia.
Qed.

(*
Corollary map_wedge_cdata_wedgerep:
*)


(*I'm not sure what this is for
Instance SWEGA_VST: SpatialWEdgeListGraphAssum mpred. Proof. refine (Build_SpatialWEdgeListGraphAssum _ _ _ _ _). Defined.

Instance SWEG_VST (sh: share): SpatialWEdgeListGraph pointer_val mpred.
Proof.
  (*should I include graph->V and graph->E too? i.e. the full graph struct*)
  (*I have no idea what the ordering of the lst is. Maybe I need Permutation or something*)
  exact (fun pt lst => data_at sh (tarray t_struct_edge (Z.of_nat (length lst)))
                              (map wedge_to_cdata lst) (pointer_val_val pt) (*I think this is wrong, should be just pt*)
        ).
Defined.
*)
Definition wedgearray_graph_rep sh (g: FiniteWEdgeListGraph) gptr eptr : mpred :=
  data_at sh (t_wedgearray_graph) (
    Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val eptr)
  ) (pointer_val_val gptr)
  *
  data_at sh (tarray t_struct_edge (numE g)) (map wedge_to_cdata (graph_to_wedgelist g)) (pointer_val_val eptr)
  *
  data_at sh (tarray t_struct_edge (MAX_EDGES - (numE g)))
    (list_repeat (Z.to_nat MAX_EDGES - Z.to_nat (numE g)) (Vundef, (Vundef, Vundef)))
    (offset_val ((numE g) * sizeof t_struct_edge) (pointer_val_val eptr))
  .

(* See if I need something like this next time
Lemma graph_unfold: forall sh contents ptr i,
    0 <= i < (Zlength contents) ->
    graph_rep sh contents ptr =
    iter_sepcon.iter_sepcon (list_rep sh MAX_EDGES ptr contents)
            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh MAX_EDGES ptr contents i *
           iter_sepcon.iter_sepcon (list_rep sh MAX_EDGES ptr contents)
             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros. unfold graph_rep.
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
  repeat rewrite iter_sepcon.iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.
*)

(*
Lemma graph_sep: forall sh graph ptr,
    graph_rep sh graph ptr =
	data_at tint (numV g) ptr *
	data_at tint (numE g) (?) *
	SWEG_VST (?) (graph_to_wedgelist graph).
Proof.
*)
