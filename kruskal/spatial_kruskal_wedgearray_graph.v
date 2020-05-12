Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope logic.
(*I'm not sure what this is for*)
Instance SWEGA_VST: SpatialWEdgeListGraphAssum mpred. Proof. refine (Build_SpatialWEdgeListGraphAssum _ _ _ _ _). Defined.

Definition wedge_to_cdata (wedge : LE*EType) : reptype t_struct_edge :=
  (Vint (Int.repr (fst wedge)),
    (Vint (Int.repr (fst (snd wedge))),
      Vint (Int.repr (snd (snd wedge)))
    )
  ).

Instance SWEG_VST (sh: share): SpatialWEdgeListGraph pointer_val mpred.
Proof.
  (*should I include graph->V and graph->E too? i.e. the full graph struct*)
  (*I have no idea what the ordering of the lst is. Maybe I need Permutation or something*)
  exact (fun pt lst => data_at sh (tarray t_struct_edge (Z.of_nat (length lst)))
                              (map wedge_to_cdata lst) (pointer_val_val pt) (*I think this is wrong, should be just pt*)
  (*
                       *
                       data_at sh  (tarray t_struct_edge (Z.of_nat (length lst)))
                              (?) (pointer_val_val (pt+(Z.of_nat (length lst)))).
    Perhaps should be memory_block? but I do reference it like an array when adding edges
    Maybe I should zero the array beforehand?
    I don't remove edges, so ok for kruskal's, but for general purposes this may not be good
    Pretty sure splitting a tarray into smaller tarrays and vice versa is fine, maybe a lemma can be written
    Actually, do I even need this? This is just a wrapper right? Whatever is held in the other parts of the array can be explicitly stated outside
  *)
        ).
Defined.

Eval compute in reptype t_struct_edge.
Eval compute in reptype t_edgearray_graph.

Definition graph_rep sh (g: LGraph) {fg: FiniteGraph g} gaddr : mpred :=
  data_at sh (t_edgearray_graph) (
    Vint (Int.repr (numV g)), (
      Vint (Int.repr (numE g)),
      map wedge_to_cdata (graph_to_wedgelist g)
    )
  )
  gaddr.

(* See if I need something like this next time
Lemma graph_unfold: forall sh contents ptr i,
    0 <= i < (Zlength contents) ->
    graph_rep sh contents ptr =
    iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents)
            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh SIZE ptr contents i *
           iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents)
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