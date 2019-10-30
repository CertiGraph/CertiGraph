Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.floyd_ext.share.

Instance SDAGA_VST: SpatialDijkstraArrayGraphAssum mpred. Proof. refine (Build_SpatialDijkstraArrayGraphAssum _ _ _ _ _). Defined.

Definition abstract_data_at2cdata (value : Z) : reptype vertex_type :=
  Vint (Int.repr value).

Instance SDAG_VST (sh: share): SpatialDijkstraArrayGraph pointer_val mpred.
Proof.
  exact (fun pt lst => data_at sh (tarray vertex_type (Z.of_nat (length lst)))
                               (map abstract_data_at2cdata lst) (pointer_val_val pt)).
Defined.

Lemma graph_to_mat_diagonal: forall g i,
    0 <= i < Zlength (graph_to_mat g) ->
    Znth i (Znth i (graph_to_mat g)) = 0.
Proof. Admitted.

