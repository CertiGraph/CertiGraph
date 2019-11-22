Require Import RamifyCoq.msl_application.ArrayGraph.
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

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map Vint (map Int.repr mylist)) (list_address l index size).

Definition graph_rep sh contents_graph gaddr : mpred :=
  iter_sepcon.iter_sepcon (list_rep sh SIZE gaddr contents_graph)
                          (nat_inc_list (Z.to_nat (Zlength contents_graph))).

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
  (sublist_split i (i+1) (Zlength contents)), (sublist_one i); try omega.
  2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; omega.
  rewrite nat_inc_list_i.
  2: rewrite Z2Nat_id', Z.max_r; trivial; apply Zlength_nonneg. 
  repeat rewrite iter_sepcon.iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.