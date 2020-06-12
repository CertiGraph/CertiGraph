Require Import VST.floyd.proofauto.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.kruskal.undirected_graph.

Local Open Scope logic.

Definition wedge_to_cdata (wedge : LE*EType) : reptype t_struct_edge :=
  (Vint (Int.repr (fst wedge)),
    (Vint (Int.repr (fst (snd wedge))),
      Vint (Int.repr (snd (snd wedge)))
    )
  ).

Lemma wedge_to_cdata_wedgerep:
  forall w, Int.min_signed <= fst w <= Int.max_signed ->
            Int.min_signed <= fst (snd w) <= Int.max_signed ->
            Int.min_signed <= snd (snd w) <= Int.max_signed ->
            def_wedgerep (wedge_to_cdata w).
Proof.
  intros. unfold wedge_to_cdata; unfold def_wedgerep; simpl. lia.
Qed.

Definition c_connected_by_path g P p u v :=
match u, v with
| Vint u', Vint v' => connected_by_path g P p (Int.signed u') (Int.signed v')
| _, _ => False
end.

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


Definition cdata_to_wedge (cwedge: reptype t_struct_edge) : option (LE*EType) :=
match cwedge with
| (Vint w, (Vint x, Vint y)) => Some (Int.signed w,(Int.signed x,Int.signed y))
| _ => None
end.

Lemma w2c2w:
  forall w, Int.min_signed <= fst w <= Int.max_signed ->
            Int.min_signed <= fst (snd w) <= Int.max_signed ->
            Int.min_signed <= snd (snd w) <= Int.max_signed ->
            cdata_to_wedge (wedge_to_cdata w) = Some w.
Proof.
unfold wedge_to_cdata; unfold cdata_to_wedge; intros.
repeat rewrite Int.signed_repr by auto. destruct w; destruct p; simpl; auto.
Qed.

Definition Vundef_cwedges (n: Z): list (reptype t_struct_edge) :=
    list_repeat (Z.to_nat n) (Vundef, (Vundef, Vundef)).

Lemma Vundef_cwedges_Zlength:
  forall n: Z, 0 <= n -> Zlength (Vundef_cwedges n) = n.
Proof.
intros. unfold Vundef_cwedges. apply Zlength_list_repeat. auto.
Qed.