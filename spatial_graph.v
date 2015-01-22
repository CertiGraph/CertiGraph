Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import msl_ext.
Require Import ramify_tactics.
Require Import NPeano.
Require Import Classical.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r := !!(3 | x) && ((mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r)).

Module Type NAT_GRAPH.
  Parameter pg : @PreGraph adr nat natEqDec.
  Parameter bi : BiGraph pg.
End NAT_GRAPH.

Module SpatialGraph (NatGraph : NAT_GRAPH).

  Import NatGraph.

  Definition graph_maps (v : adr) : pred world := let (dl, r) := gamma bi v in let (d, l) := dl in trinode v d l r.

  Lemma precise_graph_maps: forall v, precise (graph_maps v).
  Proof.
    intro. unfold graph_maps. destruct (gamma bi v) as [dl r]. destruct dl as [d l]. unfold trinode. apply precise_andp_right.
    apply precise_sepcon. apply precise_mapsto. apply precise_sepcon. apply precise_mapsto. apply precise_mapsto.
  Qed.

  Lemma graph_maps_sepcon_unique: sepcon_unique graph_maps.
  Proof.
    repeat intro. unfold graph_maps in *. destruct (gamma bi x) as [dl r]. destruct dl as [d l]. unfold trinode in *.
    destruct_sepcon H w. destruct H0, H1. destruct_sepcon H2 w1. destruct_sepcon H3 w2. try_join w12 w2 w122.
    try_join w12 w22 w1222. assert ((mapsto (x+2) r * mapsto (x+2) r)%pred w1222) by (exists w22, w12; split; auto).
    apply mapsto_unique in H12. auto.
  Qed.

  Definition graph (x : adr) : pred world :=
    (!!(x = 0) && emp) || EX l : list adr, !!(l <> nil /\
                                              forall y, (In y l -> reachable pg x y) /\ (~ In y l -> ~ reachable pg x y)) &&
                                             iter_sepcon l graph_maps.

  Lemma graph_unfold:
    forall x,
      graph x = (!!(x = 0) && emp) ||
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r ⊗
                                                 (graph l) ⊗ (graph r)).
  Proof.
    intro; apply pred_ext; intro w; intros. unfold graph in H. destruct H. left; auto. right. destruct H as [ll [[? ?] ?]].
    destruct (gamma bi x) as [[d l] r]. exists d, l, r.
    admit. admit.
  Qed.

End SpatialGraph.
