Require Export VST.floyd.proofauto.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.

Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.FiniteGraph.

(* The V, E, Label types get set here *)
Require Import RamifyCoq.graph.AdjMatGraph.


Require Import Coq.Classes.EquivDec.

(* This file is just one line: "Require Export priq.priq_arr_utils." 
   It can be inlined. 
   It is currently a separate file in case we want more constants stashed away *)
Require Export RamifyCoq.dijkstra.dijkstra_constants.

Local Open Scope logic.
Local Open Scope Z_scope.

(* Here is the LabeledGraph *)
Definition DijkstraLabeledGraph := AdjMatLG.

(* The soundness condition (just one item for now) *)
Class Fin (g: DijkstraLabeledGraph) :=
  { fin: FiniteGraph g; }.

(* And the GeneralGraph that we will use *)
Definition DijkstraGeneralGraph := (GeneralGraph V E DV DE DG (fun g => Fin g)).

Definition vertex_valid (g : DijkstraGeneralGraph): Prop :=
  forall v, vvalid g v <-> 0 <= v < SIZE.

Definition edge_valid (g : DijkstraGeneralGraph): Prop :=
  forall a b, evalid g (a,b) <->
            (vvalid g a /\ vvalid g b).

Definition src_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, dst g e = snd e.

Definition sound_dijk_graph (g : DijkstraGeneralGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g.

(* shouldn't this all go into soundness? *)

(* lemmas that come from soundness plugins *)
Lemma vvalid2_evalid:
  forall g a b,
    sound_dijk_graph g ->
    vvalid g a ->
    vvalid g b ->
    evalid g (a,b).
Proof.
  intros. destruct H as [_ [? _]].
  red in H; rewrite H; split; trivial.
Qed.

Lemma vvalid_range:
  forall g a,
    sound_dijk_graph g ->
    vvalid g a <-> 0 <= a < SIZE.
Proof.
  intros. destruct H as [? _]. red in H. trivial.
Qed.

Lemma valid_path_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    evalid g (u,i) ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  assert (Hrem := H).
  destruct H as [? [? [? ?]]].
  simpl; split.
  1: rewrite H4; simpl; assumption.
  unfold strong_evalid.
  rewrite H4, H5; simpl.
  split; trivial.
  red in H3; rewrite H3 in H2; trivial.
Qed.

Lemma path_ends_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.
  split.
  + destruct H0; apply H0.
  + rewrite pfoot_last.
    destruct H as [_ [_ [_ ?]]].
    rewrite H; reflexivity.
Qed.

Lemma step_in_range: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [? _]]].
  unfold vertex_valid in H.
  unfold src_edge in H2.
  assert (In_path g (fst x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| left]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
Qed.

Lemma step_in_range2: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [_ ?]]].
  unfold vertex_valid in H.
  unfold dst_edge in H2.
  assert (In_path g (snd x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| right]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
Qed.
