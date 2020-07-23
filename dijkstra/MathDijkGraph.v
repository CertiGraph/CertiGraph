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
Require Import RamifyCoq.graph.AdjMatGraph.

Require Import Coq.Classes.EquivDec.

(* This file is just one line: "Require Export priq.priq_arr_utils." 
   It can be inlined. 
   It is currently a separate file in case we want more constants stashed away *)
Require Export RamifyCoq.dijkstra.dijkstra_constants.

Local Open Scope logic.
Local Open Scope Z_scope.

(* Here is the LabeledGraph *)
Definition DijkLG := AdjMatLG.

(* The soundness condition *)
Class SoundDijk (g: DijkLG) :=
  {
  basic: (* adj_mat_soundness *)
    (* first, we can take AdjMat's soundness wholesale *)
    (@SoundAdjMat SIZE inf g);
  
  veb:
    (* from the AdjMat soundness above we already know e is representable, 
       but for Dijkstra we need a further constraint. *)
    forall e,
      evalid g e ->
      0 <= elabel g e <= Int.max_signed / SIZE;
  }.

(* And here is the GeneralGraph that we will use *)
Definition DijkGG := (GeneralGraph V E DV DE DG (fun g => SoundDijk g)).

(* Some handy coercions: *)
Definition DijkGG_DijkLG (G: DijkGG): DijkLG := lg_gg G.
Coercion DijkGG_DijkLG: DijkGG >-> DijkLG.
Identity Coercion DijkLG_AdjMatLG: DijkLG >-> AdjMatLG.
Identity Coercion AdjMatLG_LabeledGraph: AdjMatLG >-> LabeledGraph.

(* We can always drag out SoundAdjMat *)
Definition DijkGG_SoundAdjMat (g: DijkGG) :=
  @basic g ((@sound_gg _ _ _ _ _ _ _ _ g)).

(* A DijkGG can be weakened into an AdjMatGG *)
Definition DijkGG_AdjMatGG (G: DijkGG) : AdjMatGG :=
  Build_GeneralGraph DV DE DG SoundAdjMat G (DijkGG_SoundAdjMat G).

Coercion DijkGG_AdjMatGG: DijkGG >-> AdjMatGG.

(* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a DijkGG. The coercion will be seamless. 
 *)

(* For the new plugin, we create a getter: *)
Definition valid_edge_bounds (g: DijkGG) :=
  @veb g ((@sound_gg _ _ _ _ _ _ _ _ g)).


(*
Definition vertex_valid (g : DijkstraGeneralGraph): Prop :=
  forall v, vvalid g v -> 0 <= v < SIZE.

Definition edge_valid (g : DijkstraGeneralGraph): Prop :=
  forall a b, evalid g (a,b) ->
              (vvalid g a /\ vvalid g b).

Definition src_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, dst g e = snd e.

(* further develop this to comment on valid, evalid *)
Definition edge_in_range (g: DijkstraGeneralGraph): Prop :=
  forall e,
    0 <= elabel g e <= Int.max_signed / SIZE \/
    elabel g e = inf.

Definition cost_to_self_0 (g: DijkstraGeneralGraph): Prop :=
  forall v, vvalid g v -> (elabel g (v, v)) = 0.

Definition sound_dijk_graph (g : DijkstraGeneralGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g /\ edge_in_range g /\ cost_to_self_0 g.

(* shouldn't this all go into soundness? *)
 *)

(* Lemmas that come from soundness plugins *)

(* considering *)
Lemma vvalid2_evalid:
  forall (g: DijkGG) a b,
    vvalid g a ->
    vvalid g b ->
    evalid g (a,b).
Proof. Admitted.

Lemma valid_path_app_cons:
  forall (g: DijkGG) src links2u u i,
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    strong_evalid g (u,i) ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  simpl; split; trivial.
  destruct H1.
  rewrite (edge_src_fst g); simpl; assumption.
Qed.

Lemma path_ends_app_cons:
  forall (g: DijkGG) src links2u u i,
    evalid g (u,i) ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.
  split; trivial.
  rewrite pfoot_last.
  rewrite (edge_dst_snd g); trivial.
Qed.

Lemma step_in_range:
  forall (g: DijkGG) x x0,
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  rewrite (surjective_pairing x) in H.
  pose proof (valid_path_strong_evalid g _ _ _ H H0).
  destruct H1 as [? [? _]].
  rewrite <- (vvalid_meaning g), <- (edge_src_fst g); trivial.
Qed.

Lemma step_in_range2:
  forall (g: DijkGG) x x0,
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  rewrite (surjective_pairing x) in H.
  pose proof (valid_path_strong_evalid g _ _ _ H H0).
  destruct H1 as [? [_ ?]].
  rewrite <- (vvalid_meaning g), <- (edge_dst_snd g); trivial.
Qed.

Lemma valid_edge_cost_pos:
  forall (g: DijkGG) e,
    evalid g e -> 0 <= elabel g e.
Proof.
  intros.
  apply (valid_edge_bounds g); trivial.
Qed.
