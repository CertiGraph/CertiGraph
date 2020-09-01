Require Export VST.floyd.proofauto.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.

Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.AdjMatGraph.

Require Import Coq.Classes.EquivDec.

(* This file is just one line: "Require Export priq.priq_arr_utils." 
   It can be inlined. 
   It is currently a separate file in case we want more constants stashed away 
 *)
Require Export CertiGraph.dijkstra.dijkstra_constants.

Local Open Scope logic.
Local Open Scope Z_scope.

(* Here is the LabeledGraph *)
Definition DijkLG := AdjMatLG.

(* The soundness condition *)
Class SoundDijk (g: DijkLG) :=
  {
  basic:
    (* first, we can take AdjMat's soundness wholesale *)
    (@SoundAdjMat SIZE inf g);
  
  veb:
    (* from the AdjMat soundness above we already know 
       e is representable, 
       but for Dijkstra we need a further constraint. 
     *)
    forall e,
      evalid g e ->
      0 <= elabel g e <= Int.max_signed / SIZE;

  cts: (* cost_to_self *)
    forall v, vvalid g v -> elabel g (v, v) = 0;
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

(* For the two Dijkstra-specigic plugins, 
   we create getters: 
 *)
Definition valid_edge_bounds (g: DijkGG) :=
  @veb g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition cost_to_self (g: DijkGG) :=
  @cts g ((@sound_gg _ _ _ _ _ _ _ _ g)).


(* And now some lemmas that come from soundness plugins. *)

Lemma edge_cost_pos:
  forall (g: DijkGG) e,
    0 <= elabel g e.
Proof.
  intros.
  pose proof (valid_edge_bounds g e).
  pose proof (invalid_edge_weight g e).
  destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
  - apply H; trivial.
  - rewrite H0 in n.
    replace (elabel g e) with inf by trivial.
    compute; inversion 1.
Qed.

Lemma edge_representable:
  forall (g: DijkGG) e,
    Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
  intros.
  pose proof (valid_edge_bounds g e).
  pose proof (invalid_edge_weight g e).
  pose proof (edge_cost_pos g e).
  destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
  - specialize (H e0).
    split; trivial.
    1: apply Z.le_trans with (m := 0); trivial; rep_lia.
    apply Z.le_trans with (m := (Int.max_signed/SIZE)); trivial.
    apply H.
    compute; inversion 1.
  - rewrite H0 in n.
    replace (elabel g e) with inf by trivial.
    rewrite inf_eq. split; compute; inversion 1.
Qed.

Lemma strong_evalid_dijk:
  forall (g: DijkGG) a b,
    vvalid g a ->
    vvalid g b ->
    elabel g (a, b) < inf ->
    strong_evalid g (a,b).
Proof.
  intros.
  split3;
    [rewrite (evalid_meaning g) |
     rewrite (edge_src_fst g) |
     rewrite (edge_dst_snd g)]; trivial.
  split.
  - apply edge_representable.
  - intro. apply Zlt_not_le in H1.
    apply H1. rewrite <- H2.
    reflexivity.
Qed.

