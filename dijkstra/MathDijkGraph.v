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
Class SoundDijk (g: DijkLG) inf size :=
  {
  basic:
    (* first, we can take AdjMat's soundness wholesale *)
    (@SoundAdjMat size inf g);
  
  veb:
    (* from the AdjMat soundness above we already know 
       e is representable, 
       but for Dijkstra we need a further constraint. 
     *)
    forall e,
      evalid g e ->
      0 <= elabel g e <= Int.max_signed / size;

  cts: (* cost_to_self *)
    forall v, vvalid g v -> elabel g (v, v) = 0;

  sfr: (* size is further restricted *)
    size * 4 <= Int.max_signed;
  
  ifr: (* inf is further restricted *)
    0 < inf < Int.max_signed
  }.

(* And here is the GeneralGraph that we will use *)
Definition DijkGG inf size := (GeneralGraph V E DV DE DG (fun g => SoundDijk g inf size)).

(* Some handy coercions: *)
Definition DijkGG_DijkLG inf size (G: (DijkGG inf size)): DijkLG := lg_gg G.
Coercion DijkGG_DijkLG: DijkGG >-> DijkLG.
Identity Coercion DijkLG_AdjMatLG: DijkLG >-> AdjMatLG.
Identity Coercion AdjMatLG_LabeledGraph: AdjMatLG >-> LabeledGraph.

(* We can always drag out SoundAdjMat *)
Definition DijkGG_SoundAdjMat inf size (g: (DijkGG inf size)) :=
  @basic g inf size ((@sound_gg _ _ _ _ _ _ _ _ g)).

(* A DijkGG can be weakened into an AdjMatGG *)
Definition DijkGG_AdjMatGG inf size (G: (DijkGG inf size)) : AdjMatGG :=
  Build_GeneralGraph DV DE DG SoundAdjMat G (DijkGG_SoundAdjMat inf size G).

Coercion DijkGG_AdjMatGG: DijkGG >-> AdjMatGG.

(* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a DijkGG. The coercion will be seamless. 
 *)

(* For the two Dijkstra-specigic plugins, 
   we create getters: 
 *)
Definition valid_edge_bounds inf size (g: (DijkGG inf size)) :=
  @veb g inf size ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition cost_to_self inf size (g: (DijkGG inf size)) :=
  @cts g inf size ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition size_further_restricted inf size (g: (DijkGG inf size)) :=
  @sfr g inf size ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition inf_further_restricted inf size (g: (DijkGG inf size)) :=
  @ifr g inf size ((@sound_gg _ _ _ _ _ _ _ _ g)).

(* And now some lemmas that come from soundness plugins. *)

Lemma edge_cost_pos:
  forall inf size (g: (DijkGG inf size)) e,
    0 <= elabel g e.
Proof.
  intros.
  pose proof (valid_edge_bounds inf size g e).
  pose proof (invalid_edge_weight g e).
  destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
  - apply H; trivial.
  - rewrite H0 in n.
    replace (elabel g e) with inf by trivial.
    apply (@inf_representable _ _ g).
Qed.

Lemma div_pos_le:
  forall a b,
    0 <= a ->
    0 < b ->
    a / b <= a.
Proof.
Admitted.

Lemma edge_representable:
  forall inf size (g: (DijkGG inf size)) e,
    Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
  intros.
  pose proof (valid_edge_bounds inf size g e).
  pose proof (invalid_edge_weight g e).
  pose proof (edge_cost_pos inf size g e).
  destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
  - specialize (H e0).
    split; trivial.
    1: apply Z.le_trans with (m := 0); trivial; rep_lia.
    apply Z.le_trans with (m := (Int.max_signed / size)); trivial.
    apply H.
    pose proof (size_representable g).
    apply div_pos_le; lia.
  - rewrite H0 in n.
    replace (elabel g e) with inf by trivial.
    pose proof (inf_representable g).
    split; [|lia].
    apply Z.le_trans with (m := 0); [|lia].
    compute; inversion 1.
Qed.

Lemma strong_evalid_dijk:
  forall inf size (g: (DijkGG inf size)) a b,
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
  - intro. simpl in H2. lia. 
Qed.

