Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Export CertiGraph.lib.find_lemmas.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Export CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.MathAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section Mathematical_Undirected_AdjMat_Model.
  
Context {size: Z} {inf: Z}.

Definition UAdjMatLG := AdjMatLG.

(* We just add a further constraint to AdjMat's soundness *)
Class SoundUAdjMat (g: UAdjMatLG) := {
  sadjmat: @SoundAdjMat size inf g;
  uer: forall e, evalid g e -> src g e <= dst g e;
}.

Definition UAdjMatGG := (GeneralGraph V E unit Z unit (fun g => SoundUAdjMat g)).

(* Some handy coercions: *)
Identity Coercion AdjMatLG_UAdjMatLG: UAdjMatLG >-> AdjMatLG.
Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

Definition SoundUAdjMat_UAdjMatGG (g: UAdjMatGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* We can always drag out SoundAdjMat *)
Definition SoundAdjMat_UAdjMatGG (g: UAdjMatGG) :=
  @sadjmat g (SoundUAdjMat_UAdjMatGG g).

(* A UAdjMatGG can be weakened into an AdjMatGG *)
Definition AdjMatGG_UAdjMatGG (g: UAdjMatGG) : AdjMatGG :=
  Build_GeneralGraph unit Z unit SoundAdjMat g (SoundAdjMat_UAdjMatGG g).

Coercion AdjMatGG_UAdjMatGG: UAdjMatGG >-> AdjMatGG.

(* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a UAdjMatGG. The coercion will be seamless. 
 *)

(* For the one new UAdjMat-specific plugin, we create a getter *)
Definition undirected_edge_rep (g: UAdjMatGG) :=
  @uer g (SoundUAdjMat_UAdjMatGG g).

(* 
   A nice-to-do future step:
   Move any known lemmas that depend only on
   AdjMatSoundness + the above soundness plugin
   to this file instead of leaving it down below.
 *)

End Mathematical_Undirected_AdjMat_Model.
