Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.Zcomplements.

Require Import compcert.lib.Integers.
Require Import VST.floyd.sublist.

Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.path_lemmas.

Section Mathematical_Edge_Labeled_Graph_Model.

  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

  Local Open Scope Z_scope.

  Definition V : Type := Z.
  Definition E : Type := V * V * Z. (* src, dst, out-edge-number *)
  Definition DV: Type := list V. (* the vertices I point to *)
  Definition DE : Type := Z. (* the cost itself *)
  Definition DG: Type := unit.
  
  Instance V_EqDec : EqDec V eq.
  Proof.
    hnf. intros. apply Z.eq_dec.
  Defined.

  Instance E_EqDec: EqDec E eq.
  Proof.
    apply (prod_eqdec (prod_eqdec V_EqDec V_EqDec) Z.eq_dec).
  Defined.

  Context {size : Z}. 
  (* The instantiator will have to supply the number of vertices *)
  
  (* This is the basic LabeledGraph for all our Edge-Labeled representations. *)
  Definition EdgeLabLG := (@LabeledGraph V E _ _ DV DE DG).
  (* We need some further restrictions, which we will place 
     in the GeneralGraph's soundness condition.  
   *)

  (* Each field of the class is a "plugin"
     which further restricts various aspects of the graph
   *)
  Class SoundEdgeLab (g: EdgeLabLG) :=
    {
    sr: (* size_representable *)
      0 < size <= Int.max_signed;
    vm: (* vvalid_meaning *)
      forall v, vvalid g v <-> 0 <= v < size;
    em: (* evalid_meaning *)
      forall src dst out,
        evalid g (src, dst, out) <->
        Int.min_signed <= elabel g (src, dst, out) <= Int.max_signed /\
        0 <= out < Zlength (vlabel g src) /\
        Znth out (vlabel g src) = dst;
    ese: (* evalid_strong_evalid *)
      forall e, evalid g e -> strong_evalid g e;
    esf: (* edge_src_fst *)
      forall e, src g e = fst (fst e);
    eds: (* edge_dst_snd *)
      forall e, dst g e = snd (fst e);
    fin:
      FiniteGraph g
    }.
  
  (* Academic example of how to instantiate the above *)
  Definition EdgeLabGG := (GeneralGraph V E DV DE DG (fun g => SoundEdgeLab g)).
  (* In reality, clients may want to:
     1. create a new soundness condition where one of the 
        plugins is "SounndEdgeLab" above
     2. add further program-specific restrictions in 
        other plugins
     3. use this new accreted soundness condition to 
        build their GeneralGraph, as shown above.
   *)

  
  (* Getters for the plugins *)

  Definition size_representable (g: EdgeLabGG) :=
    @sr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition vvalid_meaning (g: EdgeLabGG) :=
    @vm g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_meaning (g: EdgeLabGG) :=
    @em g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_strong_evalid (g: EdgeLabGG) :=
    @ese g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_src_fst (g: EdgeLabGG) :=
    @esf g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_dst_snd (g: EdgeLabGG) :=
    @eds g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition finGraph (g: EdgeLabGG) :=
    @fin g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  
  (* Some lemmas from the above soundness plugins *)
  
  Lemma valid_path_app_cons:
    forall (g: EdgeLabGG) src links2u u i o,
      valid_path g (src, links2u) ->
      pfoot g (src, links2u) = u ->
      strong_evalid g (u,i, o) ->
      valid_path g (src, links2u +:: (u,i, o)).
  Proof.
    intros.
    apply valid_path_app.
    split; [assumption|].
    simpl; split; trivial.
    destruct H1.
    rewrite (edge_src_fst g); simpl; assumption.
  Qed.
  
  Lemma path_ends_app_cons:
    forall (g: EdgeLabGG) a b c o a' a2b,
      a = a' ->
      path_ends g (a, a2b) a b ->
      path_ends g (a, a2b +:: (b, c, o)) a' c.
  Proof.
    split; trivial.
    rewrite pfoot_last.
    rewrite (edge_dst_snd g); trivial.
  Qed.
  
  Lemma step_in_range:
    forall (g: EdgeLabGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (src g x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [? _]]. trivial.
  Qed.
  
  Lemma step_in_range2:
    forall (g: EdgeLabGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (dst g x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [_ ?]]. trivial.
  Qed.

End Mathematical_Edge_Labeled_Graph_Model.
