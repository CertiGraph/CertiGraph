Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.

Require Import compcert.lib.Integers.

Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.path_lemmas.

Section Mathematical_AdjMat_Model.

  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

  Local Open Scope Z_scope.

  (* Most of the types are constrained because 
     we want easy AdjMat representation. *)
  Definition V : Type := Z.
  Definition E : Type := V * V.
  Definition DV: Type := unit.
  Definition DE : Type := Z.
  Definition DG: Type := unit.

  Instance V_EqDec : EqDec V eq. Proof. hnf. intros. apply Z.eq_dec. Defined.
  Instance E_EqDec: EqDec E eq.
  Proof. apply (prod_eqdec V_EqDec V_EqDec). Defined.

  Context {size : Z}. 
  Context {inf : Z}.
  (* The instantiator will have to supply a max number of vertices
     and a special "infinity" value to indicate unreachability 
   *)
  
  (* This is the basic LabeledGraph for all our AdjMat representations. *)
  Definition AdjMatLG := (@LabeledGraph V E _ _ DV DE DG).
  (* We need some further restrictions, which we will place 
     in the GeneralGraph's soundness condition.  
   *)

  (* Each field of the class is a "plugin"
     which further restricts various aspects of the graph
   *)
  Class SoundAdjMat (g: AdjMatLG) :=
    {
    sr: (* size_representable *)
      0 < size <= Int.max_signed;
    ir: (* inf_representable *)
      0 < inf <= Int.max_signed; 
    vm: (* vvalid_meaning *)
      forall v, vvalid g v <-> 0 <= v < size;
    em: (* evalid_meaning *)
      forall e, evalid g e <-> 
                Int.min_signed <= elabel g e <= Int.max_signed /\
                elabel g e <> inf;
    ese: (* evalid_strong_evalid *)
      forall e, evalid g e -> strong_evalid g e;
    iew: (* invalid_edge_weight *)
      forall e, ~ evalid g e <-> elabel g e = inf;
    esf: (* edge_src_fst *)
      forall e, src g e = fst e;
    eds: (* edge_dst_snd *)
      forall e, dst g e = snd e;
    fin:
      FiniteGraph g
    }.
  
  (* Academic example of how to instantiate the above *)
  Definition AdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundAdjMat g)).
  (* In reality, clients may want to:
     1. create a new soundness condition where one of the 
        plugins is "SoundAdjMat" above
     2. add further program-specific restrictions in 
        other plugins
     3. use this new accreted soundness condition to 
        build their GeneralGraph, as shown above.
   *)

  
  (* Getters for the plugins *)

  Definition size_representable (g: AdjMatGG) :=
    @sr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition inf_representable (g: AdjMatGG) :=
    @ir g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition vvalid_meaning (g: AdjMatGG) :=
    @vm g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_meaning (g: AdjMatGG) :=
    @em g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_strong_evalid (g: AdjMatGG) :=
    @ese g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition invalid_edge_weight (g: AdjMatGG) :=
    @iew g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_src_fst (g: AdjMatGG) :=
    @esf g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_dst_snd (g: AdjMatGG) :=
    @eds g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition finGraph (g: AdjMatGG) :=
    @fin g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Existing Instance finGraph.
  Coercion finGraph: AdjMatGG >-> FiniteGraph.

  (* Some lemmas from the above soundness plugins *)
  
  Lemma valid_path_app_cons:
    forall (g: AdjMatGG) src links2u u i,
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
    forall (g: AdjMatGG) a b c a' a2b,
      a = a' ->
      path_ends g (a, a2b) a b ->
      path_ends g (a, a2b +:: (b, c)) a' c.
  Proof.
    split; trivial.
    rewrite pfoot_last.
    rewrite (edge_dst_snd g); trivial.
  Qed.
  
  Lemma step_in_range:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (fst x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [? _]].
    rewrite <- (edge_src_fst g); trivial.
  Qed.
  
  Lemma step_in_range2:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (snd x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [_ ?]].
    rewrite <- (edge_dst_snd g); trivial.
  Qed.

  Lemma path_ends_one_step:
    forall (g: AdjMatGG) a b,
      path_ends g (a, (a, b)::nil) a b.
  Proof.
    intros. split; trivial.
    simpl. rewrite (edge_dst_snd g); trivial.
  Qed.

  Lemma epath_to_vpath_path_glue_one_step:
    forall (g: AdjMatGG) (a b c : V) p,
      valid_path g p ->
      path_ends g p a b -> 
      Permutation (epath_to_vpath g (path_glue p (b, (b, c)::nil)))
                  (c :: epath_to_vpath g p).
  Proof.
    intros.
    rewrite (surjective_pairing p) in *.
    remember (snd p) as a2b.
    replace (fst p) with a in *.
    2: destruct H0 as [? _]; simpl in H0; Lia.lia.
    clear Heqa2b.
    
    generalize dependent H.
    generalize dependent H0.
    generalize dependent b.
    generalize dependent a.
    generalize dependent a2b.

    induction a2b.
    - intros. simpl. red in H0. simpl in H0; destruct H0 as [_ ?].
      subst a. rewrite (edge_dst_snd g), (edge_src_fst g); simpl.
      apply perm_swap.
    - intros. rename a into new.
      inversion H. clear H2.
      unfold path_glue. simpl fst; simpl snd.
      rewrite <- app_comm_cons.
      repeat rewrite epath_to_vpath_cons_eq; trivial.
      pose proof (perm_swap c a0 (epath_to_vpath g (dst g new, a2b))).
      apply Permutation_trans with (l' := (a0 :: c :: epath_to_vpath g (dst g new, a2b))); trivial.
      apply perm_skip.
      apply IHa2b.
      + red. split; trivial.
        destruct H0. rewrite pfoot_cons in H3; trivial.
      + apply valid_path_cons in H; trivial.
  Qed.

  Lemma in_path_app_cons:
    forall (g: AdjMatGG) step p2a src a b,
      valid_path g p2a ->
      evalid g (a,b) ->
      path_ends g p2a src a ->
      In_path g step (fst p2a, snd p2a +:: (a, b)) ->
      In_path g step p2a \/ step = b.
  Proof.
    intros. destruct H2; simpl in H2.
    1: left; unfold In_path; left; trivial.
    destruct H2 as [? [? ?]].
    assert (evalid g x). {
      apply in_app_or in H2. simpl in H2.
      destruct H2 as [? | [? | ?]]; [| | Lia.lia]; [|subst;trivial].
      rewrite (surjective_pairing p2a) in H.
      apply (valid_path_evalid _ _ _ _ H H2).
    }
    rewrite (edge_src_fst g) in H3; trivial.
    apply in_app_or in H2; simpl in H2.
    destruct H2 as [? | [? | ?]]; [| | Lia.lia]; destruct H3.
    - left. unfold In_path. right.
      exists x. rewrite (edge_src_fst g); trivial.
      split; [|left]; trivial.
    - left. unfold In_path. right.
      exists x. rewrite (edge_src_fst g); trivial.
      split; [|right]; trivial.
    - left. apply pfoot_in.
      destruct H1. rewrite H3, <- H2; simpl; trivial.
    - unfold In_path. right.
      rewrite H3, <- H2; simpl; trivial.
      rewrite (edge_dst_snd g); trivial.
  Qed.

  Lemma acyclic_foot_empty: forall (g : AdjMatGG) src l,
      valid_path g (src, l) ->
      acyclic_path g (src, l) ->
      pfoot g (src, l) = src ->
      l = nil.
  Proof.
    destruct l; auto. intros. exfalso. assert (fst e = src). { destruct H.
                                                               rewrite (edge_src_fst g) in H. auto. }
                                                             apply pfoot_ptail in H1. simpl ptail in H1.
    rewrite pfoot_spec in H1. destruct H1.
    * rewrite (edge_dst_snd g) in H1. inversion H1. subst. 
      red in H0. simpl in H0. rewrite (edge_src_fst g), (edge_dst_snd g) in H0.
      rewrite H4 in H0. inversion H0. apply H5. left. trivial.
    * destruct H1 as [v' [l' [e' [? ?]]]]. subst src. inversion H1. subst v' l.
      rename H into Hx. clear H1.
      red in H0.
      rewrite <- (edge_src_fst g) in H2.
      rewrite epath_to_vpath_cons_eq in H0; auto.
      rewrite NoDup_cons_iff in H0. destruct H0 as [? _].
      apply H. clear H H2.
      rewrite in_path_eq_epath_to_vpath.
      eapply path_ends_In_path_dst. split. reflexivity.
      rewrite pfoot_last. trivial.
      apply valid_path_tail in Hx. apply Hx.
  Qed.

  Lemma In_links_snd_In_path:
    forall (g: AdjMatGG) step path,
      In step (snd path) ->
      In_path g (snd step) path.
  Proof.
    intros. unfold In_path. right.
    exists step. split; trivial.
    right. rewrite (edge_dst_snd g); trivial.
  Qed.

  Lemma In_links_fst_In_path:
    forall (g: AdjMatGG) step path,
      In step (snd path) ->
      In_path g (fst step) path.
  Proof.
    intros. unfold In_path. right.
    exists step. split; trivial.
    left. rewrite (edge_src_fst g); trivial.
  Qed.
  
End Mathematical_AdjMat_Model.
