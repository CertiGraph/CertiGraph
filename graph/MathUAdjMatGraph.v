Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Export CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.MathAdjMatGraph.
Require Export CertiGraph.lib.find_lemmas.

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

  Definition UAdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundUAdjMat g)).

  (* Some handy coercions: *)
  Identity Coercion AdjMatLG_UAdjMatLG: UAdjMatLG >-> AdjMatLG.
  Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

  Definition SoundUAdjMat_UAdjMatGG (g: UAdjMatGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

  (* We can always drag out SoundAdjMat *)
  Definition SoundAdjMat_UAdjMatGG (g: UAdjMatGG) :=
    @sadjmat g (SoundUAdjMat_UAdjMatGG g).

  (* A UAdjMatGG can be weakened into an AdjMatGG *)
  Definition AdjMatGG_UAdjMatGG (g: UAdjMatGG) : AdjMatGG :=
    Build_GeneralGraph DV DE DG SoundAdjMat g (SoundAdjMat_UAdjMatGG g).

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

  (* Downstream, we will need a little utility to
   reorder our vertices for the purposes of representation *)
  Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

  (* Some lemmas about eformat *)

  Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
  Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

  Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
  Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

  Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
  Proof.
    intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
  Qed.

  Lemma eformat_eq:
    forall u v a b, eformat (u,v) = eformat (a,b) -> ((u=a /\ v=b) \/ (u=b /\ v=a)).
  Proof.
    intros. destruct (Z.le_ge_cases u v); destruct (Z.le_ge_cases a b).
    rewrite eformat1, eformat1 in H. apply pair_equal_spec in H. left; auto. simpl; auto. simpl; auto. simpl; auto.
    rewrite eformat1, eformat2 in H. simpl in H. apply pair_equal_spec in H. right; auto. simpl; auto. simpl; auto.
    rewrite eformat2, eformat1 in H. simpl in H. apply pair_equal_spec in H. right; split; apply H. simpl; auto. simpl; auto.
    rewrite eformat2, eformat2 in H. simpl in H. apply pair_equal_spec in H. left; split; apply H. simpl; auto. simpl; auto.
  Qed.

  Lemma eformat_symm:
    forall u v, eformat (u,v) = eformat (v,u).
  Proof.
    intros. destruct (Z.lt_trichotomy u v).
    rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
    destruct H.
    rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
    rewrite eformat2'. rewrite eformat1. simpl; auto. simpl; lia. simpl; lia.
  Qed.

  Instance Finite_UAdjMatGG (g: UAdjMatGG):
    FiniteGraph g.
  Proof. apply (finGraph g). Qed.

  Lemma vert_bound:
    forall (g: UAdjMatGG) v, vvalid g v <-> 0 <= v < size.
  Proof.
    intros. apply (vvalid_meaning g).
  Qed.

  Lemma UAdjMatGG_VList:
    forall (g: UAdjMatGG), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
  Proof.
    intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
    intros. rewrite VList_vvalid. rewrite vert_bound.
    rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
    destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
    destruct H. rewrite H. unfold Z.max; simpl. split; lia.
    rewrite Z.max_l by lia. split; auto.
  Qed.

  Lemma evalid_form: (*useful for a = (u,v) etc*)
    forall (g: UAdjMatGG) e, evalid g e -> e = (src g e, dst g e).
  Proof.
    intros.
    rewrite (edge_src_fst g).
    rewrite (edge_dst_snd g).
    destruct e; simpl; auto.
  Qed.

  Lemma evalid_vvalid:
    forall (g: UAdjMatGG) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
  Proof.
    intros. apply (evalid_strong_evalid g) in H. destruct H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in H0 by auto.
    simpl in H0; auto.
  Qed.

  Lemma evalid_adjacent:
    forall (g: UAdjMatGG) u v, evalid g (u,v) -> adjacent g u v.
  Proof.
    intros. exists (u,v); split. apply (evalid_strong_evalid g); auto.
    rewrite (edge_src_fst g), (edge_dst_snd g) by auto. left; simpl; auto.
  Qed.

  Lemma weight_representable:
    forall (g: UAdjMatGG) e, Int.min_signed <= elabel g e <= Int.max_signed.
  Proof.
    intros. destruct (evalid_dec g e).
    apply (evalid_meaning g e); auto.
    rewrite (invalid_edge_weight g) in n.
    replace (elabel g e) with inf in * by trivial.
    pose proof (inf_representable g). rep_lia. 
  Qed.

  Lemma adj_edge_form:
    forall (g: UAdjMatGG) u v a b, adj_edge g (u,v) a b -> a <= b -> (u = a /\ v = b).
  Proof.
    intros. destruct H. assert (src g (u,v) <= dst g (u,v)).
    apply (undirected_edge_rep g). apply H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in *.
    simpl in *. destruct H1. auto. destruct H1; subst u; subst v. lia.
    all: apply H.
  Qed.

  Lemma eformat_evalid_vvalid:
    forall (g: UAdjMatGG) u v, evalid g (eformat (u,v)) -> vvalid g u /\ vvalid g v.
  Proof.
    intros. apply (evalid_strong_evalid g) in H.
    destruct (Z.lt_trichotomy u v).
    rewrite eformat1 in H. destruct H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in H1; auto. simpl; lia.
    destruct H0.
    subst u. rewrite eformat1 in H. destruct H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in H0; auto. simpl; lia.
    rewrite eformat2 in H. simpl in H; destruct H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in H1; auto. simpl in H1.
    split; apply H1. simpl; lia.
  Qed.

  Lemma eformat_adj': forall (g : UAdjMatGG) u v, evalid g (eformat (u,v)) -> adj_edge g (eformat (u,v)) u v.
  Proof.
    intros. split. apply (evalid_strong_evalid g); auto.
    destruct (Z.le_ge_cases u v).
    rewrite eformat1 in *. left. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
    rewrite eformat2 in *. right. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
  Qed.

  Lemma eformat_adj: forall (g: UAdjMatGG) u v, adjacent g u v <-> evalid g (eformat (u,v)).
  Proof.
    intros. split. intros.
    +
      destruct H. destruct H. destruct H.
      destruct H0; destruct H0. assert (x = (u,v)). {
        rewrite (edge_src_fst g) in H0.
        rewrite (edge_dst_snd g) in H2. rewrite <- H0, <- H2. destruct x; simpl; auto.
      } subst x.
      rewrite eformat1; auto. simpl.
      rewrite <- H0. rewrite <- H2 at 2. apply (undirected_edge_rep g); auto.
      assert (x = (v,u)). {
        rewrite (edge_src_fst g) in H0; rewrite (edge_dst_snd g) in H2.
        rewrite <- H0, <- H2. destruct x; simpl; auto.
      } subst x.
      rewrite eformat2. simpl. auto. simpl. rewrite <- H0. rewrite <- H2 at 2.
      apply (undirected_edge_rep g); auto.
    +intros. destruct (Z.lt_trichotomy u v).
     rewrite eformat1 in H. 2: simpl; lia.
     assert (evalid g (u,v)). auto.
     exists (u,v). split. apply (evalid_strong_evalid g); auto. left.
     rewrite (edge_src_fst g), (edge_dst_snd g); auto.
     (*equal, repeat*)
     destruct H0. rewrite eformat1 in H. 2: simpl; lia.
     assert (evalid g (u,v)). auto.
     exists (u,v). split. apply (evalid_strong_evalid g); auto. left.
     rewrite (edge_src_fst g), (edge_dst_snd g); auto.
     rewrite eformat2 in H. 2: simpl; lia. simpl in H.
     assert (evalid g (v,u)). auto.
     exists (v,u). split. apply (evalid_strong_evalid g); auto.
     rewrite (edge_src_fst g), (edge_dst_snd g); auto.
  Qed.

  Section EDGELESS_UADJMATGRAPH.

    Context {inf_bound: 0 < inf <= Int.max_signed}.
    Context {size_bound: 0 < size <= Int.max_signed}.

    Definition edgeless_lgraph : UAdjMatLG :=
      @Build_LabeledGraph V E V_EqDec E_EqDec unit Z unit
                          (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
                          (fun v => tt) (fun e => inf) tt. 

    Instance SoundUAdjMat_edgeless:
      SoundUAdjMat edgeless_lgraph.
    Proof. 
      constructor.
      all: simpl; intros; try contradiction.
      constructor. 
      auto. auto. 
      all: simpl; intros; try auto; try contradiction.
      split; intros; auto.
      split; intros. contradiction. destruct H.
      apply H0; reflexivity.
      split; intros; auto.
      constructor; unfold EnumEnsembles.Enumerable.
      (*vertices*)
      exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
      simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
      destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
      destruct H. rewrite H. unfold Z.max; simpl. split; lia.
      rewrite Z.max_l by lia. split; auto.
      (*edges*)
      exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
    Qed.

    Definition edgeless_graph: UAdjMatGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
                          edgeless_lgraph SoundUAdjMat_edgeless.

    Lemma edgeless_graph_evalid:
      forall e, ~ evalid edgeless_graph e.
    Proof.
      intros. unfold edgeless_graph; simpl. auto.
    Qed.

    Lemma edgeless_graph_EList:
      EList edgeless_graph = nil.
    Proof.
      intros. unfold edgeless_graph, EList.
      destruct finiteE. simpl in *.
      destruct a.
      destruct x; [trivial | exfalso].
      assert (In e (e::x)) by (apply in_eq).
      apply (H0 e). apply H1.
    Qed.

    Lemma edgeless_partial_lgraph:
      forall (g: UAdjMatGG), is_partial_lgraph edgeless_graph g.
    Proof.
      intros. split. unfold is_partial_graph.
      split. intros. simpl. simpl in H. rewrite vert_bound. auto.
      split. intros. pose proof (edgeless_graph_evalid e). contradiction.
      split. intros. pose proof (edgeless_graph_evalid e). contradiction.
      intros. pose proof (edgeless_graph_evalid e). contradiction.
      split. unfold preserve_vlabel; intros. destruct vlabel; destruct vlabel. auto.
      unfold preserve_elabel; intros. pose proof (edgeless_graph_evalid e). contradiction.
    Qed.

    Lemma uforest'_edgeless_graph:
      uforest' edgeless_graph.
    Proof.
      split; intros.
      (*no self-loops*)
      apply edgeless_graph_evalid in H; contradiction.
      split; intros.
      (*only one edge between two vertices*)
      destruct H. destruct H. destruct H.
      apply edgeless_graph_evalid in H; contradiction.
      (*no rubbish edges*)
      split; intros.
      apply edgeless_graph_evalid in H; contradiction.
      (*main forest definition*)
      unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
      destruct p1. inversion H3. destruct p1.
      inversion H3. inversion H4. subst u; subst v.
      destruct H2 as [? [? ?]]. destruct p2. inversion H5.
      destruct p2. inversion H5. subst v. auto.
      destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
      destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
    Qed.

    Lemma edgeless_graph_disconnected:
      forall u v, u <> v -> ~ connected edgeless_graph u v.
    Proof.
      unfold not; intros.
      destruct H0 as [p [? [? ?]]].
      destruct p. inversion H1.
      destruct p. inversion H1; inversion H2. subst u; subst v. contradiction.
      destruct H0. destruct H0. destruct H0. destruct H0.
      pose proof (edgeless_graph_evalid x). contradiction.
    Qed.

  End EDGELESS_UADJMATGRAPH.

  Section ADD_EDGE_UADJMATGRAPH.

    Context {g: UAdjMatGG}.
    Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
    Context {w: Z} {w_rep: Int.min_signed <= w < inf}.

    Definition UAdjMatGG_adde':=
      labeledgraph_add_edge g (u,v) u v w.

    Instance Fin_UAdjMatGG_adde':
      FiniteGraph (UAdjMatGG_adde').
    Proof.
      unfold UAdjMatGG_adde'.
      unfold labeledgraph_add_edge.
      apply pregraph_add_edge_finite.
      apply Finite_UAdjMatGG.
    Qed.

    Instance SoundUAdjMat_adde':
      SoundUAdjMat UAdjMatGG_adde'.
    Proof.
      constructor; simpl. constructor; simpl.
      +apply (size_representable g).
      +apply (inf_representable g).
      +apply (vvalid_meaning g).
      +unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
       split; intros. destruct H. unfold equiv_dec; destruct E_EqDec.
       split. pose proof (inf_representable g); lia. lia.
       apply (evalid_meaning g) in H. apply H.
       subst e. unfold equiv_dec. destruct E_EqDec.
       split. pose proof (inf_representable g); lia. lia.
       unfold complement, equiv in c; contradiction.
       unfold equiv_dec in H; destruct (E_EqDec (u,v)).
       hnf in e0; subst e. right; auto.
       left. apply (evalid_meaning g). auto.
      +unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e);  destruct H.
       hnf in e0. subst e.
       apply add_edge_strong_evalid; trivial.
       hnf in e0. subst e.
       apply add_edge_strong_evalid; trivial.
       apply add_edge_preserves_strong_evalid; trivial.
       apply (evalid_strong_evalid g); trivial.
       hnf in c. exfalso. apply c. hnf. auto. 
      + split; intros; unfold update_elabel, equiv_dec in *; destruct (E_EqDec (u,v) e).
      - exfalso. apply H. right. hnf in e0. auto.
      - apply Decidable.not_or in H. destruct H.
        apply (invalid_edge_weight g); trivial.
      - rewrite H in w_rep. lia.
      - apply Classical_Prop.and_not_or.
        split. apply <- (invalid_edge_weight g); trivial.
        auto.
        + unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
          unfold equiv in e0; subst e. simpl; auto.
          apply (edge_src_fst g e).
        +unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
         unfold equiv in e0; subst e. simpl; auto.
         apply (edge_dst_snd g e).
        +apply Fin_UAdjMatGG_adde'.
        +unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
         destruct (E_EqDec (u,v) e). hnf in e0; subst e. trivial. 
         unfold complement, equiv in c. destruct H.
         apply (undirected_edge_rep g e); auto.
         exfalso. apply c.
         symmetry. trivial.
    Qed.

    Definition UAdjMatGG_adde: UAdjMatGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
                          UAdjMatGG_adde' (SoundUAdjMat_adde').

    Lemma adde_vvalid:
      vvalid g v <-> vvalid UAdjMatGG_adde v.
    Proof.
      intros. simpl. split; auto.
    Qed.

    Lemma adde_evalid_or:
      forall e, evalid UAdjMatGG_adde e <-> (evalid g e \/ e = (u,v)).
    Proof. unfold UAdjMatGG_adde; simpl; unfold addValidFunc. intros; split; auto. Qed.

    (*all the Elist stuff are useless by themselves, because (@fin .. sound_matrx) clashes with Fin for some reason*)
    Lemma adde_EList_new:
      ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList UAdjMatGG_adde).
    Proof.
      intros. apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
      intros; split; intros. rewrite EList_evalid, adde_evalid_or. destruct H0.
      right; symmetry; auto. left; rewrite EList_evalid in H0; auto.
      rewrite EList_evalid, adde_evalid_or in H0. destruct H0. right; rewrite EList_evalid; auto. left; symmetry; auto.
    Qed.

    Lemma adde_EList_old:
      forall e, In e (EList g) -> In e (EList UAdjMatGG_adde).
    Proof.
      intros. unfold EList. destruct finiteE. simpl. destruct a.
      apply H1. rewrite adde_evalid_or. left; rewrite <- EList_evalid; apply H.
    Qed.

    Lemma adde_EList_rev:
      forall l, ~ evalid g (u,v) ->
                Permutation ((u,v)::l) (EList UAdjMatGG_adde) ->
                Permutation l (EList g).
    Proof.
      intros. apply NoDup_Permutation.
      apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
      apply NoDup_EList.
      intros; split; intros. assert (In x (EList UAdjMatGG_adde)).
      apply (Permutation_in (l:=(u,v)::l)). auto. right; auto.
      apply EList_evalid in H2. apply adde_evalid_or in H2. destruct H2.
      rewrite EList_evalid; auto.
      subst x. assert (NoDup ((u,v)::l)). apply NoDup_Perm_EList in H0; auto.
      apply NoDup_cons_2 in H2. contradiction.
      destruct (E_EqDec x (u,v)). unfold equiv in e. subst x. apply EList_evalid in H1; contradiction.
      unfold complement, equiv in c.
      apply adde_EList_old in H1.
      apply (Permutation_in (l':=(u,v)::l)) in H1. destruct H1. symmetry in H1; contradiction. auto.
      apply Permutation_sym; auto.
    Qed.

    Lemma adde_src:
      forall e', evalid g e' -> src UAdjMatGG_adde e' = src g e'.
    Proof.
      intros.
      pose proof (edge_src_fst g e').
      pose proof (edge_src_fst UAdjMatGG_adde e').
      replace (src g e') with (fst e') by trivial.
      replace (src UAdjMatGG_adde e') with (fst e') by trivial.
      reflexivity.
    Qed.

    Lemma adde_dst:
      forall e', evalid g e' -> dst UAdjMatGG_adde e' = dst g e'.
    Proof.
      intros.
      pose proof (edge_dst_snd g e').
      pose proof (edge_dst_snd UAdjMatGG_adde e').
      replace (dst g e') with (snd e') by trivial.
      replace (dst UAdjMatGG_adde e') with (snd e') by trivial.
      reflexivity.
    Qed.

    Lemma adde_elabel_new:
      elabel UAdjMatGG_adde (u,v) = w.
    Proof.
      intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec. auto.
      unfold complement, equiv in c. contradiction.
    Qed.

    Lemma adde_elabel_old:
      forall e, e <> (u,v) -> elabel UAdjMatGG_adde e = elabel g e.
    Proof.
      intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec.
      unfold equiv in e0. symmetry in e0; contradiction.
      auto.
    Qed.

    Lemma adde_partial_graph:
      forall (g': UAdjMatGG), is_partial_graph g g' -> evalid g' (u,v) -> is_partial_graph UAdjMatGG_adde g'.
    Proof.
      intros. destruct H as [? [? [? ?]]].
      split. intros. simpl. apply H. auto.
      split. intros. rewrite adde_evalid_or in H4. destruct H4.
      apply H1; auto. subst e; auto.
      split. intros. rewrite adde_evalid_or in H4. destruct H4.
      rewrite <- H2. apply adde_src. auto. auto. rewrite adde_src in H5 by auto. simpl in H5; auto.
      subst e. rewrite (edge_src_fst g').
      rewrite (edge_src_fst UAdjMatGG_adde); auto.
      intros. rewrite adde_evalid_or in H4. destruct H4.
      rewrite <- H3. apply adde_dst. auto. auto. rewrite adde_dst in H5 by auto. simpl in H5; auto.
      subst e. rewrite (edge_dst_snd g'), (edge_dst_snd UAdjMatGG_adde); auto.
    Qed.

    Lemma adde_partial_lgraph:
      forall (g': UAdjMatGG), is_partial_lgraph g g' -> evalid g' (u,v) -> w = elabel g' (u,v) -> is_partial_lgraph UAdjMatGG_adde g'.
    Proof.
      intros. split. apply adde_partial_graph. apply H. auto.
      split. unfold preserve_vlabel; intros.
      destruct vlabel. destruct vlabel. auto.
      unfold preserve_elabel; intros.
      destruct H. destruct H3. unfold preserve_elabel in H4.
      destruct (E_EqDec e (u,v)).
      unfold equiv in e0. subst e. rewrite adde_elabel_new. rewrite H1. auto.
      unfold complement, equiv in c. apply add_edge_evalid_rev in H2. rewrite adde_elabel_old.
      rewrite <- H4. all: auto.
    Qed.

  End ADD_EDGE_UADJMATGRAPH.

  Section REMOVE_EDGE_UADJMATGRAPH.

    Context {g: UAdjMatGG}.
    Context {e: E} {evalid_e: evalid g e}.

    Definition UAdjMatGG_eremove':=
      @Build_LabeledGraph V E V_EqDec E_EqDec unit Z unit (pregraph_remove_edge g e)
                          (vlabel g)
                          (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
                          (glabel g).

    Instance Fin_UAdjMatGG_eremove':
      FiniteGraph (UAdjMatGG_eremove').
    Proof.
      constructor; unfold EnumEnsembles.Enumerable; simpl.
      (*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
      (*edge*)
      unfold removeValidFunc.
      (*case e already inside*)
      exists (remove E_EqDec e (EList g)). split. apply nodup_remove_nodup. apply NoDup_EList.
      intros. rewrite remove_In_iff, EList_evalid; auto. split; auto.
    Qed.

    Instance SoundPrim_eremove':
      SoundUAdjMat UAdjMatGG_eremove'.
    Proof.
      constructor; simpl. constructor; simpl.
      ++apply (size_representable g).
      ++apply (inf_representable g).
      ++apply (vvalid_meaning g).
      ++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e).
        destruct H. hnf in e1. contradiction.
        apply (evalid_meaning g). apply H.
        destruct H. exfalso. apply H0; reflexivity.
        apply (evalid_meaning g) in H; auto.
      ++ intros. red in H. destruct H.
         apply remove_edge_preserves_strong_evalid; split; auto.
         apply (evalid_strong_evalid g); trivial.
      ++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e); trivial.
        ** apply Classical_Prop.not_and_or in H.
           destruct H.
           apply (invalid_edge_weight g); trivial.
           exfalso. apply H. apply c.
        ** apply Classical_Prop.or_not_and. right.
           unfold not. intro. apply H0. apply e1.
        ** apply Classical_Prop.or_not_and. left.
           apply <- (invalid_edge_weight g); trivial.
      ++apply (edge_src_fst g).
      ++apply (edge_dst_snd g).
      ++apply Fin_UAdjMatGG_eremove'.
      ++unfold removeValidFunc; intros. destruct H.
        apply (undirected_edge_rep g); trivial.
    Qed.

    Definition UAdjMatGG_eremove: UAdjMatGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
                          UAdjMatGG_eremove' (SoundPrim_eremove').

    Lemma eremove_EList:
      forall l, Permutation (e::l) (EList g) -> Permutation l (EList UAdjMatGG_eremove).
    Proof.
      intros. assert (Hel: NoDup (e::l)). apply NoDup_Perm_EList in H; auto.
      apply NoDup_Permutation.
      apply NoDup_cons_1 in Hel; auto.
      apply NoDup_EList.
      intros. rewrite EList_evalid. simpl. unfold removeValidFunc. rewrite <- EList_evalid. split; intros.
      split. apply (Permutation_in (l:=(e::l))). apply H. right; auto.
      unfold not; intros. subst e. apply NoDup_cons_2 in Hel. contradiction.
      destruct H0. apply Permutation_sym in H. apply (Permutation_in (l':=(e::l))) in H0. 2: auto.
      destruct H0. symmetry in H0; contradiction. auto.
    Qed.

    Lemma eremove_EList_rev:
      forall l, evalid g e -> Permutation l (EList (UAdjMatGG_eremove)) -> Permutation (e::l) (EList g).
    Proof.
      intros. assert (~ In e (EList UAdjMatGG_eremove)).
      rewrite EList_evalid. simpl. unfold removeValidFunc, not; intros. destruct H1. contradiction.
      assert (~ In e l). unfold not; intros.
      apply (Permutation_in (l':= (EList UAdjMatGG_eremove))) in H2. contradiction. auto.
      apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
      apply NoDup_EList.
      intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
      apply (Permutation_in (l':= (EList UAdjMatGG_eremove))) in H3; auto.
      rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
      destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
      unfold complement, equiv in c. right.
      assert (evalid UAdjMatGG_eremove x).
      simpl. unfold removeValidFunc. rewrite EList_evalid in H3. split; auto.
      rewrite <- EList_evalid in H4.
      apply (Permutation_in (l:= (EList UAdjMatGG_eremove))). apply Permutation_sym; auto. apply H4.
    Qed.

  End REMOVE_EDGE_UADJMATGRAPH.

  (**************MST****************)

  Definition minimum_spanning_forest (t g: UAdjMatGG) :=
    labeled_spanning_uforest t g /\
    forall (t': UAdjMatGG), labeled_spanning_uforest t' g ->
                            Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

  Lemma partial_lgraph_spanning_equiv:
    forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
                                 -> labeled_spanning_uforest t2 g -> Permutation (EList t1) (EList t2).
  Proof.
    intros. apply NoDup_Permutation.
    apply NoDup_EList. apply NoDup_EList.
    intros. repeat rewrite EList_evalid. split; intros.
    apply H. auto.
    destruct (evalid_dec t1 x). auto. exfalso.
    pose proof (trivial_path1 t2 x (evalid_strong_evalid t2 x H2)). destruct H3.
    assert (connected t1 (src t2 x) (dst t2 x)).
    apply H0. apply H1. exists (src t2 x :: dst t2 x :: nil); auto.
    destruct H5 as [p ?].
    apply connected_by_upath_exists_simple_upath in H5. clear p.
    destruct H5 as [p [? ?]].
    assert (exists l, fits_upath t1 l p). apply connected_exists_list_edges in H5; auto.
    destruct H7 as [l ?].
    assert (~ In x l). unfold not; intros. apply (fits_upath_evalid t1 p l) in H8; auto.
    assert (fits_upath t2 l p).
    apply (fits_upath_transfer' p l t1 t2) in H7; auto.
    intros; split; intros. apply H. auto. rewrite vert_bound in *; auto.
    intros. apply H. apply (fits_upath_evalid t1 p l); auto.
    intros. apply H. auto. apply (evalid_strong_evalid t1); auto.
    intros. apply H. auto. apply (evalid_strong_evalid t1); auto.
    assert (p = (src t2 x :: dst t2 x :: nil)). assert (unique_simple_upath t2). apply H1.
    unfold unique_simple_upath in H10. apply (H10 (src t2 x) (dst t2 x)).
    split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
    apply connected_exists_list_edges'. intros. rewrite vert_bound. apply (valid_upath_vvalid t1) in H11.
    rewrite vert_bound in H11; auto. apply H6.
    exists l. auto.
    apply H5. apply H5.
    split. apply H3. apply NoDup_cons.
    unfold not; intros. destruct H11. 2: contradiction.
    symmetry in H11. assert (src t2 x <> dst t2 x). apply H1. auto. contradiction.
    apply NoDup_cons. unfold not; intros; contradiction. apply NoDup_nil.
    apply H3.
    assert (x :: nil = l). apply (uforest'_unique_lpath p (x::nil) l t2).
    apply H1. split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
    rewrite H10; auto. auto.
    rewrite <- H11 in H8. apply H8. left; auto.
  Qed.

  Corollary partial_lgraph_spanning_sum_LE:
    forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
                                 -> labeled_spanning_uforest t2 g -> sum_DE Z.add t1 0 = sum_DE Z.add t2 0.
  Proof.
    intros. assert (Permutation (EList t1) (EList t2)).
    apply (partial_lgraph_spanning_equiv t1 t2 g); auto.
    unfold sum_DE. apply fold_left_comm.
    intros. lia.
    unfold DEList.
    replace (map (elabel t1) (EList t1)) with (map (elabel g) (EList t1)).
    replace (map (elabel t2) (EList t2)) with (map (elabel g) (EList t2)).
    apply Permutation_map; auto.
    apply map_ext_in. intros. symmetry; apply H1. rewrite EList_evalid in H3; auto.
    apply map_ext_in. intros. symmetry; apply H0. rewrite EList_evalid in H3; auto.
  Qed.

  Corollary partial_lgraph_spanning_mst:
    forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
                                 -> minimum_spanning_forest t2 g -> minimum_spanning_forest t1 g.
  Proof.
    intros. split. auto.
    intros. apply (Z.le_trans _ (sum_DE Z.add t2 0) _ ).
    apply Z.eq_le_incl. apply (partial_lgraph_spanning_sum_LE t1 t2 g); auto. apply H1.
    apply H1; auto.
  Qed.

  (*The following are to let us reason about lists instead of graphs*)
  Lemma sum_DE_equiv:
    forall (g: UAdjMatGG) (l: list E),
      Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
  Proof.
    unfold DEList; intros. apply fold_left_comm. intros; lia.
    apply Permutation_map. auto.
  Qed.

  Lemma partial_graph_incl:
    forall (t g: UAdjMatGG), is_partial_graph t g -> incl (EList t) (EList g).
  Proof.
    unfold incl; intros. rewrite EList_evalid in *. apply H; auto.
  Qed.

  Lemma exists_dec:
    forall (g: UAdjMatGG) l, (exists (t: UAdjMatGG), labeled_spanning_uforest t g /\ Permutation l (EList t)) \/
                             ~ (exists (t: UAdjMatGG), labeled_spanning_uforest t g /\ Permutation l (EList t)).
  Proof.
    intros. tauto.
  Qed.

  Lemma partial_lgraph_elabel_map:
    forall (t g: UAdjMatGG) l, is_partial_lgraph t g -> incl l (EList t) ->
                               map (elabel t) l = map (elabel g) l.
  Proof.
    induction l; intros. simpl; auto.
    simpl. replace (elabel g a) with (elabel t a). rewrite IHl; auto.
    apply incl_cons_inv in H0; auto.
    destruct H0; trivial. apply H. rewrite <- EList_evalid. apply H0. left; auto.
  Qed.

  Lemma Zlt_Zmin:
    forall x y, x < y -> Z.min x y = x.
  Proof. intros. rewrite Zmin_spec. destruct (zlt x y); lia. Qed.

End Mathematical_Undirected_AdjMat_Model.
