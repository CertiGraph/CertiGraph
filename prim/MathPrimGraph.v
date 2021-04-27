Require Import CertiGraph.prim.prim_env.
Require Export CertiGraph.graph.MathUAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section MathPrimGraph.
  
  Context {size : Z}.
  Context {inf : Z}.

  (* Here is the LabeledGraph *)
  Definition PrimLG := UAdjMatLG.

  (* The soundness condition *)
  Class SoundPrim (g: PrimLG) :=
    {
    basic:
      (* first, we can take AdjMat's soundness wholesale *)
      @SoundUAdjMat size inf g;

    em: (* evalid_meaning *)
      forall e, evalid g e <-> 
                Int.min_signed <= elabel g e <= Int.max_signed /\
                elabel g e < inf
    }.

  (* And here is the GeneralGraph that we will use *)
  Definition PrimGG := (GeneralGraph V E DV DE DG (fun g => SoundPrim g)).

  (* Some handy coercions: *)
  Identity Coercion UAdjMatLG_PrimLG: PrimLG >-> UAdjMatLG.
  Identity Coercion AdjMatLG_UAdjMatLG: UAdjMatLG >-> AdjMatLG.
  Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

  (* We can drag out the soundness condition *)
  Definition SoundPrim_PrimGG (g: PrimGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

  (* We can always drag out SoundAdjMat *)
  Definition SoundUAdjMat_PrimGG (g: PrimGG) :=
    @basic g (SoundPrim_PrimGG g).

  (* A PrimGG can be weakened into an AdjMatGG *)
  Definition UAdjMatGG_PrimGG (g: PrimGG) : UAdjMatGG :=
    Build_GeneralGraph DV DE DG SoundUAdjMat g (SoundUAdjMat_PrimGG g).

  Coercion UAdjMatGG_PrimGG: PrimGG >-> UAdjMatGG.
  
  Definition PrimGG_FiniteGraph (g : PrimGG) : FiniteGraph g := g.
  Coercion PrimGG_FiniteGraph: PrimGG >-> FiniteGraph. 
  Existing Instance PrimGG_FiniteGraph.
  Existing Instance Finite_UAdjMatGG.

  (* Great! So now when we want to access an AdjMat
     plugin, we can simply use the AdjMat getter 
     and pass it a PrimGG. The coercion will be seamless. 
   *)

  (* For the one new plugin, we create a getter: *)
  Definition evalid_meaning (g: PrimGG) :=
    @em g (SoundPrim_PrimGG g).


  (* Lemmas based on the above *)

  Lemma evalid_inf_iff:
    forall (g: PrimGG) e, evalid g e <-> elabel g e < inf.
  Proof.
    intros; split; intros.
    apply (evalid_meaning g); auto.
    destruct (evalid_dec g e). 
    auto. exfalso.
    rewrite (invalid_edge_weight g) in n.
    replace (elabel g e) with inf in * by trivial.
    lia.
  Qed.
  
  Lemma weight_inf_bound:
    forall (g: PrimGG) e, elabel g e <= inf.
  Proof.
    intros. destruct (evalid_dec g e).
    apply Z.lt_le_incl. apply (evalid_meaning  g e). auto.
    apply (invalid_edge_weight g) in n.
    replace (elabel g e) with inf in * by trivial. lia.
  Qed.

  Corollary eformat_adj_elabel: forall (g: PrimGG) u v, adjacent g u v <-> elabel g (eformat (u,v)) < inf.
  Proof.
    intros. rewrite (eformat_adj g). apply evalid_inf_iff.
  Qed.

  (*The following two could not be moved because they require a massage allowing in_dec
to be used as a bool, and I don't know what allows it*)
  Lemma filter_list_Permutation:
    forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A),
      NoDup l2 ->
      Permutation
        ((filter (fun x => in_dec EA x l1) l2) ++ (filter (fun x => negb (in_dec EA x l1)) l2))
        l2.
  Proof.
    intros. apply NoDup_Permutation.
    apply NoDup_app_inv. apply NoDup_filter. auto. apply NoDup_filter. auto.
    intros. rewrite filter_In in H0. rewrite filter_In. destruct H0.
    unfold not; intros. destruct H2. destruct (in_dec EA x l1).
    inversion H3. inversion H1. auto.
    intros; split; intros.
    apply in_app_or in H0; destruct H0; rewrite filter_In in H0; destruct H0; auto.
    apply in_or_app. repeat rewrite filter_In.
    destruct (in_dec EA x l1). left; split; auto. right; split; auto.
  Qed.

  Corollary path_partition_checkpoint2:
    forall (g: PrimGG) {fg: FiniteGraph g} (l: list V) p l' a b, In a l -> ~ In b l ->
                                                                 connected_by_path g p a b -> fits_upath g l' p ->
                                                                 exists v1 v2, In v1 p /\ In v2 p /\
                                                                               In v1 l /\ ~ In v2 l /\ (exists e, adj_edge g e v1 v2 /\ In e l').
  Proof.
    intros.
    apply (path_partition_checkpoint' g
                                      (filter (fun x => (in_dec V_EqDec x l)) (VList g))
                                      (filter (fun x => negb (in_dec V_EqDec x l)) (VList g)) p l' a b
          ) in H2.
    2: { apply filter_list_Permutation. apply NoDup_VList. }
    2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
         destruct (in_dec V_EqDec a l). auto. contradiction. }
    2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
         destruct (In_dec V_EqDec b l). contradiction. auto. }
    2: auto.
    destruct H2 as [v1 [v2 [? [? [? [? ?]]]]]].
    exists v1; exists v2. split. auto. split. auto.
    split. rewrite filter_In in H4. destruct H4. destruct (in_dec V_EqDec v1 l). auto. inversion H7.
    split. rewrite filter_In in H5. destruct H5. destruct (in_dec V_EqDec v2 l). inversion H7. auto.
    auto.
  Qed.

  Context {inf_bound: 0 < inf <= Int.max_signed}.
  Context {size_bound: 0 < size <= Int.max_signed}.
  
  Definition edgeless_lgraph : PrimLG :=
    @Build_LabeledGraph
      V E V_EqDec E_EqDec DV DE DG
      (@Build_PreGraph V E V_EqDec E_EqDec
                       (fun v => 0 <= v < size)
                       (fun e => False) fst snd)
      (fun v => tt) (fun e => inf) tt.
  
  Instance SoundPrim_edgeless:
    SoundPrim edgeless_lgraph.
  Proof. 
    constructor.
    { constructor.
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
    }
    split; intros.
    inversion H. destruct H. simpl in H0.
    exfalso.
    apply Zlt_not_le in H0. apply H0. reflexivity.    
    Qed.

    Definition edgeless_graph: PrimGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG SoundPrim
                          edgeless_lgraph SoundPrim_edgeless.

    Lemma edgeless_graph_evalid:
      forall e, ~ evalid edgeless_graph e.
    Proof.
      intros. unfold edgeless_graph; simpl. auto.
    Qed.

    Lemma vert_bound:
      forall (g: PrimGG) v, vvalid g v <-> 0 <= v < size.
    Proof.
      intros. apply (vvalid_meaning g).
    Qed.
    
    Lemma edgeless_partial_lgraph:
      forall (g: PrimGG), is_partial_lgraph edgeless_graph g.
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

    Section REMOVE_EDGE_PRIGRAPH.

    Context {g: PrimGG}.
    Context {e: E} {evalid_e: evalid g e}.

    Definition PrimGG_eremove':=
      @Build_LabeledGraph V E V_EqDec E_EqDec unit Z unit (pregraph_remove_edge g e)
                          (vlabel g)
                          (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
                          (glabel g).

        Instance SoundPrim_eremove':
      SoundPrim PrimGG_eremove'.
    Proof.
      constructor; simpl. constructor; simpl. constructor; simpl.
      ++apply (size_representable g).
      ++apply (inf_representable g).
      ++apply (vvalid_meaning g).
      ++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e).
        destruct H. hnf in e1. contradiction.
        split.
        ** apply (evalid_meaning g). apply H.
        ** intro.
           pose proof (evalid_meaning g e0).
           destruct H.
           rewrite H1 in H. destruct H. rewrite H0 in H3.
           apply Zlt_not_le in H3. apply H3. reflexivity.
        ** destruct H. exfalso. apply H0; reflexivity.
        ** admit.
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
      ++apply pregraph_remove_edge_finite, PrimGG_FiniteGraph.
      ++unfold removeValidFunc; intros. destruct H.
        apply (undirected_edge_rep g); trivial.
      ++ admit.
    Admitted.


        
    Definition PrimGG_eremove: PrimGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundPrim
                          PrimGG_eremove' (SoundPrim_eremove').
            
    Lemma eremove_EList:
      forall l, Permutation (e::l) (EList g) -> Permutation l (EList PrimGG_eremove).
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

    End REMOVE_EDGE_PRIGRAPH.

  Section ADD_EDGE_UADJMATGRAPH.

    Context {g: PrimGG}.
    Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
    Context {w: Z} {w_rep: Int.min_signed <= w < inf}.

    Definition PrimGG_adde':=
      labeledgraph_add_edge g (u,v) u v w.

        Instance Fin_PrimGG_adde':
      FiniteGraph (PrimGG_adde').
    Proof.
      unfold PrimGG_adde'.
      unfold labeledgraph_add_edge.
      apply pregraph_add_edge_finite.
      apply PrimGG_FiniteGraph.
    Qed.

    Instance SoundPrim_adde':
      SoundPrim PrimGG_adde'.
    Proof.
      constructor; simpl. constructor; simpl. constructor; simpl.
      +apply (size_representable g).
      +apply (inf_representable g).
      +apply (vvalid_meaning g).
      +unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
       split; intros. destruct H. unfold equiv_dec; destruct E_EqDec.
       split. pose proof (inf_representable g); lia. lia.
       apply (evalid_meaning g) in H. admit.
       (* apply H. *)
       subst e. unfold equiv_dec. destruct E_EqDec.
       split. pose proof (inf_representable g); lia. lia.
       unfold complement, equiv in c; contradiction.
       unfold equiv_dec in H; destruct (E_EqDec (u,v)).
       hnf in e0; subst e. right; auto.
       left. apply (evalid_meaning g). auto. admit.
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
        +apply pregraph_add_edge_finite, PrimGG_FiniteGraph.
        +unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
         destruct (E_EqDec (u,v) e). hnf in e0; subst e. trivial. 
         unfold complement, equiv in c. destruct H.
         apply (undirected_edge_rep g e); auto.
         exfalso. apply c.
         symmetry. trivial.
        + admit.
    Admitted.

    Definition PrimGG_adde: PrimGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundPrim
                          PrimGG_adde' (SoundPrim_adde').


    End ADD_EDGE_UADJMATGRAPH.
    
  Lemma exists_labeled_spanning_uforest_pre:
    forall (l: list E) (g: PrimGG), Permutation l (EList g) -> exists (t: PrimGG), labeled_spanning_uforest t g.
  Proof.
    induction l; intros.
    (*nil case*)
    exists edgeless_graph.
    split. split.
    (* admit. *)
    apply edgeless_partial_lgraph. split. apply uforest'_edgeless_graph.
    unfold spanning; intros. destruct (V_EqDec u v).
    hnf in e. subst v. split; intros; apply connected_refl.
    apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
    apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
    unfold complement, equiv in c. split; intros. exfalso. destruct H0.
    unfold connected_by_path in H0. destruct H0. destruct H1. destruct x. inversion H1.
    destruct x. inversion H1. inversion H2. subst v0. contradiction.
    destruct H0. destruct H0. destruct H0. destruct H0.
    rewrite <- EList_evalid in H0. rewrite <- H in H0. contradiction.
    pose proof (edgeless_graph_disconnected u v c).
    contradiction.
    unfold preserve_vlabel, preserve_elabel; split; intros.
    destruct vlabel. destruct vlabel. auto.
    pose proof (edgeless_graph_evalid e).
    contradiction.
    (*inductive step*)
    set (u:=src g a). set (v:=dst g a).
    assert (connected g u v). apply adjacent_connected. exists a.
    unfold u; unfold v; apply strong_evalid_adj_edge.
    apply (evalid_strong_evalid g). rewrite <- EList_evalid, <- H. left; auto.
    set (remove_a:=(@PrimGG_eremove g a)).
    assert (Ha_evalid: evalid g a). {
      rewrite <- EList_evalid. apply (Permutation_in (l:=(a::l))).
      apply H. left; auto. }
    specialize IHl with (remove_a Ha_evalid).
    destruct IHl as [t ?]. {
      unfold remove_a.
      pose proof (@eremove_EList _ a Ha_evalid l H).
      apply NoDup_Permutation. assert (NoDup (a::l)). apply (Permutation_NoDup (l:=EList g)).
      apply Permutation_sym; auto. apply NoDup_EList. apply NoDup_cons_1 in H2; auto.
      apply NoDup_EList.
      intros. rewrite EList_evalid. split; intros.
      pose proof (Permutation_in (l:=l) (l':=_) x H1 H2). rewrite EList_evalid in H3; auto.
      apply Permutation_sym in H1.
      apply (Permutation_in (l:=_) (l':=l) x H1). rewrite EList_evalid; auto.
    }
    assert (Htg: is_partial_lgraph t g). {
      destruct H1. destruct H2. destruct H1. destruct H4. split.
      split. intros. apply H1 in H6. auto.
      split. intros. destruct H1. destruct H7. apply H7. auto.
      split. intros. apply H1 in H7. simpl in H7. auto. auto.
      intros. apply H1 in H7. simpl in H7. auto. auto.
      unfold preserve_vlabel, preserve_elabel; split; intros.
      destruct vlabel. destruct vlabel. auto.
      rewrite H3 by auto. simpl. destruct (E_EqDec e a). unfold equiv in e0.
      subst e. assert (evalid (remove_a Ha_evalid) a). apply H1; auto.
      simpl in H7. unfold removeValidFunc in H7. destruct H7; contradiction.
      auto.
    }
    destruct (connected_dec (remove_a Ha_evalid) u v).
    (*already connected*)
    ++
      exists t. destruct H1.  destruct H3. destruct H1. destruct H5.
      split. split.
      (*partial_graph*)
      apply Htg.
      (*uforest*)
      split. auto.
      (*spanning*)
      unfold spanning in *. intros. rewrite <- H6. split; intros.
      {(*---------->*)
        destruct H7 as [p ?].
        apply (connected_by_upath_exists_simple_upath) in H7. destruct H7 as [p' [? ?]]. clear p.
        assert (exists l, fits_upath g l p'). apply (connected_exists_list_edges g p' u0 v0); auto.
        destruct H9 as [l' ?]. destruct (in_dec E_EqDec a l').
        **(*yes: split the path*)
          assert (NoDup l'). apply (simple_upath_list_edges_NoDup g p' l'); auto.
          apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
          destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. subst l'. fold u in H11. fold v in H11.
          assert (~ In a l1). unfold not; intros.
          apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14. apply H14.
          apply in_or_app. left; left; auto.
          assert (~ In a l2). unfold not; intros.
          apply NoDup_app_r in H10. apply (NoDup_app_not_in E (a::nil) l2 H10 a).
          left; auto. auto.
          destruct H11; destruct H11.
          ****
            apply (connected_trans _ u0 u). exists p1. split.
            apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
            apply (connected_trans _ u v). auto.
            exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
          ****
            apply (connected_trans _ u0 v). exists p1. split.
            apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
            apply (connected_trans _ v u). apply connected_symm; auto.
            exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
        **(*no: fits_upath_transfer*)
          exists p'. split. apply (remove_edge_valid_upath _ a p' l'); auto. apply H7. apply H7.
      } { (*<---*)
        destruct H7 as [p [? ?]]. exists p. split.
        apply remove_edge_unaffected in H7; auto. auto.
      }
      (*labels*)
      apply Htg.
    ++
      assert (vvalid g u /\ vvalid g v). apply connected_vvalid in H0; auto. destruct H3.
      assert (u <= v). apply (undirected_edge_rep g). auto.
      set (w:= elabel g a).
      assert (Int.min_signed <= w < inf). unfold w. split.
      pose proof (weight_representable g a). apply H6. apply (evalid_meaning g). auto.
      rewrite vert_bound in H3, H4. rewrite <- (vert_bound t) in H3, H4.
      assert (Ha: a = (u,v)). unfold u, v; apply (evalid_form g); auto. rewrite Ha in *.
      set (adde_a:=@PrimGG_adde t u v H3 H4 H5 w H6).
      exists adde_a. split. split.
      admit.
      split.
      (*uforest*)
      apply add_edge_uforest'; auto. apply H1.
      unfold not; intros.
      apply (is_partial_lgraph_connected t (remove_a Ha_evalid)) in H7. contradiction.
      split. apply H1. apply H1.
      (*spanning*)
      unfold spanning; intros. assert (Ht_uv: ~ evalid t (u,v)). unfold not; intros.
      assert (evalid (remove_a Ha_evalid) (u,v)). apply H1; auto.
      simpl in H8. rewrite Ha in H8. unfold removeValidFunc in H8. destruct H8; contradiction.
      split; intros.
      { (*-->*) destruct H7 as [p ?]. apply connected_by_upath_exists_simple_upath in H7.
        destruct H7 as [p' [? ?]]. clear p.
        assert (exists l', fits_upath g l' p'). apply connected_exists_list_edges in H7; auto.
        destruct H9 as [l' ?]. assert (NoDup l'). apply simple_upath_list_edges_NoDup in H9; auto.
        destruct (in_dec E_EqDec a l').
        **
          apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
          destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. fold u in H11. fold v in H11. subst l'.
          assert (~ In a l1). unfold not; intros. apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14.
          apply H14. apply in_or_app. left; left; auto.
          assert (~ In a l2). unfold not; intros. apply NoDup_app_r in H10.
          apply (NoDup_app_not_in E (a::nil) l2 H10 a). left; auto. auto.
          destruct H11; destruct H11.
          ****
            apply (connected_trans _ u0 u). apply add_edge_connected; auto.
            apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
            apply (connected_trans _ u v). apply adjacent_connected.
            exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
            apply add_edge_connected; auto. apply H1. exists p2. split.
            apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
          ****
            apply (connected_trans _ u0 v). apply add_edge_connected; auto.
            apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
            apply (connected_trans _ v u). apply adjacent_connected. apply adjacent_symm.
            exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
            apply add_edge_connected; auto. apply H1. exists p2. split.
            apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
        **
          apply add_edge_connected; auto.
          apply H1. exists p'. split. 2: apply H7.
          apply (remove_edge_valid_upath g a p' l'); auto. apply H7.
      } {
        apply (is_partial_lgraph_connected adde_a g).
        admit. auto.
      }
      (*labels*)
      unfold preserve_vlabel, preserve_elabel; split; intros.
      destruct vlabel; destruct vlabel; auto.
      simpl. unfold update_elabel, equiv_dec.
      destruct (E_EqDec (u,v) e). hnf in e0. subst e. unfold w; rewrite Ha; auto.
      apply Htg. simpl in H7. unfold addValidFunc in H7. destruct H7. apply H7.
      unfold complement, equiv in c. symmetry in H7; contradiction.
  Admitted.

  Corollary exists_labeled_spanning_uforest:
    forall (g: PrimGG), exists (t: PrimGG), labeled_spanning_uforest t g.
  Proof.
    intros. apply (exists_labeled_spanning_uforest_pre (EList g)). apply Permutation_refl.
  Qed.


  (* needs PrimGG and NoDup_incl_ordered_powerlist, which means it should probably stay right here *) 
  Lemma exists_msf:
    forall {E_EqDec : EqDec E eq} (g: PrimGG), exists (t: PrimGG), minimum_spanning_forest t g.
  Proof.
  Admitted.
  (*
    intros. pose proof (NoDup_incl_ordered_powerlist (EList g) (NoDup_EList g)).
    destruct H as [L ?].
    (*now what I need is the subset of L that exists t, labeled_spanning_uforest t g ...*)
    destruct (list_decidable_prop_reduced_list
                (fun l' => NoDup l' /\ incl l' (EList g) /\ (forall x y, In x l' -> In y l' ->
                                                                         (find l' x 0 <= find l' y 0 <-> find (EList g) x 0 <= find (EList g) y 0)))
                (fun l => (exists (t: PrimGG), labeled_spanning_uforest t g /\ Permutation l (EList t)))
                L
             ).
    apply exists_dec.
    intros; split; intros. rewrite <- H in H0. destruct H0 as [? [? ?]].
    split. apply H0. split. apply H1. apply H2.
    rewrite <- H. auto.
    rename x into Lspan.
    assert (Lspan <> nil). unfold not; intros. {
      destruct (exists_labeled_spanning_uforest g) as [t ?].
      destruct (test2 (EList t) (EList g)) as [lt ?]. apply NoDup_EList. apply NoDup_EList.
      apply partial_graph_incl. apply H2. destruct H3.
      assert (In lt Lspan). apply H0. split. split. apply (Permutation_NoDup (l:=EList t)).
      apply Permutation_sym; auto. apply NoDup_EList.
      split. unfold incl; intros. apply (Permutation_in (l':=EList t)) in H5; auto.
      apply (partial_graph_incl t g) in H5; auto. apply H2. apply H4.
      exists t. split; auto.
      rewrite H1 in H5; contradiction.
    }
    pose proof (exists_Zmin Lspan (fun l => fold_left Z.add (map (elabel g) l) 0) H1).
    destruct H2 as [lmin [? ?]].
    apply H0 in H2. destruct H2. destruct H2 as [? [? ?]]. destruct H4 as [msf [? ?]].
    exists msf. unfold minimum_spanning_forest. split. apply H4. intros.
    destruct (test2 (EList t') (EList g)) as [lt' ?]. apply NoDup_EList. apply NoDup_EList.
    apply partial_graph_incl. apply H8. destruct H9.
    rewrite (sum_DE_equiv msf lmin). 2: apply Permutation_sym; auto.
    rewrite (sum_DE_equiv t' lt'). 2: apply Permutation_sym; auto.
    replace (map (elabel msf) lmin) with (map (elabel g) lmin).
    replace (map (elabel t') lt') with (map (elabel g) lt').
    apply H3. apply H0. split. split.
    apply (Permutation_NoDup (l:=EList t')). apply Permutation_sym; auto. apply NoDup_EList.
    split. unfold incl; intros. apply (Permutation_in (l':=EList t')) in H11; auto.
    apply (partial_graph_incl t' g) in H11. auto. apply H8.
    apply H10. exists t'. split; auto.
    symmetry; apply partial_lgraph_elabel_map. split. apply H8. apply H8.
    apply Permutation_incl; auto.
    symmetry; apply partial_lgraph_elabel_map. split. apply H4. apply H4.
    apply Permutation_incl; auto.
  Qed.
   *)
  
 Lemma msf_if_le_msf:
forall {E_EqDec : EqDec E eq} (t g: PrimGG), labeled_spanning_uforest t g ->
  (forall t', minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
  (@minimum_spanning_forest size inf t g).
 Proof.
 Admitted.
 (*
intros. unfold minimum_spanning_forest. split. auto.
intros. destruct (exists_msf g) as [msf ?].
apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
apply H2. auto.
Qed.
*)

  Corollary msf_if_le_msf':
    forall {E_EqDec : EqDec E eq} (t t' g: PrimGG), labeled_spanning_uforest t g ->
                                                       minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
                                                       minimum_spanning_forest t g.
  Proof.
  Admitted.
  (*
    intros. apply msf_if_le_msf; auto.
    intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
    apply H0. apply H2.
  Qed.
   *)

End MathPrimGraph.
