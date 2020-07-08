Require Import VST.floyd.proofauto.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
(*for ufgraph *)
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
(*for unionfind*)
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
(*edgelist*)
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
Require Import RamifyCoq.kruskal.kruskal_uf_specs.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [makeSet_spec; find_spec; union_spec;
      mallocK_spec; free_spec; fill_edge_spec; init_empty_graph_spec; sort_edges_spec; kruskal_spec
  ]).

Local Open Scope Z_scope.

Lemma reachable_uf_equiv_connected:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    reachable g1 u v ->
    connected g2 u v.
Proof.
  intros.
  pose proof (reachable_foot_valid _ _ _ H0).
  pose proof (reachable_head_valid _ _ _ H0).
  destruct H.
  assert (EnumEnsembles.EnumCovered Z (evalid g2)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  assert (EnumEnsembles.EnumCovered Z (evalid g1)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  assert (vvalid g2 u). {
    apply H; trivial.
  }
  assert (vvalid g2 v). {
    apply H; trivial.
  }
  pose proof (uf_root_always_exists g1 (liGraph g1) u X0 H2).
  pose proof (uf_root_always_exists g1 (liGraph g1) v X0 H1).
  pose proof (uf_root_always_exists g2 (liGraph g2) u X H4).
  pose proof (uf_root_always_exists g2 (liGraph g2) v X H5).
  destruct H6 as [ur1 ?].
  destruct H7 as [vr1 ?].
  destruct H8 as [ur2 ?].
  destruct H9 as [vr2 ?].
  pose proof (H3 _ _ _ H6 H8).
  pose proof (H3 _ _ _ H7 H9).
  pose proof (uf_root_reachable _ _ _ _ H0 H7).
  pose proof (uf_root_unique _ _ _ _ _ H6 H12).
  subst ur1. subst vr1. subst vr2.
  clear H6 H7.
  destruct H8 as [? _].
  destruct H9 as [? _].
  apply reachable_implies_connected in H6.
  apply reachable_implies_connected in H7.
  apply connected_symm in H7.
  apply (connected_trans _ _ _ _ H6 H7).
Qed.

Lemma uf_equiv_adjacent_connected:
  forall (g1 g2 : UFGraph) u v,
    uf_equiv g1 g2 ->
    adjacent g1 u v ->
    connected g2 u v.
Proof.
  intros.
  apply adjacent_reachable in H0.
  destruct H0.
  - apply (reachable_uf_equiv_connected g1); trivial.
  - apply connected_symm.
    apply (reachable_uf_equiv_connected g1); trivial.
Qed.

Lemma uf_equiv_connected':
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    connected g1 u v ->
    connected g2 u v.
Proof.
  intros.
  rewrite connected_exists_path in H0.
  destruct H0 as [p [? [? ?]]].
  generalize dependent u.
  induction p.
  - intros. inversion H1.
  - destruct p.
    + intros. simpl in H1, H2.
      inversion H1. inversion H2.
      subst.
      apply connected_refl; trivial.
      simpl in H0. destruct H. apply H; trivial.
    + destruct H0.
      rewrite last_error_cons in H2.
      2: unfold not; inversion 1.
      specialize (IHp H1 H2).
      intros.
      simpl in H3. inversion H3; subst a; clear H3.
      assert (connected g2 z v). {
        apply adjacent_requires_vvalid in H0.
        destruct H0.
        apply IHp; trivial.
      }
      apply (uf_equiv_adjacent_connected _ g2) in H0; trivial.
      apply (connected_trans _ _ _ _ H0 H3).
Qed.

Lemma uf_equiv_connected:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    connected g1 u v <-> connected g2 u v.
Proof.
  intros. split; intros.
  - apply (uf_equiv_connected' g1); trivial.
  - apply uf_equiv_sym in H.
    apply (uf_equiv_connected' g2); trivial.
Qed.

Lemma adjacent_ufroot_same:
  forall (g: UFGraph) u v,
    adjacent g u v ->
    ufroot_same g u v.
Proof.
  intros.
  apply adjacent_reachable in H.
  destruct H.
  - apply (reachable_ufroot_same _ (liGraph g)); trivial. 
  - apply ufroot_same_symm, (reachable_ufroot_same _ (liGraph g)); trivial.
Qed.

Lemma connected_ufroot_same:
  forall (g: UFGraph) u v,
    connected g u v ->
    ufroot_same g u v.
Proof.
  intros.
  rewrite connected_exists_path in H.
  destruct H as [p [? [? ?]]].
  generalize dependent u.
  induction p.
  - intros. inversion H1.
  - destruct p.
    + intros. simpl in H1, H0.
      inversion H1. inversion H0.
      subst. apply (ufroot_same_refl _ (liGraph g)).
      simpl in H; trivial.
    + destruct H.
      rewrite last_error_cons in H1.
      2: unfold not; inversion 1.
      specialize (IHp H0 H1).
      intros.
      simpl in H2. inversion H2; subst a; clear H2.
      apply adjacent_ufroot_same in H.
      apply (ufroot_same_trans _ (liGraph g) _ z); trivial.       apply IHp. trivial.
Qed.

Lemma ufroot_same_connected:
  forall (g: UFGraph) u v,
    ufroot_same g u v ->
    connected g u v.
Proof.
  intros.
  destruct H as [r [[? _] [? _]]].
  apply reachable_implies_connected in H.
  apply reachable_implies_connected in H0.
  apply connected_symm in H0.
  apply (connected_trans _ _ _ _ H H0).
Qed.

Lemma connected_ufroot_same_iff:
  forall (g: UFGraph) u v,
    connected g u v <-> ufroot_same g u v. 
Proof.
  intros. split; intros.
  apply connected_ufroot_same; trivial.
  apply ufroot_same_connected; trivial.
Qed.

Lemma uf_equiv_ufroot_same:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    ufroot_same g1 u v <-> ufroot_same g2 u v.
Proof.
(*Probably can be independent of the connectedness
Using for now for convenience, given connected gives vvalid*)
intros. do 2 rewrite <- connected_ufroot_same_iff. apply uf_equiv_connected. auto.
Qed.

(* basic UF helpers local to this verification. 
can be inlined or moved to UF *)
Lemma uf_root_unique':
  forall (g: UFGraph) x r1 r2,
    uf_root g x r1 ->
    uf_root g x r2 ->
    r1 = r2.
Proof.
  intros. apply (uf_root_unique _ (liGraph g) x); trivial.
Qed.

Lemma ufroot_vvalid_rt:
  forall (g: UFGraph) rt v,
    uf_root g v rt ->
    vvalid g rt.
Proof.
  intros. destruct H as [? _].
  apply (reachable_foot_valid _ _ _ H).
Qed.

Lemma ufroot_vvalid_vert:
  forall (g: UFGraph) rt v,
    uf_root g v rt ->
    vvalid g v.
Proof.
  intros. destruct H as [? _].
  apply (reachable_head_valid _ _ _ H).
Qed.

Lemma ufroot_uf_set_in:
  forall (g: UFGraph) u u_rt,
    uf_root g u u_rt ->
    uf_set_in g (ufroot_same g u).
Proof.
  intros. right. exists u_rt. split.
  - apply connected_ufroot_same. destruct H as [? _].
    apply reachable_implies_connected; trivial.
  - intros. split; intros.
    + destruct H0 as [? [? ?]].
      replace u_rt with x0; trivial.
      apply (uf_root_unique _ (liGraph g) u); trivial.
    + exists u_rt; split; trivial.
Qed.

(* Just a little utility to cleanly drag out 
   a valid vertex's root *) 
Lemma vvalid_get_ufroot:
  forall (g: UFGraph) x,
    vvalid g x ->
    exists x_rt, uf_root g x x_rt.
Proof.
  intros.
  assert (EnumEnsembles.EnumCovered Z (evalid (UFGraph_LGraph g))). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
    }
  pose proof (uf_root_always_exists _ (liGraph g) x X H).
  destruct H0 as [x_rt ?].
  exists x_rt; trivial.
Qed.

Lemma inhabited_set_nonempty:
  forall U (S: Ensemble U) v,
    S v ->
    Same_set S (Empty_set U) ->
    False.
Proof.
  intros.
  assert (Ensembles.Inhabited _ S). {
    apply (Ensembles.Inhabited_intro _ _ v); trivial.
  }
  apply (Constructive_sets.Inhabited_not_empty _ _ H1).
  apply Ensembles.Extensionality_Ensembles; trivial.
Qed.

Lemma same_set_contra:
  forall (U: Type) S1 S2 x,
    @Same_set U S1 S2 ->
    S1 x ->
    ~ S2 x ->
    False.
Proof.
  intros. 
  apply Ensembles.Extensionality_Ensembles in H.
  apply H1. rewrite <- H; trivial.
Qed.

Lemma ufroot_same_false:
  forall (g: UFGraph) a b a_rt b_rt,
    uf_root g a a_rt ->
    uf_root g b b_rt ->
    a_rt <> b_rt ->
    ufroot_same g a b ->
    False.
Proof.
  intros.
  destruct H2 as [? [? ?]].
  apply H1.
  pose proof (uf_root_unique _ (liGraph g) _ _ _ H2 H).
  pose proof (uf_root_unique _ (liGraph g) _ _ _ H3 H0).
  lia.
Qed.

(* the vertices that were unaffected by union u v *)
Lemma uf_union_unaffected_gen:
  forall (g1 g2 : UFGraph) a b (S1 S2 S3 : uf_set),
    S1 a ->
    S2 b ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    ~ Same_set S3 S1 ->
    ~ Same_set S3 S2 ->
    uf_set_in g1 S3 ->
    uf_union g1 a b g2 ->
    uf_set_in g2 S3.
Proof.
  intros. specialize (H6 _ _ H H0 H1 H2).
  destruct H6 as [? [? ?]].
  specialize (H7 _ H3 H4 H5); trivial.
Qed.

Lemma uf_union_unaffected_inhabited:
  forall (g1 g2 : UFGraph) a b v (S1 S2 S3 : uf_set),
    S1 a ->
    S2 b ->
    S3 v -> (* new thing *)
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    ~ Same_set S3 S1 ->
    ~ Same_set S3 S2 ->
    uf_set_in g1 S3 ->
    uf_union g1 a b g2 ->
    exists rt : Z, S3 rt /\ (forall x : Z, S3 x <-> uf_root g2 x rt).
Proof.
  intros.
  apply (uf_union_unaffected_gen _ _ _ _ S1 S2 S3) in H7; trivial.
  unfold uf_set_in in H7. destruct H7; trivial.
  exfalso; apply (inhabited_set_nonempty _ _ _ H1 H7).
Qed.

(* and specifically, this gives us vvalid... *)
Lemma uf_union_unaffected_vvalid:
  forall (g1 g2 : UFGraph) a b v (S1 S2 S3 : uf_set),
    S1 a ->
    S2 b ->
    S3 v ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    ~ Ensembles.Same_set S3 S1 ->
    ~ Ensembles.Same_set S3 S2 ->
    uf_set_in g1 S3 ->
    uf_union g1 a b g2 ->
    vvalid g2 v.
Proof.
  intros.
  apply (uf_union_unaffected_inhabited _ _ _ _ v S1 S2 S3) in H7; trivial.
  destruct H7 as [? [? ?]].
  apply (ufroot_vvalid_vert _ x), H8; trivial.
Qed.

(* commenting on the items that _were_ in S1 *)
(* by commutativity of Union, this comments on items
   that were in S1 or S2 *)   
Lemma uf_union_affected_gen:
  forall (g1 g2 : UFGraph) (a b : Z) (S1 S2 : uf_set),
    S1 a ->
    S2 b ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    uf_union g1 a b g2 ->
    uf_set_in g2 (Ensembles.Union Z S1 S2).
Proof.
  intros. red in H3.
  destruct (H3 _ _ H H0 H1 H2) as [? _]; trivial.
Qed.

Lemma uf_union_affected_inhabited:
  forall (g1 g2 : UFGraph) (a b : Z) (S1 S2 : uf_set),
    S1 a ->
    S2 b ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    uf_union g1 a b g2 ->
    exists rt : Z, Ensembles.Union Z S1 S2 rt /\ (forall x : Z, Ensembles.Union Z S1 S2 x <-> uf_root g2 x rt).
Proof.
  intros.
  apply (uf_union_affected_gen _ _ _ _ S1 S2) in H3; trivial.
  destruct H3; trivial.
  exfalso.
  apply (inhabited_set_nonempty _ (Ensembles.Union Z S1 S2) a); trivial.
  apply Union_introl; trivial.
Qed.

(* and specifically, this gives us vvalid... *)
Lemma uf_union_affected_vvalid:
  forall (g1 g2 : UFGraph) (a b v : Z) (S1 S2 : uf_set),
    S1 a ->
    S2 b ->
    S1 v ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    uf_union g1 a b g2 ->
    vvalid g2 v.
Proof.
  intros.
  apply (uf_union_affected_inhabited _ _ _ _ S1 S2) in H4; trivial.
  destruct H4 as [? [? ?]].
  apply (ufroot_vvalid_vert _ x),  H5, Union_introl; trivial.
Qed.

Lemma uf_union_backwards_cases:
  forall (g1 g2: UFGraph) (S1 S2 S : uf_set) a b x,
    S1 a ->
    S2 b ->
    uf_set_in g1 S1 ->
    uf_set_in g1 S2 ->
    S x ->
    uf_set_in g2 S ->
    uf_union g1 a b g2 ->
    Same_set S (Ensembles.Union Z S1 S2) \/ uf_set_in g1 S.
Proof.
  intros.
  specialize (H5 _ _ H H0 H1 H2).
  destruct H5 as [_ [_ ?]]. apply H5; trivial.
Qed.

Lemma ufroot_same_uf_root_trans:
  forall (g : UFGraph) a b rt,
    ufroot_same g a b ->
    uf_root g a rt ->
    uf_root g b rt.
Proof.
  intros.
  destruct H as [? [? ?]].
  replace rt with x; trivial.
  apply (uf_root_unique _ (liGraph g) a); trivial.
Qed.

Lemma uf_union_create_precons:
  forall (g: UFGraph) u v,
    vvalid g u ->
    vvalid g v ->
    exists u_rt v_rt,
      uf_root g u u_rt /\
      uf_root g v v_rt /\
      ufroot_same g u u /\
      ufroot_same g v v /\
      uf_set_in g (ufroot_same g u) /\
      uf_set_in g (ufroot_same g v).
Proof.
  intros.
  pose proof (ufroot_same_refl _ (liGraph g) u H).
  pose proof (ufroot_same_refl _ (liGraph g) v H0).  assert (H3 := H1).
  assert (H4 := H2).  
  destruct H1 as [u_rt [? _]].
  destruct H2 as [v_rt [? _]].
  pose proof (ufroot_uf_set_in _ _ _ H1).
  pose proof (ufroot_uf_set_in _ _ _ H2).
  exists u_rt, v_rt.
  split3; [| |split3; [| |split]]; trivial.
Qed.

Lemma uf_union_vvalid:
  forall (g1 g2: UFGraph) u v x,
    vvalid g1 u ->
    vvalid g1 v ->
    uf_union g1 u v g2 ->
    vvalid g1 x <-> vvalid g2 x.
Proof.
  intros.
  pose proof (uf_union_create_precons _ _ _ H H0).
  destruct H2 as [u_rt [v_rt [? [? [? [? [? ?]]]]]]].
  split; intros.
  (* -> *)
  - pose proof (vvalid_get_ufroot _ _ H8).
    destruct H9 as [x_rt ?].
    (* now we take cases to see whether x was
       connected to u, to v, or to neither
     *)
    destruct (Z.eq_dec x_rt u_rt). {
      (* x was connected to u in g1 *)
      subst x_rt.
      assert (ufroot_same g1 u x). {
        exists u_rt; split; trivial.
      }
      apply (uf_union_affected_vvalid g1 g2 _ _ _ _ _ H4 H5); trivial.
    }

    destruct (Z.eq_dec x_rt v_rt). {
      (* x was connected to v in old graph *)
      subst x_rt.
      assert (ufroot_same g1 v x). {
        exists v_rt; split; trivial.
      }
      apply (uf_union_affected_vvalid g1 g2 _ _ _ _ _ H5 H4); trivial.
      apply uf_union_sym; trivial.
    }

    (* x was not connected to either u or v in g1 *)
    assert (ufroot_same g1 x x). {
      apply (ufroot_same_refl _ (liGraph g1)); trivial.
    }
    apply (uf_union_unaffected_vvalid g1 g2 _ _ _
                               _ _ _
                               H4 H5 H10 H6 H7); trivial.
    + intro.
      apply (same_set_contra _ _ _ x H11); trivial.
      intro.
      apply (ufroot_same_false _ _ _ _ _ H9 H2 n); trivial.
      apply ufroot_same_symm; trivial.
    + intro.
      apply (same_set_contra _ _ _ x H11); trivial.
      intro.
      apply (ufroot_same_false _ _ _ _ _ H9 H3 n0); trivial.
      apply ufroot_same_symm; trivial.
    + apply (ufroot_uf_set_in _ x x_rt); trivial.

  (* <- *)
  - pose proof (vvalid_get_ufroot _ _ H8).
    destruct H9 as [x_rt ?].

    assert (uf_set_in g2 (ufroot_same g2 x)). {
      apply (ufroot_uf_set_in _ _ x_rt); trivial.
    }

    assert (ufroot_same g2 x x). {
      apply (ufroot_same_refl _ (liGraph g2)); trivial.
    }
    apply (uf_union_backwards_cases _ _ _ _ _ _ _ _
                                    H4 H5 H6 H7 H11) in H1; trivial.
    
    destruct H1.
    + (* x is in the union of S1 and S2 *)
      apply Ensembles.Extensionality_Ensembles in H1.
      rewrite H1 in H11.
      apply Constructive_sets.Union_inv in H11.
      destruct H11 as [[? [_ ?]] | [? [_ ?]]];
        apply (ufroot_vvalid_vert _ x0); trivial.
    + (* not *)
      destruct H1 as [? | [? [? ?]]].
      * exfalso.
        apply (inhabited_set_nonempty _ _ _ H11 H1).
      * apply (ufroot_vvalid_vert _ x0).
        apply H12, (ufroot_same_refl _ (liGraph g2)); trivial. 
Qed.

Lemma uf_union_preserves_connected:
(* Any two vertices that were connected already 
   remain so after union. i.e., union doesn't split 
 *)
  forall (g1 g2: UFGraph) u v a b,
    vvalid g1 u ->
    vvalid g1 v ->
    uf_union g1 u v g2 ->
    ufroot_same g1 a b ->
    ufroot_same g2 a b.
Proof.
  intros.
  pose proof (uf_union_create_precons _ _ _ H H0).
  destruct H3 as [u_rt [v_rt [? [? [? [? [? ?]]]]]]].
  destruct H2 as [ab_rt [? ?]].
  
  (* now we take cases to see whether a and b were
     in connected to u, to v, or to neither
   *)
  destruct (Z.eq_dec ab_rt u_rt). {
    (* a and b were connected to u in g1 *)
    subst ab_rt.
    assert (ufroot_same g1 u a). {
      exists u_rt; split; trivial.
    }
    assert (ufroot_same g1 u b). {
      exists u_rt; split; trivial.
    } 
    apply (uf_union_affected_inhabited
             _ _ _ _ _ _ H5 H6 H7 H8) in H1.
    destruct H1 as [rt [? ?]].
    exists rt; split; apply H12, Union_introl; trivial.
  }
  
  destruct (Z.eq_dec ab_rt v_rt). {
    (* a and b were connected to v in g1 *)
    subst ab_rt.
    assert (ufroot_same g1 v a). {
      exists v_rt; split; trivial.
    }
    assert (ufroot_same g1 v b). {
      exists v_rt; split; trivial.
    }
    apply uf_union_sym in H1.
    apply (uf_union_affected_inhabited
             _ _ _ _ _ _ H6 H5 H8 H7) in H1.
    destruct H1 as [rt [? ?]].
    exists rt; split; apply H12, Union_introl; trivial.
  }

  (* a and b were not connected to either u or v in g1 *)
    
  assert (ufroot_same g1 a a). {
    apply (ufroot_same_refl _ (liGraph g1)).
    apply (ufroot_vvalid_vert _ ab_rt); trivial.
  }

  assert (ufroot_same g1 a b). {
    exists ab_rt; split; trivial.
  }

  apply (uf_union_unaffected_inhabited
           _ _ _ _ a _ _ (ufroot_same g1 a) H5 H6) in H1; trivial.

  destruct H1 as [rt [? ?]].
  exists rt; split; apply H12; trivial.
  - intro.
    apply (same_set_contra _ _ _ a H12); trivial.
    intro.
    apply (ufroot_same_false g1 a u ab_rt u_rt); trivial.
    apply ufroot_same_symm; trivial.
  - intro.
    apply (same_set_contra _ _ _ a H12); trivial.
    intro.
    apply (ufroot_same_false g1 a v ab_rt v_rt); trivial.
    apply ufroot_same_symm; trivial.
  - apply (ufroot_uf_set_in _ a ab_rt); trivial.
Qed.

Lemma uf_union_connected:
  (* After union(u,v), u and v are "joined" *)
  forall (g1 g2: UFGraph) u v,
    vvalid g1 u ->
    vvalid g1 v ->
    uf_union g1 u v g2 ->
    ufroot_same g2 u v.
Proof.
  intros.
  pose proof (uf_union_create_precons _ _ _ H H0).
  destruct H2 as [u_rt [v_rt [? [? [? [? [? ?]]]]]]].
  
  (* two cases: either they were already joined or not *)
  destruct (Z.eq_dec u_rt v_rt).
  - (* they were already joined *)
    subst v_rt. 
    assert (ufroot_same g1 u v). {
      exists u_rt; split; trivial.
    }
    apply (uf_union_affected_inhabited _ _ _ _ _ _ H4 H5) in H1; trivial.
    destruct H1 as [rt [? ?]].
    exists rt. split; apply H9, Union_introl; trivial.
  - (* there were separate in g1 *)
    apply (uf_union_affected_inhabited _ _ _ _ _ _ H4 H5) in H1; trivial.
    destruct H1 as [rt [? ?]]. exists rt.
    split; apply H8;
      [apply Union_introl | apply Union_intror]; trivial.
Qed.

Lemma uf_union_remains_disconnected1:
  (* If a was disjoint from u and v, 
     then after union(u,v) it remains disjoint from u *)
  forall (g1 g2: UFGraph) u v a,
    vvalid g1 u ->
    vvalid g1 v ->
    vvalid g1 a -> (* added *)
    uf_union g1 u v g2 ->
    ~ ufroot_same g1 a u ->
    ~ ufroot_same g1 a v ->
    ~ ufroot_same g2 a u.
Proof.
  intros.
  pose proof (uf_union_create_precons _ _ _ H H0).
  destruct H5 as [u_rt [v_rt [? [? [? [? [? ?]]]]]]].

  assert (ufroot_same g1 a a). {
    apply (ufroot_same_refl _ (liGraph g1)); trivial.
  }
  apply (uf_union_unaffected_inhabited
           _ _ _ _ _ _ _ _
           H7 H8 H11 H9 H10) in H2.
  destruct H2 as [rt [? ?]]. intro.
  rewrite H12 in *.
  apply H3, (ufroot_same_uf_root_trans _ a); trivial. 
  - intro. apply (same_set_contra _ _ _ a H12); trivial.
    intro. apply H3. apply ufroot_same_symm; trivial.
  - intro. apply (same_set_contra _ _ _ a H12); trivial.
    intro. apply H4. apply ufroot_same_symm; trivial.
  - destruct H11 as [a_rt [? _]].
    apply (ufroot_uf_set_in _ a a_rt); trivial.
Qed.

Lemma uf_union_remains_disconnected2:
(*If a was disjoint from u and v, then after union(u,v) it remains disjoint from v*)
forall (g1 g2: UFGraph) u v a,
  vvalid g1 u ->
  vvalid g1 v ->
  vvalid g1 a -> (* added *)
  uf_union g1 u v g2 ->
  ~ ufroot_same g1 a u ->
  ~ ufroot_same g1 a v ->
  ~ ufroot_same g2 a v.
Proof.
  intros. apply uf_union_sym in H2.
  apply (uf_union_remains_disconnected1 g1 _ _ u); trivial. 
Qed.

Lemma uf_union_joins_only_uv:
  (* If x and y were disjoint from u and v,
     and from each other,     
     then after union(u,v) x and y remain disjoint *)
  forall (g1 g2: UFGraph) u v x y,
    vvalid g1 u ->
    vvalid g1 v ->
    vvalid g1 x ->
    vvalid g1 y ->
    uf_union g1 u v g2 ->
    ~ ufroot_same g1 x u ->
    ~ ufroot_same g1 x v ->
    ~ ufroot_same g1 x y ->
    ~ ufroot_same g2 x y.
Proof.
  intros.
  pose proof (uf_union_create_precons _ _ _ H H0).
  destruct H7 as [u_rt [v_rt [? [? [? [? [? ?]]]]]]].
  
  assert (ufroot_same g1 x x). {
    apply (ufroot_same_refl _ (liGraph g1)); trivial.
  }

  apply (uf_union_unaffected_inhabited
           _ _ _ _ _ _ _ _
           H9 H10 H13) in H3; trivial.

  destruct H3 as [rt [? ?]].
  rewrite H14 in *.
  intro. apply H6.
  apply (ufroot_same_uf_root_trans _ x); trivial.
  - intro. apply (same_set_contra _ _ _ x H14); trivial.
    intro. apply H4. apply ufroot_same_symm; trivial.
  - intro. apply (same_set_contra _ _ _ x H14); trivial.
    intro. apply H5. apply ufroot_same_symm; trivial.
  - apply vvalid_get_ufroot in H1.
    destruct H1 as [x_rt ?].
    apply (ufroot_uf_set_in _ x x_rt); trivial.
Qed.

(*************************************************************)

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

(*************************************************************)

Lemma connected_dec:
forall (g: FiniteWEdgeListGraph) u v, connected g u v \/ ~ connected g u v.
Proof. intros. tauto. Qed.

(*Moved this here because:
-universe inconsistency, proof is too long and I'm too tired to track it down
--the inconsistency comes from some bugger needing full parameters instead of referring
-requires one lemma from VST.floyd.proofauto.
-Ugly and specific to kruskal proof anyway
Application: t1 is the arbitrary spanning forest, t2 is our msf
*)
Lemma kruskal_minimal_induction:
forall ldiff lsame (g t1 t2: FiniteWEdgeListGraph), sound_weighted_edge_graph g ->
  labeled_spanning_uforest t1 g -> labeled_spanning_uforest t2 g ->
  Permutation (ldiff++lsame) (EList t1) -> incl lsame (EList t2) ->
  (forall e, In e ldiff -> ~ In e (EList t2)) ->
  (forall e, In e ldiff -> exists p l, connected_by_path t2 p (src t1 e) (dst t1 e) /\ NoDup p /\ fits_upath t2 l p /\ forall e', In e' l -> elabel g e' <= elabel g e) ->
  (forall i j, 0 <= i < j -> j < Zlength ldiff -> elabel g (Znth i ldiff) <= elabel g (Znth j ldiff)) ->
  exists lmsf, Zlength ldiff = Zlength lmsf /\ Permutation (lmsf++lsame) (EList t2) /\
      (forall i, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff))
  .
Proof.
induction ldiff; intros. rename H6 into Hsorted.
+(*nil case; no edges differ in t1. Then no edges should differ in t2*)
exists nil. split. auto.
rewrite app_nil_l in H2; rewrite app_nil_l.
assert (sound_weighted_edge_graph t1). apply (spanning_uforest_sound t1 g); auto.
assert (sound_weighted_edge_graph t2). apply (spanning_uforest_sound t2 g); auto.
assert (NoDup lsame). apply NoDup_Perm_EList in H2; auto.
split. apply NoDup_Permutation. auto. apply NoDup_EList.
intros; split; intros. apply H3; auto.
apply EList_evalid in H9. destruct x as [u v].
destruct (in_dec E_EqDec (u,v) lsame). auto.
(*u is connected to v in all graphs. So if u-v is not in lsame, exists another path in t1
Then, exists a list of edges l, fits_upath l p. All of l's edges must belong in EList t1, thus in lsame.
Thus, incl l t2. Which means connected_by_path t2 p u v. But (u,v) is an alternative path in t2. contra*)
assert (connected_by_path t2 (u::v::nil) u v).
  split. simpl. split. exists (u,v). split. apply sound_strong_evalid; auto.
  left. destruct H7 as [? [? [? [? ?]]]]. rewrite H12; auto. rewrite H13; auto.
  apply (sound_uv_vvalid t2 u v); auto. simpl; split; auto.
assert (connected t1 u v). apply H0. apply H1. exists (u::v::nil). auto. destruct H11 as [p ?].
pose proof (connected_exists_list_edges t1 p u v H11). destruct H12 as [l ?].
assert (~ In (u,v) l). unfold not; intros. (*If it were, then it is in lsame*)
  assert (evalid t1 (u,v)). apply (fits_upath_evalid t1 p l (u,v) H12 ). auto.
  rewrite <- EList_evalid in H14. apply (Permutation_in (l':=lsame)) in H14. contradiction.
  apply Permutation_sym. apply H2.
apply (sound_fits_upath_transfer  p l t1 t2) in H12; auto.
  2: { intros.
        rewrite <- (spanning_preserves_vertices g t1). apply (spanning_preserves_vertices g t2). apply H1. apply H0. }
  2: { intros. assert (In e lsame). apply (Permutation_in (l:=(EList t1))). apply Permutation_sym. apply H2.
        apply EList_evalid. apply (fits_upath_evalid t1 p l); auto. rewrite <- EList_evalid. apply H3. auto. }
apply (forest_edge' p l t2 (u,v)) in H12. contradiction.
apply H1. apply H1. auto. rewrite <- sound_src; auto. rewrite <- sound_dst; auto. simpl. split.
apply valid_upath_exists_list_edges'. exists l; auto. apply H11.
intros. rewrite Zlength_nil in H9. lia.
+ (*inductive step: there is at least one edge differing*)
rename H6 into Hsorted.
simpl in H2.
destruct a as (u1,v1).
assert (Ha: evalid t1 (u1,v1)). rewrite <- EList_evalid. apply (Permutation_in (l:=((u1, v1) :: ldiff ++ lsame))). apply H2. left; auto.
assert (Ht2_u1v1: ~ evalid t2 (u1,v1)). rewrite <- EList_evalid. apply H4. left; auto.
assert (Ht1_sound: sound_weighted_edge_graph t1). apply (spanning_uforest_sound t1 g); auto.
assert (Ht2_sound: sound_weighted_edge_graph t2). apply (spanning_uforest_sound t2 g); auto.
assert (H_NoDup_ldiff: NoDup ((u1,v1)::ldiff++lsame)). apply NoDup_Perm_EList in H2; auto.
(*In t1, a connects (u1,v1). In t2, (u1,v1) is also connected by some p2 l2. but since a isn't inside t2, a isn't inside l2.
If everything in l2 is in l1, then connected_by_path t1 p2 u1 v1 /\ fits_upath t1 p2 l2. Thus by forest_edge', In a l2. contra
Therefore, at least one edge must not be in l1*)
  assert (connected t2 u1 v1). apply H1. apply H0. exists (u1::v1::nil).
    assert (connected_by_path t1 (src t1 (u1, v1) :: dst t1 (u1, v1) :: nil) (src t1 (u1, v1)) (dst t1 (u1, v1))).
    apply (trivial_path1 t1 (u1,v1)). apply sound_strong_evalid; auto.
    replace (src t1 (u1,v1)) with (fst (u1, v1)) in H6. replace (dst t1 (u1,v1)) with (snd (u1, v1)) in H6. simpl in H6. auto.
    apply sound_dst; auto. apply sound_src; auto.
  destruct H6 as [p2' ?].
  assert (exists p', connected_by_path t2 p' u1 v1 /\ simple_upath t2 p').
  apply (connected_by_upath_exists_simple_upath t2 p2' u1 v1). auto.
  clear p2' H6. destruct H7 as [p2 [? ?]].
  assert (exists l2, fits_upath t2 l2 p2). apply (connected_exists_list_edges t2 p2 u1 v1). auto. destruct H8 as [l2 ?].
(*show that this path's edges are <= weight of (u1,v1)*)
assert (H_l2_weight: forall e, In e l2 -> elabel g e <= elabel g (u1,v1)). {
  intros. specialize H5 with ((u1,v1)).
  assert (exists (p : upath) (l : list EType),
         connected_by_path t2 p (src t1 (u1, v1)) (dst t1 (u1, v1)) /\
         NoDup p /\
         fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g (u1, v1))).
  apply H5. left; auto. destruct H10 as [p' [l' [? [? [? ?]]]]].
  rewrite <- sound_src in H10; auto. rewrite <- sound_dst in H10; auto. simpl in H10.
  assert (l' = l2). assert (unique_simple_upath t2). apply H1.
  assert (p' = p2). apply (H14 u1 v1 p' p2); auto. split. apply H10. apply H11.
  apply (uforest'_unique_lpath p2 l' l2 t2); auto. apply H1. rewrite <- H15; auto.
  apply H13. rewrite H14. auto.
}
(*now find the matching edge for a. I need ~forall -> exists...*)
assert (exists b, In b (EList t2) /\ ~ In b (EList t1) /\ bridge t2 b u1 v1). {
  (*main thing is just show In b l2 /\ ~ In b (EList t1).
  Do the ~ forall -> exists thing on l2.
  Then (prove and) use a lemma that every edge in a simple path of a uforest' is a bridge*)
  assert (exists b : EType, In b l2 /\ ~ In b (EList t1)). apply list_not_forall_exists.
  unfold not; intros. subst l2. destruct p2. destruct H6. destruct H9. inversion H9.
  destruct p2. destruct H6. destruct H9. inversion H9. inversion H10. subst u1; subst v1.
  (*means a is a self-loop, which is cannot be possible*)
  destruct H0. destruct H0. destruct H12. destruct H12. assert (src t1 (v, v) <> dst t1 (v, v)). auto.
  rewrite <- sound_src in H15; auto. rewrite <- sound_dst in H15; auto.
  simpl in H8. contradiction.
  apply EList_In_dec.
  unfold not; intros.
  (*If everything in l2 is in l1, then connected_by_path t1 p2 u1 v1 /\ fits_upath t1 p2 l2.*)
  assert (fits_upath t1 l2 p2). apply (sound_fits_upath_transfer  p2 l2 t2 t1); auto.
  intros; split; intros. apply (spanning_preserves_vertices g). apply H0. apply (spanning_preserves_vertices g t2). apply H1. auto.
  apply (spanning_preserves_vertices g). apply H1. apply (spanning_preserves_vertices g t1). apply H0. auto.
  intros. rewrite <- EList_evalid. apply H9. auto.
  assert (connected_by_path t1 p2 u1 v1). split. apply valid_upath_exists_list_edges'. exists l2. auto. apply H6.
  assert (In (u1,v1) l2). apply (forest_edge' p2 l2 t1 (u1,v1)); auto. apply H0. apply sound_strong_evalid; auto.
  rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
  apply Ht2_u1v1. apply (fits_upath_evalid t2 p2 l2); auto.
  (*whew!*)
  destruct H9 as [b [? ?]].
  exists b. split. apply EList_evalid. apply (fits_upath_evalid t2 p2 l2); auto.
  split. auto.
  (*finally, the bridge...*)
  apply (forest_simple_bridge p2 l2); auto. apply H1.
}
destruct H9 as [b [? [? ?]]].
(*now show b <= a*)
assert (elabel g b <= elabel g (u1,v1)).
  assert (exists (p : upath) (l : list EType),
       connected_by_path t2 p (src t1 (u1, v1)) (dst t1 (u1, v1)) /\
       NoDup p /\ fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g (u1, v1))).
  apply H5. left; auto. destruct H12 as [p [l ?]]. apply H12.
  unfold bridge in H11. apply (H11 p l).
  rewrite <- sound_src in H12; auto. rewrite <- sound_dst in H12; auto.
  apply H12. apply H12.
(*b is a bridge -> p can be split, and thus l can be split*)
pose proof (bridge_splittable p2 t2 u1 v1 b H6 H11). destruct H13 as [p2a [p2b [? ?]]].
assert (Hevalid_b: evalid t2 b). apply EList_evalid in H9; auto.
rewrite <- sound_src in H14; auto. rewrite <- sound_dst in H14; auto.
(*pose proof (fits_upath_split' t2 p2 l2).*)
assert (exists l2a l2x l2b : list EType,
        fits_upath t2 l2a p2a /\ fits_upath t2 l2b p2b /\ l2 = l2a ++ l2x ++ l2b).
apply (fits_upath_split t2 p2a p2b l2). rewrite <- H13. auto.
destruct H15 as [l2a [l2x [l2b [? [? ?]]]]].
(*prepare for reasoning about swap*)
set (swap:=(FiniteWEdgeListGraph_adde (FiniteWEdgeListGraph_eremove t2 b) (u1, v1) (elabel t1 (u1, v1)))).
assert (Hsound_swap: sound_weighted_edge_graph swap). {
  apply adde_sound. apply eremove_sound. auto.
  simpl. apply (connected_by_path_vvalid t2 p2 u1 v1); auto.
  apply (connected_by_path_vvalid t2 p2 u1 v1); auto. apply Ht1_sound. auto.
} destruct b as (u2,v2). simpl in H14.
assert (Hevalid_swap_u1v1: evalid swap (u1,v1)). simpl. unfold addValidFunc, removeValidFunc. right; auto.
(*after a swap, b~=(u2,v2) will be connected by a path going through u1,v1*)
assert (Hnew: exists p l, connected_by_path swap p u2 v2 /\ fits_upath swap l p
/\ In (u1,v1) l /\ forall e', In e' l -> elabel g e' <= elabel g (u1,v1)). {
(*WLOG, used to be u1--u2--v2--v1
After swap, exists u2--u1--v1--v2*)
destruct H14.
+
exists ((rev p2a)++(rev p2b)). exists (rev l2a ++ (u1,v1)::nil ++ rev l2b).
assert (fits_upath swap (rev l2a ++ (u1, v1) :: nil ++ rev l2b) (rev p2a ++ rev p2b)). {
  apply (fits_upath_app swap (rev p2a) (rev p2b) (rev l2a) (rev l2b) (u1,v1) u1 v1).
  apply fits_upath_rev. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2a l2a); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2a (u2,v2) l2a) in H18.
    rewrite <- sound_src in H18; auto. rewrite <- sound_dst in H18; auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H7. rewrite H13 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 v2). auto. apply hd_error_In. apply H14. auto.
  apply fits_upath_rev. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2b l2b); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2b (u2,v2) l2b) in H18.
    rewrite <- sound_src in H18; auto. rewrite <- sound_dst in H18; auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H7. rewrite H13 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 u2). auto. apply last_error_In. apply H14. auto. auto.
  rewrite <- rev_hd_last. apply H14.
  rewrite rev_hd_last, rev_involutive. apply H14.
  split. apply adde_strong_evalid1.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H6.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H6.
    left. rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
}
split. split. apply valid_upath_exists_list_edges'.
exists (rev l2a ++ (u1, v1) :: nil ++ rev l2b); auto.
split. apply (hd_error_app (rev p2b) (rev p2a) u2). rewrite rev_hd_last, rev_involutive. apply H14.
apply (last_err_app (rev p2a) (rev p2b) v2). rewrite <- rev_hd_last. apply H14.
split. auto. split. simpl. apply in_or_app. right; left; auto.
  intros. apply in_app_or in H19. destruct H19. apply in_rev in H19. apply H_l2_weight.
  rewrite H17. apply in_or_app. left; auto.
  simpl in H19. destruct H19. subst e'. lia. apply in_rev in H19. apply H_l2_weight.
  rewrite H17. apply in_or_app. right; apply in_or_app. auto.
+(*near repeat*)
exists (p2b++p2a). exists (l2b ++ (u1,v1)::nil ++ l2a).
assert (fits_upath swap (l2b ++ (u1, v1) :: nil ++ l2a) (p2b ++ p2a)). {
  apply (fits_upath_app swap (p2b) (p2a) l2b (l2a) (u1,v1) v1 u1).
  apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2b l2b); auto.
  unfold not; intros.
    subst e. apply (fits_upath_vertex_in_path t2 p2b (u2,v2) l2b) in H18.
    rewrite <- sound_src in H18; auto. rewrite <- sound_dst in H18; auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H7. rewrite H13 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 v2). auto. apply last_error_In. apply H14. auto. auto.
  apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2a l2a); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2a (u2,v2) l2a) in H18.
    rewrite <- sound_src in H18; auto. rewrite <- sound_dst in H18; auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H7. rewrite H13 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 u2).  auto. apply hd_error_In. apply H14. auto.
  apply H14. apply H14.
  split. apply adde_strong_evalid1.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H6.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H6.
    right. rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
}
split. split. apply valid_upath_exists_list_edges'.
exists (l2b ++ (u1, v1) :: nil ++ l2a); auto.
split. apply hd_error_app. apply H14.
apply last_err_app. apply H14.
split. auto. split. simpl. apply in_or_app. right; left; auto.
  intros. apply in_app_or in H19. destruct H19. apply H_l2_weight.
  rewrite H17. apply in_or_app. right. apply in_or_app. auto.
  simpl in H19. destruct H19. subst e'. lia. apply H_l2_weight.
  rewrite H17. apply in_or_app. left; auto.
} destruct Hnew as [p' [l' Hnew]].
set (b:=(u2,v2)).
(*specialize inductive step with (t2 + a - b). It's a "step" closer to t2 and it's diff edges are in ldiff.
By induction, exists lmsf containing t2's diff edges*)
specialize IHldiff with ((u1,v1)::lsame) g t1 swap.
clear H13 H14 H15 H16 H17.
assert (exists lmsf : list EType,
            Zlength ldiff = Zlength lmsf /\
            Permutation (lmsf ++ (u1, v1) :: lsame) (EList swap) /\
            (forall i : Z, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff))).
apply IHldiff; clear IHldiff. (*BEGONE*)
auto.
auto.
{ split. split.
(*partial graph*) {
  split. intros. simpl in H13. apply (spanning_preserves_vertices g t2). apply H1. auto.
  split. intros. simpl in H13. unfold addValidFunc, removeValidFunc in H13. destruct H13.
    destruct H13. apply H1. auto.
    apply H0. rewrite H13. auto.
  split. simpl. unfold addValidFunc, removeValidFunc, updateEdgeFunc, EquivDec.equiv_dec. intros.
    destruct (E_EqDec (u1, v1) e). unfold Equivalence.equiv in e0. subst e. rewrite <- sound_src; auto. apply H0. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. destruct H13. destruct H13. apply H1. auto. auto. symmetry in H13; contradiction.
  simpl. unfold addValidFunc, removeValidFunc, updateEdgeFunc, EquivDec.equiv_dec. intros.
    destruct (E_EqDec (u1, v1) e). unfold Equivalence.equiv in e0. subst e. rewrite <- sound_dst; auto. apply H0. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. destruct H13. destruct H13. apply H1. auto. auto. symmetry in H13; contradiction.
} split.
(*uforest'*) {
  assert (uforest' (FiniteWEdgeListGraph_eremove t2 b) /\ ~ connected (FiniteWEdgeListGraph_eremove t2 b) (src t2 b) (dst t2 b)).
  apply (eremove_uforest' t2 b). auto. apply H1. apply EList_evalid in H9. auto. destruct H13.
  apply uforest'_adde. auto. apply eremove_sound. auto. auto.
  apply eremove_vvalid. apply (spanning_preserves_vertices g t2). apply H1. apply (spanning_preserves_vertices g t1). apply H0.
  apply sound_strong_evalid in Ha; auto. destruct Ha. rewrite <- sound_src in H16; auto. rewrite <- sound_dst in H16; auto. apply H16.
  apply eremove_vvalid. apply (spanning_preserves_vertices g t2). apply H1. apply (spanning_preserves_vertices g t1). apply H0.
  apply sound_strong_evalid in Ha; auto. destruct Ha. rewrite <- sound_src in H16; auto. rewrite <- sound_dst in H16; auto. apply H16.
  apply Ht1_sound.
  auto.
  (*need an eremove_bridge*)
  unfold not, connected; intros. destruct H15 as [p ?].
  pose proof (connected_exists_list_edges (FiniteWEdgeListGraph_eremove t2 b) p u1 v1 H15). destruct H16 as [l ?].
  assert (fits_upath t2 l p). apply (sound_fits_upath_transfer p l _ t2) in H16. auto.
  apply eremove_sound; auto. auto. apply eremove_vvalid. intros. apply (fits_upath_evalid _ p l e H16) in H17.
  simpl in H17. unfold removeValidFunc in H17. apply H17.
  assert (connected_by_path t2 p u1 v1). split. apply valid_upath_exists_list_edges'. exists l. auto. apply H15.
  assert (In b l). apply (H11 p l). auto. auto.
  assert (evalid (FiniteWEdgeListGraph_eremove t2 b) b). apply (fits_upath_evalid _ p l). auto. auto.
  pose proof (eremove_evalid1 t2 b). auto.
}
(*spanning*) {
  unfold spanning; intros. assert (spanning t2 g). apply H1. unfold spanning in H13. rewrite H13. clear H13.
  split; intros; destruct H13 as [p ?]. (*I may need simple upath?*)
  pose proof (connected_by_upath_exists_simple_upath t2 p u v H13).
  clear p H13. destruct H14 as [p [? ?]].
  assert (exists l, fits_upath t2 l p). apply (connected_exists_list_edges t2 p u v); auto.
  destruct H15 as [l ?].
  (*Was (u2,v2) inside?*)
  destruct (in_dec E_EqDec (u2,v2) l).
  (*yes: split into l1++(u2,v2)++l2, p1++p2. replace with (u2,v2) with l'*)
  unfold b; fold swap. assert (HNoDup_l: NoDup l). apply (simple_upath_list_edges_NoDup t2 p l); auto.
  pose proof (fits_upath_split' t2 p l (u2,v2) H15 i). destruct H16 as [pb1 [pb2 [lb1 [lb2 ?]]]].
  {
  destruct H16 as [? [? [? [? ?]]]].
  rewrite <- sound_src in H17; auto. rewrite <- sound_dst in H17; auto. destruct H17; simpl in H17.
  (*it's a pain to declare the full path, so use transitivity
  Hm, could I have simplified the previous proofs?*)
  (*connected swap pb1 u u2*)
  assert (Hc1: connected swap u u2). exists pb1. split. apply valid_upath_exists_list_edges'.
    exists lb1. apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H20. apply in_or_app. left; auto.
    unfold not; intros. rewrite H20 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H21. apply H21. left; auto.
    destruct H17. destruct pb1. inversion H17. destruct H13. rewrite H16 in H22. destruct H22; inversion H22.
    subst v0. simpl; auto.
  assert (Hc2: connected swap u2 v2). exists p'; apply Hnew.
  assert (Hc3: connected swap v2 v). exists pb2. split. apply valid_upath_exists_list_edges'.
    exists lb2. apply (sound_fits_upath_transfer pb2 lb2 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H20. apply in_or_app. right. apply in_or_app. right; auto.
    unfold not; intros. rewrite H20 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
    split. apply H17. destruct pb2. destruct H17. inversion H21.
    rewrite <- (last_err_split2 pb1 pb2 v0). rewrite <- H16. apply H13.
    apply (connected_trans swap u v2 v); auto. apply (connected_trans swap u u2 v2); auto.
  (*repeat...*)
  assert (Hc1: connected swap u v2). exists pb1. split. apply valid_upath_exists_list_edges'.
    exists lb1. apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H20. apply in_or_app. left; auto.
    unfold not; intros. rewrite H20 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H21. apply H21. left; auto.
    destruct H17. destruct pb1. inversion H17. destruct H13. rewrite H16 in H22. destruct H22; inversion H22.
    subst v0. simpl; auto.
  assert (Hc2: connected swap v2 u2). apply connected_symm. exists p'; apply Hnew.
  assert (Hc3: connected swap u2 v). exists pb2. split. apply valid_upath_exists_list_edges'.
    exists lb2. apply (sound_fits_upath_transfer pb2 lb2 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H20. apply in_or_app. right. apply in_or_app. right; auto.
    unfold not; intros. rewrite H20 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
    split. apply H17. destruct pb2. destruct H17. inversion H21.
    rewrite <- (last_err_split2 pb1 pb2 v0). rewrite <- H16. apply H13.
    apply (connected_trans swap u u2 v); auto. apply (connected_trans swap u v2 u2); auto.
  }
  (*no: it can't have gone through (u1,v1) which isn't in t2, therefore unaffected*)
  exists p. split. apply adde_valid_upath. apply eremove_sound; auto. unfold b.
  apply (valid_upath_eremove _ _ p l); auto. apply H13. apply H13.
  (*<----------------------*)
  pose proof (connected_by_upath_exists_simple_upath swap p u v H13).
  clear p H13. destruct H14 as [p [? ?]].
  assert (exists l, fits_upath swap l p). apply (connected_exists_list_edges swap p u v); auto.
  destruct H15 as [l ?].
  (*does it go through (u1,v1)*)
  destruct (in_dec E_EqDec (u1,v1) l).
  (*yes: split into la1++... replace (u1,v1) with l2*)
  assert (HNoDup_l: NoDup l). apply (simple_upath_list_edges_NoDup swap p l); auto.
  pose proof (fits_upath_split' swap p l (u1,v1) H15 i). destruct H16 as [pa1 [pa2 [la1 [la2 ?]]]].
  {
    destruct H16 as [? [? [? [? ?]]]].
    rewrite <- sound_src in H17; auto. rewrite <- sound_dst in H17; auto. destruct H17; simpl in H17.
    (*assert connectedness*)
    assert (Hc1: connected t2 u u1). exists pa1. split. apply valid_upath_exists_list_edges'.
      exists la1. apply (sound_fits_upath_transfer pa1 la1 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l); auto. rewrite H20. apply in_or_app. left; auto.
      simpl in H22. unfold addValidFunc, removeValidFunc in H22. destruct H22. apply H22.
      rewrite H20 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H21. exfalso. apply H21. left; auto.
      destruct H17. destruct pa1. inversion H17. destruct H13. rewrite H16 in H22. destruct H22; inversion H22.
      subst v0. simpl; auto.
    assert (Hc2: connected t2 u1 v1). exists p2; auto.
    assert (Hc3: connected t2 v1 v). exists pa2. split. apply valid_upath_exists_list_edges'.
      exists la2. apply (sound_fits_upath_transfer pa2 la2 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H20. apply in_or_app. right. apply in_or_app. right; auto.
      simpl in H22. unfold addValidFunc, removeValidFunc in H22. destruct H22. apply H22.
      rewrite H20 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
      split. apply H17. destruct pa2. destruct H17. inversion H21.
      rewrite <- (last_err_split2 pa1 pa2 v0). rewrite <- H16. apply H13.
      apply (connected_trans t2 u v1 v); auto. apply (connected_trans t2 u u1 v1); auto.
    (*repeat...*)
    assert (Hc1: connected t2 u v1). exists pa1. split. apply valid_upath_exists_list_edges'.
      exists la1. apply (sound_fits_upath_transfer pa1 la1 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H20. apply in_or_app. left; auto.
      simpl in H22. unfold addValidFunc, removeValidFunc in H22. destruct H22. apply H22.
      rewrite H20 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H21. exfalso. apply H21. left; auto.
      destruct H17. destruct pa1. inversion H17. destruct H13. rewrite H16 in H22. destruct H22; inversion H22.
      subst v0. simpl; auto.
    assert (Hc2: connected t2 v1 u1). apply connected_symm. exists p2; auto.
    assert (Hc3: connected t2 u1 v). exists pa2. split. apply valid_upath_exists_list_edges'.
      exists la2. apply (sound_fits_upath_transfer pa2 la2 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H20. apply in_or_app. right. apply in_or_app. right; auto.
      simpl in H22. unfold addValidFunc, removeValidFunc in H22. destruct H22. apply H22.
      rewrite H20 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
      split. apply H17. destruct pa2. destruct H17. inversion H21.
      rewrite <- (last_err_split2 pa1 pa2 v0). rewrite <- H16. apply H13.
      apply (connected_trans t2 u u1 v); auto. apply (connected_trans t2 u v1 u1); auto.
  }
  (*no: unaffected*)
  exists p. split. unfold swap in H14.
  assert (fits_upath (FiniteWEdgeListGraph_eremove t2 (u2,v2)) l p).
  apply (sound_fits_upath_transfer _ _ swap _). auto. apply eremove_sound; auto.
  simpl. intros; split; auto.
  intros. simpl. unfold removeValidFunc.
  assert (evalid swap e). apply (fits_upath_evalid swap p l) in H16; auto.
  simpl in H17. unfold addValidFunc, removeValidFunc in H17. destruct H17.
  auto. subst e. contradiction. auto.
  apply (eremove_unaffected t2 (u2,v2)).
  apply (adde_unaffected _ (u1,v1) (elabel t1 (u1,v1))). apply H13.
  exists l; auto.
  apply H13.
}
split.
(*preserve vlabel*)
unfold preserve_vlabel; intros. destruct vlabel. destruct vlabel. auto.
(*preserve elabel*)
unfold preserve_elabel; intros. simpl in H13. unfold addValidFunc, removeValidFunc in H13.
simpl. unfold update_elabel. unfold EquivDec.equiv_dec. destruct E_EqDec.
unfold Equivalence.equiv in e0. subst e. apply H0. auto.
unfold RelationClasses.complement, Equivalence.equiv in c. destruct H13.
apply H1. apply H13. symmetry in H13. contradiction.
}
(*Permutation of EList t1*)
apply (Permutation_trans (l':=((u1, v1) :: ldiff ++ lsame))). 2: auto.
apply (Permutation_trans (l':=((u1, v1) :: lsame ++ ldiff))). apply Permutation_app_comm.
apply perm_skip. apply Permutation_app_comm.
(*incl*)
unfold incl; intros.
apply EList_evalid. simpl. unfold addValidFunc, removeValidFunc.
destruct H13. right; auto.
left; split. apply H3 in H13. apply EList_evalid in H13. auto.
unfold not; intros. subst a. apply H10. apply (Permutation_in (l:=((u1, v1) :: ldiff ++ lsame))). auto.
right. apply in_or_app. right; auto.
(*In e ldiff -> ~ In e swapped_graph*)
intros. rewrite EList_evalid. simpl. unfold addValidFunc, removeValidFunc, not; intros.
destruct H14. destruct H14. rewrite <- EList_evalid in H14. apply H4 in H14. auto. right; auto.
subst e.
apply NoDup_cons_2 in H_NoDup_ldiff. apply H_NoDup_ldiff. apply in_or_app. left; auto.
(*weight*) {
intros. unfold b; fold swap.
assert (exists (p : upath) (l : list EType),
       connected_by_path t2 p (src t1 e) (dst t1 e) /\
       NoDup p /\ fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g e)).
apply H5. right; auto. destruct H14 as [p [l [? [? [? ?]]]]].
(*is (u2,v2) in l?*)
destruct (in_dec E_EqDec (u2,v2) l).
(*yes: split*)
+
pose proof (fits_upath_split' t2 p l (u2,v2) H16 i).
destruct H18 as [pb1 [pb2 [lb1 [lb2 ?]]]]. destruct H18 as [? [? [? [? ?]]]].
assert (Hl: NoDup l). apply (simple_upath_list_edges_NoDup t2 p). split. apply H14. auto. auto.
rewrite <- sound_src in H19; auto. rewrite <- sound_dst in H19; auto. simpl in H19.
set (u:=src t1 e). set (v:=dst t1 e).
destruct H19; destruct H19.
++ (*pb1 --- u2 -- v2 -- pb2*)
set (pnew:=(pb1 ++ (tail p') ++ (tail pb2))). set (lnew:=(lb1++l'++lb2)).
(*first settle that the vertices match*)
assert (Hv1: last_error pb1 = hd_error p'). { rewrite H19. symmetry. apply Hnew. }
assert (Hv2: last_error p' = hd_error pb2). { rewrite H23. apply Hnew. }
assert (fits_upath swap lnew pnew). {
  unfold pnew, lnew. destruct l'. destruct Hnew as [? [? [? ?]]]. contradiction.
  destruct p'. destruct Hnew as [? [? [? ?]]]. contradiction.
  destruct p'. destruct Hnew as [? [? [? ?]]]. simpl in H25; contradiction.
  replace (lb1 ++ (e0 :: l') ++ lb2)  with (lb1 ++ (e0 :: nil) ++ (l'++lb2)). 2: simpl; auto.
  apply (fits_upath_app _ _ _ _ _ e0 u2 v3).
  -apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 pb1 lb1); auto. unfold not; intros. subst e1.
  rewrite H22 in Hl. apply (NoDup_app_not_in _ _ _ Hl) in H24. apply H24. simpl; left; auto.
  -destruct pb2. inversion H23. destruct pb2. destruct lb2.
  simpl. do 2 rewrite app_nil_r. simpl in H23; inversion H23. subst v4. apply Hnew.
  destruct Hnew as [? [? [? ?]]]. simpl in H21. contradiction.
  destruct lb2. destruct Hnew as [? [? [? ?]]]. simpl in H21. contradiction.
  apply (fits_upath_app _ _ _ _ _ e1 v2 v5). apply Hnew.
  apply (sound_fits_upath_transfer _ _ t2 swap); auto. simpl; intros; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left; split.
    apply (fits_upath_evalid t2 (v4::v5::pb2) (e1::lb2)); auto. right; auto.
    unfold not; intros. subst e2. rewrite H22 in Hl. apply NoDup_app_r in Hl.
    apply (NoDup_app_not_in EType ((u2,v2)::nil) (e1::lb2) Hl (u2,v2)). left; auto.
    right; auto. apply H21. simpl. apply Hnew. simpl; auto. simpl in H23; inversion H23. subst v4. destruct H21.
    assert (evalid t2 e1). apply (fits_upath_evalid t2 p l); auto.
    rewrite H22. apply in_or_app. right. apply in_or_app. right. left; auto.
  split. split. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply H21. unfold not; intros. subst e1. rewrite H22 in Hl. apply NoDup_app_r in Hl.
  apply (NoDup_app_not_in EType ((u2,v2)::nil) ((u2,v2)::lb2) Hl (u2,v2)). left; auto. left; auto.
  simpl. unfold updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
  unfold Equivalence.equiv in e2. subst e1. contradiction.
  apply sound_strong_evalid in H25; auto. apply H25.
  simpl. unfold updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
  unfold Equivalence.equiv in e2. subst e1. contradiction. apply H21.
  -auto.
  -simpl. auto.
  -destruct Hnew as [? [? [? ?]]]. destruct H25. destruct H24. destruct H29. simpl in H29; inversion H29. subst v0. apply H25.
}
assert (connected_by_path swap pnew u v). split. apply valid_upath_exists_list_edges'.
  exists lnew; auto.
  unfold pnew; split. destruct H14. rewrite H18 in H25; destruct H25.
  destruct pb1. inversion H19. simpl in H25. simpl. auto.
  destruct pb2. inversion H23. destruct pb2. simpl in Hv2. simpl in H23. inversion H23. subst v0.
  destruct H14. destruct H25. rewrite H18 in H26. rewrite last_err_appcons in H26. inversion H26.
  simpl. rewrite app_nil_r. unfold v; rewrite <- H28. subst v2.
  destruct Hnew as [? [? [? ?]]].
  destruct p'. inversion Hv2. destruct p'. destruct l'. contradiction. simpl in H28; contradiction.
  simpl. rewrite last_error_cons in Hv2. apply last_err_app. auto. unfold not; intros. inversion H31.
  simpl. apply last_err_app. apply last_err_app. destruct H14. destruct H25.
  rewrite H18 in H26. rewrite last_err_split2 in H26. rewrite last_error_cons in H26. auto.
  unfold not; intros. inversion H27.
assert (forall e' : EType, In e' lnew -> elabel g e' <= elabel g e).
  unfold lnew; intros. apply in_app_or in H26. destruct H26.
  apply H17. rewrite H22. apply in_or_app. left; auto.
  apply in_app_or in H26; destruct H26.
  apply (Z.le_trans _ (elabel g (u1,v1)) _). apply Hnew. auto.
(*In_Znth_iff requires floyd... ideally move the whole proof to verif kruskal, or create a copy of the lemma in list_ext...*)
assert (In e ((u1, v1) :: ldiff)). right; auto.
apply In_Znth_iff in H27. destruct H27 as [i' [? ?]]. rewrite <- H28.
replace (u1,v1) with (Znth 0 ((u1,v1)::ldiff)). 2: apply Znth_0_cons.
destruct (Z.lt_trichotomy 0 i').
apply Hsorted. lia. apply H27. destruct H29.
subst i'. do 2 rewrite Znth_0_cons. lia. lia.
apply H17. rewrite H22. apply in_or_app. right; right; auto.
(*now simplify*)
pose proof (upath_simplifiable_edges swap pnew lnew u v H25 H24).
destruct H27 as [psim [lsim [? [? [? [? ?]]]]]]. exists psim; exists lsim.
split. auto. split. apply H28. split. apply H30. intros. apply H26. apply H31. apply H32.
(*repeat...*)
++
 (*pb1 --- v2 -- u2 -- pb2*)
set (pnew:=(pb1 ++ (tail (rev p')) ++ (tail pb2))). set (lnew:=(lb1++(rev l')++lb2)).
(*first settle that the vertices match*)
assert (Hv1: last_error pb1 = hd_error (rev p')). {
rewrite H19. symmetry. rewrite rev_hd_last, rev_involutive. apply Hnew.
}
assert (Hv2: last_error (rev p') = hd_error pb2). {
  rewrite H23. rewrite <- rev_hd_last. apply Hnew.
}
assert (fits_upath swap lnew pnew). {
  unfold pnew, lnew. destruct Hnew as [? [? [? ?]]].
  assert (connected_by_path swap (rev p') v2 u2). split. apply valid_upath_rev. apply H24.
  split. rewrite rev_hd_last, rev_involutive. apply H24. rewrite <- rev_hd_last; apply H24.
  assert (fits_upath swap (rev l') (rev p')). apply fits_upath_rev. auto.
  assert (In (u1,v1) (rev l')). apply in_rev. rewrite rev_involutive. auto.
  destruct (rev l'). contradiction. destruct (rev p'). simpl in H29; contradiction.
  destruct l1. simpl in H29; contradiction.
  replace (lb1 ++ (e0 :: l0) ++ lb2) with (lb1 ++ (e0::nil) ++ (l0++lb2)). 2: simpl; auto.
  apply (fits_upath_app _ _ _ _ _ e0 v2 v3).
-apply (sound_fits_upath_transfer _ _ t2 swap); auto. simpl; intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 p l). auto. rewrite H22. apply in_or_app. left; auto.
  unfold not; intros. subst e1.
  assert (~ In (u2,v2) ((u2, v2) :: nil ++ lb2)). apply (NoDup_app_not_in EType lb1 (((u2,v2)::nil)++lb2)).
  simpl. rewrite H22 in Hl. simpl in Hl. auto. auto. apply H32. left; auto.
-destruct pb2. inversion H23. destruct pb2. destruct lb2.
  simpl. do 2 rewrite app_nil_r. simpl in H23; inversion H23. subst v4. apply H29.
  simpl in H21. contradiction. rename l1 into revp'.
  destruct lb2. simpl in H21. contradiction.
  apply (fits_upath_app _ _ _ _ _ e1 u2 v5).
  simpl. apply H29. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl; intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 p l). auto. rewrite H22. apply in_or_app. right. apply in_or_app. right. right; auto.
  unfold not; intros. subst e2. rewrite H22 in Hl; simpl in Hl. apply NoDup_app_r in Hl.
  apply NoDup_cons_2 in Hl. apply Hl. right; auto.
  apply H21.
  rewrite H23 in Hv2. apply Hv2.
  simpl; auto.
  assert (evalid swap e1). simpl. unfold addValidFunc, removeValidFunc.
  left. split. apply H21. unfold not; intros. subst e1. rewrite H22 in Hl. simpl in Hl.
  apply NoDup_app_r in Hl. apply NoDup_cons_2 in Hl. apply Hl. left; auto.
  destruct H21. simpl in H23. inversion H23. subst v4. destruct H21.
  split. apply sound_strong_evalid; auto.
  rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
  simpl in H31. unfold addValidFunc, removeValidFunc in H31. destruct H31.
  destruct H31. rewrite <- sound_src in H33; auto. rewrite <- sound_dst in H33; auto.
  exfalso. subst e1. destruct H21. contradiction.
-auto.
-simpl. auto.
-destruct H29. rewrite H19 in Hv1. simpl in Hv1. inversion Hv1. auto.
}
assert (connected_by_path swap pnew u v). split. apply valid_upath_exists_list_edges'.
  exists lnew; auto.
  unfold pnew; split. destruct H14. rewrite H18 in H25; destruct H25.
  destruct pb1. inversion H19. simpl in H25. simpl. auto.
  destruct pb2. inversion H23. destruct pb2. simpl in Hv2. simpl in H23. inversion H23. subst v0.
  destruct H14. destruct H25. rewrite H18 in H26. rewrite last_err_appcons in H26. inversion H26.
  simpl. rewrite app_nil_r. unfold v; rewrite <- H28. subst u2.
  destruct Hnew as [? [? [? ?]]].
  destruct (rev p') eqn:revp. inversion Hv2. destruct l0. destruct l'. contradiction.
  assert (p' = v0::nil). symmetry. rewrite <- rev_involutive. rewrite revp. simpl; auto. rewrite H31 in H28. contradiction.
  simpl. rewrite last_err_split2. apply Hv2.
  simpl. rewrite app_assoc. rewrite last_err_split2. destruct H14. destruct H25. rewrite H18 in H26.
  rewrite last_err_split2 in H26. apply H26.
assert (forall e' : EType, In e' lnew -> elabel g e' <= elabel g e).
  unfold lnew; intros. apply in_app_or in H26. destruct H26.
  apply H17. rewrite H22. apply in_or_app. left; auto.
  apply in_app_or in H26; destruct H26.
  apply (Z.le_trans _ (elabel g (u1,v1)) _). apply Hnew. apply in_rev. auto.
(*In_Znth_iff requires floyd... move the whole proof to verif kruskal...*)
assert (In e ((u1, v1) :: ldiff)). right; auto.
apply In_Znth_iff in H27. destruct H27 as [i' [? ?]]. rewrite <- H28.
replace (u1,v1) with (Znth 0 ((u1,v1)::ldiff)). 2: apply Znth_0_cons.
destruct (Z.lt_trichotomy 0 i').
apply Hsorted. lia. apply H27. destruct H29.
subst i'. do 2 rewrite Znth_0_cons. lia. lia.
apply H17. rewrite H22. apply in_or_app. right; right; auto.
(*now simplify*)
pose proof (upath_simplifiable_edges swap pnew lnew u v H25 H24).
destruct H27 as [psim [lsim [? [? [? [? ?]]]]]]. exists psim; exists lsim.
split. auto. split. apply H28. split. apply H30. intros. apply H26. apply H31. apply H32.
+
(*no: not affected*)
exists p. exists l.
assert (fits_upath swap l p). apply (sound_fits_upath_transfer _ _ t2 swap); auto.
simpl. intros; split; auto.
intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
apply (fits_upath_evalid t2 p l); auto.
unfold not; intros. subst e0. contradiction.
split. split. apply valid_upath_exists_list_edges'.
exists l; auto. apply H14.
split. auto. split. auto.
auto.
}
intros. specialize Hsorted with (i+1) (j+1).
replace (Znth i ldiff) with (Znth (i+1) ((u1,v1)::ldiff)).
replace (Znth j ldiff) with (Znth (j+1) ((u1,v1)::ldiff)). apply Hsorted.
lia. rewrite Zlength_cons. lia. rewrite Znth_pos_cons. rewrite Z.add_simpl_r. auto.
lia. rewrite Znth_pos_cons. rewrite Z.add_simpl_r. auto. lia.

(*finally*)
destruct H13 as [lmsf [? [? ?]]].
exists (b::lmsf). split.
do 2 rewrite Zlength_cons. rewrite H13. auto. split.

assert (Permutation ((u1,v1)::lmsf++lsame) (EList swap)). apply (Permutation_trans (l':=(lmsf ++ (u1, v1) :: lsame))).
apply Permutation_middle. auto.
assert (Permutation (lmsf++lsame) (EList (FiniteWEdgeListGraph_eremove t2 b))).
apply (adde_EList_rev (FiniteWEdgeListGraph_eremove t2 b) (u1,v1) (elabel t1 (u1,v1))).
simpl. unfold removeValidFunc.
unfold not; intros. destruct H17.
assert (~ In (u1,v1) (EList t2)). apply H4. left; auto. rewrite EList_evalid in H19. contradiction.
unfold b; fold swap. auto.
simpl. apply eremove_EList_rev. unfold b; auto. auto.

intros. rewrite Zlength_cons in H16. destruct (Z.lt_trichotomy i 0). lia. destruct H17.
subst i. do 2 rewrite Znth_0_cons. unfold b; auto.
do 2 rewrite Znth_pos_cons by lia. apply H15. split. lia.
destruct H16.
apply (Z.sub_lt_mono_r i (Z.succ (Zlength lmsf)) 1) in H18.
replace (Z.succ (Zlength lmsf) - 1) with (Zlength lmsf) in H18. auto.
lia.
Qed.

(*******************************BODY OF IMPLEMENTATIONS*****************************)

Lemma body_fill_edge: semax_body Vprog Gprog f_fill_edge fill_edge_spec.
Proof.
start_function.
forward. forward. forward. entailer!.
Qed.

Lemma body_init_empty_graph: semax_body Vprog Gprog f_init_empty_graph init_empty_graph_spec.
Proof.
start_function.
forward_call (sh, sizeof t_wedgearray_graph).
set (j := Int.max_unsigned) in *; compute in j; subst j. simpl; lia.
Intros gptr.
assert (memory_block sh (sizeof t_wedgearray_graph) (pointer_val_val gptr) =
        data_at_ sh (t_wedgearray_graph) (pointer_val_val gptr)). {
  rewrite <- memory_block_data_at_; auto.
} rewrite H0. clear H0.
assert (data_at_ sh t_wedgearray_graph (pointer_val_val gptr) =
        data_at sh t_wedgearray_graph (Vundef,(Vundef,Vundef)) (pointer_val_val gptr)). {
  unfold data_at_, field_at_, data_at.
  assert (default_val (nested_field_type t_wedgearray_graph []) = (Vundef,(Vundef,Vundef))) by reflexivity.
  rewrite H0. auto.
} rewrite H0. clear H0. (*that was easier than I thought :]*)
forward.
forward_call (sh, MAX_EDGES*(sizeof t_struct_edge)).
set (j := Int.max_unsigned) in *; compute in j; subst j. simpl; lia.
Intros eptr.
assert (memory_block sh (MAX_EDGES * (sizeof t_struct_edge)) (pointer_val_val eptr) = data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr)). {
  assert (memory_block sh (MAX_EDGES*(sizeof t_struct_edge)) (pointer_val_val eptr) = memory_block sh (sizeof (tarray t_struct_edge MAX_EDGES)) (pointer_val_val eptr)). {
    simpl. auto.
  } rewrite <- memory_block_data_at_; auto.
} rewrite H1. clear H1.
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr) = data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges MAX_EDGES) (pointer_val_val eptr)). {
  unfold data_at_, field_at_, data_at. assert (default_val (nested_field_type (tarray t_struct_edge MAX_EDGES) []) = list_repeat (Z.to_nat MAX_EDGES) (Vundef, (Vundef, Vundef))) by reflexivity.
  rewrite H1. auto.
} rewrite H1. clear H1.
forward.
forward.
forward.
forward.
forward.
Exists gptr eptr.
entailer!.
Qed.

Lemma body_kruskal: semax_body Vprog Gprog f_kruskal kruskal_spec.
Proof.
  start_function.
  forward. forward.
  (*call MakeSet*)
  forward_call (sh, (numV g)). Intros subsetsPtr.
  (*malloc mst*)
  forward_call (gv, sh). Intros mst.
  destruct mst as [gptr eptr].
  simpl fst in *. simpl snd in *. 
  forward. forward.
  assert (Hdef_g: Forall def_wedgerep (map wedge_to_cdata (graph_to_wedgelist g))) by (apply def_wedgerep_map_w2c).
  assert (Hperm_glist: Permutation (map wedge_to_cdata (graph_to_wedgelist g)) (map wedge_to_cdata glist)). apply Permutation_map. auto.
  assert (Hdef_glist: Forall def_wedgerep (map wedge_to_cdata glist)) by (apply (Forall_permutation _ _ _ Hdef_g Hperm_glist)).
  assert (HZlength_glist: Zlength (map wedge_to_cdata glist) = numE g). {
    rewrite <- (Permutation_Zlength (map wedge_to_cdata (graph_to_wedgelist g)) (map wedge_to_cdata glist) Hperm_glist).
    rewrite Zlength_map. apply g2wedgelist_numE.
  }
  assert (Hnumrange_g: Int.min_signed <= numE g <= Int.max_signed). {
    split. apply (Z.le_trans Int.min_signed 0 (numE g)). pose proof (Int.min_signed_neg); lia. apply numE_pos.
    apply (Z.le_trans (numE g) MAX_EDGES _). lia. set (j:=Int.max_signed); compute in j; subst j. unfold MAX_EDGES; lia.
  }
  rewrite (split2_data_at_Tarray_app (numE g) MAX_EDGES sh t_struct_edge
    (map wedge_to_cdata glist) (Vundef_cwedges (MAX_EDGES - numE g))).
    2: auto. 2: apply Vundef_cwedges_Zlength; lia. Intros.
  rewrite <- HZlength_glist.
  (******************************SORT******************************)
  forward_call ((wshare_share sh), 
                pointer_val_val orig_eptr,
                (map wedge_to_cdata glist)).
  - split3; [| |split]; trivial.
    rewrite HZlength_glist. split; [apply numE_pos | lia].
  - Intros sorted.
    (* some trivial assertions about sorted for convenience *)
    assert_PROP (isptr (pointer_val_val eptr)) by
        (rewrite (data_at_isptr sh); entailer!).
    rename H7 into H_eptr_isptr.
    assert (Hdef_sorted: Forall def_wedgerep sorted). {
      apply (Forall_permutation _ _ _ Hdef_glist H5).
    }
    assert (HZlength_sorted: Zlength sorted = numE g). {
      rewrite <- (Permutation_Zlength _ _ H5). apply HZlength_glist.
    } rewrite HZlength_glist. rewrite HZlength_sorted.
    (******************************THE BIG NASTY LOOP******************************) 
    forward_for_simple_bound (numE g)
    (EX i : Z,
     EX msf' : FiniteWEdgeListGraph,
     EX msflist: list (LE*EType),
     EX subsetsGraph' : UFGraph,
     PROP (forall v, vvalid msf' v <-> vvalid g v;
           numE msf' <= i;
           sound_weighted_edge_graph msf';
           is_partial_lgraph msf' g;
           uforest' msf';
           Permutation msflist (graph_to_wedgelist msf');
           forall v, vvalid g v <-> vvalid subsetsGraph' v;
           forall e u v, adj_edge g e u v -> In (wedge_to_cdata (edge_to_wedge g e)) (sublist 0 i sorted) -> ufroot_same subsetsGraph' u v;
           forall u v, ufroot_same subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           (*scoping that "incl" msflist (sublist i sorted)*)
           forall x, In x (map wedge_to_cdata msflist) -> exists j, 0 <= j < i /\ x = Znth j sorted;
           (*weight lemma: edges before i that WEREN't added, exists a upath made of edges before j
                consequently these edges have leq weight than Znth j sorted
            *)
           forall j, 0 <= j < i -> ~ In (Znth j sorted) (map wedge_to_cdata msflist) ->
            (exists p: upath, c_connected_by_path msf' p (fst (snd (Znth j sorted))) (snd (snd (Znth j sorted))) /\
              (exists l, fits_upath msf' l p /\ forall w, In w l -> In (wedge_to_cdata (edge_to_wedge g w)) (sublist 0 j sorted)))
          )
     LOCAL (temp _graph_E (Vint (Int.repr (numE g)));
            temp _graph__1 (pointer_val_val orig_gptr);
            temp _subsets (pointer_val_val subsetsPtr);
            temp _mst (pointer_val_val gptr))
     SEP (
          (*the irritating global haha*)
          data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
          (*orig graph with sorted edgelist*)
          data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr);
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
             (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr));
          (*msf'*)
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata msflist ++ (Vundef_cwedges (MAX_EDGES - numE msf'))) (pointer_val_val eptr);
          (*ufgraph*)
          whole_graph sh subsetsGraph' subsetsPtr
    ))%assert.
    + (******PRECON******)
      Exists (edgeless_WEdgeGraph (numV g)).
      Exists (graph_to_wedgelist (edgeless_WEdgeGraph (numV g))). (*=nil*)
      Exists (makeSet_discrete_Graph (Z.to_nat (numV g))).
        rewrite edgeless_WEdgeGraph_numV by lia.
        rewrite edgeless_WEdgeGraph_numE. rewrite Z.sub_0_r.
        rewrite graph_to_wedgelist_edgeless_WEdgeGraph. rewrite app_nil_l.
      entailer!. (*LAAAAAAAAG*)
      split3; [| | split3].
      * apply edgeless_WEdgeGraph_sound.
          split. lia. assert ((Int.max_signed/8) < Int.max_signed). apply Z.div_lt.
          set (k:=Int.max_signed); compute in k; subst k. lia. lia. lia.
      * repeat split; intros.
        rewrite <- edgeless_WEdgeGraph_vvalid in H25; apply H0; auto.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        unfold preserve_vlabel; intros. simpl. destruct vlabel. auto.
        unfold preserve_elabel; intros. apply edgeless_WEdgeGraph_evalid in H25; contradiction.
      * apply uforest'_edgeless_WEdgeGraph.
      * intros; split; intros. apply H0 in H25. apply makeSet_vvalid. rewrite Z2Nat.id by lia. lia.
          apply H0. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. lia.
      * unfold connected; unfold connected_by_path.
          (*will like to prove this without connectedness, but will have to create a lemma on makeSet's roots, which seems annoying*)
          intros. rewrite <- connected_ufroot_same_iff. split; intros.
        { destruct H25 as [p [? [? ?]]].
          destruct p eqn:Hp; simpl in H25; simpl in H26; inversion H26.
          subst z. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H27; inversion H27. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
          simpl. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. apply H25.
          (*case p = u::z0::u0.
            Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...*)
          destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25. destruct H30.
          rewrite makeSet_vvalid in H31. rewrite Z2Nat.id in H31 by lia.
          destruct H29; destruct H29;
            rewrite H32 in H31; rewrite makeSet_dst in H32; rewrite <- H32 in H31; lia.
        }
        { (*more or less same deal...*)
          destruct H25 as [p [? [? ?]]].
          destruct p eqn:Hp; simpl in H26; inversion H26.
          subst v0. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H27; inversion H27. subst u. subst p. destruct H25.
          apply connected_refl. apply makeSet_vvalid. rewrite Z2Nat.id; lia.
          (*case p = u::z0::u0.
            then u z0 is adjacent in edgeless, contradiction...
          *)
          destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25.
          apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        }
  + (******LOOP BODY******)
  Intros.
  assert (HnumV_msf': numV msf' = numV g). {
    unfold numV. apply Permutation_Zlength. apply NoDup_Permutation.
    apply NoDup_VList. apply NoDup_VList. intros. repeat rewrite VList_vvalid. apply H8.
  }
  (*some assertions about Znth i sorted, for convenience*)
  assert (Hdef_i: def_wedgerep (Znth i sorted)).
    rewrite Forall_forall in Hdef_sorted. apply Hdef_sorted. apply Znth_In. lia.
  assert (HIn_i: In (Znth i sorted) (map wedge_to_cdata glist)). {
    apply Permutation_sym in H5. apply (@Permutation_in _ _ _ _ H5). apply Znth_In. lia.
  }
  apply list_in_map_inv in HIn_i.
  destruct HIn_i as [e [Heq_i HIn_i]].
  destruct e as [w [u v]].
  assert (Htmp: elabel g (u,v) = w /\ evalid g (u,v)). {
    apply Permutation_sym in H3. apply (Permutation_in (A:= prod LE EType) (l:=glist) (l':=graph_to_wedgelist g) (w,(u,v)) H3) in HIn_i.
    unfold graph_to_wedgelist in HIn_i. apply list_in_map_inv in HIn_i. destruct HIn_i. destruct H19.
    inversion H19. split. auto. apply EList_evalid in H20. rewrite <- H23 in H20. apply H20.
  } destruct Htmp as [Helabel_w_i Hevalid_uv_i].
  assert (Htmp: vvalid g u /\ vvalid g v). { apply sound_uv_vvalid; auto. }
  destruct Htmp as [Hvvalid_g_u Hvvalid_g_v].
  assert (Hvvalid_subsetsGraph'_u: vvalid subsetsGraph' u). apply H14. apply Hvvalid_g_u.
  assert (Hvvalid_subsetsGraph'_v: vvalid subsetsGraph' v). apply H14. apply Hvvalid_g_v.
  assert (HZlength_msflist: Zlength msflist = numE msf'). {
    rewrite (Permutation_Zlength _ _  H13). unfold graph_to_wedgelist.
    rewrite Zlength_map. reflexivity.
  }
  assert (Hu_i: fst (snd (Znth i sorted)) = Vint (Int.repr u)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
  assert (Hv_i: snd (snd (Znth i sorted)) = Vint (Int.repr v)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
  assert (Hw_i: fst (Znth i sorted) = Vint (Int.repr w)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
  assert (Hrepable_u: Int.min_signed <= u <= Int.max_signed).
    rewrite <- H0 in Hvvalid_g_u. split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  assert (Hrepable_v: Int.min_signed <= v <= Int.max_signed).
    rewrite <- H0 in Hvvalid_g_v. split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  assert (H_evalid_g_uv: evalid g (u,v)). rewrite <- EList_evalid.
    assert (In (w, (u, v)) (graph_to_wedgelist g)). apply (Permutation_in (l:=glist)).
    apply Permutation_sym; auto. apply HIn_i. unfold graph_to_wedgelist in H19.
    apply list_in_map_inv in H19. destruct H19; destruct H19.
    unfold edge_to_wedge in H19. inversion H19. rewrite H23; apply H20.
  assert (Hrepable_w: Int.min_signed <= w <= Int.max_signed).
    rewrite <- Helabel_w_i. apply H. apply H_evalid_g_uv.

  forward. forward. entailer!.
    rewrite (surjective_pairing (Znth i sorted)).
    rewrite (surjective_pairing (snd (Znth i sorted))).
    apply Hdef_i.
  forward. forward. entailer!.
    rewrite (surjective_pairing (Znth i sorted)).
    rewrite (surjective_pairing (snd (Znth i sorted))).
    apply Hdef_i.
 rewrite (surjective_pairing (Znth i sorted)).
 rewrite (surjective_pairing (snd (Znth i sorted))).
  (*find(u)*)
  forward_call (sh, subsetsGraph', subsetsPtr, u).
  Intros u_root. destruct u_root as [subsetsGraph_u u_root].
  simpl fst.
  (*find v*)
  forward_call (sh, subsetsGraph_u, subsetsPtr, v).
  destruct H19 as [? _]; rewrite <- H19. apply Hvvalid_subsetsGraph'_v.
  Intros v_root. destruct v_root as [subsetsGraph_uv v_root].
  simpl fst in *. simpl snd in *.

  (*assertions about u_root and v_root*)
  assert (H_subsetsGraph'_uroot: uf_root subsetsGraph' u u_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply H20.
  assert (Htmp: uf_root subsetsGraph_u v v_root). apply (uf_equiv_root_the_same subsetsGraph_u subsetsGraph_uv). apply H21. apply H22.
  assert (H_subsetsGraph'_vroot: uf_root subsetsGraph' v v_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply Htmp. clear Htmp.
  assert (Hvvalid_uroot: vvalid subsetsGraph' u_root). apply (reachable_foot_valid subsetsGraph' u). apply H_subsetsGraph'_uroot.
  assert (Hvvalid_vroot: vvalid subsetsGraph' v_root). apply (reachable_foot_valid subsetsGraph' v). apply H_subsetsGraph'_vroot.
  assert (Hrepable_uroot: Int.min_signed <= u_root <= Int.max_signed).
    apply H14 in Hvvalid_uroot. apply H0 in Hvvalid_uroot.
    split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  assert (Hrepable_vroot: Int.min_signed <= v_root <= Int.max_signed).
    apply H14 in Hvvalid_vroot. apply H0 in Hvvalid_vroot.
    split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  assert (Hequiv_trans: uf_equiv subsetsGraph' subsetsGraph_uv).
    apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
  assert (Hvvalid_subsetsGraph_uv_u: vvalid subsetsGraph_uv u). {
    destruct Hequiv_trans as [Htmp ]; rewrite <- Htmp; apply Hvvalid_subsetsGraph'_u.
  }
  assert (Hvvalid_subsetsGraph_uv_v: vvalid subsetsGraph_uv v). {
    destruct Hequiv_trans as [Htmp ]; rewrite <- Htmp; apply Hvvalid_subsetsGraph'_v.
  }
  (*remove subsetsGraph_u*)
  clear H19 H20 H21. rename H22 into H19.
  forward_if.
  --- (* yes, add this edge.*)
    forward. forward. entailer!. apply Hdef_i.
    forward. forward. rewrite (surjective_pairing (Znth i sorted)).
    (*split. UGLY*)
    rewrite (split2_data_at_Tarray_app (numE msf') MAX_EDGES sh t_struct_edge
      (map wedge_to_cdata msflist) (Vundef_cwedges (MAX_EDGES - numE msf'))).
    2: rewrite Zlength_map; auto. 2: apply Vundef_cwedges_Zlength; lia. Intros.
    replace (Vundef_cwedges (MAX_EDGES - numE msf')) with
      ((Vundef_cwedges 1)++(Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))).
    2: { pose proof (Vundef_cwedges_Zlength (MAX_EDGES - numE msf')).
          rewrite <- (sublist_same 0 (MAX_EDGES - numE msf') (Vundef_cwedges (MAX_EDGES - numE msf'))) by lia.
          rewrite (sublist_split 0 1 (MAX_EDGES - numE msf')) by lia.
          rewrite sublist_one by lia. unfold Vundef_cwedges. rewrite Znth_list_repeat_inrange by lia.
          rewrite sublist_list_repeat by lia. rewrite Z.sub_add_distr by lia. simpl; auto.
    }
    rewrite (split2_data_at_Tarray_app 1 (MAX_EDGES - numE msf') sh t_struct_edge
      (Vundef_cwedges 1) (Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))).
    2: apply Vundef_cwedges_Zlength; lia. 2: rewrite Z.sub_add_distr by lia; apply Vundef_cwedges_Zlength; lia. Intros.
    replace (Vundef_cwedges 1) with [(Vundef,(Vundef,Vundef))] by (simpl; auto).
    rewrite (data_at_singleton_array_eq' sh t_struct_edge (Vundef,(Vundef,Vundef))).
    set (a:= field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE msf')] (pointer_val_val eptr)).
    assert_PROP(isptr a). rewrite data_at_isptr. entailer!.
    assert (Ha_offset: a = offset_val (12*numE msf') (pointer_val_val eptr)). {
      unfold a; rewrite field_address0_clarify. simpl. auto. fold a. apply isptr_is_pointer_or_null. auto.
    }
    (*now, call fill_edge*)
    forward_call (sh, a, fst (Znth i sorted), fst (snd (Znth i sorted)), snd (snd (Znth i sorted)), (Vundef, (Vundef, Vundef))).
    replace (fst (Znth i sorted), (fst (snd (Znth i sorted)), snd (snd (Znth i sorted)))) with (Znth i sorted).
    2: rewrite (surjective_pairing (Znth i sorted)); rewrite (surjective_pairing (snd (Znth i sorted))); auto.
    (*refold. UGLY*)
    unfold SEPx. simpl. rewrite sepcon_comm. repeat rewrite <- sepcon_assoc. repeat rewrite sepcon_emp. repeat rewrite sepcon_assoc.
    rewrite (sepcon_comm _ (data_at sh t_struct_edge (Znth i sorted) a)).
    rewrite <- (data_at_singleton_array_eq' sh t_struct_edge).
    rewrite <- (split2_data_at_Tarray_app 1 (MAX_EDGES - numE msf') sh t_struct_edge
          [Znth i sorted] (Vundef_cwedges (MAX_EDGES - (numE msf' + 1))) a
    ).
    2: { rewrite Zlength_cons. rewrite Zlength_nil. auto. }
    2: { rewrite Vundef_cwedges_Zlength by lia. lia. }
    unfold a.
    rewrite <- (split2_data_at_Tarray_app (numE msf') MAX_EDGES sh t_struct_edge
      (map wedge_to_cdata msflist) ([Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
      (pointer_val_val eptr)).
    2: { rewrite Zlength_map. apply HZlength_msflist. }
    2: { rewrite Zlength_app. rewrite Zlength_cons; rewrite Zlength_nil. rewrite Vundef_cwedges_Zlength by lia. lia. }
    repeat rewrite sepcon_assoc.
    (*yessss. now for stupidity*)
    assert (Htmp:
    (whole_graph sh subsetsGraph_uv subsetsPtr *
      (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES) *
        (data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr) *
          (data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr) *
            (data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
               (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr)) *
             (data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr) *
              data_at sh (tarray t_struct_edge MAX_EDGES) (map wedge_to_cdata msflist ++
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1))) (pointer_val_val eptr)
              ))))))%logic
    = fold_right_sepcon [
      whole_graph sh subsetsGraph_uv subsetsPtr;
      data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
      data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr);
      data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
      data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
        (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr));
      data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
      data_at sh (tarray t_struct_edge MAX_EDGES) (map wedge_to_cdata msflist ++
                   [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1))) (pointer_val_val eptr)
      ]). simpl. rewrite sepcon_emp. reflexivity. rewrite Htmp; clear Htmp.
      fold (SEPx (A:=environ) [
      whole_graph sh subsetsGraph_uv subsetsPtr;
      data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
      data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr);
      data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
      data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
        (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr));
      data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
      data_at sh (tarray t_struct_edge MAX_EDGES) (map wedge_to_cdata msflist ++
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1))) (pointer_val_val eptr)
    ]).
  replace (map wedge_to_cdata msflist ++
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
  with (map wedge_to_cdata (msflist+::(w,(u,v))) ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1))).
  2: { rewrite Heq_i. rewrite map_app. rewrite <- app_assoc. reflexivity. }
  (*done with the SEP manipulation*)
  forward. forward.

  (*before we union, show that u-v doesn't exist in msf'*)
  assert (HsubsetsGraph'_ufroot_uv: ~ ufroot_same subsetsGraph' u v). {
    unfold not; intros Htmp. destruct Htmp as [x [? ?]].
    assert (u_root = x). apply (uf_root_unique' subsetsGraph' u u_root x); auto.
    assert (v_root = x). apply (uf_root_unique' subsetsGraph' v v_root x); auto.
    subst u_root; subst v_root; contradiction.
  }
  assert (Hconnected_uv: ~ connected msf' u v). rewrite <- H16; auto.
  assert(H_msf'_uv: ~ evalid msf' (u,v)). {
    unfold not; intros.
    assert (connected msf' u v). {
      apply adjacent_connected. exists (u,v).
      split. apply sound_strong_evalid; auto. left.
      rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
    } contradiction.
  }
  assert (Hsound: sound_weighted_edge_graph (FiniteWEdgeListGraph_adde msf' (u,v) (elabel g (u,v)))).
  { apply adde_sound. auto.
      simpl; apply H8; auto. simpl; apply H8; auto. apply H. auto. }
  forward_call (sh, subsetsGraph_uv, subsetsPtr, u, v).
  (*postcon*)
  Exists (FiniteWEdgeListGraph_adde msf' (u,v) w).
  Exists (msflist+::(w,(u,v))).
  Intros uv_union. Exists uv_union.
  (*before we entailer, preemptively fix up some of the SEPs*)
  replace (numV (FiniteWEdgeListGraph_adde msf' (u, v) w)) with (numV msf').
  2: { symmetry; apply adde_numV. }
  replace (numE (FiniteWEdgeListGraph_adde msf' (u, v) w)) with (numE msf' + 1).
  2: { symmetry; apply adde_numE. apply H_msf'_uv. }
  replace (Int.add (Int.repr (numE msf')) (Int.repr 1)) with (Int.repr (numE msf' + 1)).
  2: { symmetry; apply add_repr. }
  (*ok!*)
  entailer!. (*lalalalalag*)
  clear H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44.
  split3. 3: split3. 5: split3. 7: split. (*my invariant sure grew unwieldy*)
    +++
    split3. split3.
      intros. apply H8. apply adde_vvalid in H23. apply H23.
      intros. apply adde_evalid_or in H23. destruct H23. apply H11; auto. subst e; auto.
      split. intros. apply adde_evalid_or in H23. destruct H23.
        rewrite <- sound_src; auto. rewrite <- sound_src; auto. apply H11; auto. apply adde_evalid2. auto.
        subst e. rewrite <- sound_src; auto. rewrite <- sound_src; auto. apply adde_evalid1. auto.
      intros. apply adde_evalid_or in H23. destruct H23.
        rewrite <- sound_dst; auto. rewrite <- sound_dst; auto. apply H11; auto. apply adde_evalid2. auto.
        subst e. rewrite <- sound_dst; auto. rewrite <- sound_dst; auto. apply adde_evalid1. auto.
      unfold preserve_vlabel; intros. simpl. destruct vlabel. destruct vlabel. auto.
      unfold preserve_elabel; intros. simpl. unfold graph_gen.update_elabel. simpl in H23. unfold graph_gen.addValidFunc in H23.
        unfold EquivDec.equiv_dec. destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. auto.
        destruct H23. apply H11. auto. unfold RelationClasses.complement, Equivalence.equiv in c. symmetry in H23. contradiction.
    +++
    apply uforest'_adde; auto. apply H8; auto. apply H8; auto.
    +++
    apply NoDup_Permutation. apply NoDup_app_inv.
    apply (Permutation_NoDup (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto. apply NoDup_g2wedgelist.
    apply NoDup_cons. auto. apply NoDup_nil.
    unfold not; intros. simpl in H24. destruct H24; try contradiction.
    apply (Permutation_in (l':=graph_to_wedgelist msf')) in H23.
    rewrite <- H24 in H23. apply g2wedgelist_evalid in H23. simpl in H23. contradiction.
    auto. apply NoDup_g2wedgelist.
    intros; split; intros. apply in_app_or in H23. destruct H23.
    apply (Permutation_in (l':=graph_to_wedgelist msf')) in H23. 2: auto.
    apply list_in_map_inv in H23. destruct H23; destruct H23. rewrite H23. apply EList_evalid in H24.
    apply adde_g2wedgelist_2.
    unfold not; intros; rewrite <- H25 in H24; contradiction. apply H24.
    simpl in H23. destruct H23. rewrite <- H23.
    apply adde_g2wedgelist_1. contradiction.
    destruct x as [w e].
    unfold graph_to_wedgelist in H23. apply list_in_map_inv in H23.
    destruct H23; destruct H23.
    apply EList_evalid in H24.
    unfold edge_to_wedge in H23; simpl in H23. unfold graph_gen.update_elabel in H23.
    unfold EquivDec.equiv_dec in H23. destruct (E_EqDec (u, v) x).
    unfold Equivalence.equiv in e0. rewrite H23. rewrite e0. apply in_or_app. right. left. auto.
    apply adde_evalid_or in H24. destruct H24.
    apply in_or_app. left. apply (Permutation_in (l:=graph_to_wedgelist msf')).
    apply Permutation_sym; auto.
    replace (w,e) with (edge_to_wedge msf' e). apply in_map. apply EList_evalid. inversion H23. apply H24.
    unfold edge_to_wedge; simpl. inversion H23. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. rewrite H24 in c; contradiction.
    +++
    intros. rewrite <- (uf_union_vvalid subsetsGraph_uv uv_union u v); auto.
    destruct Hequiv_trans. rewrite <- H23. apply H14.
    +++
    intros. rewrite (sublist_split 0 i (i+1)) in H24 by lia. apply in_app_or in H24.
    destruct H24.
    (*case of every edge that was before*)
    apply (uf_union_preserves_connected subsetsGraph_uv _ u v); auto.
    apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv). auto.
    apply (H15 e); auto.
    (*the newly added edge*)
    rewrite (sublist_one i (i+1) _) in H24 by lia.
    destruct H24. 2: contradiction.
    rewrite Heq_i in H24.
    destruct H23. unfold edge_to_wedge in H24.
    inversion H24.
    do 2 rewrite Int.Z_mod_modulus_eq in H28. do 2 rewrite Int.Z_mod_modulus_eq in H29.
    destruct H as [Hvertex_valid [Hedge_valid [Hweight_valid [Hsrc_edge Hdst_edge]]]].
    destruct H23. destruct H23.
    rewrite Hsrc_edge in H23, H25; auto. rewrite Hdst_edge in H26, H25; auto.
    assert (u = fst e /\ v = snd e). {
      apply Hvertex_valid in Hvvalid_g_u.
      apply Hvertex_valid in Hvvalid_g_v.
      apply Hvertex_valid in H23.
      apply Hvertex_valid in H26.
      set (q:=Int.max_signed) in *; compute in q; subst q.
      set (q:=Int.modulus) in *; compute in q; subst q.
      do 2 rewrite Z.mod_small in H28 by lia.
      do 2 rewrite Z.mod_small in H29 by lia. split; auto.
    }
    destruct H30.
    destruct H25; destruct H25; subst u0; subst v0; rewrite <- H30; rewrite <- H31.
    (*both cases: apply union_ufroot_same.*)
    2: apply ufroot_same_symm.
    all: apply (uf_union_connected subsetsGraph_uv); auto.
    +++
    intros a b; split; intros.
    ***
    (*----------->*)
    (*this is a mess with 10 cases because at the time, there were no backward lemmas about uf_union
      Will also need an analog of cross_bridge_implies_endpoints, and a ufroot_same_dec analog of the in_dec
    *)
    assert (Hvvalid_subsetsGraph_uv_a: vvalid subsetsGraph_uv a).
      apply (uf_union_vvalid subsetsGraph_uv uv_union u v a); auto.
      destruct H23 as [rt [? ?]]. apply (ufroot_vvalid_vert uv_union rt a). auto.
    assert (Hvvalid_subsetsGraph_uv_b: vvalid subsetsGraph_uv b).
      apply (uf_union_vvalid subsetsGraph_uv uv_union u v b); auto.
      destruct H23 as [rt [? ?]]. apply (ufroot_vvalid_vert uv_union rt b). auto.
    destruct (connected_dec msf' a b); rename H24 into Hab. apply adde_connected; auto.
    destruct (connected_dec msf' a u).
    (*a-u*)
      destruct (connected_dec msf' a v). apply connected_symm in H24. apply (connected_trans msf' u a v H24) in H25. contradiction.
      destruct (connected_dec msf' u b). apply (connected_trans msf' a u b H24) in H26. apply adde_connected. auto. auto.
      destruct (connected_dec msf' v b). apply adde_connected_through_bridge1; auto.
      rewrite <- H16 in H24, H26, H27.
      rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H24, H26, H27; auto.
      assert (~ ufroot_same subsetsGraph_uv b u). { unfold not; intros.
        apply ufroot_same_symm in H28. contradiction. }
      apply (uf_union_remains_disconnected1 _ uv_union u v) in H28; auto.
      2: auto. 2: { unfold not; intros. apply ufroot_same_symm in H29. contradiction. }
      apply (uf_union_preserves_connected _ uv_union u v) in H24; auto.
      apply ufroot_same_symm in H23.
      apply (ufroot_same_trans _ (liGraph uv_union) b a u) in H23; auto. contradiction.
    (*a not connected to u*)
    (*destruct connected msf' a v, repeat the above...*)
    destruct (connected_dec msf' a v).
      destruct (connected_dec msf' u b). apply adde_connected_through_bridge2; auto.
        destruct (connected_dec msf' v b). apply (connected_trans msf' a v b H25) in H27.
          apply adde_connected; auto.
        rewrite <- H16 in H25, H26, H27.
        rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H25, H26, H27; auto.
        assert (~ ufroot_same subsetsGraph_uv b v). { unfold not; intros.
          apply ufroot_same_symm in H28. contradiction. }
        apply (uf_union_remains_disconnected2 _ uv_union u v) in H28; auto.
          2: { rewrite ufroot_same_symm. auto. }
        apply (uf_union_preserves_connected _ uv_union u v) in H25; auto.
        apply ufroot_same_symm in H23.
        apply (ufroot_same_trans _ (liGraph uv_union) b a v) in H23; auto. contradiction.
      destruct (connected_dec msf' u b). apply H16 in H26.
        apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H26; auto.
        apply (uf_union_preserves_connected _ uv_union u v) in H26; auto.
        apply ufroot_same_symm in H26.
        apply (ufroot_same_trans _ (liGraph uv_union) a b u H23) in H26.
        (*However, ~ connected msf' a u -> ... -> ~ ufroot_same uv_union, contradiction*)
        assert (~ ufroot_same uv_union a u). {
          rewrite <- H16 in H24, H25. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H24, H25; auto.
          apply (uf_union_remains_disconnected1 subsetsGraph_uv uv_union u v a); auto. }
        contradiction.
        destruct (connected_dec msf' v b). apply H16 in H27. apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H27; auto.
          apply (uf_union_preserves_connected _ uv_union u v) in H27; auto. apply ufroot_same_symm in H27.
          apply (ufroot_same_trans _ (liGraph uv_union) a b v H23) in H27.
          (*However, ~ connected msf' a u -> ... -> ~ ufroot_same uv_union, contradiction*)
          assert (~ ufroot_same uv_union a v). {
            rewrite <- H16 in H24, H25. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H24, H25; auto.
            apply (uf_union_remains_disconnected2 subsetsGraph_uv uv_union u v a); auto. }
          contradiction.
        (*finally, neither were connected to u or v*)
        rewrite <- H16 in Hab, H24, H25, H26, H27.
        rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in Hab, H24, H25, H26, H27; auto.
        assert (~ ufroot_same uv_union a b). {
          apply (uf_union_joins_only_uv subsetsGraph_uv uv_union u v a b); auto.
        }
        contradiction.
    ***
    (*<-----------*)
    (*assert exists list edges... destruct In (u,v) l.
      Yes: then apply connected_bridge_implies_endpoints, destruct
        a-u,b-v: then by union_preserves_connected, and union_connected...
        a-v,b-u: same
      No: then apply adde_unaffected.
    *)
    destruct H23 as [p0 ?]. 
    apply connected_by_upath_exists_simple_upath in H23. clear p0; destruct H23 as [p [H23 Hp_simpl]].
    assert (exists l : list EType, fits_upath (FiniteWEdgeListGraph_adde msf' (u, v) (elabel g (u, v))) l p).
    apply connected_exists_list_edges in H23; auto. destruct H24 as [l ?].
    destruct (in_dec E_EqDec (u,v) l).
    (*Yes*) assert (connected msf' a u /\ connected msf' v b \/ connected msf' a v /\ connected msf' u b).
      apply (cross_bridge_implies_endpoints msf' u v (elabel g (u,v)) p l); auto.
      destruct H25; destruct H25;
        rewrite <- H16 in H25, H26;
        rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H25, H26; auto;
        apply (uf_union_preserves_connected subsetsGraph_uv uv_union u v) in H25; auto;
        apply (uf_union_preserves_connected subsetsGraph_uv uv_union u v) in H26; auto.
        assert (ufroot_same uv_union u v).
          apply (uf_union_connected subsetsGraph_uv uv_union u v); auto.
        apply (ufroot_same_trans _ (liGraph uv_union) u v b H27) in H26.
        apply (ufroot_same_trans _ (liGraph uv_union) a u b); auto.
        assert (ufroot_same uv_union u v).
          apply (uf_union_connected subsetsGraph_uv uv_union u v); auto.
        apply ufroot_same_symm in H27.
        apply (ufroot_same_trans _ (liGraph uv_union) v u b H27) in H26.
        apply (ufroot_same_trans _ (liGraph uv_union) a v b); auto.
    (*No *) assert (connected msf' a b). exists p. destruct H23. split.
    apply (adde_unaffected msf' (u,v) (elabel g (u,v))). apply H23. exists l. split. apply (adde_fits_upath_rev msf' (u,v) (elabel g (u,v))); auto. auto.
    auto.
    rewrite <- H16 in H25. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H25; auto.
    apply (uf_union_preserves_connected subsetsGraph_uv uv_union u v) in H25; auto.
    +++
    intros. rewrite map_app in H23. apply in_app_or in H23; destruct H23.
    apply H17 in H23. destruct H23; destruct H23. exists x0; split; [lia | auto].
    simpl in H23. destruct H23. exists i; split. lia. rewrite <- H23. symmetry; apply Heq_i.
    contradiction.
    +++
    intros.
    destruct (Z.lt_trichotomy j i).
    (*j<i*) 1: {
      assert (~ In (Znth j sorted) (map wedge_to_cdata msflist)). {
        unfold not; intros. assert (In (Znth j sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
        rewrite map_app. apply in_or_app. left. auto. contradiction. }
      apply H18 in H26. 2: lia. destruct H26 as [p ?]; destruct H26. destruct H27 as [l ?]; destruct H27.
      exists p.
      (*replace Znth j sorted with (w',(u',v'))*)
      assert (HIn_j: In (Znth j sorted) (map wedge_to_cdata glist)). {
        apply Permutation_sym in H5. apply (@Permutation_in _ _ _ _ H5). apply Znth_In. lia.
      }
      apply list_in_map_inv in HIn_j.
      destruct HIn_j as [e' [Heq_j HIn_j]].
      destruct e' as [w' [u' v']]. unfold wedge_to_cdata in Heq_j. simpl in Heq_j.
      replace (fst (snd (Znth j sorted))) with (Vint (Int.repr u')). 2: rewrite Heq_j; simpl; auto.
      replace (snd (snd (Znth j sorted))) with (Vint (Int.repr v')). 2: rewrite Heq_j; simpl; auto.
      rewrite Heq_j in H26; simpl in H26.
      (*we''ll deal with the vvalid etc when we need it...*)
      split. unfold c_connected_by_path. unfold c_connected_by_path in H26.
      apply adde_connected_by_path. auto. apply H26. exists l.
      split. apply adde_fits_upath. auto. apply H27. apply H28.
    }
    (*the rest are trivial*)
    destruct H25. subst j.
    assert (In (Znth i sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
      rewrite Heq_i. apply in_map. apply in_or_app. right. left; auto. contradiction.
    lia.
 --- (* no, don't add this edge *)
  forward.
  Exists msf' msflist subsetsGraph_uv.
  entailer!.
  clear H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40.
  split3; [| |split3].
  +++
  intros. rewrite H14. symmetry. destruct Hequiv_trans. rewrite H20. split; auto.
  +++
  intros. rewrite (sublist_split 0 i (i+1) sorted) in H21 by lia. apply in_app_or in H21. destruct H21.
  apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv); auto.
  apply (H15 e u0 v0 H20 H21).
  rewrite sublist_one in H21 by lia. destruct H21. 2: contradiction.
  apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv). auto.
  rewrite Heq_i in H21.
    destruct H as [Hvertex_valid [Hedge_valid [Hweight_valid [Hsrc_edge Hdst_edge]]]].
    destruct H20. destruct H. destruct H22.
    rewrite (Hsrc_edge e) in H22, H20; auto. rewrite Hdst_edge in H23, H20; auto.
    assert (u = fst e /\ v = snd e). {
      unfold edge_to_wedge in H21. inversion H21.
      do 2 rewrite Int.Z_mod_modulus_eq in H26. do 2 rewrite Int.Z_mod_modulus_eq in H27.
      apply Hvertex_valid in Hvvalid_g_u.
      apply Hvertex_valid in Hvvalid_g_v.
      apply Hvertex_valid in H22.
      apply Hvertex_valid in H23.
      set (q:=Int.max_signed) in *; compute in q; subst q.
      set (q:=Int.modulus) in *; compute in q; subst q.
      do 2 rewrite Z.mod_small in H26 by lia.
      do 2 rewrite Z.mod_small in H27 by lia. split; auto.
    } destruct H24.
  destruct H20; destruct H20; subst u0; subst v0; rewrite <- H24; rewrite <- H25.
  exists v_root; split; auto. exists v_root; split; auto.
  +++ intros.
  rewrite <- H16.
  apply uf_equiv_ufroot_same. apply uf_equiv_sym. trivial.
  +++ intros.
  destruct (H17 _ H20) as [y [? ?]].
  exists y.
  split; trivial; lia.
  +++ intros.
  destruct (Z.eq_dec j i).
  2: apply H18; trivial; lia.
  subst j. (* hrmm *)
  rewrite Hu_i; rewrite Hv_i.
  unfold c_connected_by_path.
  assert (connected msf' u v). { apply H16. exists v_root. split; auto. }
  destruct H22 as [p ?]. exists p. split.
  rewrite <- H0 in Hvvalid_g_u. rewrite <- H0 in Hvvalid_g_v.
  repeat rewrite Int.signed_repr. auto.
  split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  apply connected_exists_list_edges in H22. destruct H22 as [l ?]. exists l.
  split. auto. intros. assert (In w (EList msf')). apply EList_evalid.
  apply (fits_upath_evalid msf' p l); auto.
  assert (In (wedge_to_cdata (edge_to_wedge msf' w)) (map wedge_to_cdata msflist)).
  apply in_map. apply (Permutation_in (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto.
  apply in_map. auto.
  assert (edge_to_wedge msf' w = edge_to_wedge g w). unfold edge_to_wedge.
  assert (elabel msf' w = elabel g w). apply H11. apply EList_evalid in H24; apply H24. rewrite H26; auto.
  rewrite <- H26.
  assert (incl (map wedge_to_cdata msflist) (sublist 0 i sorted)).
  unfold incl; intros. apply H17 in H27. destruct H27; destruct H27. rewrite H28.
  assert (Znth (x+0) sorted = Znth x (sublist 0 i sorted)).
  symmetry. apply (Znth_sublist 0 x i sorted). lia. lia. rewrite Z.add_0_r in H29. rewrite H29.
  apply Znth_In. rewrite Zlength_sublist by lia; lia.
  apply H27. apply H25.
  (*******************************AFTER LOOP****************************)
  + Intros msf. Intros msflist.
    Intros subsetsGraph'.
    replace (sublist 0 (numE g) sorted) with sorted in *. 2: {
      rewrite <- HZlength_sorted. rewrite sublist_same by auto. auto.
    }
    assert (forall p u v, connected_by_path g p u v -> ufroot_same subsetsGraph' u v). {
      induction p; intros.
      + destruct H18; destruct H18; destruct H19. inversion H19.
      + destruct p. destruct H18. simpl in H18. destruct H19; inversion H19; inversion H20. subst u; subst v.
        apply (ufroot_same_refl _ (liGraph subsetsGraph')). apply H13. auto.
        destruct H18. destruct H18. destruct H19. inversion H19; subst a.
        apply (ufroot_same_trans _ (liGraph subsetsGraph') u v0 v).
          destruct H18. apply (H14 x). auto.
          assert (In x (EList g)). apply EList_evalid. apply H18.
          assert (In (edge_to_wedge g x) glist). apply (Permutation_in (l:=graph_to_wedgelist g) (l':=glist)).
          auto. apply in_map. auto.
          apply (Permutation_in (l:=map wedge_to_cdata glist)). auto. apply in_map. auto.
        apply IHp. split. auto. split. simpl; auto. rewrite last_error_cons in H21; auto. unfold not; intros; inversion H22.
    }
    assert (forall u v, connected g u v -> ufroot_same subsetsGraph' u v). {
      intros. destruct H19. apply (H18 x u v H19).
    }
    assert (Hspanning: forall u v, connected g u v <-> connected msf u v). {
      intros; split; intros. apply H15. apply H19. auto.
      apply (is_partial_lgraph_connected msf g); auto.
    }
    (*everything we want from unionfind is done. We can free and clear it*)
    clear H18 H19. forward_call (sh, subsetsPtr, subsetsGraph').

    (* In hindsight, this wouldn't be needed with better definitions. But let's just soldier on
       Don't put this up on top, I worry about the effect of VST attempting to yank a value out
    *)
    apply (Permutation_trans Hperm_glist) in H5.
    assert (Permutation (graph_to_wedgelist g) (map cdata_to_wedge sorted)). {
      rewrite <- (w2c2w_map (graph_to_wedgelist g)).
      2: { intros. apply (sound_g2wedgelist_repable g); auto. }
      apply Permutation_map. auto.
    } set (lsorted:=map cdata_to_wedge sorted).
    assert (map wedge_to_cdata lsorted = sorted). apply c2w2c_map. auto.
    forward.
    Exists gptr eptr msf msflist lsorted.
    entailer!.
    (*handle the SEP*)
    2: { replace sorted with (map wedge_to_cdata (map cdata_to_wedge sorted)).
      fold lsorted.
      rewrite (split2_data_at_Tarray sh t_struct_edge MAX_EDGES (numE g)
        (map wedge_to_cdata lsorted ++ Vundef_cwedges (MAX_EDGES - numE g))
        (map wedge_to_cdata lsorted ++ Vundef_cwedges (MAX_EDGES - numE g))
        (map wedge_to_cdata lsorted) (Vundef_cwedges (MAX_EDGES - numE g))).
      entailer!.
      split. apply numE_pos. auto.
      rewrite Zlength_app. rewrite H19. rewrite HZlength_sorted. rewrite Vundef_cwedges_Zlength by lia. lia.
      rewrite sublist_same; auto.
      rewrite Zlength_app. rewrite H19. rewrite HZlength_sorted. rewrite Vundef_cwedges_Zlength by lia. lia.
      rewrite sublist0_app1. rewrite sublist_same. auto. auto. rewrite H19. lia.
      rewrite H19. lia. rewrite sublist_app2. rewrite H19. rewrite HZlength_sorted.
      replace (numE g - numE g) with 0 by lia. rewrite sublist_same. auto. lia. rewrite Vundef_cwedges_Zlength by lia. auto.
      rewrite H19. lia.
    }
    clear H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38.
    assert (Hmsf: labeled_spanning_uforest msf g).
      split. split3. apply H10. auto. unfold spanning. auto. apply H10.
    (*minimum spanning tree*)
    split. auto.
    (*minimum...*)
    intros.
assert (Hsound_t': sound_weighted_edge_graph t'). { apply (spanning_uforest_sound t' g); auto. }
(*idea: first obtain a list of edges in t' but not in msf (ldiff)
  Use the induct to find a pair of edges in msf but not in (lmsf), and have the property of being a bridge for the edge in ldiff
  By the weight lemma, a path p exists with all edges before ldiff in lsorted.
  Thus, Znth i lmsf must be in this path, meaning it's weight is lower
  Thus, sum of lsame++lmsf <= lsame++ldiff
*)
assert (exists lsame ldiff : list EType,
    NoDup lsame /\ NoDup ldiff /\
    Permutation (lsame ++ ldiff) (EList t') /\
    incl lsame (EList msf) /\ (forall e : EType, In e ldiff -> ~ In e (EList msf))).
    { apply list_same_diff. apply NoDup_EList. apply NoDup_EList. }
destruct H21 as [lsame [ldiff [? [? [? [? ?]]]]]].
pose proof (sort_perm t' ldiff). set (ldiff':=sort t' ldiff). fold ldiff' in H26.
assert (H23': Permutation (lsame++ldiff') (EList t')). {
  apply (Permutation_trans (l':=lsame++ldiff)). apply Permutation_app_head. apply Permutation_sym; auto. apply H23.
}
assert (Hpreserve_msf: preserve_elabel msf g). apply Hmsf.
assert (Hpreserve_t': preserve_elabel t' g). apply H20.
assert (forall e, In e ldiff' -> evalid t' e). {
  intros. rewrite <- EList_evalid. apply (Permutation_in (l:=lsame++ldiff')). apply H23'.
  apply in_or_app. right. auto.
}
assert (WeightedEdgeListGraph.sorted' t' ldiff'). { apply sorted_sorted'. unfold ldiff'. apply sort_sorted. }

(*apply induction to obtain lmsf*)
assert (exists lmsf, Zlength ldiff' = Zlength lmsf /\ Permutation (lmsf++lsame) (EList msf) /\
      (forall i, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff'))).
  apply (kruskal_minimal_induction ldiff' lsame g t' msf); auto.
  apply (Permutation_trans (l':=lsame++ldiff')). apply Permutation_app_comm. auto.
  intros. apply H25. apply (Permutation_in (l:=ldiff')). apply Permutation_sym; auto. auto.
  { intros.
    assert (He: evalid t' e). apply H27; auto.
    assert (exists j : Z, 0 <= j < Zlength sorted /\ Znth j sorted = wedge_to_cdata (edge_to_wedge t' e)).
    apply (In_Znth_iff sorted (wedge_to_cdata (edge_to_wedge t' e))).
    apply (Permutation_in (l:=(map wedge_to_cdata (graph_to_wedgelist g)) )). auto.
    apply in_map. replace (edge_to_wedge t' e) with (edge_to_wedge g e).
    unfold graph_to_wedgelist. apply in_map. apply EList_evalid. apply H20. auto.
    unfold edge_to_wedge. replace (elabel g e) with (elabel t' e); auto.
    destruct H30 as [j [? ?]].
    assert (~ In (Znth j sorted) (map wedge_to_cdata msflist)). {
      (*this should be cleaned up*)
      rewrite H31. unfold not; intros. apply (H25 e). apply (Permutation_in (l:=ldiff')). apply Permutation_sym; auto. auto.
      apply list_in_map_inv in H32. destruct H32. destruct H32.
      apply (Permutation_in (l':=graph_to_wedgelist msf)) in H33. 2: auto.
      apply list_in_map_inv in H33. destruct H33 as [e' [? ?]]. subst x.
      unfold edge_to_wedge in H32; simpl in H32.
      replace (elabel t' e) with (elabel g e) in H32. 2: symmetry; apply Hpreserve_t'; auto.
      assert (He': evalid msf e'). rewrite <- EList_evalid; apply H34.
      replace (elabel (FiniteWEdgeListGraph_WEdgeListGraph msf) e') with (elabel g e') in H32. 2: symmetry; apply Hpreserve_msf; auto.
      assert (vvalid t' (fst e) /\ vvalid t' (snd e)).
      rewrite (sound_src t'); auto. rewrite (sound_dst t'); auto. apply (sound_strong_evalid); auto.
      destruct H33. apply Hsound_t' in H33. apply Hsound_t' in H35.
      assert (vvalid msf (fst e') /\ vvalid msf (snd e')).
      rewrite (sound_src msf); auto. rewrite (sound_dst msf); auto. apply (sound_strong_evalid); auto.
      destruct H36. apply H9 in H36. apply H9 in H37.
      unfold wedge_to_cdata in H32. inversion H32. clear H32.
      do 2 rewrite Int.Z_mod_modulus_eq in H40, H41.
      set (k:=Int.max_signed) in *; compute in k; subst k.
      set (k:=Int.modulus) in *; compute in k; subst k.
      rewrite Z.mod_small in H40, H41 by lia. rewrite Z.mod_small in H40, H41 by lia.
      rewrite (surjective_pairing e). rewrite H40; rewrite H41. rewrite <- (surjective_pairing e'). auto.
    }
    apply H17 in H32. 2: lia. destruct H32 as [p [? [l [? ?]]]].
    rewrite H31 in H32; simpl in H32.
    apply sound_strong_evalid in He; auto.
    rewrite Int.signed_repr in H32. rewrite Int.signed_repr in H32.
    2: { rewrite (sound_dst t'); auto.
      split. apply (Z.le_trans _ 0 _). apply Z.lt_le_incl. apply Int.min_signed_neg.
      apply Hsound_t'. apply He. apply Z.lt_le_incl. apply Hsound_t'. apply He.
    }
    2: { rewrite (sound_src t'); auto.
      split. apply (Z.le_trans _ 0 _). apply Z.lt_le_incl. apply Int.min_signed_neg.
      apply Hsound_t'. apply He. apply Z.lt_le_incl. apply Hsound_t'. apply He.
    }
    assert (forall e' : EType, In e' l -> elabel g e' <= elabel g e). {
      intros. assert (evalid g e'). apply Hmsf. apply (fits_upath_evalid msf p l); auto.
      apply H34 in H35. apply In_Znth_iff in H35. destruct H35 as [i [? ?]].
      rewrite Zlength_sublist in H35 by lia. rewrite Z.sub_0_r in H35.
      rewrite Znth_sublist in H37 by lia. rewrite Z.add_0_r in H37 by lia.
      assert (wedge_le (Znth i sorted) (Znth j sorted)). apply H6; lia.
      rewrite H37 in H38; rewrite H31 in H38. simpl in H38.
      rewrite Int.signed_repr in H38. rewrite Int.signed_repr in H38.
      assert (elabel t' e = elabel g e). apply H20. auto. lia.
      apply Hsound_t'. auto. apply H. auto.
    }
    (*now that we have those properties, simplify the path*)
    pose proof (upath_simplifiable_edges msf p l (fst e) (snd e) H32 H33).
    destruct H36 as [p' [l' [? [? [? [? ?]]]]]]. exists p'; exists l'.
    split. rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
    split. apply H37. split. auto.
    intros. apply H35. apply H40. auto.
  }
  { intros. assert (WeightedEdgeListGraph.sorted' t' ldiff'). apply sorted_sorted'. unfold ldiff'.
    apply sort_sorted. unfold sorted' in H29.
    replace (elabel g (Znth i ldiff')) with (elabel t' (Znth i ldiff')).
    replace (elabel g (Znth j ldiff')) with (elabel t' (Znth j ldiff')). apply H31; lia.
    rewrite Hpreserve_t'; auto. apply H27. apply Znth_In. lia.
    rewrite Hpreserve_t'; auto. apply H27. apply Znth_In. lia.
  }
(*and we get the list of edges*)
destruct H29 as [lmsf [? [? ?]]].
rewrite (sum_LE_equiv t' (ldiff'++lsame)). 2: { apply Permutation_sym. apply (Permutation_trans (l':=lsame++ldiff')); auto. apply Permutation_app_comm. }
rewrite (sum_LE_equiv msf (lmsf++lsame)). 2: { apply Permutation_sym. apply (Permutation_trans (l':=lmsf++lsame)); auto. }
do 2 rewrite map_app. do 2 rewrite fold_left_app.
replace (map (elabel (FiniteWEdgeListGraph_WEdgeListGraph msf)) lsame) with
        (map (elabel (FiniteWEdgeListGraph_WEdgeListGraph g)) lsame).
replace (map (elabel (FiniteWEdgeListGraph_WEdgeListGraph t')) lsame) with
        (map (elabel (FiniteWEdgeListGraph_WEdgeListGraph g)) lsame).
apply fold_left_Zadd_diff_accum.
apply fold_left_Zadd_comp. do 2 rewrite Zlength_map. auto.
intros. rewrite Zlength_map in H32. rewrite Znth_map by auto.
rewrite Znth_map by lia.
rewrite Hpreserve_msf. rewrite Hpreserve_t'. apply H31; lia.
apply H27. apply Znth_In. lia.
rewrite <- EList_evalid. apply (Permutation_in (l:=lmsf++lsame)). apply H30.
apply in_or_app. left. apply Znth_In; lia.
apply map_local_functions_eq. intros. symmetry. apply Hpreserve_t'.
rewrite <-  EList_evalid. apply (Permutation_in (l:=lsame++ldiff')). apply H23'. apply in_or_app. left; auto.
apply map_local_functions_eq. intros. symmetry. apply Hpreserve_msf.
rewrite <-  EList_evalid. apply (Permutation_in (l:=lmsf++lsame)). apply H30. apply in_or_app. right; auto.
Qed.