Require Import VST.floyd.proofauto.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
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
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
Require Import RamifyCoq.kruskal.kruskal_uf_specs.
(*spanning tree definition*)
Require Import RamifyCoq.kruskal.undirected_graph.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [makeSet_spec; find_spec; union_spec;
      mallocK_spec; free_spec; fill_edge_spec; init_empty_graph_spec; sort_edges_spec; kruskal_spec
  ]).

Local Open Scope Z_scope.

Lemma Permutation_Zlength:
  forall (A : Type) (l l' : list A),
    Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros.
  rewrite Zlength_length; [| apply Zlength_nonneg].
  rewrite Zlength_correct, Nat2Z.id.
  apply Permutation_length; trivial.
Qed.

Lemma NoDup_incl_Zlength:
  forall (A: Type) (l l' : list A),
  NoDup l -> incl l l' -> Zlength l <= Zlength l'.
Proof.
intros. repeat rewrite Zlength_correct. apply Nat2Z.inj_le. apply NoDup_incl_length; auto.
Qed.

Lemma partial_graph_EList:
  forall (g g': FiniteWEdgeListGraph), is_partial_graph g g' -> incl (EList g) (EList g').
Proof.
unfold is_partial_graph; unfold incl; intros. rewrite EList_evalid; rewrite EList_evalid in H0.
destruct H; destruct H1. apply H1. apply H0.
Qed.

Corollary partial_graph_numE:
  forall (g g': FiniteWEdgeListGraph), is_partial_graph g g' -> numE g <= numE g'.
Proof.
unfold numE; intros. apply NoDup_incl_Zlength.
apply NoDup_EList. apply partial_graph_EList; auto.
Qed.

Lemma Forall_permutation: forall {A: Type} (al bl: list A) f, Forall f al -> Permutation al bl -> Forall f bl.
Proof.
intros. rewrite Forall_forall in *; intros.
apply H. apply (Permutation_in (l:=bl) (l':=al) x). apply Permutation_sym. apply H0. apply H1.
Qed.

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

(* cleaner notation for uf_root being same *)
Definition ufroot_same (g: UFGraph) u v :=
  exists r,
    uf_root g u r /\ uf_root g v r.

Lemma ufroot_same_refl:
  forall (g : UFGraph) u,
    vvalid g u ->
    ufroot_same g u u.
Proof.
  intros.
  assert (EnumEnsembles.EnumCovered Z (evalid g)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  pose proof (uf_root_always_exists g (liGraph g) u X H).
  destruct H0. exists x. split; trivial.
Qed.

Lemma ufroot_same_symm:
  forall (g : UFGraph) u v,
    ufroot_same g u v <-> ufroot_same g v u.
Proof.
  intros. unfold ufroot_same.
  split; intros; destruct H as [r [? ?]];
    exists r; split; trivial.
Qed.

Lemma ufroot_same_trans:
  forall (g : UFGraph) u v w,
    ufroot_same g u v ->
    ufroot_same g v w ->
    ufroot_same g u w.
Proof.
  intros. unfold ufroot_same in *.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  pose proof (uf_root_unique _ _ _ _ _ H1 H0).
  subst x0. exists x; split; trivial.
Qed.

Lemma reachable_ufroot_same:
  forall (g: UFGraph) u v,
    reachable g u v ->
    ufroot_same g u v. 
Proof.
  intros.
  assert (EnumEnsembles.EnumCovered Z (evalid g)). {
    apply EnumEnsembles.Enumerable_is_EnumCovered, finiteE.
  }
  pose proof (reachable_foot_valid _ _ _ H).
  pose proof (reachable_head_valid _ _ _ H).
  pose proof (uf_root_always_exists g (liGraph g) u X H1).
  pose proof (uf_root_always_exists g (liGraph g) v X H0).
  destruct H2 as [r_u ?].
  destruct H3 as [r_v ?].
  pose proof (uf_root_reachable _ _ _ _ H H3).
  exists r_v. split; trivial.
Qed.

Lemma adjacent_reachable:
  forall (g: UFGraph) u v,
    adjacent g u v ->
    (reachable g u v \/ reachable g v u).
Proof.
  intros.
  unfold adjacent, adj_edge in H.
  destruct H as [e [? [[? ?] | [? ?]]]];
    [left | right];
    unfold reachable, reachable_by, reachable_by_path.
  - exists (u, [e]); split.
    + split; trivial.
    + unfold good_path. split; simpl.
      * split; trivial; lia.
      * unfold path_prop. split; trivial.
        rewrite Forall_forall; intros; split; trivial.
  - exists (v, [e]); split.
    + split; trivial.
    + unfold good_path. split; simpl.
      * split; trivial; lia.
      * unfold path_prop. split; trivial.
        rewrite Forall_forall; intros; split; trivial.
Qed.

Lemma adjacent_ufroot_same:
  forall (g : UFGraph) u v,
    adjacent g u v ->
    ufroot_same g u v.
Proof.
  intros.
  apply adjacent_reachable in H.
  destruct H.
  - apply reachable_ufroot_same; trivial.
  - apply ufroot_same_symm, reachable_ufroot_same; trivial.
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
      subst. apply ufroot_same_refl.
      simpl in H; trivial.
    + destruct H.
      rewrite last_error_cons in H1.
      2: unfold not; inversion 1.
      specialize (IHp H0 H1).
      intros.
      simpl in H2. inversion H2; subst a; clear H2.
      apply adjacent_ufroot_same in H.
      apply (ufroot_same_trans _ _ _ _ H); trivial.
      apply IHp. trivial.
Qed.

Lemma connected_ufroot_same_iff:
  forall (g: UFGraph) u v,
    connected g u v <-> ufroot_same g u v. 
Proof.
  intros. split; intros.
  apply connected_ufroot_same; trivial.
  apply ufroot_same_connected; trivial.
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

Lemma uf_equiv_ufroot_same:
  forall (g1 g2: UFGraph) u v,
    uf_equiv g1 g2 ->
    ufroot_same g1 u v <-> ufroot_same g2 u v.
Proof.
(*Probably can be independent of the connectedness
Using for now for convenience, given connected gives vvalid*)
intros. do 2 rewrite <- connected_ufroot_same_iff. apply uf_equiv_connected. auto.
Qed.

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
  pose proof (ufroot_same_refl g u H).
  pose proof (ufroot_same_refl g v H0).
  assert (H3 := H1).
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
      apply ufroot_same_refl; trivial.
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
      apply ufroot_same_refl; trivial.
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
        apply H12, ufroot_same_refl; trivial.  
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
    apply ufroot_same_refl.
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
    apply ufroot_same_refl; trivial.
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
    apply ufroot_same_refl; trivial.
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

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

(*************************************************************)
(****I put these in WeightedEdgeListGraph originally, universe inconsistency again
Not sure who the culprit is. simple_upath?
*)

Lemma connected_dec:
forall (g: FiniteWEdgeListGraph) u v, connected g u v \/ ~ connected g u v.
Proof. intros. tauto. Qed.

Lemma adde_bridge_split1:
forall (g: FiniteWEdgeListGraph) u v w p a b ,
connected g u a ->
connected g v b ->
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
(exists l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p /\ In (u,v) l) ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a u /\
    connected_by_path g p2 v b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l ?]. destruct H3.
destruct l. simpl in *. contradiction.
destruct p. simpl in H3. contradiction.
assert (a0 = a). destruct H4. destruct H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite FiniteWEdgeListGraph_adde_src1 in H6. rewrite FiniteWEdgeListGraph_adde_dst1 in H6.
destruct H6; destruct H6. subst a; subst v0. exists (u::nil); exists (v::p).
split. auto. split. split. apply (adde_unaffected g (u,v) w (u::nil)).
simpl. destruct H3. destruct H6. simpl in H6. unfold graph_gen.updateEdgeFunc in H6; simpl.
unfold EquivDec.equiv_dec in H6; destruct E_EqDec. auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
exists nil. simpl; auto.
simpl; split; auto.
assert (~ In (u,v) l). unfold not; intros.
assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)).
auto. auto. rewrite FiniteWEdgeListGraph_adde_src1. auto.
destruct H2. apply NoDup_cons_2 in H8. contradiction.
split. apply (adde_unaffected g (u,v) w). apply H4. exists l. split.
apply (adde_fits_upath' g (u,v) w); auto. auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. auto.
unfold not; intros. inversion H9.
subst a. contradiction.
(*otherwise*)
assert (e <> (u,v)). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite FiniteWEdgeListGraph_adde_src1 in H7; rewrite FiniteWEdgeListGraph_adde_dst1 in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)). auto. auto.
  rewrite FiniteWEdgeListGraph_adde_src1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
  assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)). auto. auto.
  rewrite FiniteWEdgeListGraph_adde_dst1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3.
  destruct H3. destruct H3. simpl in H3. unfold graph_gen.addValidFunc in H3. destruct H3. 2: contradiction.
  simpl in H9; unfold graph_gen.updateEdgeFunc in H9; unfold EquivDec.equiv_dec in H9.
  simpl in H8; unfold graph_gen.updateEdgeFunc in H8; unfold EquivDec.equiv_dec in H8; destruct E_EqDec.
  unfold equiv in e0. symmetry in e0; contradiction.
  split. split; auto. auto.
assert (exists p1 p2 : list VType,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 u /\
        connected_by_path g p2 v b). apply IHp; auto.
apply (connected_trans g u a v0). auto.
apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 ?]]. destruct H7. destruct H8.
exists (a::p1). exists p2. split. rewrite H7. simpl. auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

(*this is stupid*)
Lemma adde_bridge_split2:
forall (g: FiniteWEdgeListGraph) u v w p a b ,
connected g v a ->
connected g u b ->
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
(exists l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p /\ In (u,v) l) ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a v /\
    connected_by_path g p2 u b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l ?]. destruct H3.
destruct l. simpl in *. contradiction.
destruct p. simpl in H3. contradiction.
assert (a0 = a). destruct H4. destruct H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite FiniteWEdgeListGraph_adde_src1 in H6. rewrite FiniteWEdgeListGraph_adde_dst1 in H6.
destruct H6; destruct H6; subst a; subst v0. apply connected_symm in H. contradiction.
exists (v::nil); exists (u::p).
split. auto. split. split. apply (adde_unaffected g (u,v) w (v::nil)).
simpl. destruct H3. destruct H6. simpl in H7. unfold graph_gen.updateEdgeFunc in H7; simpl.
unfold EquivDec.equiv_dec in H7; destruct E_EqDec. auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
exists nil. simpl; auto.
simpl; split; auto.
assert (~ In (u,v) l). unfold not; intros.
assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)).
auto. auto. rewrite FiniteWEdgeListGraph_adde_dst1. auto.
destruct H2. apply NoDup_cons_2 in H8. contradiction.
split. apply (adde_unaffected g (u,v) w). apply H4. exists l. split.
apply (adde_fits_upath' g (u,v) w); auto. auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. auto.
unfold not; intros. inversion H9.
(*otherwise*)
assert (e <> (u,v)). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite FiniteWEdgeListGraph_adde_src1 in H7; rewrite FiniteWEdgeListGraph_adde_dst1 in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)). auto. auto.
  rewrite FiniteWEdgeListGraph_adde_src1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
  assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)). auto. auto.
  rewrite FiniteWEdgeListGraph_adde_dst1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3.
  destruct H3. destruct H3. simpl in H3. unfold graph_gen.addValidFunc in H3. destruct H3. 2: contradiction.
  simpl in H9; unfold graph_gen.updateEdgeFunc in H9; unfold EquivDec.equiv_dec in H9.
  simpl in H8; unfold graph_gen.updateEdgeFunc in H8; unfold EquivDec.equiv_dec in H8; destruct E_EqDec.
  unfold equiv in e0. symmetry in e0; contradiction.
  split. split; auto. auto.
assert (exists p1 p2 : list VType,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 v /\
        connected_by_path g p2 u b). apply IHp; auto.
apply (connected_trans g v a v0). auto. apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
split. auto.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 ?]]. destruct H7. destruct H8.
exists (a::p1). exists p2. split. rewrite H7. simpl. auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

Lemma cross_bridge_implies_endpoints:
forall (g: FiniteWEdgeListGraph) u v w p a b,
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b ->
(exists l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p /\ In (u,v) l) ->
((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
Proof.
induction p; intros. destruct H1. destruct H3. inversion H3.
assert (a = a0). destruct H1. destruct H3. inversion H3. auto. subst a0. (*that was weird*)
destruct H2 as [l ?]. destruct H2. destruct l. contradiction.
destruct p. contradiction.
(*so we show that v0 is connected to one of them. By trans, a0 is connected to one*)
(*case where (u,v) is first in list. Then we show a = u or a = v*)
destruct H3. subst e.
destruct H2. destruct H2. destruct H2.
rewrite FiniteWEdgeListGraph_adde_src1 in *. rewrite FiniteWEdgeListGraph_adde_dst1 in *.
destruct H5. apply FiniteWEdgeListGraph_adde_vvalid in H5. apply FiniteWEdgeListGraph_adde_vvalid in H6.
assert (~ In (u,v) l).  unfold not; intros.
  destruct H4; destruct H4; subst a; subst v0; destruct H0.
  assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)).
  apply H3. auto.
  rewrite FiniteWEdgeListGraph_adde_src1. auto. apply NoDup_cons_2 in H4. contradiction.
  assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)).
  apply H3. auto.
  rewrite FiniteWEdgeListGraph_adde_dst1. auto. apply NoDup_cons_2 in H4. contradiction.
destruct H4; destruct H4; subst a; subst v0.
left. split. apply connected_refl. auto. exists (v::p).
split. apply (adde_unaffected g (u,v) w). apply H0.
exists l. split. apply (adde_fits_upath' g (u,v) w). apply H3. auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
right. split. apply connected_refl. auto. exists (u::p).
split. apply (adde_unaffected g (u,v) w). apply H0.
exists l. split. apply (adde_fits_upath' g (u,v) w). apply H3. auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
(*Case where (u-v) is somewhere in the middle*)
assert (Hav0: connected g a v0). {
  apply adjacent_connected. destruct H2. destruct H2.
  assert (e <> (u,v)). unfold not; intros. subst e.
    rewrite FiniteWEdgeListGraph_adde_src1 in *; rewrite FiniteWEdgeListGraph_adde_dst1 in *.
    destruct H5; destruct H5; subst a; subst v0.
    assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
    apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)). auto. auto.
    rewrite FiniteWEdgeListGraph_adde_src1. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
    assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
    apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)). auto. auto.
    rewrite FiniteWEdgeListGraph_adde_dst1. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
  exists e. destruct H2. simpl in *. unfold graph_gen.updateEdgeFunc in *. unfold EquivDec.equiv_dec in *.
  unfold graph_gen.addValidFunc in H2.
  split. split. destruct H2. auto. contradiction.
  destruct E_EqDec. unfold equiv in e0. symmetry in e0; contradiction. auto.
  destruct E_EqDec. unfold equiv in e0. symmetry in e0; contradiction. auto.
}
(*IHp on v0*)
assert (connected g v0 u /\ connected g v b \/ connected g v0 v /\ connected g u b).
apply IHp. auto. split. apply H0.
destruct H0. apply NoDup_cons_1 in H4. auto.
destruct H1. destruct H4. split. apply H0.
split. simpl; auto. rewrite last_error_cons in H5. auto.
unfold not; intros; inversion H6.
exists l. split. destruct H2. auto. auto.
destruct H4; destruct H4. left. split.
apply (connected_trans g a v0 u); auto. auto.
right. split.
apply (connected_trans g a v0 v); auto. auto.
Qed.

Lemma uforest_adde:
forall (g: FiniteWEdgeListGraph) u v w, uforest g -> ~ connected g u v ->
  uforest (FiniteWEdgeListGraph_adde g (u,v) w).
Proof.
unfold uforest; intros. rename u0 into a; rename v0 into b.
assert (exists l : list EType, fits_upath (FiniteWEdgeListGraph_adde g (u, v) w) l p1).
apply connected_exists_list_edges in H2; auto.
assert (exists l : list EType, fits_upath (FiniteWEdgeListGraph_adde g (u, v) w) l p2).
apply connected_exists_list_edges in H4; auto.
destruct H5 as [l1 ?]. destruct H6 as [l2 ?].
destruct (in_dec E_EqDec (u,v) l1); destruct (in_dec E_EqDec (u,v) l2).
+ (*In (u,v) l1, In (u,v) l2*)
(*   connected g a u /\ v b \/ (av bu)
...? p1 = p1_a++p1_b. p1_a connects a-u, p1_b connects v-b
     p2 = p2_a++p2_b. p2_a connects to u
So connected p1_a u a /\ connected p2_a u a, both are simple. By uforest g, both are same
*)
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p1); auto. exists l1; split; auto.
destruct H7; destruct H7.
(*case a-u and v-b*)
  apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a u /\
      connected_by_path g p1_b v b)).
  apply (adde_bridge_split1 g u v w p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a u /\
      connected_by_path g p2_b v b)).
  apply (adde_bridge_split1 g u v w p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  (*by H, we have p1_a = p2_a*)
  assert (p1_a = p2_a). apply (H a u).
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H v b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  (*thus, rewrite*)
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.
(*case a-v and u-b...*)
apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a v /\
      connected_by_path g p1_b u b)).
  apply (adde_bridge_split2 g u v w p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a v /\
      connected_by_path g p2_b u b)).
  apply (adde_bridge_split2 g u v w p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  (*by H, we have p1_a = p2_a*)
  assert (p1_a = p2_a). apply (H a v).
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H u b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  (*thus, rewrite*)
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.
+ (*In (u,v) l1, ~In (u,v) l2*)
(* Then p1 = p1_a++p1_b. p1_a connects a-u, p1_b connects v-b
Whereas p2 is valid in g, connected a b
p1_a does not contain u-v by simpleness, so it is unaffected and valid in g
Ditto p1_b
Thus, connected g u a, connected g v b, connected g a b. Thus, connected g u v. Contra
Repeat for a-v,b-u...
*)
apply adde_fits_upath' in H6; auto.
destruct H4. apply adde_unaffected in H4. 2: { exists l2. split; auto. }
assert (connected g a b). exists p2. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p1); auto. exists l1; split; auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.
+ (*~In (u,v) l1, In (u,v) l2*)
apply adde_fits_upath' in H5; auto.
destruct H2. apply adde_unaffected in H2. 2: { exists l1. split; auto. }
assert (connected g a b). exists p1. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p2); auto. exists l2; split; auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.
+ (*~In (u,v) l1, ~In (u,v) l2*)
(*then both p1 and p2 are valid in g*)
apply adde_fits_upath' in H5; auto. apply adde_fits_upath' in H6; auto.
destruct H2. apply adde_unaffected in H2.
destruct H4. apply adde_unaffected in H4.
apply (H a b).
split. apply H2. apply H1. split; auto.
split. apply H4. apply H3. split; auto.
exists l2. split; auto. exists l1. split; auto.
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
    rewrite <- (Permutation_Zlength (reptype t_struct_edge) (map wedge_to_cdata (graph_to_wedgelist g)) (map wedge_to_cdata glist) Hperm_glist).
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
      rewrite <- (Permutation_Zlength _ _ _ H5). apply HZlength_glist.
    } rewrite HZlength_glist. rewrite HZlength_sorted.
    (******************************THE BIG NASTY LOOP******************************) 
    forward_for_simple_bound
    (numE g)
    (EX i : Z,
     EX msf' : FiniteWEdgeListGraph,
     EX msflist: list (LE*EType),
     EX subsetsGraph' : UFGraph,                      
     PROP (forall v, vvalid msf' v <-> vvalid g v; (*which should give numV msf' = numV g*)
           numE msf' <= i;
           sound_weighted_edge_graph msf';
           is_partial_lgraph msf' g;
           uforest msf';
           Permutation msflist (graph_to_wedgelist msf');
           forall v, vvalid g v <-> vvalid subsetsGraph' v;
           forall e u v, adj_edge g e u v -> In (wedge_to_cdata (edge_to_wedge g e)) (sublist 0 i sorted) -> ufroot_same subsetsGraph' u v;
           forall u v, ufroot_same subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           (*weight lemmas...*)
           forall x, In x (map wedge_to_cdata msflist) -> exists j, 0 <= j < i /\ x = Znth j sorted;
           (*2. edges before i that WEREN't added, exists a upath made of edges before j
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
      * apply uforest_edgeless_WEdgeGraph.
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
    rewrite (Permutation_Zlength _ _ _  H13). unfold graph_to_wedgelist.
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
      assert (src_edge msf') by (apply H10). assert (dst_edge msf') by (apply H10).
      split. split. apply H22. rewrite H23, H24; simpl. split; apply H8; auto.
      rewrite H23; rewrite H24; simpl. left; auto.
    } contradiction.
  }
  forward_call (sh, subsetsGraph_uv, subsetsPtr, u, v).
  (*postcon*)
  Exists (FiniteWEdgeListGraph_adde msf' (u,v) w).
  Exists (msflist+::(w,(u,v))).
  Intros uv_union. Exists uv_union.
  (*before we entailer, preemptively fix up some of the SEPs*)
  replace (numV (FiniteWEdgeListGraph_adde msf' (u, v) w)) with (numV msf').
  2: { symmetry; apply FiniteWEdgeListGraph_adde_numV. }
  replace (numE (FiniteWEdgeListGraph_adde msf' (u, v) w)) with (numE msf' + 1).
  2: { symmetry; apply FiniteWEdgeListGraph_adde_numE. apply H_msf'_uv. }
  replace (Int.add (Int.repr (numE msf')) (Int.repr 1)) with (Int.repr (numE msf' + 1)).
  2: { symmetry; apply add_repr. }
  (*ok!*)
  entailer!. (*lalalalalag*)
  clear H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44.
  split3. 3: split3. 5: split3. 7: split3. (*8 props... my invariant sure grew unwieldy*)
    +++
    apply FiniteWEdgeListGraph_adde_sound. auto.
      simpl; apply H8; auto. simpl; apply H8; auto. apply H. auto.
    +++
    split3. split3.
      intros. apply H8. apply FiniteWEdgeListGraph_adde_vvalid in H23. apply H23.
      intros. simpl in H23. unfold graph_gen.addValidFunc in H23. destruct H23. apply H11. apply H23. rewrite H23. auto.
      split. intros. simpl. unfold graph_gen.updateEdgeFunc. unfold EquivDec.equiv_dec.
        assert (src_edge g) by (apply H). assert (src_edge msf') by (apply H10).
        destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. rewrite H25; simpl; auto.
        rewrite H25; rewrite H26. auto.
      intros. simpl. unfold graph_gen.updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
        unfold Equivalence.equiv in e0; rewrite <- e0. assert (dst_edge g) by (apply H). rewrite H25; simpl; auto.
        assert (dst_edge g) by (apply H). assert (dst_edge msf') by (apply H10). rewrite H25; rewrite H26. auto.
      unfold preserve_vlabel; intros. simpl. destruct vlabel. destruct vlabel. auto.
      unfold preserve_elabel; intros. simpl. unfold graph_gen.update_elabel. simpl in H23. unfold graph_gen.addValidFunc in H23.
        unfold EquivDec.equiv_dec. destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. auto.
        destruct H23. apply H11. auto. unfold RelationClasses.complement, Equivalence.equiv in c. symmetry in H23. contradiction.
    +++
    apply uforest_adde; auto.
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
    apply FiniteWEdgeListGraph_adde_g2wedgelist_2.
    unfold not; intros; rewrite <- H25 in H24; contradiction. apply H24.
    simpl in H23. destruct H23. rewrite <- H23.
    apply FiniteWEdgeListGraph_adde_g2wedgelist_1. contradiction.
    destruct x as [w e].
    unfold graph_to_wedgelist in H23. apply list_in_map_inv in H23.
    destruct H23; destruct H23.
    apply EList_evalid in H24.
    unfold edge_to_wedge in H23; simpl in H23. unfold graph_gen.update_elabel in H23.
    unfold EquivDec.equiv_dec in H23. destruct (E_EqDec (u, v) x).
    unfold Equivalence.equiv in e0. rewrite H23. rewrite e0. apply in_or_app. right. left. auto.
    apply FiniteWEdgeListGraph_adde_evalid_or in H24. destruct H24.
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
    rewrite Hsrc_edge in H23, H25. rewrite Hdst_edge in H26, H25.
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
        apply H8; auto. apply H8; auto.
      rewrite <- H16 in H24, H26, H27.
      rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H24, H26, H27; auto.
      assert (~ ufroot_same subsetsGraph_uv b u). { unfold not; intros.
        apply ufroot_same_symm in H28. contradiction. }
      apply (uf_union_remains_disconnected1 _ uv_union u v) in H28; auto.
      2: auto. 2: { unfold not; intros. apply ufroot_same_symm in H29. contradiction. }
      apply (uf_union_preserves_connected _ uv_union u v) in H24; auto.
      apply ufroot_same_symm in H23.
      apply (ufroot_same_trans uv_union b a u) in H23; auto. contradiction.
    (*a not connected to u*)
    (*destruct connected msf' a v, repeat the above...*)
    destruct (connected_dec msf' a v).
      destruct (connected_dec msf' u b). apply adde_connected_through_bridge2; auto.
        apply H8; auto. apply H8; auto.
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
        apply (ufroot_same_trans uv_union b a v) in H23; auto. contradiction.
      destruct (connected_dec msf' u b). apply H16 in H26.
        apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H26; auto.
        apply (uf_union_preserves_connected _ uv_union u v) in H26; auto.
        apply ufroot_same_symm in H26.
        apply (ufroot_same_trans uv_union a b u H23) in H26.
        (*However, ~ connected msf' a u -> ... -> ~ ufroot_same uv_union, contradiction*)
        assert (~ ufroot_same uv_union a u). {
          rewrite <- H16 in H24, H25. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H24, H25; auto.
          apply (uf_union_remains_disconnected1 subsetsGraph_uv uv_union u v a); auto. }
        contradiction.
        destruct (connected_dec msf' v b). apply H16 in H27. apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H27; auto.
          apply (uf_union_preserves_connected _ uv_union u v) in H27; auto. apply ufroot_same_symm in H27.
          apply (ufroot_same_trans uv_union a b v H23) in H27.
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
      apply (cross_bridge_implies_endpoints msf' u v (elabel g (u,v)) p); auto.
      exists l. split; auto.
      destruct H25; destruct H25;
        rewrite <- H16 in H25, H26;
        rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H25, H26; auto;
        apply (uf_union_preserves_connected subsetsGraph_uv uv_union u v) in H25; auto;
        apply (uf_union_preserves_connected subsetsGraph_uv uv_union u v) in H26; auto.
        assert (ufroot_same uv_union u v).
          apply (uf_union_connected subsetsGraph_uv uv_union u v); auto.
        apply (ufroot_same_trans uv_union u v b H27) in H26.
        apply (ufroot_same_trans uv_union a u b); auto.
        assert (ufroot_same uv_union u v).
          apply (uf_union_connected subsetsGraph_uv uv_union u v); auto.
        apply ufroot_same_symm in H27.
        apply (ufroot_same_trans uv_union v u b H27) in H26.
        apply (ufroot_same_trans uv_union a v b); auto.
    assert (connected msf' a b). exists p. destruct H23. split. apply (adde_unaffected msf' (u,v) (elabel g (u,v))).
    apply H23. exists l. split. apply (adde_fits_upath' msf' (u,v) (elabel g (u,v))). auto. auto. auto.
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
    rewrite (Hsrc_edge e) in H22, H20. rewrite Hdst_edge in H23, H20.
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
  assert (connected msf' u v).
   apply H16. exists v_root. split; auto.
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
        apply ufroot_same_refl. apply H13. auto.
        destruct H18. destruct H18. destruct H19. inversion H19; subst a.
        apply (ufroot_same_trans subsetsGraph' u v0 v).
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
    } clear H18 H19.
    forward_call (sh, subsetsPtr, subsetsGraph').
    (* In hindsight, this wouldn't be needed with better definitions. But let's just soldier on
       Don't put this up on top, I worry about the effect of VST attempting to yank a value out
    *)
    apply (Permutation_trans Hperm_glist) in H5.
    assert (Permutation (graph_to_wedgelist g) (map cdata_to_wedge sorted)). {
      rewrite <- (w2c2w_map (graph_to_wedgelist g)).
      2: { intros. apply (sound_g2wedgelist_repable g); auto. }
      apply Permutation_map. auto.
    } set (lsorted:=map cdata_to_wedge sorted).
    assert (map wedge_to_cdata lsorted = sorted). apply (c2w2c_map). auto.
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
    (*minimum spanning tree*)
    split. split. split3. split3. apply H10. auto. unfold spanning. auto. apply H10. apply H10.
    intros. apply sound_strong_evalid; auto.
    (*minimum...*)

Abort.
