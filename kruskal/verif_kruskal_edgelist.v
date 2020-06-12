Require Import VST.floyd.proofauto.
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
(*Require Import RamifyCoq.sample_mark.specs_unionfind_arr.*)
(*edgelist*)
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
Require Import RamifyCoq.kruskal.kruskal_uf_specs.
(*spanning tree definition*)
Require Import RamifyCoq.kruskal.mst.
Require Import RamifyCoq.kruskal.undirected_graph.
(*Require Import RamifyCoq.graph.spanning_tree.*)

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

Lemma connected_exists_path:
  forall (g : UFGraph) u v,
    connected g u v <->
    exists p, 
      valid_upath g p /\
      hd_error p = Some u /\ last_error p = Some v.
Proof.
  intros. split; intros.
  - unfold connected, connected_by, connected_by_path in H.
    destruct H as [p [[? ?] [? ?]]].
    exists p; split3; trivial.
  - unfold connected, connected_by, connected_by_path.
    destruct H as [p [? [? ?]]].
    exists p.
    unfold good_upath.
    split3; trivial.
    split; trivial.
    unfold upath_prop.
    rewrite Forall_forall; intros; trivial.
Qed.

Lemma connected_refl:
  forall g u, vvalid g u -> connected g u u.
Proof.
  intros. exists [u].
  unfold connected_by_path; split3; trivial.
  unfold good_upath; split; trivial.
  unfold upath_prop. rewrite Forall_forall.
  intros; trivial.
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
Definition ufroot_same g u v :=
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
  forall g u v,
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

Lemma uf_root_unique':
  forall (g: UFGraph) x r1 r2,
    uf_root g x r1 ->
    uf_root g x r2 ->
    r1 = r2.
Proof.
  intros. apply (uf_root_unique _ (liGraph g) x); trivial.
Qed.

Lemma uf_union_vvalid:
forall g g' u v, uf_union g u v g' -> forall x, vvalid g x <-> vvalid g' x.
Proof.
Admitted.

Lemma uf_union_preserves_connected:
forall g g' u v, uf_union g u v g' -> (forall a b, connected g a b -> connected g' a b). (*converse is not true*)
Proof.
Admitted.

Lemma uf_union_connected:
forall g g' u v, uf_union g u v g' -> connected g' u v.
Proof.
Admitted.

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

(*this needs to be placed somewhere else*)
Definition is_partial_lgraph (g1 g2: FiniteWEdgeListGraph) :=
  is_partial_graph g1 g2 /\
  (forall v, vvalid g1 v -> vlabel g1 v = vlabel g2 v) /\
  (forall e, evalid g1 e -> elabel g1 e = elabel g2 e).

Lemma is_partial_lgraph_refl: forall g,
    is_partial_lgraph g g.
Proof. intros. split3; auto. apply is_partial_graph_refl. Qed.

Lemma is_partial_lgraph_trans: forall g1 g2 g3,
    is_partial_lgraph g1 g2 -> is_partial_lgraph g2 g3 -> is_partial_lgraph g1 g3.
Proof.
  intros. split3. apply (is_partial_graph_trans g1 g2 g3). apply H. apply H0.
  intros. destruct H. destruct H2. rewrite H2. destruct H0. destruct H4. rewrite H4. auto.
  apply H. auto. auto.
  intros. destruct H. destruct H2. rewrite H3. destruct H0. destruct H4. rewrite H5. auto.
  apply H. auto. auto.
Qed.

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
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr) = data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges (MAX_EDGES)) (pointer_val_val eptr)). {
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
           forall u v, (exists wedge, In wedge msflist /\ (fst (snd wedge) = u \/ snd (snd wedge) = u))
                    -> (exists wedge, In wedge msflist /\ (fst (snd wedge) = v \/ snd (snd wedge) = v))
                    -> (connected subsetsGraph' u v <-> connected g u v);
           (*forall u v, connected subsetsGraph' u v -> connected g u v; *)
           forall u v, connected subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           (*weight lemmas...*)
           forall x, In x (map wedge_to_cdata msflist) -> exists j, 0 <= j < i /\ x = Znth j sorted;
           (*2. edges before i that WEREN't added, exists a upath made of edges before j
                consequently these edges have leq weight than Znth j sorted
            *)
           forall j, 0 <= j < i -> ~ In (Znth j sorted) (map wedge_to_cdata msflist) ->
            (exists p: upath, c_connected_by_path msf' (fun _ => True) p (fst (snd (Znth j sorted))) (snd (snd (Znth j sorted))) /\
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
      split3; [| | split3]. 5: split.
      * apply edgeless_WEdgeGraph_sound.
          split. lia. assert ((Int.max_signed/8) < Int.max_signed). apply Z.div_lt.
          set (k:=Int.max_signed); compute in k; subst k. lia. lia. lia.
      * repeat split; intros.
        rewrite <- edgeless_WEdgeGraph_vvalid in H25; apply H0; auto.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
        simpl. destruct vlabel. auto.
        apply edgeless_WEdgeGraph_evalid in H25; contradiction.
      * (*maybe I should do this in WeightedEdgeListGraph*)
        unfold uforest; unfold acyclic_ugraph; unfold simple_ucycle; unfold ucycle. intros.
        destruct H25; destruct H25.
          destruct p. contradiction.
          destruct p. contradiction.
        unfold not; intros. destruct H28. unfold adjacent in H28; unfold adj_edge in H28.
        destruct H28. destruct H28. destruct H28.
        apply edgeless_WEdgeGraph_evalid in H28; contradiction.
      * intros; split; intros. apply H0 in H25. apply makeSet_vvalid. rewrite Z2Nat.id by lia. lia.
          apply H0. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. lia.
      (*
      * unfold connected; unfold connected_by; unfold connected_by_path; unfold good_upath.
        unfold valid_upath; intros. destruct H25 as [p ?]. destruct H25. destruct H25.
        destruct H26. destruct p eqn:Hp; simpl in H25; simpl in H26; inversion H26.
        rewrite H30 in *. destruct u0.
        (*single vertex in upath. Thus u=v, trivially connected*)
        simpl in H28; inversion H28. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
        split. simpl. apply H0. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. apply H25.
        unfold upath_prop; rewrite Forall_forall. intros; auto.
        (*case p = u::z0::u0.
          Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...*)
        destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25. destruct H32.
        rewrite makeSet_vvalid in H33. rewrite Z2Nat.id in H33 by lia.
        destruct H31; destruct H31;
          rewrite H34 in H33; rewrite makeSet_dst in H34; rewrite <- H34 in H33; lia.
      *)
      * intros. destruct H25; destruct H25. contradiction.
      * unfold connected; unfold connected_by; unfold connected_by_path; unfold good_upath; unfold valid_upath.
        intros; split; intros.
        { (*Same thing as above, show that it can't be connected*)
          destruct H25 as [p ?]. destruct H25. destruct H25. destruct H26.
          destruct p eqn:Hp; simpl in H25; simpl in H26; inversion H26.
          rewrite H30 in *. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H28; inversion H28. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
          split. simpl. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. apply H25.
          unfold upath_prop; rewrite Forall_forall. intros; auto.
          (*case p = u::z0::u0.
            Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...*)
          destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25. destruct H32.
          rewrite makeSet_vvalid in H33. rewrite Z2Nat.id in H33 by lia.
          destruct H31; destruct H31;
            rewrite H34 in H33; rewrite makeSet_dst in H34; rewrite <- H34 in H33; lia.
        }
        { (*more or less same deal...*)
          destruct H25 as [p ?]. destruct H25. destruct H25. destruct H26.
          destruct p eqn:Hp; simpl in H26; inversion H26.
          rewrite H30 in *. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H28; inversion H28. exists p. rewrite Hp. simpl; split; auto.
          (*case p = u::z0::u0.
            Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...
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
  assert (Htmp: vvalid g u /\ vvalid g v). { apply H. auto. }
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
    (*now, fill in the edge*)
    forward_call (sh, a, fst (Znth i sorted), fst (snd (Znth i sorted)), snd (snd (Znth i sorted)), (Vundef, (Vundef, Vundef))).
    replace (fst (Znth i sorted), (fst (snd (Znth i sorted)), snd (snd (Znth i sorted)))) with (Znth i sorted).
    2: rewrite (surjective_pairing (Znth i sorted)); rewrite (surjective_pairing (snd (Znth i sorted))); auto.
    (*refold. UGLY*)
    unfold SEPx. simpl. rewrite sepcon_comm. repeat rewrite <- sepcon_assoc. repeat rewrite sepcon_emp. repeat rewrite sepcon_assoc.
    rewrite (sepcon_comm _ (data_at sh t_struct_edge (Znth i sorted) a)).
    (*rewrite <- (sepcon_assoc _ (data_at sh t_struct_edge (Znth i sorted) a) _).*)
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
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
                (pointer_val_val eptr)))))))%logic
    = fold_right_sepcon [
    whole_graph sh subsetsGraph_uv subsetsPtr;
    data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
    data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr);
    data_at sh t_wedgearray_graph (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
    data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
      (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr));
    data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
    data_at sh (tarray t_struct_edge MAX_EDGES) (map wedge_to_cdata msflist ++
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
                (pointer_val_val eptr)
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
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
                (pointer_val_val eptr)
    ]).
  replace (map wedge_to_cdata msflist ++
                 [Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))
  with (map wedge_to_cdata (msflist+::(w,(u,v))) ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1))).
  2: { rewrite Heq_i. rewrite map_app. rewrite <- app_assoc. reflexivity. }
  (*done with the SEP manipulation*)
  forward. forward.
  (*before we union, show that u-v doesn't exist in msf'*)

  assert (Hconnected_uv: ~ connected subsetsGraph' u v). {
    unfold not; intros.
    apply connected_ufroot_same_iff in H25. destruct H25. destruct H25.
    assert (uf_root subsetsGraph' u u_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply H20.
    assert (uf_root subsetsGraph_u v v_root). apply (uf_equiv_root_the_same subsetsGraph_u subsetsGraph_uv). apply H21. apply H22.
    assert (uf_root subsetsGraph' v v_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply H28.
    assert (u_root = x). apply (uf_root_unique' subsetsGraph' u u_root x). apply H27. apply H25.
    assert (v_root = x). apply (uf_root_unique' subsetsGraph' v v_root x). apply H29. apply H26.
    rewrite H30 in H23; rewrite H31 in H23. contradiction.
  }

  assert(H_msf'_uv: ~ evalid msf' (u,v)). {
    (*we state that u and v are not connected in subsetsGraph'*)
    (*by invariant, it means they aren't connected in msf'*)
    rewrite H16 in Hconnected_uv.
    (*but presence of u-v means they are connected*)
    unfold not; intros.
    assert (connected msf' u v). {
      apply adjacent_connected. exists (u,v).
      assert (src_edge msf') by (apply H10). assert (dst_edge msf') by (apply H10).
      split. split. apply H25. split. rewrite H26; simpl. apply H8. auto. rewrite H27; simpl. apply H8. auto.
      rewrite H26; rewrite H27; simpl. left; split; auto.
    } contradiction.
  }
  forward_call (sh, subsetsGraph_uv, subsetsPtr, u, v).
  assert (Htmp: uf_equiv subsetsGraph' subsetsGraph_uv). {
     apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
   } destruct Htmp. do 2 rewrite <- H25.
  split; auto.

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
  split3. 3: split3. 5: split3. 7: split3. (*8 props... my invariant sure grew unwieldy*)
    +++
    apply FiniteWEdgeListGraph_adde_sound. auto.
      simpl; apply H8; auto. simpl; apply H8; auto. apply H. auto.
    +++
    split3. split3.
      intros. apply H8. apply FiniteWEdgeListGraph_adde_vvalid in H48. apply H48.
      intros. simpl in H48. unfold graph_gen.addValidFunc in H48. destruct H48. apply H11. apply H48. rewrite H48. auto.
      split. intros. simpl. unfold graph_gen.updateEdgeFunc. unfold EquivDec.equiv_dec.
        assert (src_edge g) by (apply H). assert (src_edge msf') by (apply H10).
        destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. rewrite H50; simpl; auto.
        rewrite H50; rewrite H51. auto.
      intros. simpl. unfold graph_gen.updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
        unfold Equivalence.equiv in e0; rewrite <- e0. assert (dst_edge g) by (apply H). rewrite H50; simpl; auto.
        assert (dst_edge g) by (apply H). assert (dst_edge msf') by (apply H10). rewrite H50; rewrite H51. auto.
      intros. simpl. destruct vlabel. destruct vlabel. auto.
      intros. simpl. unfold graph_gen.update_elabel. simpl in H48. unfold graph_gen.addValidFunc in H48.
        unfold EquivDec.equiv_dec. destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. auto.
        destruct H48. apply H11. auto. unfold RelationClasses.complement, Equivalence.equiv in c. symmetry in H48. contradiction.
    +++
    (*Prove this somewhere:
      if graph is uforest and u,v are unconnected, then adding (u,v) maintains uforest
      uforest -> simple_ucycle -> ~ valid_upath
      intros; unfold not; intros. since p is valid_upath, exists l: list E, ...
      assert (forall g e w, evalid adde g e w -> e<>(u,v) -> evalid g e).
      case In (u,v) l:
        then, u::v in p. split p into p1++[u::v]++p2
        ?
      case no:
        then every edge in l is in g, therefore connected g u v by p
    *)
    unfold uforest, acyclic_ugraph. unfold simple_ucycle. intros.
    admit.
    +++
    apply NoDup_Permutation. apply NoDup_app_inv.
    apply (Permutation_NoDup (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto. apply NoDup_g2wedgelist.
    apply NoDup_cons. auto. apply NoDup_nil.
    unfold not; intros. simpl in H49. destruct H49; try contradiction.
    apply (Permutation_in (l':=graph_to_wedgelist msf')) in H48.
    rewrite <- H49 in H48. apply g2wedgelist_evalid in H48. simpl in H48. contradiction.
    auto. apply NoDup_g2wedgelist.
    intros; split; intros. apply in_app_or in H48. destruct H48.
    apply (Permutation_in (l':=graph_to_wedgelist msf')) in H48. 2: auto.
    apply list_in_map_inv in H48. destruct H48; destruct H48. rewrite H48. apply EList_evalid in H49.
    apply FiniteWEdgeListGraph_adde_g2wedgelist_2.
    unfold not; intros; rewrite <- H50 in H49; contradiction. apply H49.
    simpl in H48. destruct H48. rewrite <- H48.
    apply FiniteWEdgeListGraph_adde_g2wedgelist_1. contradiction.
    destruct x as [w e].
    unfold graph_to_wedgelist in H48. apply list_in_map_inv in H48.
    destruct H48; destruct H48.
    apply EList_evalid in H49.
    unfold edge_to_wedge in H48; simpl in H48. unfold graph_gen.update_elabel in H48.
    unfold EquivDec.equiv_dec in H48. destruct (E_EqDec (u, v) x).
    unfold Equivalence.equiv in e0. rewrite H48. rewrite e0. apply in_or_app. right. left. auto.
    assert (Ha: forall (g: FiniteWEdgeListGraph) e w e', evalid (FiniteWEdgeListGraph_adde g e w) e' -> (evalid g e' \/ e' = e)). {
      (*I put this in WeightEdgeGraphList, but don't want to recompile*)
      unfold FiniteWEdgeListGraph_adde; simpl; unfold graph_gen.addValidFunc. intros. auto.
    }
    apply Ha in H49. destruct H49. clear Ha.
    apply in_or_app. left. apply (Permutation_in (l:=graph_to_wedgelist msf')).
    apply Permutation_sym; auto.
    replace (w,e) with (edge_to_wedge msf' e). apply in_map. apply EList_evalid. inversion H48. apply H49.
    unfold edge_to_wedge; simpl. inversion H48. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. rewrite H49 in c; contradiction.
    +++
    assert (uf_union_vvalid:
      forall g g' u v, uf_union g u v g' -> forall x, vvalid g x <-> vvalid g' x). admit.
    intros; split; intros.
    rewrite <- (uf_union_vvalid subsetsGraph_uv uv_union u v H25).
    destruct H21; rewrite <- H21. destruct H19; rewrite <- H19. apply H14; auto.
    apply H14. apply H19. apply H21. apply (uf_union_vvalid subsetsGraph_uv uv_union u v H25). auto.
    +++
    intros.
    (*destruct whether *)
    admit.
    +++
    admit.
    +++
    intros. rewrite map_app in H48. apply in_app_or in H48; destruct H48.
    apply H17 in H48. destruct H48; destruct H48. exists x0; split; [lia | auto].
    simpl in H48. destruct H48. exists i; split. lia. rewrite <- H48. symmetry; apply Heq_i.
    contradiction.
    +++
    intros.
    destruct (Z.lt_trichotomy j i).
    (*j<i*) 1: {
      assert (~ In (Znth j sorted) (map wedge_to_cdata msflist)). {
        unfold not; intros. assert (In (Znth j sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
        rewrite map_app. apply in_or_app. left. auto. contradiction. }
      apply H18 in H51. 2: lia. destruct H51 as [p ?]; destruct H51. destruct H52 as [l ?]; destruct H52.
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
      rewrite Heq_j in H51; simpl in H51.
      (*we''ll deal with the vvalid etc when we need it...*)
      split. unfold c_connected_by_path. unfold c_connected_by_path in H51.
      apply adde_connected2. auto. apply H51. exists l.
      split. apply adde_fits_upath. auto. apply H52. apply H53.
    }
    (*the rest are trivial*)
    destruct H50. subst j.
    assert (In (Znth i sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
      rewrite Heq_i. apply in_map. apply in_or_app. right. left; auto. contradiction.
    lia.
 --- (* no, don't add this edge *)
  forward.
  Exists msf' msflist subsetsGraph_uv.
  assert (uf_equiv subsetsGraph_uv subsetsGraph'). {
    apply uf_equiv_sym in H19.
    apply uf_equiv_sym in H21.
    apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
  }
  entailer!.
  split3; [| |split3]; intros.
  +++
  rewrite H14. symmetry. apply H24.
  +++
  rewrite <- (H15 u0 v0 H23 H45). apply uf_equiv_connected. apply H24.
  +++
  rewrite <- H16.
  apply uf_equiv_connected; trivial.
  +++
  destruct (H17 _ H23) as [y [? ?]].
  exists y.
  split; trivial; lia.
  +++
  destruct (Z.eq_dec j i).
  2: apply H18; trivial; lia.
  subst j. (* hrmm *)
  rewrite Hu_i; rewrite Hv_i.
  unfold c_connected_by_path.
  assert (connected msf' u v). {
   apply H16. apply connected_ufroot_same_iff. exists v_root.
   split; auto.
  }
  destruct H46 as [p ?]. exists p. split.
  rewrite <- H0 in Hvvalid_g_u. rewrite <- H0 in Hvvalid_g_v.
  repeat rewrite Int.signed_repr. auto.
  split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  split. set (k:=Int.min_signed); compute in k; subst k. lia.
    apply (Z.le_trans _ (Int.max_signed/8)). lia. apply Z.lt_le_incl. apply Z.div_lt. lia. lia.
  apply connected_exists_list_edges in H46. destruct H46 as [l ?]. exists l.
  split. auto. intros. assert (In w (EList msf')). apply EList_evalid.
  apply (fits_upath_evalid msf' p l); auto.
  assert (In (wedge_to_cdata (edge_to_wedge msf' w)) (map wedge_to_cdata msflist)).
  apply in_map. apply (Permutation_in (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto.
  apply in_map. auto.
  assert (edge_to_wedge msf' w = edge_to_wedge g w). unfold edge_to_wedge.
  assert (elabel msf' w = elabel g w). apply H11. apply EList_evalid in H48; apply H48. rewrite H50; auto.
  rewrite <- H50.
  assert (incl (map wedge_to_cdata msflist) (sublist 0 i sorted)).
  unfold incl; intros. apply H17 in H51. destruct H51; destruct H51. rewrite H52.
  assert (Znth (x+0) sorted = Znth x (sublist 0 i sorted)).
  symmetry. apply (Znth_sublist 0 x i sorted). lia. lia. rewrite Z.add_0_r in H53. rewrite H53.
  apply Znth_In. rewrite Zlength_sublist by lia; lia.
  apply H51. apply H49.
  + Intros msf. Intros msflist.
    Intros subsetsGraph'.
    forward_call ((pointer_val_val subsetsPtr)).
    forward.

    Exists gptr eptr msf msflist.
    entailer!.
    admit.
Abort.
