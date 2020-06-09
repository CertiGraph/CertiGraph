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

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [makeSet_spec; find_spec; union_spec;
      mallocK_spec; free_spec; fill_edge_spec; init_empty_graph_spec; sort_edges_spec; kruskal_spec
  ]).

Local Open Scope Z_scope.

Lemma numE_pos: forall g, 0 <= numE g.
Proof.
  intros. unfold numE. apply Zlength_nonneg.
Qed.

Lemma g2wedgelist_numE:
  forall g,
    Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist.
  rewrite Zlength_map. trivial.
Qed.

Lemma Permutation_Zlength:
  forall (A : Type) (l l' : list A),
    Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros.
  rewrite Zlength_length; [| apply Zlength_nonneg].
  rewrite Zlength_correct, Nat2Z.id.
  apply Permutation_length; trivial.
Qed.

Lemma def_wedgerep_map_w2c:
  forall g,
    Forall def_wedgerep (map wedge_to_cdata (graph_to_wedgelist g)).
Proof.
  intros.
  rewrite Forall_forall; intros.
  apply list_in_map_inv in H.
  destruct H as [? [? _]].
  unfold wedge_to_cdata in H.
  unfold def_wedgerep.
  rewrite (surjective_pairing x) in *.
  inversion H; clear H.
  destruct x.
  rewrite (surjective_pairing c) in *.
  simpl fst in *; simpl snd in *.
  inversion H2; clear H2.
  rewrite H1, H0, H3. split3; trivial.
Qed.

Lemma partial_graph_EList:
  forall (g g': FiniteWEdgeListGraph), is_partial_graph g g' -> incl (EList g) (EList g').
Proof.
unfold is_partial_graph; unfold incl; intros. rewrite EList_evalid; rewrite EList_evalid in H0.
destruct H; destruct H1. apply H1. apply H0.
Qed.

Lemma NoDup_incl_Zlength:
  forall (A: Type) (l l' : list A),
  NoDup l -> incl l l' -> Zlength l <= Zlength l'.
Proof.
intros. repeat rewrite Zlength_correct. apply Nat2Z.inj_le. apply NoDup_incl_length; auto.
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
forall (g: UFGraph) x r1 r2, uf_root g x r1 -> uf_root g x r2 -> r1 = r2.
Proof.
Admitted.

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
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
     PROP (numV msf' = numV g; (*which combined with below should give vvalid msf' v <-> vvalid g v, see if we need it later*)
           numE msf' <= i;
           sound_weighted_edge_graph msf';
           is_partial_graph msf' g;
           uforest msf';
           Permutation msflist (graph_to_wedgelist msf');
           forall v, vvalid g v <-> vvalid subsetsGraph' v;
           forall u v, (exists j, 0<=j<i /\ (fst (snd (Znth j msflist)) = u \/ snd (snd (Znth j msflist)) = u))
                    -> (exists j, 0<=j<i /\ (fst (snd (Znth j msflist)) = v \/ snd (snd (Znth j msflist)) = v))
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
      * split. unfold vertex_valid; intros. apply edgeless_WEdgeGraph_vvalid in H25.
          split. lia. assert ((Int.max_signed/8) < Int.max_signed). apply Z.div_lt.
          set (k:=Int.max_signed); compute in k; subst k. lia. lia. lia.
        split. unfold edge_valid; intros. apply edgeless_WEdgeGraph_evalid in H25. contradiction.
        unfold weight_valid; intros. apply edgeless_WEdgeGraph_evalid in H25. contradiction.
      * unfold is_partial_graph. repeat split; intros.
        1: rewrite <- edgeless_WEdgeGraph_vvalid in H25; apply H0; auto.
        all: apply edgeless_WEdgeGraph_evalid in H25; contradiction.
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
      * intros. destruct H25; destruct H25. lia.
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
  (*some assertions about Znth i sorted, for convenience*)
  assert (Hdef_i: def_wedgerep (Znth i sorted)).
    rewrite Forall_forall in Hdef_sorted. apply Hdef_sorted. apply Znth_In. lia.
  assert (HIn_i: In (Znth i sorted) (map wedge_to_cdata glist)). {
    apply Permutation_sym in H5.
    apply (@Permutation_in _ _ _ _ H5).
    apply Znth_In. lia.
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
  assert(H_msf'_uv: ~ evalid msf' (u,v)). {
    (*we state that u and v are not connected in subsetsGraph'*)
    assert (~ connected subsetsGraph' u v). {
      unfold not; intros.
      apply connected_ufroot_same_iff in H25. destruct H25. destruct H25.
      assert (uf_root subsetsGraph' u u_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply H20.
      assert (uf_root subsetsGraph_u v v_root). apply (uf_equiv_root_the_same subsetsGraph_u subsetsGraph_uv). apply H21. apply H22.
      assert (uf_root subsetsGraph' v v_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H19. apply H28.
      assert (u_root = x). admit.
      assert (v_root = x). admit.
      rewrite H30 in H23; rewrite H31 in H23. contradiction.
    }
    (*by invariant, it means they aren't connected in msf'*)
    rewrite H16 in H25.
    (*but presence of u-v means they are connected*)
    unfold not; intros.
    assert (connected msf' u v). {
      (*
      exists [u;v]. split. split. simpl. split. exists (u,v). split. split. apply H26.
      split. simpl.
      *)
    } contradiction.
  }
  forward_call (sh, subsetsGraph_uv, subsetsPtr, u, v).
   +++
    assert (Htmp: uf_equiv subsetsGraph' subsetsGraph_uv). {
       apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
     } destruct Htmp. do 2 rewrite <- H25.
    split; auto.
   +++
    (*ASDF*)
    Exists (FiniteWEdgeListGraph_adde msf' (u,v) w).
    Exists (msflist+::(w,(u,v))).
    Intros vret. Exists vret.
    (*before we entailer, preemptively fix up some of the SEPs*)

    admit.

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
     rewrite H14.
     destruct H24. symmetry. apply H24.
   +++
     admit.
   +++
     rewrite <- H16.
     apply uf_equiv_connected; trivial.
   +++
     destruct (H17 _ H45) as [y [? ?]].
     exists y.
     split; trivial; lia.
   +++
     destruct (Z.eq_dec j i).
     2: apply H18; trivial; lia.
     subst j. (* hrmm *)
     rewrite Hu_i; rewrite Hv_i.
     unfold c_connected_by_path.
     (*idea:
        u_root = v_root
        therefore, connected msf' u v := exists l: upath, ...
        between every two vertices in l, exists edge, adj_edge... <-- requires induction?
        this edge is in msf', thus in msflist due to Permutation
        by the 1st 'weight' lemma, incl msflist (sublist 0 i sorted)
      *)
     (* getting a bit lost, can you take a glance? *)
     admit.     
    + Intros msf. Intros msflist.
      Intros subsetsGraph'.
      forward_call ((pointer_val_val subsetsPtr)).
      forward.

      Exists gptr eptr msf msflist.
      entailer!.
      admit.
Abort.
