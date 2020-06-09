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

Lemma numE_range:
  forall g,
    numE g <= MAX_EDGES ->
    Int.min_signed <= numE g <= Int.max_signed.
Proof.
  intros.
  pose proof (numE_pos g).
  unfold MAX_EDGES in H.
  assert (Int.min_signed <= 0) by now compute.
  assert (8 <= Int.max_signed) by now compute.
  lia.
Qed.

Lemma numE_pred_range:
  forall g,
    numE g <= MAX_EDGES ->
    Int.min_signed <= numE g - 1 <= Int.max_signed.
Proof.
  intros.
  pose proof (numE_pos g).
  unfold MAX_EDGES in H.
  assert (Int.min_signed <= -1) by now compute.
  assert (7 <= Int.max_signed) by now compute.
  lia.
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

(* Stealing from verif_binary_heap, but eventually
        they should both use them from a central library *)
Lemma upd_Znth_overwrite:
  forall {A} (l : list A) i a b,
    0 <= i < Zlength l ->
    upd_Znth i (upd_Znth i l a) b = upd_Znth i l b.
Proof.
  intros.
  rewrite upd_Znth_unfold by now rewrite upd_Znth_Zlength.
  rewrite upd_Znth_Zlength; trivial.
  repeat rewrite upd_Znth_unfold by trivial.
  rewrite sublist0_app1.
  2: rewrite Zlength_sublist; lia.
  rewrite sublist_sublist00 by lia.
  f_equal. f_equal.
  rewrite app_assoc.
  rewrite sublist_app2.
  2: { rewrite Zlength_app, Zlength_sublist by lia.
       unfold Zlength. simpl. lia.
  }
  rewrite Zlength_app, Zlength_sublist by lia.
  unfold Zlength at 1; simpl.
  rewrite sublist_same; trivial.
  - lia.
  - unfold Zlength at 2; simpl.
    rewrite Zlength_sublist by lia. lia.
Qed.

Lemma vint_repr_force_clean:
  forall i,
    is_int I32 Signed i ->
    Vint (Int.repr (force_signed_int i)) = i.
Proof.
  intros. 
  apply is_int_e in H.
  destruct H as [? [? _]].
  unfold wedgerep_inhabitant in *.
  rewrite H.
  simpl.
  rewrite Int.repr_signed. trivial.
Qed.

Lemma numE_succ_range:
  forall g,
    numE g <= MAX_EDGES ->
    Int.min_signed <= numE g + 1 <= Int.max_signed.
Proof.
  intros.
  pose proof (numE_pos g).
  unfold MAX_EDGES in H.
  assert (Int.min_signed <= 1) by now compute.
  assert (9 <= Int.max_signed) by now compute.
  lia.
Qed.

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

Lemma tarray_data_at_isolate:
  forall (sh : Share.t) (t : type) (N n : Z)
    (l : list (reptype t)) (p : val),
  0 <= n < N ->
  N = Zlength l ->
  data_at sh (tarray t N) l p =
  sepcon (data_at sh (tarray t n) (sublist 0 n l) p)
   (sepcon (data_at sh t (Znth n l) (field_address0 (Tarray t (n+1) noattr) [ArraySubsc n] p))
     (data_at sh (tarray t (N-(n+1))) (sublist (n+1) N l)
     (field_address0 (Tarray t N noattr) [ArraySubsc (n+1)] p))
   ).
Proof.
intros.
rewrite (split2_data_at_Tarray sh t N (n+1) l l (sublist 0 (n+1) l) (sublist (n+1) N l)).
rewrite (split2_data_at_Tarray sh t (n+1) n
          (sublist 0 (n+1) l) (sublist 0 (n+1) l)
          (sublist 0 n l) (sublist n (n+1) l)).
assert (n+1-n = 1) by lia. rewrite H1.
assert (Hdummy: sublist n (n + 1) l = [Znth n l]). apply sublist_one. lia. lia. lia.
rewrite Hdummy. rewrite (data_at_singleton_array_eq sh t (Znth n l) [Znth n l]).
repeat rewrite sepcon_assoc. reflexivity.
reflexivity. lia. rewrite Zlength_sublist by lia; lia.
rewrite (sublist_same 0 (n+1) (sublist 0 (n+1) l)). reflexivity.
lia. rewrite Zlength_sublist by lia; lia.
rewrite sublist_sublist00 by lia. reflexivity.
rewrite sublist_sublist by lia. repeat rewrite Z.add_0_r. reflexivity.
lia. lia. rewrite sublist_same by lia. reflexivity.
reflexivity. reflexivity.
Qed.

(*this is stupid*)
Corollary tarray_data_at_isolate2:
  forall P (sh : Share.t) (t : type) (N n : Z)
    (l : list (reptype t)) (p : val),
  0 <= n < N ->
  N = Zlength l ->
  sepcon P (data_at sh (tarray t N) l p) =
  sepcon P (sepcon (data_at sh (tarray t n) (sublist 0 n l) p)
   (sepcon (data_at sh t (Znth n l) (field_address0 (Tarray t (n+1) noattr) [ArraySubsc n] p))
     (data_at sh (tarray t (N-(n+1))) (sublist (n+1) N l)
     (field_address0 (Tarray t N noattr) [ArraySubsc (n+1)] p)))).
Proof.
intros. rewrite (tarray_data_at_isolate sh t N n l p H H0).
reflexivity.
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
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr) = data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges (Z.to_nat MAX_EDGES)) (pointer_val_val eptr)). {
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
  rewrite <- HZlength_glist.
  (******************************SORT******************************) 
  forward_call ((wshare_share sh), 
                pointer_val_val orig_eptr,
                (map wedge_to_cdata glist)).
  - split3; [| |split]; trivial.
    rewrite HZlength_glist.
      split; [ apply numE_pos | apply numE_range; trivial].
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
           is_partial_graph msf' g;
           uforest msf';
           Permutation msflist (graph_to_wedgelist msf');
           forall u v, connected subsetsGraph' u v -> connected g u v; (*uf represents components of graph*)
           forall u v, connected subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           uf_equiv (makeSet_discrete_Graph (Z.to_nat (numV g))) subsetsGraph'; (*WX: If I'm not wrong the 2nd part isn't right, we just need the vvalid?*)
           (*weight lemmas...*)
           forall x, In x (map wedge_to_cdata msflist) -> exists j, 0 <= j < i /\ x = Znth j sorted;
           (*2. edges before i that WEREN't added, exists a upath made of edges before j*)
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
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (Z.to_nat (MAX_EDGES - numE g))) (offset_val (numE g * sizeof t_struct_edge) (pointer_val_val orig_eptr));
          (*msf'. fold this into wedgearray_graph_rep?*)
          data_at sh (tarray t_struct_edge (numE msf')) (map wedge_to_cdata msflist) (pointer_val_val eptr);
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE msf')) (Vundef_cwedges (Z.to_nat (MAX_EDGES - numE msf'))) (offset_val (numE msf' * sizeof t_struct_edge) (pointer_val_val eptr));
          (*ufgraph*)
          whole_graph sh subsetsGraph' subsetsPtr
    ))%assert.
    + apply numE_range; trivial.
    + (******PRECON******)
      Exists (edgeless_WEdgeGraph (numV g)).
      (*Exists (nil (A:=LE*EType)).*) Exists (graph_to_wedgelist (edgeless_WEdgeGraph (numV g))).
      Exists (makeSet_discrete_Graph (Z.to_nat (numV g))).
      rewrite edgeless_WEdgeGraph_numV by lia.
      rewrite edgeless_WEdgeGraph_numE. rewrite Z.sub_0_r.
      replace ((Z.to_nat MAX_EDGES - Z.to_nat 0)%nat) with (Z.to_nat MAX_EDGES) by lia.
      rewrite data_at_zero_array_eq. 2: simpl; auto. 2: auto.
      2: { unfold graph_to_wedgelist. rewrite edgeless_WEdgeGraph_EList. simpl; auto. }
      entailer!. (*LAAAAAAAAG*)
      split3; [| | split3]. 5: split. (*the last lemma got purged? probably because of 0<=j<0*)
      * unfold is_partial_graph.
        repeat split; intros.
        1: rewrite <- edgeless_WEdgeGraph_vvalid in H25; apply H0; auto.
        all: rewrite <- EList_evalid, edgeless_WEdgeGraph_EList in H25; contradiction.
      * (*maybe I should do this in WeightedEdgeListGraph*)
        unfold uforest. unfold acyclic_ugraph.
        intros. unfold simple_ucycle in H25. unfold ucycle in H25.
        destruct H25; destruct H25.
          destruct p. contradiction.
          destruct p. contradiction.
        unfold not; intros. destruct H28. unfold adjacent in H28; unfold adj_edge in H28.
        destruct H28. destruct H28. destruct H28.
        assert (~ evalid (edgeless_WEdgeGraph (numV g)) x). rewrite <- EList_evalid.
          rewrite edgeless_WEdgeGraph_EList. auto.
        contradiction.
      * intros. unfold connected in H25. unfold connected_by in H25. destruct H25 as [p ?]. unfold connected_by_path in H25.
        destruct H25. unfold good_upath in H25. destruct H25. unfold valid_upath in H25. destruct H26.
        destruct p eqn:Hp; simpl in H25. simpl in H26; inversion H26. simpl in H26; inversion H26.
        rewrite H30 in *.
        destruct u0.
        (*single vertex in upath. Thus u=v, trivially connected*)
        simpl in H28; inversion H28. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
        split. simpl. apply H0. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. apply H25.
        unfold upath_prop; rewrite Forall_forall. intros; auto.
        (*case p = u::z0::u0.
          Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...
        *)
        destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25. destruct H32.
        rewrite makeSet_vvalid in H33. rewrite Z2Nat.id in H33 by lia.
        destruct H31; destruct H31;
          rewrite H34 in H33; rewrite makeSet_dst in H34; rewrite <- H34 in H33; lia.
      * (*WX: working on this*)
        intros; split; intros.
        { (*Same thing as above, show that it can't be connected*)
          unfold connected in H25; unfold connected_by in H25; destruct H25 as [p ?]. unfold connected_by_path in H25.
          destruct H25. unfold good_upath in H25. destruct H25. unfold valid_upath in H25. destruct H26.
          destruct p eqn:Hp; simpl in H25. simpl in H26; inversion H26. simpl in H26; inversion H26.
          rewrite H30 in *. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H28; inversion H28. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
          split. simpl. apply makeSet_vvalid in H25. rewrite Z2Nat.id in H25 by lia. apply H25.
          unfold upath_prop; rewrite Forall_forall. intros; auto.
          (*case p = u::z0::u0.
            Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...
          *)
          destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25. destruct H32.
          rewrite makeSet_vvalid in H33. rewrite Z2Nat.id in H33 by lia.
          destruct H31; destruct H31;
            rewrite H34 in H33; rewrite makeSet_dst in H34; rewrite <- H34 in H33; lia.
        }
        { (*more or less same deal...*)
          unfold connected in H25; unfold connected_by in H25; destruct H25 as [p ?]. unfold connected_by_path in H25.
          destruct H25. unfold good_upath in H25. destruct H25. unfold valid_upath in H25. destruct H26.
          destruct p eqn:Hp. simpl in H26; inversion H26. simpl in H26; inversion H26.
          rewrite H30 in *. destruct u0.
          (*single vertex in upath. Thus u=v, trivially connected*)
          simpl in H28; inversion H28. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
          split. simpl. rewrite makeSet_vvalid. rewrite Z2Nat.id by lia. apply H25.
          unfold upath_prop; rewrite Forall_forall. intros; auto.
          (*case p = u::z0::u0.
            Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...
          *)
          destruct H25. destruct H25. unfold adj_edge in H25. destruct H25. destruct H25.
          rewrite <- EList_evalid in H25. rewrite edgeless_WEdgeGraph_EList in H25. contradiction.
        }
      * apply (uf_equiv_refl _ (liGraph (makeSet_discrete_Graph (Z.to_nat (numV g))))).
      * intros. unfold graph_to_wedgelist in H25; rewrite edgeless_WEdgeGraph_EList in H25; simpl in H25.
        contradiction.
    + (******LOOP BODY******)
      Intros.
      assert (Hdef_i: def_wedgerep (Znth i sorted)). {
        rewrite Forall_forall in Hdef_sorted. apply Hdef_sorted. apply Znth_In. lia. }
      forward. forward.
      * entailer!.
        rewrite (surjective_pairing (Znth i sorted)).
        rewrite (surjective_pairing (snd (Znth i sorted))).
        apply Hdef_i.
      * (* inside the for loop *) 
 forward. forward.
 1: { entailer!.
      rewrite (surjective_pairing (Znth i sorted)).
      rewrite (surjective_pairing (snd (Znth i sorted))).
      apply Hdef_i.
 }
 rewrite (surjective_pairing (Znth i sorted)).
 rewrite (surjective_pairing (snd (Znth i sorted))).

  (*some assertions about Znth i sorted, for convenience*)
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
    unfold graph_to_wedgelist in HIn_i. apply list_in_map_inv in HIn_i. destruct HIn_i. destruct H18.
    inversion H18. split. auto. apply EList_evalid in H19. rewrite <- H22 in H19. apply H19.
 } destruct Htmp as [Hw_i Huv_i].
 assert (Htmp: vvalid g u /\ vvalid g v). {
  destruct H. destruct H18. unfold edge_valid in H18. apply H18 in Huv_i. auto.
 } destruct Htmp as [Hu_i Hv_i].
 forward_call (sh,
               subsetsGraph',
               subsetsPtr,
               (force_signed_int
                  (fst (snd (Znth i sorted))))).
 ++
  entailer!. simpl.
  clear - Hdef_i.
  destruct Hdef_i as [_ [? _]].
  apply is_int_e in H.
  destruct H as [? [? _]].
  unfold wedgerep_inhabitant in *.
  replace ((fst (snd (Znth i sorted)))) with (Vint x).
  simpl.
  rewrite Int.repr_signed. trivial.
 ++
  unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl.
  destruct H15 as [? _].
  rewrite <- H15. apply H4. apply H0 in Hu_i. rewrite !Int.signed_repr. lia.
    apply H0 in Hu_i. destruct H. apply H in Hu_i.
    split. apply (Z.le_trans Int.min_signed 0 u). apply Z.lt_le_incl. apply Int.min_signed_neg. apply Hu_i.
    apply Z.lt_le_incl; apply Hu_i.
 ++
  Intros u_root.
  destruct u_root as [subsetsGraph_u u_root].
  (* 1. the UFGraph after finding u
     2. u's root 
   *)
  simpl fst.
  forward_call (sh,
                subsetsGraph_u,
                subsetsPtr,
                (force_signed_int
                   (snd (snd (Znth i sorted))))).
  **
   entailer!.
   simpl.
   destruct Hdef_i as [_ [_ ?]].
   rewrite vint_repr_force_clean; trivial.
  **
  unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl.
  destruct H18 as [? _]; rewrite <- H18.
  (*WX: If I'm not wrong we need to change H14, but only the first part is used here so won't affect much*)
  destruct H15 as [? _]; rewrite <- H15.
  apply H4. apply H0 in Hv_i. rewrite !Int.signed_repr. lia.
    apply H0 in Hv_i. destruct H. apply H in Hv_i.
    split. apply (Z.le_trans Int.min_signed 0 v). apply Z.lt_le_incl. apply Int.min_signed_neg. apply Hv_i.
    apply Z.lt_le_incl; apply Hv_i.
  **
   Intros v_root.
   destruct v_root as [subsetsGraph_uv v_root].
   simpl fst in *. simpl snd in *.
   forward_if.
   --- admit.
       (* under heavy reconstruction, c/o Wei Xiang *)

       (*
     (* yes, add this edge.
          the bulk of the proof *)
     (*ASDF: isolate the part of the array being updated*)

     (*THIS IS GOING TO BE UGLY*)
     rewrite (tarray_data_at_isolate sh t_struct_edge (MAX_EDGES - numE msf') 0
              (Vundef_cwedges (Z.to_nat (MAX_EDGES - numE msf')))
              (offset_val (numE msf' * sizeof t_struct_edge) (pointer_val_val eptr))
     ). 2: { (*need an assertion somewhere that numE msf' <= i*) admit. }
     2: { unfold Vundef_cwedges. rewrite Zlength_list_repeat. lia.
          (*same thing as above, so should declare it at the start of loopbody*) admit.
        } Intros.

    (*this part should be replaceable now*)
     forward. forward.
     1: { entailer!. rewrite (surjective_pairing (Znth i sorted)).
          destruct Hdef_i; trivial.
     }
     forward. forward.
     forward. forward.
     1: { admit. (* something is quite wrong *) }
     forward. forward. forward. forward.
     1: { entailer!.
          rewrite (surjective_pairing (Znth i sorted)).
          destruct Hdef_i as [? _]. trivial.
     }
     forward.
     1: { admit. (* something is quite wrong *) }
     forward. forward.
     1: { entailer!.
          rewrite Int.signed_repr.
          2: { apply numE_range.
               (* should be easy to get this via an 
                  assert_PROP? *)
               admit.
          }
          rewrite Int.signed_repr.
          2: rep_lia.
          apply numE_succ_range.
          (* again, should be easy to get via assert_PROP? *)
          admit.
     }

     (* Okie let's do some cleanup... *)
     rewrite (surjective_pairing (Znth i sorted)).
     rewrite (surjective_pairing (Znth (numE msf') (map wedge_to_cdata msflist))).
     rewrite (surjective_pairing (snd (Znth (numE msf') (map wedge_to_cdata msflist)))).
     rewrite (surjective_pairing (Znth (numE msf')
                  (upd_Znth (numE msf') (map wedge_to_cdata msflist)
                     (fst (Znth (numE msf') (map wedge_to_cdata msflist)),
                     (fst (snd (Znth i sorted)),
                     snd (snd (Znth (numE msf') (map wedge_to_cdata msflist)))))))).
     rewrite (surjective_pairing (snd
                  (Znth (numE msf')
                     (upd_Znth (numE msf') (map wedge_to_cdata msflist)
                        (fst (Znth (numE msf') (map wedge_to_cdata msflist)),
                        (fst (snd (Znth i sorted)),
                        snd (snd (Znth (numE msf') (map wedge_to_cdata msflist))))))))).
     rewrite (surjective_pairing (Znth (numE msf')
              (upd_Znth (numE msf')
                 (upd_Znth (numE msf') (map wedge_to_cdata msflist)
                    (fst (Znth (numE msf') (map wedge_to_cdata msflist)),
                    (fst (snd (Znth i sorted)),
                    snd (snd (Znth (numE msf') (map wedge_to_cdata msflist))))))
                 (fst
                    (Znth (numE msf')
                       (upd_Znth (numE msf') (map wedge_to_cdata msflist)
                          (fst (Znth (numE msf') (map wedge_to_cdata msflist)),
                          (fst (snd (Znth i sorted)),
                          snd (snd (Znth (numE msf') (map wedge_to_cdata msflist))))))),
                 (fst
                    (snd
                       (Znth (numE msf')
                          (upd_Znth (numE msf') (map wedge_to_cdata msflist)
                             (fst (Znth (numE msf') (map wedge_to_cdata msflist)),
                             (fst (snd (Znth i sorted)),
                             snd
                               (snd (Znth (numE msf') (map wedge_to_cdata msflist)))))))),
                 snd (snd (Znth i sorted))))))).
     simpl fst in *.
     simpl snd in *.
     repeat rewrite upd_Znth_overwrite.
     repeat rewrite upd_Znth_same.
     
     6: rewrite upd_Znth_Zlength.
     2: { rewrite Zlength_map.
          rewrite <- g2wedgelist_numE.
          rewrite (Permutation_Zlength _ _ _ H11).
          (* something is quite wrong. *)
          admit.
     }
     2-6: admit. (* exactly the same *)
     
     simpl fst in *.
     simpl snd in *.
     
     forward_call (sh, subsetsGraph_uv, subsetsPtr,
                   (force_signed_int (fst (snd (Znth i sorted)))),
                   (force_signed_int (snd (snd (Znth i sorted))))).
     +++
       entailer!.
       simpl.
       destruct Hdef_i as [_ [? ?]].
       repeat rewrite vint_repr_force_clean; trivial.
     +++
       destruct Hdef_i as [_ [? ?]].
       apply is_int_e in H20.
       apply is_int_e in H21.
       destruct H20 as [? [? _]].
       destruct H21 as [? [? _]].
       rewrite H20, H21.
       simpl.
       assert (uf_equiv subsetsGraph subsetsGraph_uv). {
         apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
         apply (uf_equiv_trans _ (liGraph subsetsGraph')); trivial.
       }
       destruct H22 as [? _].
       do 2 rewrite <- H22.
       split; apply H4. admit. admit. (* leaving for WX *)
     +++ 
       admit. *)
   --- (* no, don't add this edge *)
    forward. entailer!.
    (* the variables are uncertain but here's a guess: *)
    Exists msf' msflist subsetsGraph_uv.
    assert (uf_equiv subsetsGraph_uv subsetsGraph'). {
      apply uf_equiv_sym in H18.
      apply uf_equiv_sym in H20.
      apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
    }
    entailer!. 

    Set Nested Proofs Allowed.

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

    Lemma reachable_ufroot_same:
      forall {g: UFGraph} {v1 v2 r1 r2},
        reachable g v1 v2 ->
        uf_root g v1 r1 ->
        uf_root g v2 r2 ->
        r1 = r2. 
    Proof.
      intros.
      pose proof (uf_root_reachable g _ _ r2 H H1).
      apply (uf_root_unique _ _ _ _ _ H0 H2).
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

    Lemma valid_upath_vvalid:
      forall g v l,
        valid_upath g (v :: l) -> vvalid g v.
    Proof.
      intros.
      destruct l.
      - simpl in H; trivial.
      - destruct H as [? _].
        red in H. destruct H as [e ?].
        red in H. destruct H as [[? [? ?]] [[? ?] | [? ?]]];
                  subst; trivial.
    Qed.
    
    Lemma reachable_uf_equiv_connected:
      forall (g1 g2: UFGraph) u v,
        vvalid g1 u ->
        vvalid g1 v ->
        uf_equiv g1 g2 ->
        reachable g1 u v ->
        connected g2 u v.
    Proof.
      intros.
      destruct H1.
      assert (EnumEnsembles.EnumCovered Z (evalid g2)) by admit.
      assert (EnumEnsembles.EnumCovered Z (evalid g1)) by admit.
      (* will investigate how Shengyi does these *)
      assert (vvalid g2 u). {
        apply H1; trivial.
      }
      assert (vvalid g2 v). {
        apply H1; trivial.
      }

      pose proof (uf_root_always_exists g1 (liGraph g1) u X0 H).
      pose proof (uf_root_always_exists g1 (liGraph g1) v X0 H0).
      pose proof (uf_root_always_exists g2 (liGraph g2) u X H4).
      pose proof (uf_root_always_exists g2 (liGraph g2) v X H5).
      destruct H6 as [ur1 ?].
      destruct H7 as [vr1 ?].
      destruct H8 as [ur2 ?].
      destruct H9 as [vr2 ?].
      pose proof (H3 _ _ _ H6 H8).
      pose proof (H3 _ _ _ H7 H9).
      pose proof (uf_root_reachable _ _ _ _ H2 H7).
      pose proof (uf_root_unique _ _ _ _ _ H6 H12).
      subst ur1. subst vr1. subst vr2.
      clear H6 H7.
      destruct H8 as [? _].
      destruct H9 as [? _].
      apply reachable_implies_connected in H6.
      apply reachable_implies_connected in H7.
      apply connected_symm in H7.
      apply (connected_trans _ _ _ _ H6 H7).
    Admitted.

    Lemma uf_equiv_adjacent_connected:
      forall (g1 g2 : UFGraph) u v,
        uf_equiv g1 g2 ->
        vvalid g1 u ->
        vvalid g1 v ->
        adjacent g1 u v ->
        connected g2 u v.
    Proof.
      intros.
      apply adjacent_reachable in H2.
      destruct H2.
      - apply (reachable_uf_equiv_connected g1); trivial.
      - apply connected_symm.
        apply (reachable_uf_equiv_connected g1); trivial.
    Qed.

          
  Lemma uf_equiv_connected':
    forall (g1 g2: UFGraph) u v,
      uf_equiv g1 g2 ->
      vvalid g1 u ->
      vvalid g1 v ->
      vvalid g2 u ->
      vvalid g2 v ->
      connected g1 u v ->
      connected g2 u v.
  Proof.
    intros.
    rewrite connected_exists_path in H4.
    destruct H4 as [p [? [? ?]]].
    generalize dependent u.
    induction p.
    - intros. inversion H5.
    - destruct p.
      + intros. simpl in H5, H6.
        inversion H5. inversion H6.
        subst.
        apply connected_refl; trivial.
      + destruct H4.
        rewrite last_error_cons in H6.
        2: unfold not; inversion 1.
        specialize (IHp H2 H6).
        intros.
        simpl in H7. inversion H7; subst a; clear H7.
        assert (connected g2 z v). {
          

          
          apply valid_upath_vvalid in H2.
          apply IHp; trivial.
          destruct H.
          apply H; trivial.
        }
        apply (uf_equiv_adjacent_connected _ g2) in H0; trivial.
        2: apply (valid_upath_vvalid _ _ p); trivial.
        apply (connected_trans _ _ _ _ H0 H7).
  Qed.

  Lemma uf_equiv_connected:
    forall (g1 g2: UFGraph) u v,
      uf_equiv g1 g2 ->
      vvalid g1 u ->
      vvalid g1 v ->
      vvalid g2 u ->
      vvalid g2 v ->
      connected g1 u v <->
      connected g2 u v.
  Proof.
    intros. split; intros.
    - apply (uf_equiv_connected' g1); trivial.
    - apply uf_equiv_sym in H.
      apply (uf_equiv_connected' g2); trivial.
  Qed.
      
    Unset Nested Proofs Allowed.
    
    split3; [| |split3]; intros.
    +++
     apply H13.
     apply (uf_equiv_connected' subsetsGraph_uv); trivial; admit.
   +++
      rewrite <- H14.
      apply uf_equiv_connected; trivial; admit.
    +++
      apply uf_equiv_sym in H46.
      apply (uf_equiv_trans _ (liGraph subsetsGraph')); trivial.
    +++ admit.
    +++ admit.
    + Intros msf. Intros msflist.
       Intros subsetsGraph'.
      forward_call ((pointer_val_val subsetsPtr)).
      forward.
      admit.
Abort.
