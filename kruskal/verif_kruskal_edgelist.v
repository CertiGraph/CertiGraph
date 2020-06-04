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
(*edgelist*)
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
(*spanning tree definition*)
Require Import RamifyCoq.kruskal.mst.
Require Import RamifyCoq.kruskal.kruskal_uf_specs.
(*Require Import RamifyCoq.graph.spanning_tree.*)

Require Import RamifyCoq.kruskal.undirected_graph.

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
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) (pointer_val_val eptr) = data_at sh (tarray t_struct_edge MAX_EDGES) (list_repeat (Z.to_nat MAX_EDGES) (Vundef, (Vundef, Vundef))) (pointer_val_val eptr)). {
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
  forward_call (sh, (numV g)). Intros subsets.
  forward_call (gv, sh). Intros mst.
  destruct subsets as [subsetsGraph subsetsPtr].
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
  (*- entailer!. simpl. rewrite HZlength_glist. reflexivity.
  - rewrite HZlength_glist. entailer!. rewrite Zlength_map, g2wedgelist_numE. entailer!.*)
  - split3; [| |split]; trivial.
    rewrite HZlength_glist.
      split; [ apply numE_pos | apply numE_range; trivial].
  - Intros sorted.
    (* a little cleanup... *)
    (*rewrite empty_WEdgeListGraph_numE.
    rewrite <- Z2Nat.inj_sub, Z.sub_0_r. 2: lia.
    rewrite Z.mul_0_l.*)
    assert_PROP (isptr (pointer_val_val eptr)) by
        (rewrite (data_at_isptr sh); entailer!).
    rename H7 into H_eptr_isptr.
    assert (Hdef_sorted: Forall def_wedgerep sorted). {
      apply (Forall_permutation _ _ _ Hdef_glist H5).
    }
    (*clear Hdef_g.*)
    assert (HZlength_sorted: Zlength sorted = numE g). {
      rewrite <- (Permutation_Zlength _ _ _ H5). apply HZlength_glist.
    } rewrite HZlength_glist. rewrite HZlength_sorted.
    (* done with cleanup. *)

    (******************************THE BIG NASTY LOOP******************************) 
    forward_for_simple_bound
    (numE g)
    (EX i : Z,
     EX msf' : FiniteWEdgeListGraph,
     EX msflist: list (LE*EType),
     EX subsetsGraph' : UFGraph,                      
     PROP (numV msf' = numV g; (*which combined with below should give vvalid msf' v <-> vvalid g v, see if we need it later*)
           is_partial_graph msf' g;
           uforest msf';
           Permutation msflist (graph_to_wedgelist msf');
           True; (* something about min wt *)
           forall u v, connected subsetsGraph' u v -> connected g u v; (*uf represents components of graph*)
           forall u v, connected subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
           uf_equiv subsetsGraph subsetsGraph' (*WX: If I'm not wrong the 2nd part isn't right, we just need the vvalid?*)
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
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (list_repeat (Z.to_nat MAX_EDGES - Z.to_nat (numE g)) (Vundef, (Vundef, Vundef))) (offset_val (numE g * sizeof t_struct_edge) (pointer_val_val orig_eptr));
          (*msf'. fold this into wedgearray_graph_rep?*)
          data_at sh (tarray t_struct_edge (numE msf')) (map wedge_to_cdata msflist) (pointer_val_val eptr);
          data_at sh t_wedgearray_graph (Vint (Int.repr (numV msf')), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge (MAX_EDGES - numE msf')) (list_repeat (Z.to_nat MAX_EDGES - Z.to_nat (numE msf')) (Vundef, (Vundef, Vundef))) (offset_val (numE msf' * sizeof t_struct_edge) (pointer_val_val eptr));
          (*ufgraph*)
          whole_graph sh subsetsGraph' subsetsPtr
    ))%assert.
    + apply numE_range; trivial.
    + (******PRECON******)
      Exists (edgeless_WEdgeGraph (numV g)).
      (*Exists (nil (A:=LE*EType)).*) Exists (graph_to_wedgelist (edgeless_WEdgeGraph (numV g))).
      Exists subsetsGraph.
      rewrite edgeless_WEdgeGraph_numV by lia.
      rewrite edgeless_WEdgeGraph_numE. rewrite Z.sub_0_r.
      replace ((Z.to_nat MAX_EDGES - Z.to_nat 0)%nat) with (Z.to_nat MAX_EDGES) by lia.
      rewrite data_at_zero_array_eq. 2: simpl; auto. 2: auto.
      2: { unfold graph_to_wedgelist. rewrite edgeless_WEdgeGraph_EList. simpl; auto. }
      entailer!. (*LAAAAAAAAG*)
      split3; [| | split3].
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
      * assert (subsetsGraph = makeSet_discrete_Graph (Z.to_nat (numV g))). admit.
        intros. unfold connected in H26. unfold connected_by in H26. destruct H26 as [p H26]. unfold connected_by_path in H26.
        destruct H26. unfold good_upath in H26. destruct H26. unfold valid_upath in H26. destruct H27.
        destruct p eqn:Hp; simpl in H26. simpl in H27; inversion H27.
        assert (z = u). simpl in H27; inversion H27; reflexivity. rewrite H30 in *.
        destruct u0.
        (*single vertex in upath
          then u=v, trivially connected
        *)
        simpl in H29; inversion H29. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
        split. simpl. apply H0. rewrite H25 in H26. apply makeSet_vvalid in H26. rewrite Z2Nat.id in H26 by lia. apply H26.
        unfold upath_prop; rewrite Forall_forall. intros; auto.
        (*case p = u::z0::u0.
          Thus exists e,. dst subsetsGraph e = z0
          But by makeSet_dst...
        *)
        destruct H26. destruct H26. unfold adj_edge in H26. destruct H26. destruct H32; rewrite H25 in H32.
          destruct H32.
        admit. admit. (*WX: working on this*)
      * admit.  (*WX: working on this*)
      * apply (uf_equiv_refl _ (liGraph subsetsGraph)).
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

  (*In (Znth i sorted) sorted, 
    which is a Permutation of map wedge_to_cdata glist
    so 
    In (Znth i sorted) map wedge_to_cdata glist
   *)
  assert (HIn_i: In (Znth i sorted) (map wedge_to_cdata glist)). {
    apply Permutation_sym in H5.
    apply (@Permutation_in _ _ _ _ H5).
    apply Znth_In. lia.
  }
  (* thus, exists e, eevalid g e /\ (Znth i sorted) = wedge_to_cdata e <--add such a lemma to spatial *)
  apply list_in_map_inv in HIn_i.
  destruct HIn_i as [e [Heq_i HIn_i]].
  destruct e as [w [u v]].
 assert (elabel g (u,v) = w /\ evalid g (u,v)). {
    apply Permutation_sym in H3. Check Permutation_in. apply (Permutation_in (A:= prod LE EType) (l:=glist) (l':=graph_to_wedgelist g) (w,(u,v)) H3) in HIn_i.
    unfold graph_to_wedgelist in HIn_i. apply list_in_map_inv in HIn_i. destruct HIn_i. destruct H15.
    inversion H15. split. auto. apply EList_evalid in H16. rewrite <- H19 in H16. apply H16.
 } destruct H15 as [Hw_i Huv_i].
 assert (vvalid g u /\ vvalid g v). {
  destruct H. destruct H15. unfold edge_valid in H15. apply H15 in Huv_i. auto.
 } destruct H15 as [Hu_i Hv_i].
 forward_call (sh,
               subsetsGraph',
               subsetsPtr,
               (force_signed_int
                  (fst (snd (Znth i sorted))))).
 ++
  entailer!. simpl.
  destruct Hdef_i as [_ [? _]].
  rewrite vint_repr_force_clean; trivial.
 ++
  unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl.
  destruct H14 as [? _].
  rewrite <- H14. apply H4. apply H0 in Hu_i. rewrite !Int.signed_repr. lia.
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
  destruct H15 as [? _]; rewrite <- H15.
  (*WX: If I'm not wrong we need to change H14, but only the first part is used here so won't affect much*)
  destruct H14 as [? _]; rewrite <- H14.
  apply H4. apply H0 in Hv_i. rewrite !Int.signed_repr. lia.
    apply H0 in Hv_i. destruct H. apply H in Hv_i.
    split. apply (Z.le_trans Int.min_signed 0 v). apply Z.lt_le_incl. apply Int.min_signed_neg. apply Hv_i.
    apply Z.lt_le_incl; apply Hv_i.
  **
   Intros v_root.
   destruct v_root as [subsetsGraph_uv v_root].
   simpl fst in *. simpl snd in *.
   forward_if.
   --- (* yes, add this edge.
          the bulk of the proof *)
     forward. forward. forward.
     1: { admit. (* something is quite wrong *) }
     forward. forward. forward.
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
       admit. (* leaving for WX *)
     +++
       admit.
   --- (* no, don't add this edge *)
    forward. entailer!.
    (* the variables are uncertain but here's a guess: *)
    Exists msf' msflist subsetsGraph_uv.
    assert (uf_equiv subsetsGraph_uv subsetsGraph'). {
      apply uf_equiv_sym in H17.
      apply uf_equiv_sym in H15.
      apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
    }
    entailer!.

    Set Nested Proofs Allowed.
    Lemma uf_equiv_connected:
      forall {g1 g2 u v},
        uf_equiv g1 g2 ->
        connected g1 u v <->
        connected g2 u v.
    Proof.
     (* Hrmm I've thrashed around here
        a fair bit but I don't quite see
        why this needs to be true. Maybe we can do a    
        call to discuss. Alternately we can leave this
        alone until the loop's invariant has fully
        settled down and we are sure we need this
      *)
    Admitted.
    Unset Nested Proofs Allowed.
    
    split3; intros.
    +++
     apply H12.
     apply (uf_equiv_connected H43); trivial.
    +++
      rewrite <- H13.
      apply uf_equiv_connected; trivial.
    +++
      apply uf_equiv_sym in H43.
      apply (uf_equiv_trans _ (liGraph subsetsGraph')); trivial.
    + Intros msf. Intros msflist.
       Intros subsetsGraph'.
      forward_call ((pointer_val_val subsetsPtr)).
      forward.
      admit.
Abort.

Print Assumptions body_init_empty_graph.
(*
Idea of proof:
int graph_V = graph->V;
int graph_E = graph->E;
struct subset *subsets = makeSet(graph_V); (*ufgraph with V vertices all distinct*)
struct graph *mst = init_empty_graph();

mst->V = graph_V; <-- mst is now a graph with V vertices and 0 edges

sort_edges(graph->edge_list,0,graph_E-1);

    //invariant: is_partial_graph mst orig_graph /\ uforest mst
    //   connected ufgraph u v <-> connected in mst (also connected ufgraph u v -> connected graph u v)
    // showing forest is a problem... need an easy-to-work-with definition
    // and something about minimum weight...
    //precon: mst has no edges, is a trivial subset, trivial forest. subsets are all disjoint
    for (int i = 0; i < graph_E; ++i) {

        int u = graph->edge_list[i].u;
        int v = graph->edge_list[i].v;

        int ufind = find(subsets, u);		//returned g' is: uf_root g' i rt
        int vfind = find(subsets, v);

        //need a join postcon?
        //ufind != vfind <-> not connected in mst
        //not_connected -> add edge -> no cycle <-- Need a lemma in undirected_graph.v
        //also show that edge here: minimum of all (u,v) edges
        if (ufind != vfind) {
            mst->edge_list[mst->E].u = u;
            mst->edge_list[mst->E].v = v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            mst->E += 1;
            Union(subsets, u, v);

            //mst = mst + (u,v), thus u,v are connected
            //ifcon (loopcon): is_partial_graph (mst + (u,v)) orig
            //mst is still uforest (using the needed lemma above)
            //same_subset(u,v) /\ u,v connected (*trivially <->*)
        }
        //need an elsecon?
        //uf_root p u -> reachable g u p -> connected p u (reachable_implies_connected)
        //connected p u -> connected p v -> connected u v (connected_trans)
    }
    //postcon

    //before free, need to prove that same_subset(u,v) <-> connected orig u v
    //from invariant, same_subset(u,v) <-> connected in mst
    //thus, connected in mst <-> connected in orig: spanning definition

    free(subsets);

    //worried about proving minimum
    return mst;

*)
