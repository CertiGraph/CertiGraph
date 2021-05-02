Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
(*for ufgraph *)
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.graph_relation.
(*for unionfind*)
Require Import CertiGraph.msl_application.ArrayGraph.
Require Import CertiGraph.unionfind.env_unionfind_arr.
(*edgelist*)
Require Import CertiGraph.kruskal.WeightedEdgeListGraph.
Require Import CertiGraph.kruskal.spatial_wedgearray_graph.
Require Import CertiGraph.kruskal.kruskal_specs.
Require Import CertiGraph.graph.undirected_uf_lemmas.

Local Open Scope Z_scope.

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

(*************************************************************)

Context {size: Z}.

(*Moved this here because:
-universe inconsistency, proof is too long and I'm too tired to track it down
--the inconsistency comes from some bugger needing full parameters instead of referring
-requires one lemma from VST.floyd.proofauto.
-Ugly and specific to kruskal proof anyway
Application: t1 is the arbitrary spanning forest, t2 is our msf
*)
Lemma kruskal_minimal_induction:
forall ldiff lsame (g t1 t2: @EdgeListGG size) {fg: FiniteGraph g} {ft1: FiniteGraph t1} {ft2: FiniteGraph t2},
  labeled_spanning_uforest t1 g -> labeled_spanning_uforest t2 g ->
  Permutation (ldiff++lsame) (EList t1) -> incl lsame (EList t2) ->
  (forall e, In e ldiff -> ~ In e (EList t2)) ->
  (forall e, In e ldiff -> exists p l, connected_by_path t2 p (src t1 e) (dst t1 e) /\ NoDup p /\ fits_upath t2 l p /\ forall e', In e' l -> elabel g e' <= elabel g e) ->
  (forall i j, 0 <= i < j -> j < Zlength ldiff -> elabel g (Znth i ldiff) <= elabel g (Znth j ldiff)) ->
  exists lmsf, Zlength ldiff = Zlength lmsf /\ Permutation (lmsf++lsame) (EList t2) /\
      (forall i, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff))
  .
Proof.
induction ldiff; intros. rename H5 into Hsorted.
+(*nil case; no edges differ in t1. Then no edges should differ in t2*)
exists nil. split. auto.
rewrite app_nil_l in H1; rewrite app_nil_l.
assert (NoDup lsame). apply NoDup_Perm_EList in H1; auto.
split. apply NoDup_Permutation. auto. apply NoDup_EList.
intros; split; intros. apply H2; auto.
apply EList_evalid in H6. destruct x as [u v].
destruct (in_dec E_EqDec (u,v) lsame). auto.
(*u is connected to v in all graphs. So if u-v is not in lsame, exists another path in t1
Then, exists a list of edges l, fits_upath l p. All of l's edges must belong in EList t1, thus in lsame.
Thus, incl l t2. Which means connected_by_path t2 p u v. But (u,v) is an alternative path in t2. contra*)
assert (connected_by_path t2 (u::v::nil) u v).
  split. simpl. split. exists (u,v). split. apply evalid_strong_evalid; auto.
  left. rewrite (src_fst t2), (dst_snd t2) by auto. auto.
  apply evalid_uv_vvalid in H6. apply H6.
  simpl. split; auto.
assert (connected t1 u v). apply H. apply H0. exists (u::v::nil). auto. destruct H8 as [p ?].
pose proof (connected_exists_list_edges t1 p u v H8). destruct H9 as [l ?].
assert (~ In (u,v) l). unfold not; intros. (*If it were, then it is in lsame*)
  assert (evalid t1 (u,v)). apply (fits_upath_evalid t1 p l (u,v) H9 ). auto.
  rewrite <- EList_evalid in H11. apply (Permutation_in (l':=lsame)) in H11. contradiction.
  apply Permutation_sym. apply H1.
apply (sound_fits_upath_transfer  p l t1 t2) in H9; auto.
  2: { intros.
        rewrite <- (spanning_preserves_vertices g t1). apply (spanning_preserves_vertices g t2). apply H0. apply H. }
  2: { intros. assert (In e lsame). apply (Permutation_in (l:=(EList t1))). apply Permutation_sym. apply H1.
        apply EList_evalid. apply (fits_upath_evalid t1 p l); auto. rewrite <- EList_evalid. apply H2. auto. }
apply (forest_edge' p l t2 (u,v)) in H9. contradiction.
apply H0. apply H0. auto. rewrite (src_fst t2), (dst_snd t2) by auto. simpl. split.
apply valid_upath_exists_list_edges'. exists l; auto. apply H8.
intros. rewrite Zlength_nil in Hsorted. lia.
+ (*inductive step: there is at least one edge differing*)
rename H5 into Hsorted.
simpl in H2.
destruct a as (u1,v1).
assert (Ha: evalid t1 (u1,v1)). rewrite <- EList_evalid. apply (Permutation_in (l:=((u1, v1) :: ldiff ++ lsame))). apply H1. left; auto.
assert (Ht2_u1v1: ~ evalid t2 (u1,v1)). rewrite <- EList_evalid. apply H3. left; auto.
assert (H_NoDup_ldiff: NoDup ((u1,v1)::ldiff++lsame)). apply NoDup_Perm_EList in H1; auto.
(*In t1, a connects (u1,v1). In t2, (u1,v1) is also connected by some p2 l2. but since a isn't inside t2, a isn't inside l2.
If everything in l2 is in l1, then connected_by_path t1 p2 u1 v1 /\ fits_upath t1 p2 l2. Thus by forest_edge', In a l2. contra
Therefore, at least one edge must not be in l1*)
  assert (connected t2 u1 v1). apply H0. apply H. exists (u1::v1::nil).
    assert (connected_by_path t1 (src t1 (u1, v1) :: dst t1 (u1, v1) :: nil) (src t1 (u1, v1)) (dst t1 (u1, v1))).
    apply (trivial_path1 t1 (u1,v1)). apply evalid_strong_evalid; auto.
    rewrite (src_fst t1), (dst_snd t1) in H5 by auto. auto.
  destruct H5 as [p2' ?].
  assert (exists p', connected_by_path t2 p' u1 v1 /\ simple_upath t2 p').
  apply (connected_by_upath_exists_simple_upath t2 p2' u1 v1). auto.
  clear p2' H5. destruct H6 as [p2 [? ?]].
  assert (exists l2, fits_upath t2 l2 p2). apply (connected_exists_list_edges t2 p2 u1 v1). auto. destruct H7 as [l2 ?].
(*show that this path's edges are <= weight of (u1,v1)*)
assert (H_l2_weight: forall e, In e l2 -> elabel g e <= elabel g (u1,v1)). {
  intros. specialize H4 with ((u1,v1)).
  assert (exists (p : upath) (l : list EType),
         connected_by_path t2 p (src t1 (u1, v1)) (dst t1 (u1, v1)) /\
         NoDup p /\
         fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g (u1, v1))).
  apply H4. left; auto. destruct H9 as [p' [l' [? [? [? ?]]]]].
  rewrite (src_fst t1), (dst_snd t1) in H9 by auto. simpl in H9.
  assert (l' = l2). assert (unique_simple_upath t2). apply H0.
  assert (p' = p2). apply (H13 u1 v1 p' p2); auto. split. apply H9. apply H10.
  apply (uforest'_unique_lpath p2 l' l2 t2); auto. apply H0. rewrite <- H14; auto.
  apply H12. rewrite H13. auto.
}
(*now find the matching edge for a. I need ~forall -> exists...*)
assert (exists b, In b (EList t2) /\ ~ In b (EList t1) /\ bridge t2 b u1 v1). {
  (*main thing is just show In b l2 /\ ~ In b (EList t1).
  Do the ~ forall -> exists thing on l2.
  Then (prove and) use a lemma that every edge in a simple path of a uforest' is a bridge*)
  assert (exists b : EType, In b l2 /\ ~ In b (EList t1)). apply list_not_forall_exists.
  unfold not; intros. subst l2. destruct p2. destruct H5. destruct H8. inversion H8.
  destruct p2. destruct H5. destruct H8. inversion H8. inversion H9. subst u1; subst v1.
  (*means a is a self-loop, which is cannot be possible*)
  destruct H. destruct H. destruct H11. destruct H11. assert (src t1 (v, v) <> dst t1 (v, v)). auto.
  rewrite (src_fst t1), (dst_snd t1) in H14 by auto. contradiction.
  simpl in H7; auto.
  apply EList_In_dec.
  unfold not; intros.
  (*If everything in l2 is in l1, then connected_by_path t1 p2 u1 v1 /\ fits_upath t1 p2 l2.*)
  assert (fits_upath t1 l2 p2). apply (sound_fits_upath_transfer  p2 l2 t2 t1); auto.
  intros; split; intros. apply (spanning_preserves_vertices g). apply H. apply (spanning_preserves_vertices g t2). apply H0. auto.
  apply (spanning_preserves_vertices g). apply H0. apply (spanning_preserves_vertices g t1). apply H. auto.
  intros. rewrite <- EList_evalid. apply H8. auto.
  assert (connected_by_path t1 p2 u1 v1). split. apply valid_upath_exists_list_edges'. exists l2. auto. apply H5.
  assert (In (u1,v1) l2). apply (forest_edge' p2 l2 t1 (u1,v1)); auto. apply H. apply evalid_strong_evalid; auto.
  rewrite (src_fst t1), (dst_snd t1) by auto. auto.
  apply Ht2_u1v1. apply (fits_upath_evalid t2 p2 l2); auto.
  (*whew!*)
  destruct H8 as [b [? ?]].
  exists b. split. apply EList_evalid. apply (fits_upath_evalid t2 p2 l2); auto.
  split. auto.
  (*finally, the bridge...*)
  apply (forest_simple_bridge p2 l2); auto. apply H0.
}
destruct H8 as [b [? [? ?]]].
(*now show b <= a*)
assert (elabel g b <= elabel g (u1,v1)). {
  assert (exists (p : upath) (l : list EType),
       connected_by_path t2 p (src t1 (u1, v1)) (dst t1 (u1, v1)) /\
       NoDup p /\ fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g (u1, v1))).
  apply H4. left; auto. destruct H11 as [p [l ?]]. apply H11.
  unfold bridge in H10. apply (H10 p l).
  rewrite (src_fst t1), (dst_snd t1) in H11 by auto.
  apply H11. apply H11.
}
(*b is a bridge -> p can be split, and thus l can be split*)
pose proof (bridge_splittable p2 t2 u1 v1 b H5 H10). destruct H12 as [p2a [p2b [? ?]]].
assert (Hevalid_b: evalid t2 b). apply EList_evalid in H8; auto.
rewrite (src_fst t2), (dst_snd t2) in H13 by auto.
(*pose proof (fits_upath_split' t2 p2 l2).*)
assert (exists l2a l2x l2b : list EType,
        fits_upath t2 l2a p2a /\ fits_upath t2 l2b p2b /\ l2 = l2a ++ l2x ++ l2b).
apply (fits_upath_split t2 p2a p2b l2). rewrite <- H12. auto.
destruct H14 as [l2a [l2x [l2b [? [? ?]]]]].
destruct b as (u2,v2). simpl in H13.
pose proof (size_bound g) as size_bound.
assert (Hu1: 0 <= u1 < size). rewrite <- (vertex_valid t1). apply evalid_uv_vvalid in Ha; apply Ha.
assert (Hv1: 0 <= v1 < size). rewrite <- (vertex_valid t1). apply evalid_uv_vvalid in Ha; apply Ha.
assert (Hw1: Int.min_signed <= (elabel t1 (u1, v1)) <= Int.max_signed). apply weight_valid; auto.
(*prepare for reasoning about swap*)
set (remove:=(@EdgeListGG_eremove size size_bound t2 (u2,v2))).
set (swap:=(@EdgeListGG_adde size size_bound remove u1 v1 (elabel t1 (u1, v1))) Hu1 Hv1 Hw1).
assert (Hevalid_swap_u1v1: evalid swap (u1,v1)). simpl. unfold addValidFunc, removeValidFunc. right; auto.
set (fswap:=finite swap).

assert (Hnew: exists p l, connected_by_path swap p u2 v2 /\ fits_upath swap l p
/\ In (u1,v1) l /\ forall e', In e' l -> elabel g e' <= elabel g (u1,v1)). {
(*WLOG, used to be u1--u2--v2--v1
After swap, exists u2--u1--v1--v2*)
destruct H13; destruct H13.
+
exists ((rev p2a)++(rev p2b)). exists (rev l2a ++ (u1,v1)::nil ++ rev l2b).
assert (fits_upath swap (rev l2a ++ (u1, v1) :: nil ++ rev l2b) (rev p2a ++ rev p2b)). {
  apply (fits_upath_app swap (rev p2a) (rev p2b) (rev l2a) (rev l2b) (u1,v1) u1 v1).
  apply fits_upath_rev. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2a l2a); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2a (u2,v2) l2a) in H18.
    rewrite (src_fst t2), (dst_snd t2) in H18 by auto. simpl in H18; destruct H18.
    assert (NoDup p2). apply H6. rewrite H12 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 v2). auto. apply hd_error_In. apply H17. auto.
  apply fits_upath_rev. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2b l2b); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2b (u2,v2) l2b) in H18.
    rewrite (src_fst t2), (dst_snd t2) in H18 by auto. simpl in H18; destruct H18.
    assert (NoDup p2). apply H6. rewrite H12 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 u2). auto. apply last_error_In. apply H13. auto. auto.
  rewrite <- rev_hd_last. apply H13.
  rewrite rev_hd_last, rev_involutive. apply H17.
  split. apply add_edge_strong_evalid.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H5.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H5.
    left. rewrite (src_fst swap), (dst_snd swap); auto.
}
split. split. apply valid_upath_exists_list_edges'.
exists (rev l2a ++ (u1, v1) :: nil ++ rev l2b); auto.
split. apply (hd_error_app (rev p2b) (rev p2a) u2). rewrite rev_hd_last, rev_involutive. apply H13.
apply (last_err_app (rev p2a) (rev p2b) v2). rewrite <- rev_hd_last. apply H17.
split. auto. split. simpl. apply in_or_app. right; left; auto.
  intros. apply in_app_or in H19. destruct H19. apply in_rev in H19. apply H_l2_weight.
  rewrite H16. apply in_or_app. left; auto.
  simpl in H19. destruct H19. subst e'. lia. apply in_rev in H19. apply H_l2_weight.
  rewrite H16. apply in_or_app. right; apply in_or_app. auto.
+(*near repeat*)
exists (p2b++p2a). exists (l2b ++ (u1,v1)::nil ++ l2a).
assert (fits_upath swap (l2b ++ (u1, v1) :: nil ++ l2a) (p2b ++ p2a)). {
  apply (fits_upath_app swap (p2b) (p2a) l2b (l2a) (u1,v1) v1 u1).
  apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2b l2b); auto.
  unfold not; intros.
    subst e. apply (fits_upath_vertex_in_path t2 p2b (u2,v2) l2b) in H18.
    rewrite (src_fst t2), (dst_snd t2) in H18 by auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H6. rewrite H12 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 v2). auto. apply last_error_In. apply H13. auto. auto.
  apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split. apply (fits_upath_evalid t2 p2a l2a); auto.
  unfold not; intros. (*both u2 and v2 are in p2a, which means p2 has a Dup of v2*)
    subst e. apply (fits_upath_vertex_in_path t2 p2a (u2,v2) l2a) in H18.
    rewrite (src_fst t2), (dst_snd t2) in H18 by auto. simpl in H18. destruct H18.
    assert (NoDup p2). apply H6. rewrite H12 in H20. pose proof (NoDup_app_not_in VType p2a p2b H20).
    apply (H21 u2).  auto. apply hd_error_In. apply H17. auto.
  apply H17. apply H13.
  split. apply add_edge_strong_evalid.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H5.
    simpl. apply (connected_vvalid t2 u1 v1). exists p2; apply H5.
    right. rewrite (src_fst swap), (dst_snd swap); auto.
}
split. split. apply valid_upath_exists_list_edges'.
exists (l2b ++ (u1, v1) :: nil ++ l2a); auto.
split. apply hd_error_app. apply H17.
apply last_err_app. apply H13.
split. auto. split. simpl. apply in_or_app. right; left; auto.
  intros. apply in_app_or in H19. destruct H19. apply H_l2_weight.
  rewrite H16. apply in_or_app. right. apply in_or_app. auto.
  simpl in H19. destruct H19. subst e'. lia. apply H_l2_weight.
  rewrite H16. apply in_or_app. left; auto.
} destruct Hnew as [p' [l' Hnew]].
set (b:=(u2,v2)).
(*specialize inductive step with (t2 + a - b). It's a "step" closer to t2 and it's diff edges are in ldiff.
By induction, exists lmsf containing t2's diff edges*)
specialize IHldiff with ((u1,v1)::lsame) g t1 swap ft1 fswap.
assert (exists lmsf : list EType,
            Zlength ldiff = Zlength lmsf /\
            Permutation (lmsf ++ (u1, v1) :: lsame) (EList swap) /\
            (forall i : Z, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff))).
apply IHldiff; clear IHldiff. (*BEGONE*)
auto. auto. auto.
{ split. split.
(*partial graph*) {
  split. intros. simpl in H17. apply (spanning_preserves_vertices g t2). apply H0. auto.
  split. intros. simpl in H17. unfold addValidFunc, removeValidFunc in H17. destruct H17.
    destruct H17. apply H0. auto.
    apply H. rewrite H17. auto.
  split. simpl. unfold addValidFunc, removeValidFunc, updateEdgeFunc, EquivDec.equiv_dec. intros.
    destruct (E_EqDec (u1, v1) e). unfold Equivalence.equiv in e0. subst e. rewrite (src_fst g). auto. apply H. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. destruct H17. destruct H17. apply H0. auto. auto. symmetry in H17; contradiction.
  simpl. unfold addValidFunc, removeValidFunc, updateEdgeFunc, EquivDec.equiv_dec. intros.
    destruct (E_EqDec (u1, v1) e). unfold Equivalence.equiv in e0. subst e. rewrite (dst_snd g); auto. apply H. auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. destruct H17. destruct H17. apply H0. auto. auto. symmetry in H17; contradiction.
} split.
(*uforest'*) {
  assert (uforest' remove /\ ~ connected remove (src t2 b) (dst t2 b)).
  apply (remove_edge_uforest' t2 b). auto. apply H0. apply EList_evalid in H8. auto.
  destruct H17. apply add_edge_uforest'. auto.
  simpl. apply (spanning_preserves_vertices g t2). apply H0. apply (spanning_preserves_vertices g t1). apply H.
  apply evalid_uv_vvalid in Ha; apply Ha.
  simpl. apply (spanning_preserves_vertices g t2). apply H0. apply (spanning_preserves_vertices g t1). apply H.
  apply evalid_uv_vvalid in Ha; apply Ha.
  (*need an eremove_bridge*)
  unfold not, connected; intros. destruct H19 as [p ?].
  pose proof (connected_exists_list_edges remove p u1 v1 H19). destruct H20 as [l ?].
  assert (fits_upath t2 l p). apply (sound_fits_upath_transfer p l _ t2) in H20. auto.
  simpl; intros; split; auto.
  intros. apply (fits_upath_evalid _ p l e H20) in H21.
  simpl in H21. unfold removeValidFunc in H21. apply H21.
  assert (connected_by_path t2 p u1 v1). split. apply valid_upath_exists_list_edges'. exists l. auto. apply H19.
  assert (In b l). apply (H10 p l). auto. auto.
  assert (evalid remove b). apply (fits_upath_evalid _ p l). auto. auto.
  pose proof (eremove_evalid1 H24). auto.
}
(*spanning*) {
  unfold spanning; intros. assert (spanning t2 g). apply H0. unfold spanning in H17. rewrite H17. clear H17.
  split; intros; destruct H17 as [p ?]. (*force it into a simple upath to deal with only one edge*)
  (*-------------->*)
  pose proof (connected_by_upath_exists_simple_upath t2 p u v H17).
  clear p H17. destruct H18 as [p [? ?]].
  assert (exists l, fits_upath t2 l p). apply (connected_exists_list_edges t2 p u v); auto.
  destruct H19 as [l ?].
  (*Was (u2,v2) inside?*)
  destruct (in_dec E_EqDec (u2,v2) l).
  (*yes: split into l1++(u2,v2)++l2, p1++p2. replace with (u2,v2) with l'*)
  unfold b; fold swap. assert (HNoDup_l: NoDup l). apply (simple_upath_list_edges_NoDup t2 p l); auto.
  pose proof (fits_upath_split' t2 p l (u2,v2) H19 i). destruct H20 as [pb1 [pb2 [lb1 [lb2 ?]]]].
  {
  destruct H20 as [? [? [? [? ?]]]].
  rewrite (src_fst t2), (dst_snd t2) in H21 by auto. destruct H21; simpl in H21.
  (*it's a pain to declare the full path, so use transitivity
  Hm, could I have simplified the previous proofs?*)
  (*connected swap pb1 u u2*)
  assert (Hc1: connected swap u u2). exists pb1. split. apply valid_upath_exists_list_edges'.
    exists lb1. apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H24. apply in_or_app. left; auto.
    unfold not; intros. rewrite H24 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H25. apply H25. left; auto.
    destruct H21. destruct pb1. inversion H21. destruct H17. rewrite H20 in H26. destruct H26; inversion H26.
    subst v0. simpl; auto.
  assert (Hc2: connected swap u2 v2). exists p'; apply Hnew.
  assert (Hc3: connected swap v2 v). exists pb2. split. apply valid_upath_exists_list_edges'.
    exists lb2. apply (sound_fits_upath_transfer pb2 lb2 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H24. apply in_or_app. right. apply in_or_app. right; auto.
    unfold not; intros. rewrite H24 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
    split. apply H21. destruct pb2. destruct H21. inversion H25.
    rewrite <- (last_err_split2 pb1 pb2 v0). rewrite <- H20. apply H17.
  apply (connected_trans swap u v2 v); auto. apply (connected_trans swap u u2 v2); auto.
  (*repeat...*)
  assert (Hc1: connected swap u v2). exists pb1. split. apply valid_upath_exists_list_edges'.
    exists lb1. apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H24. apply in_or_app. left; auto.
    unfold not; intros. rewrite H24 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H25. apply H25. left; auto.
    destruct H21. destruct pb1. inversion H21. destruct H17. rewrite H20 in H26. destruct H26; inversion H26.
    subst v0. simpl; auto.
  assert (Hc3: connected swap u2 v). exists pb2. split. apply valid_upath_exists_list_edges'.
    exists lb2. apply (sound_fits_upath_transfer pb2 lb2 t2 swap); auto. intros; simpl; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
    apply (fits_upath_evalid t2 p l). auto. rewrite H24. apply in_or_app. right. apply in_or_app. right; auto.
    unfold not; intros. rewrite H24 in HNoDup_l. simpl in HNoDup_l.
    subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
    split. apply H21. destruct pb2. destruct H21. inversion H25.
    rewrite <- (last_err_split2 pb1 pb2 v0). rewrite <- H20. apply H17.
  apply (connected_trans swap u u2 v); auto. apply (connected_trans swap u v2 u2); auto. apply connected_symm. exists p'. apply Hnew.
  }
  (*no: it can't have gone through (u1,v1) which isn't in t2, therefore unaffected*)
  exists p. split. apply add_edge_valid_upath.
    unfold not; simpl; unfold removeValidFunc; intros. destruct H20; contradiction.
  apply (remove_edge_valid_upath _ _ p l); auto. apply H17. apply H17.
  (*<----------------------*)
  pose proof (connected_by_upath_exists_simple_upath swap p u v H17).
  clear p H17. destruct H18 as [p [? ?]].
  assert (exists l, fits_upath swap l p). apply (connected_exists_list_edges swap p u v); auto.
  destruct H19 as [l ?].
  (*does it go through (u1,v1)*)
  destruct (in_dec E_EqDec (u1,v1) l).
  (*yes: split into la1++... replace (u1,v1) with l2*)
  assert (HNoDup_l: NoDup l). apply (simple_upath_list_edges_NoDup swap p l); auto.
  pose proof (fits_upath_split' swap p l (u1,v1) H19 i). destruct H20 as [pa1 [pa2 [la1 [la2 ?]]]].
  {
    destruct H20 as [? [? [? [? ?]]]].
    rewrite (src_fst swap), (dst_snd swap) in H21 by auto. destruct H21; simpl in H21.
    (*assert connectedness*)
    assert (Hc1: connected t2 u u1). exists pa1. split. apply valid_upath_exists_list_edges'.
      exists la1. apply (sound_fits_upath_transfer pa1 la1 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l); auto. rewrite H24. apply in_or_app. left; auto.
      simpl in H26. unfold addValidFunc, removeValidFunc in H26. destruct H26. apply H26.
      rewrite H24 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H25. exfalso. apply H25. left; auto.
      destruct H21. destruct pa1. inversion H21. destruct H17. rewrite H20 in H26. destruct H26; inversion H26.
      subst v0. simpl; auto.
    assert (Hc3: connected t2 v1 v). exists pa2. split. apply valid_upath_exists_list_edges'.
      exists la2. apply (sound_fits_upath_transfer pa2 la2 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H24. apply in_or_app. right. apply in_or_app. right; auto.
      simpl in H26. unfold addValidFunc, removeValidFunc in H26. destruct H26. apply H26.
      rewrite H24 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
      split. apply H21. destruct pa2. destruct H21. inversion H25.
      rewrite <- (last_err_split2 pa1 pa2 v0). rewrite <- H20. apply H17.
      apply (connected_trans t2 u v1 v); auto. apply (connected_trans t2 u u1 v1); auto.
      exists p2. auto.
    (*repeat...*)
    assert (Hc1: connected t2 u v1). exists pa1. split. apply valid_upath_exists_list_edges'.
      exists la1. apply (sound_fits_upath_transfer pa1 la1 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H24. apply in_or_app. left; auto.
      simpl in H26. unfold addValidFunc, removeValidFunc in H26. destruct H26. apply H26.
      rewrite H24 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply (NoDup_app_not_in _ _ _ HNoDup_l) in H25. exfalso. apply H25. left; auto.
      destruct H21. destruct pa1. inversion H21. destruct H17. rewrite H20 in H26. destruct H26; inversion H26.
      subst v0. simpl; auto.
    assert (Hc2: connected t2 v1 u1). apply connected_symm. exists p2; auto.
    assert (Hc3: connected t2 u1 v). exists pa2. split. apply valid_upath_exists_list_edges'.
      exists la2. apply (sound_fits_upath_transfer pa2 la2 swap t2); auto. intros; simpl; split; auto.
      intros. assert (evalid swap e). apply (fits_upath_evalid swap p l). auto. rewrite H24. apply in_or_app. right. apply in_or_app. right; auto.
      simpl in H26. unfold addValidFunc, removeValidFunc in H26. destruct H26. apply H26.
      rewrite H24 in HNoDup_l. simpl in HNoDup_l.
      subst e. apply NoDup_app_r in HNoDup_l. apply NoDup_cons_2 in HNoDup_l. contradiction.
      split. apply H21. destruct pa2. destruct H21. inversion H25.
      rewrite <- (last_err_split2 pa1 pa2 v0). rewrite <- H20. apply H17.
      apply (connected_trans t2 u u1 v); auto. apply (connected_trans t2 u v1 u1); auto.
  }
  (*no: unaffected*)
  exists p. split. apply (add_edge_unaffected _ (u1,v1) u1 v1 p l) in H19.
  apply (remove_edge_unaffected t2 (u2,v2)) in H19. auto.
  apply valid_upath_exists_list_edges'. exists l; auto. auto. apply H17.
}
split.
(*preserve vlabel*)
unfold preserve_vlabel; intros. destruct vlabel. destruct vlabel. auto.
(*preserve elabel*)
unfold preserve_elabel; intros. simpl in H17. unfold addValidFunc, removeValidFunc in H17.
simpl. unfold update_elabel. unfold EquivDec.equiv_dec. destruct E_EqDec.
unfold Equivalence.equiv in e0. subst e. apply H. auto.
unfold RelationClasses.complement, Equivalence.equiv in c. destruct H17.
apply H0. apply H17. symmetry in H17. contradiction.
}
(*Permutation of EList t1*)
apply (Permutation_trans (l':=((u1, v1) :: ldiff ++ lsame))). 2: auto.
apply (Permutation_trans (l':=((u1, v1) :: lsame ++ ldiff))). apply Permutation_app_comm.
apply perm_skip. apply Permutation_app_comm.
(*incl*)
unfold incl; intros.
apply EList_evalid. simpl. unfold addValidFunc, removeValidFunc.
destruct H17. right; auto.
left; split. apply H2 in H17. apply EList_evalid in H17. auto.
unfold not; intros. subst a. apply H9. apply (Permutation_in (l:=((u1, v1) :: ldiff ++ lsame))). auto.
right. apply in_or_app. right; auto.
(*In e ldiff -> ~ In e swapped_graph*)
intros. rewrite EList_evalid. simpl. unfold addValidFunc, removeValidFunc, not; intros.
destruct H18. destruct H18. rewrite <- EList_evalid in H18. apply H3 in H18. auto. right; auto.
subst e.
apply NoDup_cons_2 in H_NoDup_ldiff. apply H_NoDup_ldiff. apply in_or_app. left; auto.
(*weight*) {
intros. unfold b; fold swap.
assert (exists (p : upath) (l : list EType),
       connected_by_path t2 p (src t1 e) (dst t1 e) /\
       NoDup p /\ fits_upath t2 l p /\ (forall e' : EType, In e' l -> elabel g e' <= elabel g e)).
apply H4. right; auto. destruct H18 as [p [l [? [? [? ?]]]]].
(*is (u2,v2) in l?*)
destruct (in_dec E_EqDec (u2,v2) l).
(*yes: split*)
+
pose proof (fits_upath_split' t2 p l (u2,v2) H20 i).
destruct H22 as [pb1 [pb2 [lb1 [lb2 ?]]]]. destruct H22 as [? [? [? [? ?]]]].
assert (Hl: NoDup l). apply (simple_upath_list_edges_NoDup t2 p). split. apply H18. auto. auto.
rewrite (src_fst t2), (dst_snd t2) in H23 by auto. simpl in H23.
set (u:=src t1 e). set (v:=dst t1 e).
destruct H23; destruct H23.
++ (*pb1 --- u2 -- v2 -- pb2*)
set (pnew:=(pb1 ++ (tail p') ++ (tail pb2))). set (lnew:=(lb1++l'++lb2)).
(*first settle that the vertices match*)
assert (Hpb1: last_error pb1 = hd_error p'). { rewrite H23. symmetry. apply Hnew. }
assert (Hpb2: last_error p' = hd_error pb2). { rewrite H27. apply Hnew. }
assert (fits_upath swap lnew pnew). {
  unfold pnew, lnew. destruct l'. destruct Hnew as [? [? [? ?]]]. contradiction.
  destruct p'. destruct Hnew as [? [? [? ?]]]. contradiction.
  destruct p'. destruct Hnew as [? [? [? ?]]]. simpl in H25; contradiction.
  replace (lb1 ++ (e0 :: l') ++ lb2)  with (lb1 ++ (e0 :: nil) ++ (l'++lb2)). 2: simpl; auto.
  apply (fits_upath_app _ _ _ _ _ e0 u2 v3).
  -apply (sound_fits_upath_transfer pb1 lb1 t2 swap); auto. simpl. intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 pb1 lb1); auto. unfold not; intros. subst e1.
  rewrite H26 in Hl. apply (NoDup_app_not_in _ _ _ Hl) in H28. apply H28. simpl; left; auto.
  -destruct pb2. inversion H27. destruct pb2. destruct lb2.
  simpl. do 2 rewrite app_nil_r. simpl in H27; inversion H27. subst v4. apply Hnew.
  destruct Hnew as [? [? [? ?]]]. simpl in H25. contradiction.
  destruct lb2. destruct Hnew as [? [? [? ?]]]. simpl in H25. contradiction.
  apply (fits_upath_app _ _ _ _ _ e1 v2 v5). apply Hnew.
  apply (sound_fits_upath_transfer _ _ t2 swap); auto. simpl; intros; split; auto.
    intros. simpl. unfold addValidFunc, removeValidFunc. left; split.
    apply (fits_upath_evalid t2 (v4::v5::pb2) (e1::lb2)); auto. right; auto.
    unfold not; intros. subst e2. rewrite H26 in Hl. apply NoDup_app_r in Hl.
    apply (NoDup_app_not_in EType ((u2,v2)::nil) (e1::lb2) Hl (u2,v2)). left; auto.
    right; auto. apply H25. simpl. apply Hnew. simpl; auto. simpl in H27; inversion H27. subst v4. destruct H25.
    assert (evalid t2 e1). apply (fits_upath_evalid t2 p l); auto.
    rewrite H26. apply in_or_app. right. apply in_or_app. right. left; auto.
  split. split. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply H25. unfold not; intros. subst e1. rewrite H26 in Hl. apply NoDup_app_r in Hl.
  apply (NoDup_app_not_in EType ((u2,v2)::nil) ((u2,v2)::lb2) Hl (u2,v2)). left; auto. left; auto.
  simpl. unfold updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
  unfold Equivalence.equiv in e2. subst e1. contradiction.
  apply evalid_strong_evalid in H29; auto. apply H29.
  simpl. unfold updateEdgeFunc. unfold EquivDec.equiv_dec. destruct E_EqDec.
  unfold Equivalence.equiv in e2. subst e1. contradiction. apply H25.
  -auto.
  -simpl. auto.
  -destruct Hnew as [? [? [? ?]]]. destruct H29. destruct H28. destruct H33. simpl in H33; inversion H33. subst v0. apply H29.
}
assert (connected_by_path swap pnew u v). split. apply valid_upath_exists_list_edges'.
  exists lnew; auto.
  unfold pnew; split. destruct H18. rewrite H22 in H29; destruct H29.
  destruct pb1. inversion H23. simpl in H29. simpl. auto.
  destruct pb2. inversion H27. destruct pb2. simpl in Hpb2. simpl in H27. inversion H27. subst v0.
  destruct H18. destruct H29. rewrite H22 in H30. rewrite last_err_appcons in H30. inversion H30.
  simpl. rewrite app_nil_r. unfold v; rewrite <- H32. subst v2.
  destruct Hnew as [? [? [? ?]]].
  destruct p'. inversion Hpb2. destruct p'. destruct l'. contradiction. simpl in H32; contradiction.
  simpl. rewrite last_error_cons in Hpb2. apply last_err_app. auto. unfold not; intros. inversion H35.
  simpl. apply last_err_app. apply last_err_app. destruct H18. destruct H29.
  rewrite H22 in H30. rewrite last_err_split2 in H30. rewrite last_error_cons in H30. auto.
  unfold not; intros. inversion H31.
assert (forall e' : EType, In e' lnew -> elabel g e' <= elabel g e).
  unfold lnew; intros. apply in_app_or in H30. destruct H30.
  apply H21. rewrite H26. apply in_or_app. left; auto.
  apply in_app_or in H30; destruct H30.
  apply (Z.le_trans _ (elabel g (u1,v1)) _). apply Hnew. auto.
(*In_Znth_iff requires floyd... ideally move the whole proof to verif kruskal, or create a copy of the lemma in list_ext...*)
assert (In e ((u1, v1) :: ldiff)). right; auto.
apply In_Znth_iff in H31. destruct H31 as [i' [? ?]]. rewrite <- H32.
replace (u1,v1) with (Znth 0 ((u1,v1)::ldiff)). 2: apply Znth_0_cons.
destruct (Z.lt_trichotomy 0 i').
apply Hsorted. lia. apply H31. destruct H33.
subst i'. do 2 rewrite Znth_0_cons. lia. lia.
apply H21. rewrite H26. apply in_or_app. right; right; auto.
(*now simplify*)
pose proof (upath_simplifiable_edges swap pnew lnew u v H29 H28).
destruct H31 as [psim [lsim [? [? [? [? ?]]]]]]. exists psim; exists lsim.
split. auto. split. apply H32. split. apply H34. intros. apply H30. apply H35. apply H36.
(*repeat...*)
++
 (*pb1 --- v2 -- u2 -- pb2*)
set (pnew:=(pb1 ++ (tail (rev p')) ++ (tail pb2))). set (lnew:=(lb1++(rev l')++lb2)).
(*first settle that the vertices match*)
assert (Hpb1: last_error pb1 = hd_error (rev p')). {
rewrite H23. symmetry. rewrite rev_hd_last, rev_involutive. apply Hnew.
}
assert (Hpb2: last_error (rev p') = hd_error pb2). {
  rewrite H27. rewrite <- rev_hd_last. apply Hnew.
}
assert (fits_upath swap lnew pnew). {
  unfold pnew, lnew. destruct Hnew as [? [? [? ?]]].
  assert (connected_by_path swap (rev p') v2 u2). split. apply valid_upath_rev. apply H28.
  split. rewrite rev_hd_last, rev_involutive. apply H28. rewrite <- rev_hd_last; apply H28.
  assert (fits_upath swap (rev l') (rev p')). apply fits_upath_rev. auto.
  assert (In (u1,v1) (rev l')). apply in_rev. rewrite rev_involutive. auto.
  destruct (rev l'). contradiction. destruct (rev p'). simpl in H33; contradiction.
  destruct l1. simpl in H33; contradiction.
  replace (lb1 ++ (e0 :: l0) ++ lb2) with (lb1 ++ (e0::nil) ++ (l0++lb2)). 2: simpl; auto.
  apply (fits_upath_app _ _ _ _ _ e0 v2 v3).
-apply (sound_fits_upath_transfer _ _ t2 swap); auto. simpl; intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 p l). auto. rewrite H26. apply in_or_app. left; auto.
  unfold not; intros. subst e1.
  assert (~ In (u2,v2) ((u2, v2) :: nil ++ lb2)). apply (NoDup_app_not_in EType lb1 (((u2,v2)::nil)++lb2)).
  simpl. rewrite H26 in Hl. simpl in Hl. auto. auto. apply H36. left; auto.
-destruct pb2. inversion H27. destruct pb2. destruct lb2.
  simpl. do 2 rewrite app_nil_r. simpl in H27; inversion H27. subst v4. apply H33.
  simpl in H25. contradiction. rename l1 into revp'.
  destruct lb2. simpl in H25. contradiction.
  apply (fits_upath_app _ _ _ _ _ e1 u2 v5).
  simpl. apply H33. apply (sound_fits_upath_transfer _ _ t2 swap); auto.
  simpl; intros; split; auto.
  intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
  apply (fits_upath_evalid t2 p l). auto. rewrite H26. apply in_or_app. right. apply in_or_app. right. right; auto.
  unfold not; intros. subst e2. rewrite H26 in Hl; simpl in Hl. apply NoDup_app_r in Hl.
  apply NoDup_cons_2 in Hl. apply Hl. right; auto.
  apply H25.
  rewrite H27 in Hpb2. apply Hpb2.
  simpl; auto.
  assert (evalid swap e1). simpl. unfold addValidFunc, removeValidFunc.
  left. split. apply H25. unfold not; intros. subst e1. rewrite H26 in Hl. simpl in Hl.
  apply NoDup_app_r in Hl. apply NoDup_cons_2 in Hl. apply Hl. left; auto.
  destruct H25. simpl in H27. inversion H27. subst v4. destruct H25.
  split. apply evalid_strong_evalid; auto.
  rewrite (src_fst swap), (dst_snd swap); auto.
  simpl in H35. unfold addValidFunc, removeValidFunc in H35. destruct H35.
  destruct H35. rewrite (src_fst t2), (dst_snd t2) in H37; auto.
  exfalso. subst e1. destruct H25. contradiction.
-auto.
-simpl. auto.
-destruct H33. rewrite H23 in Hpb1. simpl in Hpb1. inversion Hpb1. auto.
}
assert (connected_by_path swap pnew u v). split. apply valid_upath_exists_list_edges'.
  exists lnew; auto.
  unfold pnew; split. destruct H18. rewrite H22 in H29; destruct H29.
  destruct pb1. inversion H23. simpl in H29. simpl. auto.
  destruct pb2. inversion H27. destruct pb2. simpl in Hpb2. simpl in H27. inversion H27. subst v0.
  destruct H18. destruct H29. rewrite H22 in H30. rewrite last_err_appcons in H30. inversion H30.
  simpl. rewrite app_nil_r. unfold v; rewrite <- H32. subst u2.
  destruct Hnew as [? [? [? ?]]].
  destruct (rev p') eqn:revp. inversion Hpb2. destruct l0. destruct l'. contradiction.
  assert (p' = v0::nil). symmetry. rewrite <- rev_involutive. rewrite revp. simpl; auto. rewrite H35 in H32. contradiction.
  simpl. rewrite last_err_split2. apply Hpb2.
  simpl. rewrite app_assoc. rewrite last_err_split2. destruct H18. destruct H29. rewrite H22 in H30.
  rewrite last_err_split2 in H30. apply H30.
assert (forall e' : EType, In e' lnew -> elabel g e' <= elabel g e).
  unfold lnew; intros. apply in_app_or in H30. destruct H30.
  apply H21. rewrite H26. apply in_or_app. left; auto.
  apply in_app_or in H30; destruct H30.
  apply (Z.le_trans _ (elabel g (u1,v1)) _). apply Hnew. apply in_rev. auto.
(*In_Znth_iff requires floyd... move the whole proof to verif kruskal...*)
assert (In e ((u1, v1) :: ldiff)). right; auto.
apply In_Znth_iff in H31. destruct H31 as [i' [? ?]]. rewrite <- H32.
replace (u1,v1) with (Znth 0 ((u1,v1)::ldiff)). 2: apply Znth_0_cons.
destruct (Z.lt_trichotomy 0 i').
apply Hsorted. lia. apply H31. destruct H33.
subst i'. do 2 rewrite Znth_0_cons. lia. lia.
apply H21. rewrite H26. apply in_or_app. right; right; auto.
(*now simplify*)
pose proof (upath_simplifiable_edges swap pnew lnew u v H29 H28).
destruct H31 as [psim [lsim [? [? [? [? ?]]]]]]. exists psim; exists lsim.
split. auto. split. apply H32. split. apply H34. intros. apply H30. apply H35. apply H36.
+
(*no: not affected*)
exists p. exists l.
assert (fits_upath swap l p). apply (sound_fits_upath_transfer _ _ t2 swap); auto.
simpl. intros; split; auto.
intros. simpl. unfold addValidFunc, removeValidFunc. left. split.
apply (fits_upath_evalid t2 p l); auto.
unfold not; intros. subst e0. contradiction.
split. split. apply valid_upath_exists_list_edges'.
exists l; auto. apply H18.
split. auto. split. auto.
auto.
}
intros. specialize Hsorted with (i+1) (j+1).
replace (Znth i ldiff) with (Znth (i+1) ((u1,v1)::ldiff)).
replace (Znth j ldiff) with (Znth (j+1) ((u1,v1)::ldiff)). apply Hsorted.
lia. rewrite Zlength_cons. lia. rewrite Znth_pos_cons. rewrite Z.add_simpl_r. auto.
lia. rewrite Znth_pos_cons. rewrite Z.add_simpl_r. auto. lia.

(*finally*)
destruct H17 as [lmsf [? [? ?]]].
exists (b::lmsf). split.
do 2 rewrite Zlength_cons. rewrite H17. auto. split.

assert (Permutation ((u1,v1)::lmsf++lsame) (EList swap)). apply (Permutation_trans (l':=(lmsf ++ (u1, v1) :: lsame))).
apply Permutation_middle. auto.
pose proof (finite remove) as fremove.
apply adde_EList_rev in H20.
apply (@eremove_EList_rev size size_bound t2 (u2,v2) Hevalid_b) in H20. unfold b; simpl. (*apply H20.*)
(*finiteGraph issues again*)
apply (Permutation_trans H20).
apply NoDup_Permutation. apply NoDup_EList. apply NoDup_EList. intros; rewrite EList_evalid; rewrite EList_evalid; split; auto.
unfold not; intros. destruct H21.
assert (~ In (u1,v1) (EList t2)). apply H3. left; auto. rewrite EList_evalid in H23. contradiction.

intros. rewrite Zlength_cons in H20. destruct (Z.lt_trichotomy i 0). lia. destruct H21.
subst i. do 2 rewrite Znth_0_cons. unfold b; auto.
do 2 rewrite Znth_pos_cons by lia. apply H19. split. lia.
destruct H20.
apply (Z.sub_lt_mono_r i (Z.succ (Zlength lmsf)) 1) in H22.
replace (Z.succ (Zlength lmsf) - 1) with (Zlength lmsf) in H22. auto.
lia.
Qed.

(*******************************BODY OF IMPLEMENTATIONS*****************************)

Lemma body_fill_edge: semax_body Vprog (@Gprog size) f_fill_edge fill_edge_spec.
Proof.
start_function.
forward. forward. forward. entailer!.
Qed.

Lemma body_init_empty_graph: semax_body Vprog (@Gprog size) f_init_empty_graph init_empty_graph_spec.
Proof.
start_function.
forward_call (gv, sh, sizeof t_wedgearray_graph).
Intros gptr.
assert (memory_block sh (sizeof t_wedgearray_graph) gptr =
        data_at_ sh (t_wedgearray_graph) gptr). {
  rewrite <- memory_block_data_at_; auto.
}
rewrite H0. clear H0.
assert (data_at_ sh t_wedgearray_graph gptr =
        data_at sh t_wedgearray_graph (Vundef,(Vundef,Vundef)) gptr). {
  unfold data_at_, field_at_, data_at.
  assert (default_val (nested_field_type t_wedgearray_graph []) = (Vundef,(Vundef,Vundef))) by reflexivity.
  rewrite H0. auto.
} rewrite H0. clear H0. (*that was easier than I thought :]*)
assert_PROP (isptr gptr). entailer!.
rename H0 into Hgptr. destruct gptr; inversion Hgptr. set (gptr:=ValidPointer b i).
forward.
forward_call (gv, sh, MAX_EDGES*(sizeof t_struct_edge)).
Intros eptr.
assert (memory_block sh (MAX_EDGES * (sizeof t_struct_edge)) eptr = data_at_ sh (tarray t_struct_edge MAX_EDGES) eptr). {
  assert (memory_block sh (MAX_EDGES*(sizeof t_struct_edge)) eptr = memory_block sh (sizeof (tarray t_struct_edge MAX_EDGES)) eptr). {
    simpl. auto.
  } rewrite <- memory_block_data_at_; auto.
} rewrite H1. clear H1.
assert (data_at_ sh (tarray t_struct_edge MAX_EDGES) eptr = data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges MAX_EDGES) eptr). {
  unfold data_at_, field_at_, data_at. assert (default_val (nested_field_type (tarray t_struct_edge MAX_EDGES) []) = repeat (Vundef, (Vundef, Vundef)) (Z.to_nat MAX_EDGES)) by reflexivity.
  rewrite H1. auto.
} rewrite H1. clear H1.
assert_PROP (isptr eptr). entailer!.
rename H0 into Heptr. destruct eptr; inversion Heptr. set (eptr:=ValidPointer b0 i0).
forward.
forward.
forward.
forward.
forward.
Exists gptr eptr.
entailer!.
Qed.

Lemma body_kruskal: semax_body Vprog (@Gprog size) f_kruskal (@kruskal_spec size).
Proof.
  start_function. rename H into Hpre1. rename H0 into Hpre2. rename H1 into Hpre3.
  pose proof (size_bound g) as size_bound.
  forward. forward.
  (*call MakeSet*)
  forward_call (gv, sh, size). Intros subsetsPtr.
  (*malloc mst*)
  forward_call (gv, sh). Intros mst.
  destruct mst as [gptr eptr]. simpl fst in *. simpl snd in *.
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
  forward_call ((*wshare_share sh*) sh, 
                pointer_val_val orig_eptr,
                (map wedge_to_cdata glist)).
  Intros sorted.
  (* some trivial assertions about sorted for convenience *)
  assert_PROP (isptr (pointer_val_val eptr)) by
      (rewrite (data_at_isptr sh); entailer!).
  rename H2 into H_eptr_isptr.
  assert (Hdef_sorted: Forall def_wedgerep sorted). {
    apply (Forall_permutation _ _ _ Hdef_glist H0).
  }
  assert (HZlength_sorted: Zlength sorted = numE g). {
    rewrite <- (Permutation_Zlength _ _ H0). apply HZlength_glist.
  } rewrite HZlength_glist. rewrite HZlength_sorted.
  (******************************THE BIG NASTY LOOP******************************) 
  forward_for_simple_bound
    (numE g)
    (EX i : Z,
     EX msf' : EdgeListGG,
     EX msflist: list (LE*EType),
     EX subsetsGraph' : UFGraph,
     PROP (numE msf' <= i;
           is_partial_lgraph msf' g;
           uforest' msf';
           Permutation msflist (graph_to_wedgelist msf');
           forall v, vvalid g v <-> vvalid subsetsGraph' v;
           forall e u v, adj_edge g e u v -> In (wedge_to_cdata (edge_to_wedge g e)) (sublist 0 i sorted) -> ufroot_same subsetsGraph' u v;
           forall u v, ufroot_same subsetsGraph' u v <-> connected msf' u v; (*correlation between uf and msf'*)
               (*scoping that "incl" msflist (sublist i sorted)*)
            forall x, In x (map wedge_to_cdata msflist) -> exists j, 0 <= j < i /\ x = Znth j sorted;
              (*weight lemma: edges before i that WEREN't added, exists a upath made of edges before j
              consequently these edges have leq weight than Znth j sorted *)
            forall j, 0 <= j < i -> ~ In (Znth j sorted) (map wedge_to_cdata msflist) ->
                      (exists p: upath, c_connected_by_path size msf' p (fst (snd (Znth j sorted))) (snd (snd (Znth j sorted))) /\
                                        (exists l, fits_upath msf' l p /\ forall w, In w l -> In (wedge_to_cdata (edge_to_wedge g w)) (sublist 0 j sorted)))
          )
          LOCAL (temp _graph_E (Vint (Int.repr (numE g)));
                 temp _graph__1 (pointer_val_val orig_gptr);
                 temp _subsets (pointer_val_val subsetsPtr);
                 temp _mst (pointer_val_val gptr))
          SEP (
            data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
            mem_mgr gv;
            (*orig graph with sorted edgelist*)
            data_at sh (tarray t_struct_edge (numE g)) sorted (pointer_val_val orig_eptr);
            data_at sh t_wedgearray_graph (Vint (Int.repr (size)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
            data_at sh (tarray t_struct_edge (MAX_EDGES - numE g)) (Vundef_cwedges (MAX_EDGES - numE g))
                    (field_address0 (tarray t_struct_edge MAX_EDGES) [ArraySubsc (numE g)] (pointer_val_val orig_eptr));
            (*msf'*)
            malloc_token' sh (MAX_EDGES * sizeof t_struct_edge) (pointer_val_val eptr);
            malloc_token' sh (sizeof t_wedgearray_graph) (pointer_val_val gptr);
            data_at sh t_wedgearray_graph (Vint (Int.repr (size)), (Vint (Int.repr (numE msf')), pointer_val_val eptr)) (pointer_val_val gptr);
            data_at sh (tarray t_struct_edge MAX_EDGES)
                    (map wedge_to_cdata msflist ++ (Vundef_cwedges (MAX_EDGES - numE msf'))) (pointer_val_val eptr);
            (*ufgraph*)
            whole_graph sh subsetsGraph' subsetsPtr
    ))%assert.
  + (******PRECON******)
    (*set (edgeless:=@edgeless_GG size size_bound).*)
    Exists (@edgeless_GG size size_bound).
    Exists (graph_to_wedgelist (@edgeless_GG size size_bound)). (*=nil*)
    Exists (makeSet_discrete_Graph (Z.to_nat size)).
    rewrite edgeless_GG_numE. rewrite Z.sub_0_r.
    rewrite graph_to_wedgelist_edgeless_GG. rewrite app_nil_l.
    assert (Hpartial: is_partial_lgraph (@edgeless_GG size size_bound) g). {
      repeat split; intros. simpl in H2. rewrite (vertex_valid g). auto.
      apply edgeless_GG_evalid in H2; contradiction.
      apply edgeless_GG_evalid in H2; contradiction.
      apply edgeless_GG_evalid in H2; contradiction.
      unfold preserve_vlabel; intros. simpl. destruct vlabel. auto.
      unfold preserve_elabel; intros. apply edgeless_GG_evalid in H2; contradiction.
    }
    assert (Huforest': uforest' (@edgeless_GG size size_bound)). { apply (@uforest'_edgeless_GG size size_bound). }
                                                                 repeat rewrite map_nil. repeat rewrite sublist_nil.
    assert (HmakeSet_vvalid: forall v : VType, vvalid g v <-> vvalid (makeSet_discrete_Graph (Z.to_nat size)) v). {
      intros; split; intros. rewrite (vertex_valid g) in H2. apply makeSet_vvalid. rewrite Z2Nat.id by lia. lia.
      apply makeSet_vvalid in H2. rewrite Z2Nat.id in H2 by lia. rewrite (vertex_valid g); auto.
    }
    assert (Hconnected: forall u v : Z, ufroot_same (makeSet_discrete_Graph (Z.to_nat (size))) u v <->
                                        connected (@edgeless_GG size size_bound) u v). {
      unfold connected; unfold connected_by_path.
      (*will like to prove this without connectedness, but will have to create a lemma on makeSet's roots, which seems annoying*)
      intros. rewrite <- connected_ufroot_same_iff. split; intros.
      { destruct H2 as [p [? [? ?]]].
        destruct p eqn:Hp; simpl in H2; simpl in H3; inversion H3.
        subst z. destruct u0.
        (*single vertex in upath. Thus u=v, trivially connected*)
        simpl in H4; inversion H4. exists p. rewrite Hp; unfold connected_by_path. simpl; split; auto.
        simpl. apply makeSet_vvalid in H2. rewrite Z2Nat.id in H2 by lia. apply H2.
        (*case p = u::z0::u0.
          Thus exists e,. dst subsetsGraph e = z0. But by makeSet_dst...*)
        destruct H2. destruct H2. unfold adj_edge in H2. destruct H2. destruct H2. destruct H7.
        rewrite makeSet_vvalid, Z2Nat.id in H8 by lia.
        destruct H6; destruct H6;
          rewrite H9 in H8; rewrite makeSet_dst in H9; rewrite <- H9 in H8; lia.
      }
      { (*more or less same deal...*)
        destruct H2 as [p [? [? ?]]].
        destruct p eqn:Hp; simpl in H3; inversion H3.
        subst v0. destruct u0.
        (*single vertex in upath. Thus u=v, trivially connected*)
        simpl in H4; inversion H4. subst u. subst p. destruct H4.
        simpl in H2. apply connected_refl. apply makeSet_vvalid. rewrite Z2Nat.id; lia.
        (*case p = u::z0::u0.
          then u z0 is adjacent in edgeless, contradiction...
         *)
        destruct H2. destruct H2. unfold adj_edge in H2. destruct H2. destruct H2.
        apply edgeless_GG_evalid in H2; contradiction.
      }
    }
    assert (forall e u v, adj_edge g e u v ->
                          In (wedge_to_cdata (edge_to_wedge g e)) [] ->
                          ufroot_same (makeSet_discrete_Graph (Z.to_nat (size))) u v). {
      intros. contradiction.
    }
    assert (forall x : reptype t_struct_edge, In x (map wedge_to_cdata []) -> exists j : Z, 0 <= j < 0 /\ x = Znth j sorted). {
      intros; contradiction.
    }
    time "loop precon (originally 187 seconds)" entailer!.
  + (******LOOP BODY******)
    Intros.
    rename H3 into Hinv1; rename H4 into Hinv2; rename H5 into Hinv3;
      rename H6 into Hinv4; rename H7 into Hinv5; rename H8 into Hinv6;
        rename H9 into Hinv7; rename H10 into Hinv8; rename H11 into Hinv9.
    (*some assertions about Znth i sorted, for convenience*)
    assert (Hdef_i: def_wedgerep (Znth i sorted)).
    rewrite Forall_forall in Hdef_sorted. apply Hdef_sorted. apply Znth_In. lia.
    assert (HIn_i: In (Znth i sorted) (map wedge_to_cdata glist)). {
      apply Permutation_sym in H0. apply (@Permutation_in _ _ _ _ H0). apply Znth_In. lia.
    }
    apply list_in_map_inv in HIn_i.
    destruct HIn_i as [e [Heq_i HIn_i]].
    destruct e as [w [u v]].
    assert (Htmp: elabel g (u,v) = w /\ evalid g (u,v)). {
      apply Permutation_sym in Hpre3. apply (Permutation_in (A:= prod LE EType) (l:=glist) (l':=graph_to_wedgelist g) (w,(u,v)) Hpre3) in HIn_i.
      unfold graph_to_wedgelist in HIn_i. apply list_in_map_inv in HIn_i. destruct HIn_i. destruct H3.
      inversion H3. split. auto. apply EList_evalid in H4. rewrite <- H7 in H4. apply H4.
    } destruct Htmp as [Helabel_w_i Hevalid_uv_i].
    assert (Htmp: vvalid g u /\ vvalid g v). { apply evalid_uv_vvalid; auto. }
                                             destruct Htmp as [Hvvalid_g_u Hvvalid_g_v].
    assert (Hvvalid_subsetsGraph'_u: vvalid subsetsGraph' u). apply Hinv5. apply Hvvalid_g_u.
    assert (Hvvalid_subsetsGraph'_v: vvalid subsetsGraph' v). apply Hinv5. apply Hvvalid_g_v.
    assert (HZlength_msflist: Zlength msflist = numE msf'). {
      rewrite (Permutation_Zlength _ _  Hinv4). unfold graph_to_wedgelist.
      rewrite Zlength_map. reflexivity.
    }
    assert (Hu_i: fst (snd (Znth i sorted)) = Vint (Int.repr u)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
    assert (Hv_i: snd (snd (Znth i sorted)) = Vint (Int.repr v)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
    assert (Hw_i: fst (Znth i sorted) = Vint (Int.repr w)).
    unfold wedge_to_cdata in Heq_i; simpl in Heq_i. rewrite Heq_i; simpl; auto.
    assert (Hrepable_u: Int.min_signed <= u <= Int.max_signed).
    pose proof (@vertex_representable size size_bound g u Hvvalid_g_u). lia.
    assert (Hrepable_v: Int.min_signed <= v <= Int.max_signed).
    pose proof (@vertex_representable size size_bound g v Hvvalid_g_v). lia.
    assert (H_evalid_g_uv: evalid g (u,v)). rewrite <- EList_evalid.
    assert (In (w, (u, v)) (graph_to_wedgelist g)). apply (Permutation_in (l:=glist)).
    apply Permutation_sym; auto. apply HIn_i. unfold graph_to_wedgelist in H3.
    apply list_in_map_inv in H3. destruct H3; destruct H3.
    unfold edge_to_wedge in H3. inversion H3. rewrite H7; apply H4.
    assert (Hrepable_w: Int.min_signed <= w <= Int.max_signed).
    rewrite <- Helabel_w_i. apply (weight_valid g). apply H_evalid_g_uv.

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
    destruct H3 as [? _]; rewrite <- H3. apply Hvvalid_subsetsGraph'_v.
    Intros v_root. destruct v_root as [subsetsGraph_uv v_root].
    simpl fst in *. simpl snd in *.

    (*assertions about u_root and v_root*)
    assert (H_subsetsGraph'_uroot: uf_root subsetsGraph' u u_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H3. apply H4.
    assert (Htmp: uf_root subsetsGraph_u v v_root). apply (uf_equiv_root_the_same subsetsGraph_u subsetsGraph_uv). apply H5. apply H6.
    assert (H_subsetsGraph'_vroot: uf_root subsetsGraph' v v_root). apply (uf_equiv_root_the_same subsetsGraph' subsetsGraph_u). apply H3. apply Htmp. clear Htmp.
    assert (Hvvalid_uroot: vvalid subsetsGraph' u_root). apply (reachable_foot_valid subsetsGraph' u). apply H_subsetsGraph'_uroot.
    assert (Hvvalid_vroot: vvalid subsetsGraph' v_root). apply (reachable_foot_valid subsetsGraph' v). apply H_subsetsGraph'_vroot.
    assert (Hrepable_uroot: Int.min_signed <= u_root <= Int.max_signed).
    apply Hinv5 in Hvvalid_uroot. apply (@vertex_representable size size_bound) in Hvvalid_uroot. lia.
    assert (Hrepable_vroot: Int.min_signed <= v_root <= Int.max_signed).
    apply Hinv5 in Hvvalid_vroot. apply (@vertex_representable size size_bound) in Hvvalid_vroot. lia.
    assert (Hequiv_trans: uf_equiv subsetsGraph' subsetsGraph_uv).
    apply (uf_equiv_trans _ (liGraph subsetsGraph_u)); trivial.
    assert (Hvvalid_subsetsGraph_uv_u: vvalid subsetsGraph_uv u). {
      destruct Hequiv_trans as [Htmp ]; rewrite <- Htmp; apply Hvvalid_subsetsGraph'_u.
    }
    assert (Hvvalid_subsetsGraph_uv_v: vvalid subsetsGraph_uv v). {
      destruct Hequiv_trans as [Htmp ]; rewrite <- Htmp; apply Hvvalid_subsetsGraph'_v.
    }
    (*remove subsetsGraph_u*)
    clear H3 H4 H5 subsetsGraph_u. rename H6 into H3.
    forward_if.
    --- (* yes, add this edge.*)
      forward. forward. entailer!. apply Hdef_i.
      forward. forward. rewrite (surjective_pairing (Znth i sorted)).
      (*this is what happens when you manually update the fields g[i].u = ...

    Tactic call ran for 83.16 secs (83.146u,0.036s) (success)
    Tactic call ran for 50.323 secs (50.332u,0.016s) (success)
    Tactic call ran for 136.395 secs (136.369u,0.093s) (success)
    Tactic call ran for 75.162 secs (75.167u,0.04s) (success)
    Tactic call ran for 90.805 secs (90.78u,0.072s) (success)
    Tactic call ran for 52.881 secs (52.874u,0.036s) (success)
    Tactic call ran for 131.789 secs (131.754u,0.1s) (success)
    Tactic call ran for 73.214 secs (73.173u,0.08s) (success)
    Tactic call ran for 141.335 secs (141.295u,0.113s) (success)
    Tactic call ran for 130.169 secs (130.179u,0.06s) (success)
    Tactic call ran for 84.157 secs (84.169u,0.024s) (success)

    time forward. time entailer!.
    time forward. time forward.
    time forward. time entailer!.
    time forward. time forward. time forward. time forward. time forward.
       *)
      (*split. UGLY*)
      rewrite (split2_data_at_Tarray_app (numE msf') MAX_EDGES sh t_struct_edge
                                         (map wedge_to_cdata msflist) (Vundef_cwedges (MAX_EDGES - numE msf'))).
      2: rewrite Zlength_map; auto. 2: apply Vundef_cwedges_Zlength; lia. Intros.
      replace (Vundef_cwedges (MAX_EDGES - numE msf')) with
          ((Vundef_cwedges 1)++(Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))).
      2: { pose proof (Vundef_cwedges_Zlength (MAX_EDGES - numE msf')).
           rewrite <- (sublist_same 0 (MAX_EDGES - numE msf') (Vundef_cwedges (MAX_EDGES - numE msf'))) by lia.
           rewrite (sublist_split 0 1 (MAX_EDGES - numE msf')) by lia.
           rewrite sublist_one by lia. unfold Vundef_cwedges. rewrite Znth_repeat_inrange by lia.
           rewrite sublist_repeat by lia. rewrite Z.sub_add_distr by lia. simpl; auto.
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
      assert (HsubsetsGraph'_ufroot_uv: ~ ufroot_same subsetsGraph' u v). {
        unfold not; intros Htmp. destruct Htmp as [x [? ?]].
        assert (u_root = x). apply (uf_root_unique _ (liGraph subsetsGraph') u u_root x); auto.
        assert (v_root = x). apply (uf_root_unique _ (liGraph subsetsGraph') v v_root x); auto.
        subst u_root; subst v_root; contradiction.
      }
      assert (Hconnected_uv: ~ connected msf' u v). rewrite <- Hinv7; auto.
      assert(H_msf'_uv: ~ evalid msf' (u,v)). {
        unfold not; intros.
        assert (connected msf' u v). {
          apply adjacent_connected. exists (u,v).
          split. apply evalid_strong_evalid; auto. left.
          rewrite (src_fst msf'), (dst_snd msf'); auto.
        } contradiction.
      }
      forward. forward.
      forward_call (sh, subsetsGraph_uv, subsetsPtr, u, v). (*union*)
      Intros uv_union.
      rewrite (vertex_valid g) in Hvvalid_g_u.
      rewrite (vertex_valid g) in Hvvalid_g_v.
      set (adde:=@EdgeListGG_adde size size_bound msf' u v w Hvvalid_g_u Hvvalid_g_v Hrepable_w).
      Exists adde.
      Exists (msflist+::(w,(u,v))).
      Exists uv_union.
      (*before we entailer, preemptively fix up some of the SEPs*)
      replace (numE adde) with (numE msf' + 1).
      2: { symmetry; apply adde_numE. apply H_msf'_uv. }
      replace (Int.add (Int.repr (numE msf')) (Int.repr 1)) with (Int.repr (numE msf' + 1)).
      2: { symmetry; apply add_repr. }
      subst w. set (w:=elabel g (u,v)).
      assert (Hpartial: is_partial_lgraph adde g). {
        split3. split3.
        intros. apply Hinv2. simpl in H7; auto.
        simpl; unfold addValidFunc; intros. destruct H7. apply Hinv2; auto. subst e; auto.
        split. intros. apply adde_evalid_or in H7. destruct H7.
        rewrite (src_fst adde), (src_fst g). auto. apply Hinv2; auto. apply add_edge_preserves_evalid; auto.
        subst e. rewrite (src_fst adde), (src_fst g). auto. auto. apply add_edge_evalid; auto.
        intros. apply adde_evalid_or in H7. destruct H7.
        rewrite (dst_snd adde), (dst_snd g). auto. apply Hinv2; auto. apply add_edge_preserves_evalid; auto.
        subst e. rewrite (dst_snd adde), (dst_snd g). auto. auto. apply add_edge_evalid; auto.
        unfold preserve_vlabel; intros. simpl. destruct vlabel. destruct vlabel. auto.
        unfold preserve_elabel; intros. simpl. unfold graph_gen.update_elabel. simpl in H7. unfold graph_gen.addValidFunc in H7.
        unfold EquivDec.equiv_dec. destruct E_EqDec. unfold Equivalence.equiv in e0; rewrite <- e0. auto.
        destruct H7. apply Hinv2. auto. unfold RelationClasses.complement, Equivalence.equiv in c. symmetry in H7. contradiction.
      }
      assert (Huforest: uforest' adde). {
        apply add_edge_uforest'; auto. rewrite (vertex_valid msf'); auto. rewrite (vertex_valid msf'); auto.
      }
      assert (Hinv_5: Permutation (msflist +:: (w, (u, v))) (graph_to_wedgelist adde)). {
        apply NoDup_Permutation. apply NoDup_app_inv.
        apply (Permutation_NoDup (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto. apply NoDup_g2wedgelist.
        apply NoDup_cons. auto. apply NoDup_nil.
        unfold not; intros. simpl in H8. destruct H8; try contradiction.
        apply (Permutation_in (l':=graph_to_wedgelist msf')) in H7.
        rewrite <- H8 in H7. apply g2wedgelist_evalid in H7. simpl in H7. contradiction.
        auto. apply NoDup_g2wedgelist.
        intros; split; intros. apply in_app_or in H7. destruct H7.
        apply (Permutation_in (l':=graph_to_wedgelist msf')) in H7. 2: auto.
        apply list_in_map_inv in H7. destruct H7; destruct H7. rewrite H7. apply EList_evalid in H8.
        apply adde_g2wedgelist_2.
        unfold not; intros; rewrite <- H9 in H8; contradiction. apply H8.
        simpl in H7. destruct H7. rewrite <- H7.
        apply adde_g2wedgelist_1. contradiction.
        destruct x as [w1 e].
        unfold graph_to_wedgelist in H7. apply list_in_map_inv in H7.
        destruct H7; destruct H7.
        apply EList_evalid in H8.
        unfold edge_to_wedge in H7; simpl in H7. unfold graph_gen.update_elabel in H7.
        unfold EquivDec.equiv_dec in H7. destruct (E_EqDec (u, v) x).
        unfold Equivalence.equiv in e0. rewrite H7. rewrite e0. apply in_or_app. right. left. subst x. auto.
        apply adde_evalid_or in H8. destruct H8.
        apply in_or_app. left. apply (Permutation_in (l:=graph_to_wedgelist msf')).
        apply Permutation_sym; auto.
        replace (w1,e) with (edge_to_wedge msf' e). apply in_map. apply EList_evalid. inversion H7. apply H8.
        unfold edge_to_wedge; simpl. inversion H7. auto.
        unfold RelationClasses.complement, Equivalence.equiv in c. rewrite H8 in c; contradiction.
      }
      assert (Hinv_6: forall v0 : VType, vvalid g v0 <-> vvalid uv_union v0). {
        intros. rewrite <- (uf_union_vvalid subsetsGraph_uv uv_union
                                            (liGraph subsetsGraph_uv) (liGraph uv_union)
                                            (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                            (maGraph subsetsGraph_uv) (maGraph uv_union)
                                            u v); auto.
        destruct Hequiv_trans. rewrite <- H7. apply Hinv5.
      }
      assert (Hinv_7: forall (e : EType) (u0 v0 : VType), adj_edge g e u0 v0 -> In (wedge_to_cdata (edge_to_wedge g e)) (sublist 0 (i + 1) sorted) -> ufroot_same uv_union u0 v0). {
        intros. rewrite (sublist_split 0 i (i+1)) in H8 by lia. apply in_app_or in H8.
        destruct H8.
        (*case of every edge that was before*)
        apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                              (liGraph subsetsGraph_uv) (liGraph uv_union)
                                              (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                              (maGraph subsetsGraph_uv) (maGraph uv_union)
                                              u v); auto.
        apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv). auto.
        apply (Hinv6 e); auto.
        (*the newly added edge*)
        rewrite (sublist_one i (i+1) _) in H8 by lia.
        destruct H8. 2: contradiction.
        rewrite Heq_i in H8.
        destruct H7. unfold edge_to_wedge in H8. inversion H8.
        do 2 rewrite Int.Z_mod_modulus_eq in H12. do 2 rewrite Int.Z_mod_modulus_eq in H13.
        assert (u = fst e /\ v = snd e). {
          destruct H7. rewrite (src_fst g), (dst_snd g) in H10 by auto. destruct H10.
          rewrite (vertex_valid g) in H10. rewrite (vertex_valid g) in H14.
          set (q:=Int.max_signed) in *; compute in q; subst q.
          set (q:=Int.modulus) in *; compute in q; subst q.
          do 2 rewrite Z.mod_small in H12 by lia. do 2 rewrite Z.mod_small in H13 by lia. auto.
        }
        destruct H10.
        destruct H9; destruct H9; rewrite (src_fst g) in H9 by (apply H7); rewrite (dst_snd g) in H15 by (apply H7);
          subst u0; subst v0; rewrite <- H14, <- H10.
        2: apply ufroot_same_symm.
        (*both cases: apply union_ufroot_same.*)
        all: apply (uf_union_ufroot_same subsetsGraph_uv uv_union
                                         (liGraph subsetsGraph_uv) (liGraph uv_union)
                                         (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                         (maGraph subsetsGraph_uv) (maGraph uv_union)); auto.
      }
      assert (Hinv_8: forall u0 v0 : Z, ufroot_same uv_union u0 v0 <-> connected adde u0 v0). {
        subst a.
        intros a b; split; intros.
        ***
          (*----------->*)
          (*this is a mess with 10 cases because there are no 'backward' lemmas about uf_union
      Will also need an analog of cross_bridge_implies_endpoints, and a ufroot_same_dec analog of the in_dec
           *)
          assert (Hvvalid_subsetsGraph_uv_a: vvalid subsetsGraph_uv a).
          apply (uf_union_vvalid subsetsGraph_uv uv_union
                                 (liGraph subsetsGraph_uv) (liGraph uv_union)
                                 (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                 (maGraph subsetsGraph_uv) (maGraph uv_union)
                                 u v); auto.
          destruct H7 as [rt [? ?]]. apply (ufroot_vvalid_vert uv_union rt a). auto.
          assert (Hvvalid_subsetsGraph_uv_b: vvalid subsetsGraph_uv b).
          apply (uf_union_vvalid subsetsGraph_uv uv_union
                                 (liGraph subsetsGraph_uv) (liGraph uv_union)
                                 (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                 (maGraph subsetsGraph_uv) (maGraph uv_union)
                                 u v); auto.
          destruct H7 as [rt [? ?]]. apply (ufroot_vvalid_vert uv_union rt b). auto.
          destruct (connected_dec msf' a b); rename H8 into Hab.
          apply add_edge_connected; auto.
          destruct (connected_dec msf' a u).
          (*a-u*)
          destruct (connected_dec msf' a v). apply connected_symm in H8. apply (connected_trans msf' u a v H8) in H9. contradiction.
          destruct (connected_dec msf' u b). apply (connected_trans msf' a u b H8) in H10. apply add_edge_connected. auto. auto.
          destruct (connected_dec msf' v b). apply add_edge_connected_through_bridge1; auto.
          rewrite <- Hinv7 in H8, H10, H11.
          rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H8, H10, H11; auto.
          assert (~ ufroot_same subsetsGraph_uv b u). {
            unfold not; intros. apply ufroot_same_symm in H12. contradiction. }
          apply (uf_union_remains_disjoint1 subsetsGraph_uv uv_union
                                            (liGraph subsetsGraph_uv) (liGraph uv_union)
                                            (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                            (maGraph subsetsGraph_uv) (maGraph uv_union)
                                            u v) in H12; auto.
          2: auto. 2: { unfold not; intros. apply ufroot_same_symm in H13. contradiction. }
          apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                u v) in H8; auto.
          apply ufroot_same_symm in H7.
          apply (ufroot_same_trans _ (liGraph uv_union) b a u) in H7; auto. contradiction.
          (*a not connected to u*)
          (*destruct connected msf' a v, repeat the above...*)
          destruct (connected_dec msf' a v).
          destruct (connected_dec msf' u b). apply add_edge_connected_through_bridge2; auto.
          destruct (connected_dec msf' v b). apply (connected_trans msf' a v b H9) in H11.
          apply add_edge_connected; auto.
          rewrite <- Hinv7 in H9, H10, H11.
          rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H9, H10, H11; auto.
          assert (~ ufroot_same subsetsGraph_uv b v). {
            unfold not; intros.
            apply ufroot_same_symm in H12. contradiction. }
          apply (uf_union_remains_disjoint2 subsetsGraph_uv uv_union
                                            (liGraph subsetsGraph_uv) (liGraph uv_union)
                                            (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                            (maGraph subsetsGraph_uv) (maGraph uv_union)
                                            u v) in H12; auto.
          2: { rewrite ufroot_same_symm. auto. }
          apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                u v) in H9; auto.
          apply ufroot_same_symm in H7.
          apply (ufroot_same_trans _ (liGraph uv_union) b a v) in H7; auto. contradiction.
          destruct (connected_dec msf' u b). apply Hinv7 in H10.
          apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H10; auto.
          apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                u v) in H10; auto.
          apply ufroot_same_symm in H10.
          apply (ufroot_same_trans _ (liGraph uv_union) a b u H7) in H10.
          (*However, ~ connected msf' a u -> ... -> ~ ufroot_same uv_union, contradiction*)
          assert (~ ufroot_same uv_union a u). {
            rewrite <- Hinv7 in H8, H9. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H8, H9; auto.
            apply (uf_union_remains_disjoint1 subsetsGraph_uv uv_union
                                              (liGraph subsetsGraph_uv) (liGraph uv_union)
                                              (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                              (maGraph subsetsGraph_uv) (maGraph uv_union)
                                              u v a); auto. }
          contradiction.
          destruct (connected_dec msf' v b). apply Hinv7 in H11. apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H11; auto.
          apply (uf_union_preserves_ufroot_same
                   subsetsGraph_uv uv_union
                   (liGraph subsetsGraph_uv)
                   (liGraph uv_union)
                   (UnionFindGraph.finGraph subsetsGraph_uv)
                   (UnionFindGraph.finGraph uv_union)
                   (maGraph subsetsGraph_uv) (maGraph uv_union)
                   u v) in H11; auto. apply ufroot_same_symm in H11.
          apply (ufroot_same_trans _ (liGraph uv_union) a b v H7) in H11.
          (*However, ~ connected msf' a u -> ... -> ~ ufroot_same uv_union, contradiction*)
          assert (~ ufroot_same uv_union a v). {
            rewrite <- Hinv7 in H8, H9. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H8, H9; auto.
            apply (uf_union_remains_disjoint2 subsetsGraph_uv uv_union
                                              (liGraph subsetsGraph_uv) (liGraph uv_union)
                                              (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                              (maGraph subsetsGraph_uv) (maGraph uv_union)
                                              u v a); auto. }
          contradiction.
          (*finally, neither were connected to u or v*)
          rewrite <- Hinv7 in Hab, H8, H9, H10, H11.
          rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in Hab, H8, H9, H10, H11; auto.
          assert (~ ufroot_same uv_union a b). {
            apply (uf_union_joins_only_uv subsetsGraph_uv uv_union
                                          (liGraph subsetsGraph_uv) (liGraph uv_union)
                                          (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                          (maGraph subsetsGraph_uv) (maGraph uv_union)
                                          u v a b); auto.
          }
          contradiction.
        ***
          (*<-----------*)
          (*assert exists list edges... destruct In (u,v) l.
      Yes: then apply connected_bridge_implies_endpoints, destruct
        a-u,b-v: then by uf_union_preserves_ufroot_same, and union_connected...
        a-v,b-u: same
      No: then apply adde_unaffected.
           *)
          destruct H7 as [p0 ?]. 
          apply connected_by_upath_exists_simple_upath in H7. clear p0; destruct H7 as [p [H7 Hp_simpl]].
          assert (exists l : list EType, fits_upath adde l p).
          apply connected_exists_list_edges in H7; auto. destruct H8 as [l ?].
          destruct (in_dec E_EqDec (u,v) l).
          (*Yes*) assert (connected msf' a u /\ connected msf' v b \/ connected msf' a v /\ connected msf' u b).
          apply (cross_bridge_implies_endpoints msf' (u,v) u v p l); auto.
          destruct H9; destruct H9;
            rewrite <- Hinv7 in H9, H10;
            rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv)
              in H9, H10; auto;
              apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                    (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                    (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                    (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                    u v) in H9; auto;
                apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                      (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                      (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                      (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                      u v) in H10; auto.
          assert (ufroot_same uv_union u v).
          apply (uf_union_ufroot_same subsetsGraph_uv uv_union
                                      (liGraph subsetsGraph_uv) (liGraph uv_union)
                                      (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                      (maGraph subsetsGraph_uv) (maGraph uv_union)
                                      u v); auto.
          apply (ufroot_same_trans _ (liGraph uv_union) u v b H11) in H10.
          apply (ufroot_same_trans _ (liGraph uv_union) a u b); auto.
          assert (ufroot_same uv_union u v).
          apply (uf_union_ufroot_same subsetsGraph_uv uv_union
                                      (liGraph subsetsGraph_uv) (liGraph uv_union)
                                      (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                      (maGraph subsetsGraph_uv) (maGraph uv_union)
                                      u v); auto.
          apply ufroot_same_symm in H11.
          apply (ufroot_same_trans _ (liGraph uv_union) v u b H11) in H10.
          apply (ufroot_same_trans _ (liGraph uv_union) a v b); auto.
          (*No *) assert (connected msf' a b). exists p. destruct H7. split.
          apply (add_edge_unaffected msf' (u,v) u v p l). apply H7. auto. auto.
          auto.
          rewrite <- Hinv7 in H9. rewrite (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv) in H9; auto.
          apply (uf_union_preserves_ufroot_same subsetsGraph_uv uv_union
                                                (liGraph subsetsGraph_uv) (liGraph uv_union)
                                                (UnionFindGraph.finGraph subsetsGraph_uv) (UnionFindGraph.finGraph uv_union)
                                                (maGraph subsetsGraph_uv) (maGraph uv_union)
                                                u v) in H9; auto.
      }
      assert (Hinv_9: forall x : reptype t_struct_edge, In x (map wedge_to_cdata (msflist +:: (w, (u, v)))) -> exists j : Z, 0 <= j < i + 1 /\ x = Znth j sorted). {
        intros. rewrite map_app in H7. apply in_app_or in H7; destruct H7.
        apply Hinv8 in H7. destruct H7; destruct H7. exists x0; split; [lia | auto].
        simpl in H7. destruct H7. exists i; split. lia. rewrite <- H7. symmetry; apply Heq_i.
        contradiction.
      }
      assert (Hinv_10: forall j : Z,
                 0 <= j < i + 1 ->
                 ~ In (Znth j sorted) (map wedge_to_cdata (msflist +:: (w, (u, v)))) ->
                 exists p : upath,
                   c_connected_by_path size adde p 
                                       (fst (snd (Znth j sorted))) (snd (snd (Znth j sorted))) /\
                   (exists l : list EType,
                       fits_upath adde l p /\
                       (forall w0 : EType,
                           In w0 l -> In (wedge_to_cdata (edge_to_wedge g w0)) (sublist 0 j sorted)))). {
        intros.
        destruct (Z.lt_trichotomy j i).
        (*j<i*) 1: {
          assert (~ In (Znth j sorted) (map wedge_to_cdata msflist)). {
            unfold not; intros. assert (In (Znth j sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
            rewrite map_app. apply in_or_app. left. auto. contradiction. }
          apply Hinv9 in H10. 2: lia. destruct H10 as [p ?]; destruct H10. destruct H11 as [l ?]; destruct H11.
          exists p.
          (*replace Znth j sorted with (w',(u',v'))*)
          assert (HIn_j: In (Znth j sorted) (map wedge_to_cdata glist)). {
            apply Permutation_sym in H0. apply (@Permutation_in _ _ _ _ H0). apply Znth_In. lia.
          }
          apply list_in_map_inv in HIn_j.
          destruct HIn_j as [e' [Heq_j HIn_j]].
          destruct e' as [w' [u' v']]. unfold wedge_to_cdata in Heq_j. simpl in Heq_j.
          replace (fst (snd (Znth j sorted))) with (Vint (Int.repr u')). 2: rewrite Heq_j; simpl; auto.
          replace (snd (snd (Znth j sorted))) with (Vint (Int.repr v')). 2: rewrite Heq_j; simpl; auto.
          rewrite Heq_j in H10; simpl in H10.
          (*we''ll deal with the vvalid etc when we need it...*)
          split. unfold c_connected_by_path. unfold c_connected_by_path in H10.
          apply add_edge_connected_by_path; auto. exists l.
          split. apply add_edge_fits_upath; auto. apply H12.
        }
        (*the rest are trivial*)
        destruct H9. subst j.
        assert (In (Znth i sorted) (map wedge_to_cdata (msflist +:: (elabel g (u, v), (u, v))))).
        rewrite Heq_i. apply in_map. apply in_or_app. right. left; auto. contradiction.
        lia.
      }
      time "if-branch postcon (originally 331.069 secs):" entailer!.
      replace (numE adde) with (numE msf' + 1). 2: { unfold adde. symmetry; apply adde_numE. auto. }
      replace (map wedge_to_cdata (msflist +:: (w, (u, v)))) with ((map wedge_to_cdata msflist) ++ [Znth i sorted]).
      2: { rewrite map_app. simpl. rewrite Heq_i; auto. } rewrite <- app_assoc.
      rewrite (split2_data_at_Tarray_app (numE msf') MAX_EDGES sh t_struct_edge
                                         (map wedge_to_cdata msflist) ([Znth i sorted] ++ Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))).
      2: { rewrite Zlength_map. rewrite (Permutation_Zlength _ _ Hinv4).
           rewrite g2wedgelist_numE. auto. }
      2: { unfold Vundef_cwedges; simpl. rewrite Zlength_cons, Zlength_repeat by lia. lia. }
      rewrite (split2_data_at_Tarray_app 1 (MAX_EDGES - numE msf') sh t_struct_edge
                                         ([Znth i sorted]) (Vundef_cwedges (MAX_EDGES - (numE msf' + 1)))).
      2: { simpl; auto. }
      2: { unfold Vundef_cwedges; simpl. rewrite Zlength_repeat by lia. lia. }
      rewrite (data_at_singleton_array_eq' sh t_struct_edge (Znth i sorted)).
      entailer!.
    --- (* no, don't add this edge *)
      forward.
      Exists msf' msflist subsetsGraph_uv.
      subst u_root.
      assert (Ha2: forall (e : EType) (u0 v0 : VType), adj_edge g e u0 v0 ->
                                                       In (wedge_to_cdata (edge_to_wedge g e)) (sublist 0 (i + 1) sorted) ->
                                                       ufroot_same subsetsGraph_uv u0 v0). {
        intros. rewrite (sublist_split 0 i (i+1) sorted) in H5 by lia. apply in_app_or in H5. destruct H5.
        apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv); auto.
        apply (Hinv6 e u0 v0 H4 H5).
        rewrite sublist_one in H5 by lia. destruct H5. 2: contradiction.
        apply (uf_equiv_ufroot_same subsetsGraph' subsetsGraph_uv). auto.
        rewrite Heq_i in H5.
        destruct H4. destruct H4.
        rewrite (src_fst g) in H6, H7; auto. rewrite (dst_snd g) in H6, H7; auto. destruct H7.
        assert (u = fst e /\ v = snd e). {
          unfold edge_to_wedge in H5. inversion H5.
          do 2 rewrite Int.Z_mod_modulus_eq in H11. do 2 rewrite Int.Z_mod_modulus_eq in H12.
          apply vertex_valid in Hvvalid_g_u.
          apply vertex_valid in Hvvalid_g_v.
          apply vertex_valid in H7.
          apply vertex_valid in H8.
          set (q:=Int.max_signed) in *; compute in q; subst q.
          set (q:=Int.modulus) in *; compute in q; subst q.
          do 2 rewrite Z.mod_small in H11 by lia.
          do 2 rewrite Z.mod_small in H12 by lia.
          split; auto.
        } destruct H9.
        destruct H6; destruct H6; subst u0; subst v0; rewrite <- H9; rewrite <- H10.
        exists v_root; split; auto. exists v_root; split; auto.
      }
      assert (Ha3: forall u0 v0 : Z, ufroot_same subsetsGraph_uv u0 v0 <-> connected msf' u0 v0). {
        intros. rewrite <- Hinv7. apply uf_equiv_ufroot_same. apply uf_equiv_sym. trivial.
      }
      assert (Ha4: forall x : reptype t_struct_edge,
                 In x (map wedge_to_cdata msflist) -> exists j : Z, 0 <= j < i + 1 /\ x = Znth j sorted). {
        intros.
        destruct (Hinv8 _ H4) as [y [? ?]].
        exists y.
        split; trivial; lia.
      }
      assert (Ha1: forall v0 : VType, vvalid g v0 <-> vvalid subsetsGraph_uv v0). {
        intros. rewrite Hinv5. symmetry. destruct Hequiv_trans. rewrite H4. split; auto.
      }
      time "else-branch postcon (originally 192 secs): " entailer!.
      clear H20 H21 H22 H23 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
      intros.
      destruct (Z.eq_dec j i).
      2: apply Hinv9; trivial; lia.
      subst j. (* hrmm *)
      rewrite Hu_i; rewrite Hv_i. (*if I shift the lemma up, I can't rewrite for some reason*)
      unfold c_connected_by_path.
      assert (connected msf' u v). { apply Hinv7. exists v_root. split; auto. }
                                   destruct H6 as [p ?]. exists p. split.
      repeat rewrite Int.signed_repr. auto. lia. lia.
      apply connected_exists_list_edges in H6. destruct H6 as [l ?]. exists l.
      split. auto. intros. pose proof (finite msf'). assert (In w (EList msf')). apply EList_evalid.
      apply (fits_upath_evalid msf' p l); auto.
      assert (In (wedge_to_cdata (edge_to_wedge msf' w)) (map wedge_to_cdata msflist)).
      apply in_map. apply (Permutation_in (l:=graph_to_wedgelist msf')). apply Permutation_sym; auto.
      apply in_map. rewrite EList_evalid in H8; rewrite EList_evalid. auto.
      assert (edge_to_wedge msf' w = edge_to_wedge g w). unfold edge_to_wedge.
      assert (elabel msf' w = elabel g w). apply Hinv2. apply EList_evalid in H8; apply H8. rewrite H10; auto.
      rewrite <- H10.
      assert (incl (map wedge_to_cdata msflist) (sublist 0 i sorted)).
      unfold incl; intros. apply Hinv8 in H11. destruct H11; destruct H11. rewrite H12.
      assert (Znth (x+0) sorted = Znth x (sublist 0 i sorted)).
      symmetry. apply (Znth_sublist 0 x i sorted). lia. lia. rewrite Z.add_0_r in H13. rewrite H13.
      apply Znth_In. rewrite Zlength_sublist by lia; lia.
      apply H11. apply H9.
  (*******************************AFTER LOOP****************************)
  + Intros msf msflist subsetsGraph'. pose proof (finite msf) as fmsf. pose proof (finite g) as fg.
    rename H2 into Hinv1; rename H3 into Hinv2; rename H4 into Hinv3;
      rename H5 into Hinv4; rename H6 into Hinv5; rename H7 into Hinv6;
        rename H8 into Hinv7; rename H9 into Hinv8; rename H10 into Hinv9.
    replace (sublist 0 (numE g) sorted) with sorted in *. 2: {
      rewrite <- HZlength_sorted. rewrite sublist_same by auto. auto.
    }
    assert (forall p u v, connected_by_path g p u v -> ufroot_same subsetsGraph' u v). {
      induction p; intros.
      + destruct H2; destruct H2; destruct H3. inversion H3.
      + destruct p. destruct H2. simpl in H2. destruct H3; inversion H3; inversion H4. subst u; subst v.
        apply (ufroot_same_refl _ (liGraph subsetsGraph')). apply Hinv5. auto.
        destruct H2. destruct H2. destruct H3. inversion H3; subst a.
        apply (ufroot_same_trans _ (liGraph subsetsGraph') u v0 v).
        destruct H2. apply (Hinv6 x). auto.
        assert (In x (EList g)). apply EList_evalid. apply H2.
        assert (In (edge_to_wedge g x) glist). apply (Permutation_in (l:=graph_to_wedgelist g) (l':=glist)).
        auto. apply in_map. rewrite EList_evalid in H6; rewrite EList_evalid; auto.
        apply (Permutation_in (l:=map wedge_to_cdata glist)). auto. apply in_map. auto.
        apply IHp. split. auto. split. simpl; auto. rewrite last_error_cons in H5; auto. unfold not; intros; inversion H6.
    }
    assert (forall u v, connected g u v -> ufroot_same subsetsGraph' u v). {
      intros. destruct H3. apply (H2 x u v H3).
    }
    assert (Hspanning: forall u v, connected g u v <-> connected msf u v). {
      intros; split; intros. apply Hinv7. apply H3. auto.
      apply (is_partial_lgraph_connected msf g); auto.
    }
    (*everything we want from unionfind is done. We can free and clear it*)
    clear H2 H3. forward_call (sh, subsetsPtr, subsetsGraph').

    (* In hindsight, this wouldn't be needed with better definitions. But let's just soldier on
       Don't put this up on top, I worry about the effect of VST attempting to yank a value out
     *)
    apply (Permutation_trans Hperm_glist) in H0.
    assert (Permutation (graph_to_wedgelist g) (map cdata_to_wedge sorted)). {
      rewrite <- (w2c2w_map (graph_to_wedgelist g)).
      2: { intros. apply (@g2wedgelist_repable size size_bound g); auto. }
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
         rewrite Zlength_app. rewrite H3. rewrite HZlength_sorted. rewrite Vundef_cwedges_Zlength by lia. lia.
         rewrite sublist_same; auto.
         rewrite Zlength_app. rewrite H3. rewrite HZlength_sorted. rewrite Vundef_cwedges_Zlength by lia. lia.
         rewrite sublist0_app1. rewrite sublist_same. auto. auto. rewrite H3. lia.
         rewrite H3. lia. rewrite sublist_app2. rewrite H3. rewrite HZlength_sorted.
         replace (numE g - numE g) with 0 by lia. rewrite sublist_same. auto. lia. rewrite Vundef_cwedges_Zlength by lia. auto.
         rewrite H3. lia.
    }
    clear H20 H21 H22 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
    assert (Hmsf: labeled_spanning_uforest msf g).
    split. split3. apply Hinv2. auto. unfold spanning. auto. apply Hinv2.
    (*minimum spanning tree*)
    split. auto.
    (*minimum...*)
    intros.
    (*idea: first obtain a list of edges in t' but not in msf (ldiff)
  Use the induct to find a pair of edges in msf but not in (lmsf), and have the property of being a bridge for the edge in ldiff
  By the weight lemma, a path p exists with all edges before ldiff in lsorted.
  Thus, Znth i lmsf must be in this path, meaning it's weight is lower
  Thus, sum of lsame++lmsf <= lsame++ldiff
     *)
    pose proof (finite t') as ft'.
    assert (exists lsame ldiff : list EType,
               NoDup lsame /\ NoDup ldiff /\
               Permutation (lsame ++ ldiff) (EList t') /\
               incl lsame (EList msf) /\ (forall e : EType, In e ldiff -> ~ In e (EList msf))).
    { apply list_same_diff. apply NoDup_EList. apply NoDup_EList. }
    destruct H5 as [lsame [ldiff [? [? [? [? ?]]]]]].
    pose proof (sort_perm t' ldiff). set (ldiff':=sort t' ldiff). fold ldiff' in H10.
    assert (H7': Permutation (lsame++ldiff') (EList t')). {
      apply (Permutation_trans (l':=lsame++ldiff)). apply Permutation_app_head. apply Permutation_sym; auto. apply H7.
    }
    assert (Hpreserve_msf: preserve_elabel msf g). apply Hmsf.
    assert (Hpreserve_t': preserve_elabel t' g). apply H4.
    assert (forall e, In e ldiff' -> evalid t' e). {
      intros. rewrite <- EList_evalid. apply (Permutation_in (l:=lsame++ldiff')). apply H7'.
      apply in_or_app. right. auto.
    }
    assert (WeightedEdgeListGraph.sorted' t' ldiff'). { apply sorted_sorted'. unfold ldiff'. apply sort_sorted. }

                                                      (*apply induction to obtain lmsf*)
                                                      assert (exists lmsf, Zlength ldiff' = Zlength lmsf /\ Permutation (lmsf++lsame) (EList msf) /\
                                                                           (forall i, 0 <= i < Zlength lmsf -> elabel g (Znth i lmsf) <= elabel g (Znth i ldiff'))).
    apply (kruskal_minimal_induction ldiff' lsame g t' msf); auto.
    apply (Permutation_trans (l':=lsame++ldiff')). apply Permutation_app_comm. auto.
    intros. apply H9. apply (Permutation_in (l:=ldiff')). apply Permutation_sym; auto. auto.
    { intros.
      assert (He: evalid t' e). apply H11; auto.
      assert (exists j : Z, 0 <= j < Zlength sorted /\ Znth j sorted = wedge_to_cdata (edge_to_wedge t' e)).
      apply (In_Znth_iff sorted (wedge_to_cdata (edge_to_wedge t' e))).
      apply (Permutation_in (l:=(map wedge_to_cdata (graph_to_wedgelist g)) )). auto.
      apply in_map. replace (edge_to_wedge t' e) with (edge_to_wedge g e).
      unfold graph_to_wedgelist. apply in_map. apply EList_evalid. apply H4. auto.
      unfold edge_to_wedge. replace (elabel g e) with (elabel t' e); auto.
      destruct H14 as [j [? ?]].
      assert (~ In (Znth j sorted) (map wedge_to_cdata msflist)). {
        (*this should be cleaned up*)
        rewrite H15. unfold not; intros. apply (H9 e). apply (Permutation_in (l:=ldiff')). apply Permutation_sym; auto. auto.
        apply list_in_map_inv in H16. destruct H16. destruct H16.
        apply (Permutation_in (l':=graph_to_wedgelist msf)) in H17. 2: auto.
        apply list_in_map_inv in H17. destruct H17 as [e' [? ?]]. subst x.
        unfold edge_to_wedge in H16; simpl in H16.
        replace (elabel t' e) with (elabel g e) in H16. 2: symmetry; apply Hpreserve_t'; auto.
        assert (He': evalid msf e'). rewrite <- EList_evalid; apply H18.
        replace (elabel (EdgeListGG_EdgeListLG msf) e') with (elabel g e') in H16. 2: symmetry; apply Hpreserve_msf; auto.
        assert (vvalid t' (fst e) /\ vvalid t' (snd e)).
        rewrite <- (src_fst t'), <- (dst_snd t'); auto. apply (evalid_strong_evalid); auto. destruct H17.
        assert (vvalid msf (fst e') /\ vvalid msf (snd e')).
        rewrite <- (src_fst msf), <- (dst_snd msf); auto. apply (evalid_strong_evalid); auto. destruct H20.
        apply vertex_valid in H20. apply vertex_valid in H21. apply vertex_valid in H17. apply vertex_valid in H19.
        unfold wedge_to_cdata in H16. inversion H16. clear H16.
        do 2 rewrite Int.Z_mod_modulus_eq in H24, H25.
        set (k:=Int.max_signed) in *; compute in k; subst k.
        set (k:=Int.modulus) in *; compute in k; subst k.
        rewrite Z.mod_small in H24, H25 by lia. rewrite Z.mod_small in H24, H25 by lia.
        rewrite (surjective_pairing e). rewrite H24; rewrite H25. rewrite <- (surjective_pairing e').
        rewrite EList_evalid; rewrite EList_evalid in H18; auto.
      }
      apply Hinv9 in H16. 2: lia. destruct H16 as [p [? [l [? ?]]]].
      rewrite H15 in H16; simpl in H16.
      apply evalid_strong_evalid in He; auto.
      rewrite Int.signed_repr in H16. rewrite Int.signed_repr in H16.
      2: { assert (Int.min_signed <= snd e < Int.max_signed). apply (@vertex_representable size size_bound t' (snd e)).
           rewrite <- (dst_snd t'). apply He. apply He. lia.
      }
      2: {  assert (Int.min_signed <= fst e < Int.max_signed). apply (@vertex_representable size size_bound t' (fst e)).
            rewrite <- (src_fst t'). apply He. apply He. lia.
      }
      assert (forall e' : EType, In e' l -> elabel g e' <= elabel g e). {
        intros. assert (evalid g e'). apply Hmsf. apply (fits_upath_evalid msf p l); auto.
        apply H18 in H19. apply In_Znth_iff in H19. destruct H19 as [i [? ?]].
        rewrite Zlength_sublist in H19 by lia. rewrite Z.sub_0_r in H19.
        rewrite Znth_sublist in H21 by lia. rewrite Z.add_0_r in H21 by lia.
        assert (wedge_le (Znth i sorted) (Znth j sorted)). apply H1; lia.
        rewrite H21 in H22; rewrite H15 in H22. simpl in H22.
        rewrite Int.signed_repr in H22. rewrite Int.signed_repr in H22.
        assert (elabel t' e = elabel g e). apply H4. auto. lia.
        apply (weight_valid t'). auto. apply (weight_valid g). auto.
      }
      (*now that we have those properties, simplify the path*)
      pose proof (upath_simplifiable_edges msf p l (fst e) (snd e) H16 H17).
      destruct H20 as [p' [l' [? [? [? [? ?]]]]]]. exists p'; exists l'.
      split. rewrite (src_fst t'), (dst_snd t') by auto. auto.
      split. apply H21. split. auto.
      intros. apply H19. apply H24. auto.
    }
    { intros. assert (WeightedEdgeListGraph.sorted' t' ldiff'). apply sorted_sorted'. unfold ldiff'.
      apply sort_sorted. unfold sorted' in H13.
      replace (elabel g (Znth i ldiff')) with (elabel t' (Znth i ldiff')).
      replace (elabel g (Znth j ldiff')) with (elabel t' (Znth j ldiff')). apply H15; lia.
      rewrite Hpreserve_t'; auto. apply H11. apply Znth_In. lia.
      rewrite Hpreserve_t'; auto. apply H11. apply Znth_In. lia.
    }
    (*and we get the list of edges*)
    destruct H13 as [lmsf [? [? ?]]].
    rewrite (sum_LE_equiv t' (ldiff'++lsame)).
    2: { apply Permutation_sym. apply (Permutation_trans (l':=lsame++ldiff')); auto. apply Permutation_app_comm.
         apply (Permutation_trans H7'). apply NoDup_Permutation. apply NoDup_EList. apply NoDup_EList.
         intros. do 2 rewrite EList_evalid. split; auto.
    }
    rewrite (sum_LE_equiv msf (lmsf++lsame)). 2: { apply Permutation_sym. apply (Permutation_trans (l':=lmsf++lsame)). auto.
                                                   apply (Permutation_trans H14). apply NoDup_Permutation. apply NoDup_EList. apply NoDup_EList.
                                                   intros. do 2 rewrite EList_evalid. split; auto.
    }
    do 2 rewrite map_app. do 2 rewrite fold_left_app.
    replace (map (elabel (EdgeListGG_EdgeListLG msf)) lsame) with
        (map (elabel (EdgeListGG_EdgeListLG g)) lsame).
    replace (map (elabel (EdgeListGG_EdgeListLG t')) lsame) with
        (map (elabel (EdgeListGG_EdgeListLG g)) lsame).
    apply fold_left_Zadd_diff_accum.
    apply fold_left_Zadd_comp. do 2 rewrite Zlength_map. auto.
    intros. rewrite Zlength_map in H16. rewrite Znth_map by auto.
    rewrite Znth_map by lia.
    rewrite Hpreserve_msf. rewrite Hpreserve_t'. apply H15; lia.
    apply H11. apply Znth_In. lia.
    rewrite <- EList_evalid. apply (Permutation_in (l:=lmsf++lsame)). apply H14.
    apply in_or_app. left. apply Znth_In; lia.
    apply map_local_functions_eq. intros. symmetry. apply Hpreserve_t'.
    rewrite <-  EList_evalid. apply (Permutation_in (l:=lsame++ldiff')). apply H7'. apply in_or_app. left; auto.
    apply map_local_functions_eq. intros. symmetry. apply Hpreserve_msf.
    rewrite <-  EList_evalid. apply (Permutation_in (l:=lmsf++lsame)). apply H14. apply in_or_app. right; auto.
Qed.
