Require Import VST.floyd.proofauto.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.unionfind.env_unionfind_arr. (*something here massages reptype (tarray...) into list (reptype ...)*)
(*edgelist*)
Require Import CertiGraph.kruskal.spatial_wedgearray_graph.
Require Import CertiGraph.kruskal.kruskal_specs.

Lemma body_swap_edges: semax_body Vprog Gprog f_swap_edges swap_edges_spec.
Proof.
start_function.
(* don't destruct a and b, or def_wedgerep.
For some reason it lags badly attempting to solve (48s when def_wedgerep destructed)
unfold def_wedgerep in H. destruct H; destruct H1. destruct H0; destruct H3.
*)
forward. entailer!. apply H. forward.
forward. entailer!. apply H. forward.
forward. entailer!. apply H. forward.
(*put b into a*)
forward. entailer!. apply H0. forward.
forward. entailer!. apply H0. forward.
forward. entailer!. apply H0. forward.
(*put tmp into b*)
forward. forward. forward. forward. forward. forward.
entailer!.
replace b with (let (x, _) := b in x,
  (let (x, _) := let (_, y) := b in y in x, let (_, y) := let (_, y) := b in y in y)).
replace a with (let (x, _) := a in x,
  (let (x, _) := let (_, y) := a in y in x, let (_, y) := let (_, y) := a in y in y)).
auto.
destruct a. destruct c. auto.
destruct b. destruct c. auto.
Qed.

Lemma body_yucky_find_min: semax_body Vprog Gprog f_yucky_find_min yucky_find_min_spec.
Proof.
start_function.
forward. forward. entailer!.
assert (def_wedgerep (Znth lo al)). rewrite Forall_forall in H; apply H. apply Znth_In. lia. unfold def_wedgerep in H4. apply H4.
forward_for_simple_bound hi
  (EX i : Z, EX min_index: Z,
   PROP (
          lo <= min_index <= i;
          min_index < hi;
          forall j, lo <= j < i -> wedge_le (Znth min_index al) (Znth j al)
        )
   LOCAL (temp _min_index (Vint (Int.repr min_index)); temp _min_value (fst (Znth min_index al)); temp _a a;
   temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
   SEP (data_at sh (tarray t_struct_edge (Zlength al)) al a)
  )%assert.
(*precon*)
{ forward. Exists lo lo. entailer!. }
(*loop body*)
{ forward. entailer!. entailer!.
  rewrite Forall_forall in H; apply H. apply Znth_In. lia.
  replace (let (x, _) := Znth i al in x) with (fst (Znth i al)). 2: { destruct (Znth i al). auto. }
  assert (def_wedgerep (Znth i al)). rewrite Forall_forall in H; apply H. apply Znth_In. lia.
  destruct (Znth i al) as [w_i [u_i v_i]] eqn:Hi; simpl in w_i; simpl in u_i; simpl in v_i. simpl.
  unfold def_wedgerep in H6. simpl in H6. destruct H6 as [? [? ?]].
  assert (def_wedgerep (Znth min_index al)). rewrite Forall_forall in H; apply H. apply Znth_In. lia.
  destruct (Znth min_index al) as [w_min [u_min v_min]] eqn:Hmin. simpl in w_min; simpl in u_min; simpl in v_min. simpl.
  unfold def_wedgerep in H9. simpl in H9. destruct H9 as [? [? ?]].
  destruct w_i; inversion H6. rename i0 into w_i. destruct w_min; inversion H9. rename i0 into w_min.
  forward_if.
  ++apply lt_false_inv in H12.
    assert (wedge_le (Znth i al) (Znth min_index al)).
    rewrite Hi; rewrite Hmin; simpl. lia.
    forward. forward.
    Exists i. entailer!.
    split; intros.
      rewrite <- Hmin in H5.
      assert (j<=i) by lia. apply Z.le_lteq in H17. destruct H17.
      assert (wedge_le (Znth min_index al) (Znth j al)). apply H5; lia.
      rewrite Hmin in H18. rewrite Hi. assert (def_wedgerep (Znth j al)). rewrite Forall_forall in H; apply H. apply Znth_In. lia.
      destruct (Znth j al). simpl in *. unfold def_wedgerep in H19. destruct H19 as [? [? ?]]. destruct y; inversion H19.
      lia. subst j. apply wedge_le_refl. rewrite Hi; unfold def_wedgerep; split3; auto. rewrite Hi; simpl; auto.
  ++apply lt_inv in H12. forward. Exists min_index; entailer!.
    split; intros.
      assert (j<=i) by lia. apply Z.le_lteq in H16. destruct H16.
      rewrite <- Hmin in H5. apply H5; lia.
      subst j. rewrite Hi, Hmin; simpl. lia.
      rewrite Hmin; simpl; auto.
}
(*postcon*)
Intros min_index. forward. Exists min_index; entailer!.
Qed.

Lemma data_at_singleton_array_eq':
  forall (sh : Share.t) (t : type) (v : reptype t) (p : val), 
  data_at sh (Tarray t 1 noattr) [v] p = data_at sh t v p.
Proof.
intros. apply data_at_singleton_array_eq. auto.
Qed.

Lemma body_sort_edges: semax_body Vprog Gprog f_sort_edges sort_edges_spec.
Proof.
start_function.
forward_loop
  (EX i, EX bl cl: list (reptype t_struct_edge),
   PROP ( 0 <= i <= Zlength al;
          Zlength bl = i;
          Zlength cl = Zlength al - i;
          Permutation (bl++cl) al;
          forall i j, 0 <= i -> i <= j -> j < Zlength bl -> wedge_le (Znth i bl) (Znth j bl);
          forall b c, In b bl -> In c cl -> wedge_le b c
        )
   LOCAL (temp _i (Vint (Int.repr i)); temp _a a; temp _length (Vint (Int.repr (Zlength al))))
   SEP (data_at sh (tarray t_struct_edge (Zlength al)) (bl++cl) a)
  )%assert
break: (
    EX bl: list (reptype t_struct_edge),
    PROP (
      Permutation bl al;
      forall i j, 0 <= i -> i <= j -> j < Zlength bl -> wedge_le (Znth i bl) (Znth j bl)
    )
    LOCAL (temp _a a; temp _length (Vint (Int.repr (Zlength al)))
    )
   SEP (data_at sh (tarray t_struct_edge (Zlength bl)) bl a)
  )%assert.
(*precon*)
++
forward. entailer!. Exists 0. Exists (nil (A:=reptype t_struct_edge)). Exists al. entailer!.
intros. rewrite Zlength_nil in H5. lia.
(*loop*)
++
Intros i bl cl.
rename H1 into Hinv_1; rename H2 into Hinv_2;
rename H3 into Hinv_3; rename H4 into Hinv_4;
rename H5 into Hinv_5; rename H6 into Hinv_6.
forward_if.
--
(*main loop: i < Zlength al - 1*)
assert (Zlength (bl++cl) = Zlength al). apply Permutation_Zlength. auto.
forward_call (sh, a, bl++cl, i, Zlength al). rewrite H2. entailer!.
split3; auto. split3. apply (Forall_permutation al); auto. apply Permutation_sym; auto.
lia. lia.
Intros j.
assert (1 <= Zlength cl). { lia. }
forward_if
  (EX cl': list (reptype t_struct_edge),
   PROP ( Permutation cl' cl;
          forall c, In c cl' -> wedge_le (Znth 0 cl') c
        )
   LOCAL (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i)); temp _a a; temp _length (Vint (Int.repr (Zlength al))))
   SEP (data_at sh (tarray t_struct_edge (Zlength (bl ++ cl'))) (bl ++ cl') a)
  )%assert.
**
(*split the array*)
rewrite H2.
replace (bl++cl) with (sublist 0 (j+1) (bl++cl) ++ sublist (j+1) (Zlength al) (bl++cl)).
2: { symmetry. rewrite <- (sublist_same 0 (Zlength (bl++cl))) at 1 by lia.
  rewrite <- H2. apply (sublist_split 0 (j+1)); lia.
}
rewrite (split2_data_at_Tarray_app (j+1) (Zlength al) sh t_struct_edge).
2: { rewrite Zlength_sublist; lia. }
2: { rewrite Zlength_sublist; lia. }
replace (sublist 0 (j + 1) (bl ++ cl)) with (sublist 0 j (bl++cl) ++ sublist j (j+1) (bl++cl)). 2: {
  symmetry. apply (sublist_split 0 j (j+1)); lia.
}
rewrite (split2_data_at_Tarray_app j (j+1) sh t_struct_edge).
2: { rewrite Zlength_sublist; lia. }
2: { rewrite Zlength_sublist; lia. }
rewrite (sublist_one j (j+1)) by lia.
replace (sublist 0 j (bl ++ cl)) with (sublist 0 (i+1) (bl++cl) ++ sublist (i+1) j (bl++cl)). 2: {
  symmetry. apply (sublist_split 0 (i+1)); lia.
}
rewrite (split2_data_at_Tarray_app (i+1) j sh t_struct_edge).
2: { rewrite Zlength_sublist; lia. }
2: { rewrite Zlength_sublist; lia. }
replace (sublist 0 (i+1) (bl ++ cl)) with (sublist 0 i (bl++cl) ++ sublist i (i+1) (bl++cl)). 2: {
  symmetry. apply (sublist_split 0 i); lia.
}
rewrite (split2_data_at_Tarray_app i (i+1) sh t_struct_edge).
2: { rewrite Zlength_sublist; lia. }
2: { rewrite Zlength_sublist; lia. }
rewrite (sublist_one i (i+1)) by lia.
(*now replace the singletons*)
replace (i+1-i) with 1 by lia.
replace (j+1-j) with 1 by lia.
rewrite (data_at_singleton_array_eq' sh (t_struct_edge) (Znth i (bl++cl))).
rewrite (data_at_singleton_array_eq' sh (t_struct_edge) (Znth j (bl++cl))).
set (ai:= field_address0 (tarray t_struct_edge (i + 1)) [ArraySubsc i] a).
assert_PROP(isptr ai). rewrite data_at_isptr. entailer!.
assert (Hai_offset: ai = offset_val (12*i) a). {
  unfold ai; rewrite field_address0_clarify. simpl. auto. fold ai. apply isptr_is_pointer_or_null. auto.
}
set (aj:= field_address0 (tarray t_struct_edge (j + 1)) [ArraySubsc j] a).
assert_PROP(isptr aj). rewrite data_at_isptr. entailer!.
assert (Haj_offset: aj = offset_val (12*j) a). {
  unfold aj; rewrite field_address0_clarify. simpl. auto. fold aj. apply isptr_is_pointer_or_null. auto.
}
(*ok, call!*)
forward_call (sh, (Znth i (bl++cl)), (Znth j (bl++cl)),
  (field_address0 (tarray t_struct_edge (i + 1)) [ArraySubsc i] a),
  (field_address0 (tarray t_struct_edge (j + 1)) [ArraySubsc j] a)).
entailer!.
****
simpl. rewrite Hai_offset, Haj_offset. auto.
****
entailer!.
****
split3. 3: split. auto. auto.
rewrite Forall_forall in H0; apply H0. apply (Permutation_in (l:=bl++cl)); auto.
apply Znth_In. lia.
rewrite Forall_forall in H0; apply H0. apply (Permutation_in (l:=bl++cl)); auto.
apply Znth_In. lia.
****
(*postcon of swap*)
Exists ([Znth j (bl++cl)] ++ (sublist (i+1) j (bl++cl)) ++ [Znth i (bl++cl)] ++ sublist (j+1) (Zlength al) (bl++cl)).
(*Exists (upd_Znth i (upd_Znth j cl (Znth i cl)) (Znth j cl)).*)
entailer!.
****** (*PROPS*)
split.
{ apply (Permutation_trans (l':=([Znth (Zlength bl) (bl ++ cl)] ++
   sublist (Zlength bl + 1) j (bl ++ cl) ++
   [Znth j (bl ++ cl)] ++ sublist (j + 1) (Zlength al) (bl ++ cl)))). 2: {
  replace [Znth j (bl++cl)] with (sublist j (j+1) (bl++cl)). 2: { rewrite sublist_one by lia. auto. }
  replace [Znth (Zlength bl) (bl++cl)] with (sublist (Zlength bl) (Zlength bl +1) (bl++cl)). 2: { rewrite sublist_one by lia. auto. }
  rewrite sublist_rejoin by lia. rewrite sublist_rejoin by lia. rewrite sublist_rejoin by lia.
  rewrite sublist_app2, Z.sub_diag, sublist_same by lia. apply Permutation_refl.
  }
repeat rewrite app_assoc. apply Permutation_app_tail.
rewrite <- app_assoc.
apply (Permutation_trans (l':=
  (sublist (Zlength bl + 1) j (bl ++ cl) +:: Znth (Zlength bl) (bl ++ cl)) ++ [Znth j (bl ++ cl)])).
apply Permutation_app_comm. apply Permutation_app_tail. apply Permutation_app_comm.
}
{ intros. rewrite Znth_app1. 2: rewrite Zlength_cons, Zlength_nil; lia. rewrite Znth_0_cons.
assert (In c cl). {
  apply in_app_or in H22. destruct H22. destruct H22. 2: contradiction.
  rewrite Znth_app2 in H22 by lia. rewrite <- H22. apply Znth_In; lia.
  apply in_app_or in H22. destruct H22.
  rewrite sublist_app2 in H22 by lia. apply sublist_In in H22. auto.
  apply in_app_or in H22. destruct H22. destruct H22. 2: contradiction.
  rewrite Znth_app2 in H22 by lia. subst c. apply Znth_In; lia.
  rewrite sublist_app2 in H22 by lia. apply sublist_In in H22. auto.
}
rewrite In_Znth_iff in H23. destruct H23 as [k [? ?]]. rewrite <- H24.
replace (Znth k cl) with (Znth (Zlength bl + k) (bl++cl)). 2: {
  rewrite Znth_app2 by lia. replace (Zlength bl + k - Zlength bl) with k by lia. auto.
}
apply H4. lia.
}
****** (*SEP*)
replace (Zlength
            (bl ++
             [Znth j (bl ++ cl)] ++
             sublist (Zlength bl + 1) j (bl ++ cl) ++
             [Znth (Zlength bl) (bl ++ cl)] ++ sublist (j + 1) (Zlength al) (bl ++ cl))) with (Zlength al). 2: {
  rewrite <- H2. repeat rewrite Zlength_app.
  rewrite Zlength_cons, Zlength_nil. rewrite Zlength_cons, Zlength_nil.
  rewrite Zlength_sublist by lia. rewrite Zlength_sublist by lia. lia.
}
(*do the splits again*)
repeat rewrite app_assoc.
rewrite (split2_data_at_Tarray_app (j+1) (Zlength al) sh t_struct_edge).
2: { repeat rewrite Zlength_app. repeat rewrite Zlength_cons. repeat rewrite Zlength_nil.
rewrite Zlength_sublist by lia. lia. }
2: { rewrite Zlength_sublist by lia. lia. }
rewrite (split2_data_at_Tarray_app j (j+1) sh t_struct_edge).
2: { repeat rewrite Zlength_app. repeat rewrite Zlength_cons. repeat rewrite Zlength_nil.
rewrite Zlength_sublist by lia. lia. }
2: { rewrite Zlength_cons, Zlength_nil. lia. }
rewrite (split2_data_at_Tarray_app (Zlength bl+1) j sh t_struct_edge).
2: { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
2: { rewrite Zlength_sublist by lia; lia. }
rewrite (split2_data_at_Tarray_app (Zlength bl) (Zlength bl+1) sh t_struct_edge).
2: lia.
2: { rewrite Zlength_cons, Zlength_nil; lia. }
replace (j+1-j) with 1 by lia. replace (Zlength bl + 1 - Zlength bl) with 1 by lia.
rewrite (data_at_singleton_array_eq' sh (t_struct_edge) (Znth (Zlength bl) (bl++cl))).
rewrite (data_at_singleton_array_eq' sh (t_struct_edge) (Znth j (bl++cl))).
replace (sublist 0 (Zlength bl) (bl++cl)) with bl. 2: {
  rewrite sublist_app1 by lia. rewrite sublist_same by lia; auto.
}
entailer!.
**
(*i = j, no swap*)
forward. Exists cl. entailer!.
assert (j = Zlength bl) by lia. subst j.
intros. apply In_Znth_iff in H9. destruct H9 as [k [? ?]]. rewrite <- H10.
replace (Znth 0 cl) with (Znth (Zlength bl) (bl++cl)). 2: {
  rewrite Znth_app2, Z.sub_diag; auto.
}
replace (Znth k cl) with (Znth (Zlength bl + k) (bl++cl)). 2: {
  rewrite Znth_app2 by lia. replace (Zlength bl + k - Zlength bl) with k by lia. auto.
}
apply H4. lia.
** (*after*)
Intros cl'. forward. Exists (i+1). Exists (bl+:: Znth 0 cl'). Exists (sublist 1 (Zlength cl) cl').
assert (Zlength cl' = Zlength cl). apply Permutation_Zlength; auto.
assert (Hpost1: Zlength (bl +:: Znth 0 cl') = Zlength bl + 1).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
assert (Hpost2: Zlength (sublist 1 (Zlength cl) cl') = Zlength al - (Zlength bl + 1)).
  rewrite <- H8. rewrite Zlength_sublist by lia. lia.
assert (Hpost3: Permutation (bl +:: Znth 0 cl' ++ sublist 1 (Zlength cl) cl') al). {
  rewrite <- app_assoc. rewrite <- H8. replace ([Znth 0 cl'] ++ sublist 1 (Zlength cl') cl') with cl'.
  apply (Permutation_trans (l':=bl++cl)). apply Permutation_app_head; auto. apply Hinv_4.
  rewrite <- (sublist_same 0 (Zlength cl') cl') at 1 by lia.
  rewrite (sublist_split 0 1 (Zlength cl')) by lia. rewrite sublist_one by lia. auto.
}
entailer!.
split.
****
intros. apply Z.le_lteq in H13; destruct H13.
2: { subst j0. apply wedge_le_refl. rewrite Forall_forall in H0; apply H0.
  apply (Permutation_in (l:=(bl +:: Znth 0 cl' ++ sublist 1 (Zlength cl) cl') )). auto.
  apply in_or_app. left. apply Znth_In. auto.
}
rewrite Zlength_app, Zlength_cons, Zlength_nil in H14.
assert (j0 <= Zlength bl) by lia. assert (i < Zlength bl) by lia.
replace (Znth i (bl+:: Znth 0 cl')) with (Znth i bl). 2: { rewrite Znth_app1; auto. }
apply Z.le_lteq in H15. destruct H15.
replace (Znth j0 (bl+:: Znth 0 cl')) with (Znth j0 bl). 2: { rewrite Znth_app1; auto. }
apply Hinv_5; lia.
subst j0. rewrite Znth_app2, Z.sub_diag by lia. rewrite Znth_0_cons.
apply Hinv_6. apply Znth_In; lia. apply (Permutation_in (l:=cl')). auto. apply Znth_In; lia.
****
intros. apply in_app_or in H12. destruct H12.
apply Hinv_6. auto. apply (Permutation_in (l:=cl')). auto. apply (sublist_In 1 (Zlength cl)). auto.
simpl in H12. destruct H12. 2: contradiction. subst b.
assert (In c cl'). apply (sublist_In 1 (Zlength cl)). auto.
apply H7; auto.
****
assert (Zlength cl' = Zlength cl). apply Permutation_Zlength. auto. rewrite <- H12.
replace (Zlength (bl++cl')) with (Zlength al).
replace (bl +:: Znth 0 cl' ++ sublist 1 (Zlength cl') cl') with (bl++cl'). auto.
rewrite <- app_assoc.
  rewrite <- (sublist_same 0 (Zlength cl') cl') at 1 by lia.
  rewrite (sublist_split 0 1 (Zlength cl')) by lia. rewrite sublist_one by lia.
replace (Zlength cl) with (Zlength cl'). auto.
rewrite <- H2. do 2 rewrite Zlength_app. lia.
--
(*break*)
forward.
assert (i = Zlength al - 1 \/ i = Zlength al). {
  destruct Hinv_1. apply Z.le_lteq in H3. destruct H3. left; lia. right; auto.
}
destruct H2.
**
(*i = Zlength al - 1. That means cl is a singleton*)
(*hm straight to the postcon*)
Exists (bl++cl). entailer!.
2: { replace (Zlength al) with (Zlength (bl++cl)); auto. }
intros.
assert (Zlength cl = 1) by lia.
destruct cl. rewrite Zlength_nil in H9; lia. destruct cl.
2: { do 2 rewrite Zlength_cons in H9. assert (0 <= Zlength cl). apply (Zlength_nonneg). lia. }
rewrite Zlength_app, Zlength_cons, Zlength_nil in H8. simpl in H8.
assert (x0 <= Zlength bl) by lia. apply Z.le_lteq in H10. destruct H10.
rewrite Znth_app1 by lia. rewrite Znth_app1 by lia. apply Hinv_5; lia.
replace (Znth x0 (bl+::r)) with r. 2: { rewrite Znth_app2. rewrite H10. rewrite Z.sub_diag. simpl; auto. lia. }
apply Z.le_lteq in H7. destruct H7.
apply Hinv_6. replace (Znth x (bl+::r)) with (Znth x bl). apply Znth_In; auto. lia.
rewrite Znth_app1. auto. lia.
left; auto.
subst x. replace (Znth x0 (bl+::r)) with r. 2: { rewrite Znth_app2. rewrite H10. rewrite Z.sub_diag. simpl; auto. lia. }
apply wedge_le_refl. rewrite Forall_forall in H0; apply H0.
apply (Permutation_in (l:= (bl+::r))). auto. apply in_or_app. right; left; auto.
**
(*i = Zlength al. That means cl = nil*)
assert (cl = nil). rewrite H2 in Hinv_3. rewrite Z.sub_diag in Hinv_3. apply Zlength_nil_inv in Hinv_3. auto.
rewrite H3. rewrite app_nil_r.
Exists bl. entailer!.
rewrite app_nil_r in Hinv_4. auto.
rewrite H2. auto.
++
(*postcon*)
Intros bl. forward. Exists bl. entailer!.
apply Permutation_sym; auto.
Qed.