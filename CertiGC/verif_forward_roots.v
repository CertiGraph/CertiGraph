Require Import CertiGraph.CertiGC.gc_spec.

Lemma frames_rep_ptr_or_null: forall sh frames,
  frames_rep sh frames |-- !! is_pointer_or_null (frames_p frames).
  Proof.
    destruct frames as [|[???]?]; simpl; entailer.
  unfold frames_rep.
  simpl.
  Intros.
  sep_apply data_at_isptr; Intros.
  apply prop_right.
  auto.
Qed.

#[export] Hint Resolve frames_rep_ptr_or_null : saturate_local.

Lemma frames_rep_valid_pointer: forall sh frames, 
   sepalg.nonidentity sh ->
   frames_rep sh frames |-- valid_pointer (frames_p frames).
Proof.
  intros.
  destruct frames as [|[???]?]; simpl frames_p; unfold frames_rep; simpl; auto with valid_pointer.
Qed.
#[export] Hint Resolve frames_rep_valid_pointer: valid_pointer.

#[export] Instance Inh_frame: Inhabitant frame := Build_frame nullval nullval nil.

Lemma frames_shell_rep_isolate:
  forall sh frs k,
   0 <= k < Zlength frs ->
   frames_shell_rep sh frs |-- 
     frame_shell_rep sh (Znth k frs) (frames_p (sublist (k+1) (Zlength frs) frs)) *
      (frame_shell_rep sh (Znth k frs) (frames_p (sublist (k+1) (Zlength frs) frs)) -* frames_shell_rep sh frs).
Proof.
  induction frs; simpl; intros.
  list_solve.
  destruct (zeq k 0).
  - subst k.
    change (a::frs) with ([a]++frs).
    autorewrite with sublist.
    cancel.
    apply wand_sepcon_adjoint. cancel.
  - 
    change (a::frs) with ([a]++frs).
    replace (Znth k ([a]++frs)) with (Znth (k-1) frs) by list_solve.
    autorewrite with sublist.
    specialize (IHfrs (k-1)).
    replace (k-1+1) with k in IHfrs by lia.
    sep_apply IHfrs; clear IHfrs. list_solve. cancel.
    apply -> wand_sepcon_adjoint.
    cancel.
    apply wand_sepcon_adjoint.
    cancel.
Qed.
    
Lemma frr_Zlength: forall from to roots g roots' g',
  forward_roots_relation from to roots g roots' g' -> Zlength roots = Zlength roots'.
Proof.
   induction 1; simpl; autorewrite with sublist; auto; lia. 
Qed.

Lemma Zlength_update_frames:
 forall frs roots,
   Zlength roots = Zlength (frames2roots frs) -> 
   Zlength (update_frames frs roots) = Zlength frs.
   induction frs; simpl; intros; auto.
   destruct a; simpl in *; autorewrite with sublist. f_equal. apply IHfrs; clear IHfrs.
   unfold frames2roots in *.
   simpl in *. list_solve.
Qed.

Lemma frames2rootpairs_app: forall al bl, frames2rootpairs (al++bl) = frames2rootpairs al ++ frames2rootpairs bl.
Proof.
 unfold frames2rootpairs.
 induction al; simpl; intros; auto.
 rewrite <- app_assoc. f_equal. auto.
Qed.

Lemma frames2rootpairs_cons: forall a bl, frames2rootpairs (a::bl) = frame2rootpairs a ++ frames2rootpairs bl.
Proof.
 intros.
 reflexivity.
Qed.

Lemma Zlength_frames2rootpairs_sublist:
 forall k frs, 0 <= k <= Zlength frs -> 
   Zlength (frames2rootpairs (sublist 0 k frs)) <= Zlength(frames2rootpairs frs).
Proof.
  intros ? ? H2.
  revert k H2; induction frs; simpl; intros.
      assert (k=0) by list_solve. subst k.
      autorewrite with sublist. lia.
      destruct (zeq k 0).
      subst k. autorewrite with sublist. rep_lia.
      rewrite sublist_0_cons by lia.
      rewrite !frames2rootpairs_cons, !Zlength_app.
      specialize (IHfrs (k-1) ltac:(list_solve)).
      set (j := sublist _ _ _) in *. clearbody j.
      unfold frames2rootpairs in *.
      rewrite !Zlength_concat in *.
      simpl in *. lia.
Qed.

Lemma frames_p_update_frames_sublist:
 forall frs roots k, 
    Zlength (frames2roots frs) = Zlength roots ->
    0 <= k <= Zlength frs ->
    frames_p (sublist k (Zlength frs) frs) = frames_p (sublist k (Zlength frs) (update_frames frs roots)).
Proof.
unfold frames2roots. 
induction frs as [|[???]?]; intros; simpl in *; auto.
rewrite Zlength_app in H.
rewrite !Zlength_cons in  *.
destruct (zeq k 0).
- subst k.
 rewrite !sublist_0_cons by list_solve. reflexivity. 
- rewrite !(sublist_pos_cons k) by lia.
  replace (Z.succ (Zlength frs) - 1) with (Zlength frs) by lia.
  apply IHfrs; clear IHfrs. list_solve. lia. 
Qed.

Lemma frames_p_isptr:
  forall sh frs,
    frames_shell_rep sh frs |-- !! forall k, 0 <= k < Zlength frs -> isptr (frames_p (sublist k (Zlength frs) frs)).
Proof.
  induction frs; simpl; intros.
  apply prop_right; list_solve.
  sep_apply IHfrs. Intros.
  rewrite prop_forall. apply allp_right. intro k.
  rewrite prop_forall. apply allp_right. intro.
  destruct (zeq k 0).
  subst. autorewrite with sublist.
  destruct a; simpl. Intros.
  entailer!.
  rewrite sublist_pos_cons by lia.
  sep_apply IHfrs.
  rewrite sepcon_andp_prop'.
  apply derives_extract_prop; intro.
  apply prop_right.
  autorewrite with sublist.
  replace (Z.succ (Zlength frs) - 1) with (Zlength frs) by lia.
  apply H0.
  list_solve.
Qed.

Lemma roots_weak_valid_pointer:
 (* This lemma does not seem to be needed, fortunately *)
     forall sh frs roots k,
       readable_share sh ->
       Zlength roots = Zlength (frames2rootpairs frs) ->
       field_compatible0 (tarray int_or_ptr_type (Zlength (fr_roots (Znth k frs)))) [] (fr_root (Znth k frs)) ->
       0 <= k < Zlength frs ->
       forall i, 
       0 <= i <= Zlength (fr_roots (Znth k frs)) ->
       roots_rep sh (frames2rootpairs (update_frames frs roots)) |-- 
         weak_valid_pointer 
           (field_address0 (tarray int_or_ptr_type (Zlength (fr_roots (Znth k frs)))) (SUB i) 
              (fr_root (Znth k frs))).
Proof.
unfold frames2rootpairs.
induction frs as [|[???]?]; simpl; intros.
list_solve.
unfold roots_rep in *.
unfold frame2rootpairs at 1 in H0.
unfold frame2rootpairs at 1.
rewrite iter_sepcon_app_sepcon.
assert (Zlength fr_roots <= Zlength roots).
 { rewrite H0. rewrite Zlength_app. simpl.
   rewrite Zlength_frame2rootpairs'. rep_lia.
 }
destruct (zeq k 0).
- subst k. rewrite !Znth_0_cons in *. simpl in *.
  clear H2.
  apply sepcon_weak_valid_pointer1; clear IHfrs.
  rewrite iter_sepcon_frame2rootpairs'.
  2: rewrite Zlength_sublist, Z.sub_0_r; auto; try list_solve.
  rewrite Zlength_sublist, Z.sub_0_r by list_solve.
  destruct (zeq 0 (Zlength fr_roots)).
  + rewrite <- e in *. assert (i=0) by lia. subst i. 
      autorewrite with sublist.
      unfold field_address0; rewrite if_true by auto with field_compatible.
      simpl.
      eapply derives_trans; [ |apply valid_pointer_weak].
      pose proof (proj1 H1).
      autorewrite with norm.
      Search data_at valid_pointer. 
      destruct fr_root; try solve [destruct H1; contradiction].
      shelve. (* false! see below at Unshelve *)
  +
  assert (0 < Zlength fr_roots) by rep_lia.
  forget (Zlength fr_roots) as j.
  clear - H3 H4 H H2.
  sep_apply data_at_data_at_.
  rewrite data_at__memory_block. Intros.
  unfold field_address0.
  rewrite if_true by auto with field_compatible.
  simpl. rewrite Z.add_0_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; auto. lia.
  nia.
- rewrite (Znth_pos_cons k) in * by lia. 
  simpl in *.
  apply sepcon_weak_valid_pointer2.
  apply IHfrs; clear IHfrs; auto.
  2:list_solve.
  rewrite Zlength_app in H0.
  rewrite Zlength_frame2rootpairs' in H0. list_solve.
Unshelve.
(* This is not provable! Fortunately we don't seem to need it. *)
Abort.

Lemma frr_app_inv: forall from to ra g1 ra' rb rb' g3,
   forward_roots_relation from to (ra++rb) g1 (ra'++rb') g3 ->
   Zlength ra = Zlength ra' ->
   exists g2, forward_roots_relation from to ra g1 ra' g2 /\ 
        forward_roots_relation from to rb g2 rb' g3.
Proof.
 intros.
 remember (ra++rb) as rab. remember (ra'++rb') as rab'.
   revert ra ra' rb rb' Heqrab Heqrab' H0.
   induction H; intros; destruct ra, ra'; inv Heqrab; inv  Heqrab'; simpl in *; subst.
   + exists g; split; constructor.
   + exists g1; split. constructor. econstructor; eauto.
   + list_solve.
   + list_solve.
   + edestruct IHforward_roots_relation as [g4 [? ?]].
     4:{ exists g4. split; try eassumption. econstructor; eauto. }
     auto. auto. list_solve.
Qed.

Lemma frr_app: forall from to ra g1 ra' g2 rb rb' g3,
  forward_roots_relation from to ra g1 ra' g2 ->
  forward_roots_relation from to rb g2 rb' g3 ->
  forward_roots_relation from to (ra++rb) g1 (ra'++rb') g3.
Proof.
 intros.
 revert rb' g3 H0; induction H; intros; auto.
 simpl.
 econstructor; eauto.
Qed.

Lemma sc_Zlength:  forall [g h rps rs outliers],
  super_compatible g h rps rs outliers ->
    Zlength rs = Zlength rps.
  Proof.
   intros.
   destruct H as [_ [? _]].
   apply (f_equal (@Zlength _)) in H.
  list_solve.
Qed.

Lemma body_forward_roots: semax_body Vprog Gprog f_forward_roots forward_roots_spec.
Proof.
  start_function.
  unfold thread_info_rep. Intros.
  forward.
  fold (frames_p fr).
  rename fr into frs.
  pose (n := Zlength frs).
  pose (nr k := (Zlength (frames2rootpairs (sublist 0 k frs)))).
  pose (oldroots k i := sublist (nr k + i) (Zlength roots) roots).
  assert_PROP (forall k, 0 <= k < Zlength frs -> isptr (frames_p (sublist k (Zlength frs) frs))) as FRAMESP. { 
    unfold frames_rep. sep_apply frames_p_isptr. entailer!.
  }
  forward_while (EX k: Z,
                 EX g': LGraph, EX h': heap, EX roots': roots_t,
      PROP (0 <= k <= n;
            forward_roots_relation from to (sublist 0 (nr k) roots) g roots' g';
            heap_relation h h';
            super_compatible g' h' 
                (update_rootpairs (frames2rootpairs frs) (map (root2val g') (roots'++oldroots k 0))) 
                (roots'++oldroots k 0)
                outlier;
            forward_condition g' h' from to)
      LOCAL (temp _frame (frames_p (sublist k n frs));
             temp _from_start (gen_start g' from);
             temp _from_limit (limit_address g' h' from);
             temp _next (heap_next_address hp to))
      SEP (all_string_constants rsh gv;
           outlier_rep outlier;
           graph_rep g';
           frames_rep sh (update_frames frs (map (root2val g') (roots'++oldroots k 0)));
           heap_rep sh h' hp))%assert.
  - Exists 0 g h (@nil root_t).
    simpl app.
    unfold oldroots, nr. autorewrite with sublist.
    pose proof (proj1 (proj2 H)). red in H2. rewrite H2.
    rewrite <- frames2roots_eq.
    rewrite update_rootpairs_frames2rootpairs by auto.
    rewrite update_frames_same.
    entailer!!.
    split. constructor. apply hr_refl. 
  - Intros.
    unfold frames_rep.
    assert (LEN: Zlength (roots' ++ oldroots k 0) = Zlength (frames2rootpairs frs)). {
    apply sc_Zlength in H, H5.
    apply frr_Zlength in H3.
    pose proof (Zlength_frames2rootpairs_sublist _ _ H2).
    rewrite Zlength_app, <- H3.
    unfold oldroots. unfold nr.
    list_solve.
    }
    rewrite <- frames_shell_rep_update by (rewrite Zlength_map; auto).
    assert (frames_shell_rep sh frs |-- valid_pointer (frames_p (sublist k n frs))). {
      clear - SH0 H2. subst n.
      revert k H2; induction frs as [ | [? ? ?] ?]; simpl; intros.
      +
      assert (k=0) by list_solve. subst k.
      autorewrite with sublist. unfold frames_p. auto with valid_pointer.
      +
      Intros.
      destruct (zeq k 0).
      * subst. autorewrite with sublist. simpl. auto with valid_pointer.
      * specialize (IHfrs (k-1)). rewrite Zlength_cons.
      rewrite sublist_pos_cons by list_solve.
      replace (Z.succ _ - _) with (Zlength frs) by lia.
      apply sepcon_valid_pointer2.
      apply IHfrs. clear - H2 n. list_solve.     
    }
    entailer!.
  - assert (k<n). {
     assert (~(k>=n)); [intro | lia].
     autorewrite with sublist in HRE. contradiction HRE. reflexivity.
    }
    rewrite (sublist_split k (k+1) n) by list_solve.
    rewrite (sublist_len_1 k) by list_solve.
    simpl frames_p.
    set (frs' := update_frames _ _).
    unfold frames_rep.
    sep_apply (frames_shell_rep_isolate sh frs' k). {
     clear - H5 H3 H2 H H7.
     subst frs' n.
     apply sc_Zlength in H,H5.
     apply frr_Zlength in H3.
     rewrite Zlength_update_frames. lia.
     rewrite Zlength_map.
     subst oldroots. simpl. autorewrite with sublist. rewrite frames2roots_eq, Zlength_map.
     rewrite <- H, <- H3.
     assert (0 <= nr k <= Zlength roots); [ | list_solve].
     unfold nr. 
     rewrite H.
     pose proof (Zlength_frames2rootpairs_sublist _ _ H2).
     rep_lia.
    }
    set (OTHERS := _ -* _).
    set (NEXT := frames_p (sublist _ _ _)).
    destruct (Znth k frs') as [a r s] eqn:?H.
    unfold frame_shell_rep.
    Intros.
    assert (Hfrs': Zlength (map (root2val g') (roots'++oldroots k 0)) = Zlength roots). {
      apply frr_Zlength in H3. apply sc_Zlength in H.
      autorewrite with sublist. rewrite <- H3.
      unfold oldroots. rewrite Z.add_0_r.
      assert (0 <= nr k <= Zlength roots); [ | list_solve].
      unfold nr. 
      pose proof (Zlength_frames2rootpairs_sublist _ _ H2). list_solve.
    }
    assert (LENfrs': Zlength frs' = Zlength frs). {
      apply sc_Zlength in H.
      subst frs'. apply Zlength_update_frames. 
      rewrite frames2roots_eq; list_solve.
    }
    replace (fr_adr (Znth k frs)) with a.
    2:{
      replace a with (fr_adr (Znth k frs')) by (rewrite H8; auto).
      apply sc_Zlength in H. rewrite  H in Hfrs'.
      clear - H2 Hfrs'. subst n frs'.
      set (jj := map _ _) in *. clearbody jj.
      clear - Hfrs' H2.
      revert jj Hfrs' k H2; induction frs as [ | [???] ?]; simpl; intros; auto.
      destruct (zeq k 0). subst k. autorewrite with sublist; simpl; auto.
      rewrite !Znth_pos_cons by lia.
      apply IHfrs; clear IHfrs; [ | list_solve].
      rewrite frames2rootpairs_cons in Hfrs'.
      rewrite Zlength_app in Hfrs'. rewrite Zlength_frame2rootpairs in Hfrs'.
      simpl in *. list_solve.
    }
    forward. forward.
    entailer!. {
       clear - H9.
       unfold field_address0.
       rewrite if_true. simpl. destruct H9, r; try contradiction; hnf; auto.
       apply arr_field_compatible0; auto. rep_lia.
    }
    forward. {
      rewrite arr_field_address0 by (auto with field_compatible; list_solve).
      entailer!.
      apply prop_right. rewrite sameblock_symm. hnf; auto.
      rewrite isptr_offset_val_sameblock; auto.
    }
    forward. {
      unfold NEXT.
      simpl tc_val.
      entailer!.
      subst frs'.
      apply sc_Zlength in H.
      replace (Zlength _) with (Zlength frs).
      rewrite <- frames_p_update_frames_sublist
          by (try (rewrite frames2roots_eq, Zlength_map, <- H); list_solve).
      destruct (zeq (k+1) (Zlength frs)).
      rewrite e. autorewrite with sublist. hnf. auto.
      apply isptr_is_pointer_or_null; apply FRAMESP; list_solve.
    }
    replace (force_val _) with (vptrofs (Zlength s)). 2: {
      rewrite arr_field_address0 by (auto with field_compatible; list_solve).
    simpl sem_binary_operation'.
    destruct r; try solve [exfalso; destruct H9; contradiction].
    unfold sem_sub_pp. simpl force_val; rewrite if_true by auto.
    simpl force_val.
    rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
    unfold WORD_SIZE in H10.
    rewrite ptrofs_divs_repr by rep_lia.
    rewrite (Z.mul_comm 8). rewrite Z.quot_mul by lia.
    auto.
    }
    forward_for_simple_bound (Zlength s) 
       (EX i: Z,  EX g'': LGraph, EX h'': heap, EX roots'':roots_t,
       PROP (
         forward_roots_relation from to (sublist 0 (nr k + i) roots) g roots'' g'';
         heap_relation h' h'';
         super_compatible g'' h'' 
           (update_rootpairs (frames2rootpairs frs) (map (root2val g'') (roots''++oldroots k i))) 
           (roots''++oldroots k i)
           outlier;
           forward_condition g'' h'' from to)
        LOCAL (temp _frame NEXT; temp _limit  (vptrofs (Zlength s));
              temp _from_start (gen_start g'' from); temp _from_limit (limit_address g'' h'' from);
              temp _start r; temp _next (heap_next_address hp to))
        SEP (all_string_constants rsh gv; outlier_rep outlier; graph_rep g'';
             data_at sh (Tstruct _stack_frame noattr)
             (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB Zlength s) r, (r, NEXT)) a; 
             OTHERS; 
            roots_rep sh (frames2rootpairs (update_frames frs (map (root2val g'') (roots''++oldroots k i))));
            heap_rep sh h'' hp))%assert.
  + unfold WORD_SIZE in H10; rep_lia.
  + Exists g' h' roots'.
    entailer!!; [ split | ]; auto.
    subst frs'.
    apply derives_refl.
  + set (rp'' := frames2rootpairs (update_frames _ _)).
    Intros.
    rename H2 into H2'; assert (H2: 0 <= k < n) by (destruct H2'; auto); clear H2'.
    clear H7; assert (H7 := I).
    assert (Hnr: (0 <= nr k /\ nr k + Zlength s <= Zlength roots) /\ Zlength s = Zlength (fr_roots (Znth k frs))). {
      rewrite and_assoc.
      subst nr; cbv beta. split. rep_lia.
      apply sc_Zlength in H.
      revert Hfrs'; set (r' := map _ _) in *; intros; clearbody r'.
      assert (fr_roots (Znth k frs') = s) by (rewrite H8; reflexivity).
      rewrite H in Hfrs'|-*.
      assert (0 <= k < n) by (destruct H2; split; auto).
      clear - H16 Hfrs' H17.
      subst frs' s n.
      revert r' k H17 Hfrs'; induction frs as [|[a r s]]; simpl; intros.
      list_solve.
      rewrite !frames2rootpairs_cons, !Zlength_app in *.
      destruct (zeq k 0).
      subst k.
      autorewrite with sublist in *.
      simpl in *.
      autorewrite with sublist.
      list_solve.
      autorewrite with sublist in H17.
      rewrite sublist_0_cons by lia.
      rewrite Znth_pos_cons by lia.
      autorewrite with sublist. simpl.
      rewrite frames2rootpairs_cons.
      autorewrite with sublist in *. simpl in *.
      rewrite Znth_pos_cons by lia.
      destruct (IHfrs (sublist (Zlength s) (Zlength r') r') (k-1)); try lia; clear IHfrs.
      list_solve.
    }
    destruct Hnr as [Hnr Hi].
    assert (LENroots'': Zlength roots'' = nr k + i)
       by (apply frr_Zlength in H12; list_solve). 
    forward_call (rsh,sh,gv,g'',h'',hp,rp'',roots''++oldroots k i,outlier,from,to,0, @inl _ (VType*Z) (nr k+i)).
    * entailer!!.
      simpl. f_equal. f_equal. f_equal. f_equal.
      subst rp''.
      apply frr_Zlength in H12.
      apply sc_Zlength in H.
      clear - H12 H8 H7 H2 H5 H3 H11 H Hnr Hi Hfrs' LENfrs'.
      unfold oldroots.
      replace r with (fr_root (Znth k frs')) by (rewrite H8; reflexivity).
      set (r3 := map (root2val g'') (roots'' ++ sublist (nr k + i) (Zlength roots) roots)).
      assert (Zlength r3 = Zlength (frames2rootpairs frs))
         by (subst r3; list_solve).
      rewrite <- frame_root_address_eq.
      2:{ rewrite <- update_rootpairs_frames2rootpairs
            by (rewrite frames2roots_eq; list_solve).
          rewrite Zlength_update_rootpairs by auto.
          list_solve.
      }
      rewrite frame_root_address_same
        by (rewrite ?frames2roots_eq; list_solve). 
      rewrite <- (frame_root_address_same frs (map (root2val g') (roots' ++ oldroots k 0)))
         by (rewrite ?frames2roots_eq; list_solve). 
      fold frs'.
      subst n.
      rewrite <- LENfrs' in H2.
      unfold nr.
      replace (Zlength (frames2rootpairs (sublist 0 k frs)))
         with (Zlength (frames2rootpairs (sublist 0 k frs'))).
      2:{
        forget (map (root2val g') (roots' ++ oldroots k 0)) as new.
        pose proof Zlength_update_frames frs new ltac:(rewrite frames2roots_eq; list_solve).        fold frs' in H1. rewrite H1 in H2.
        rewrite H in Hfrs'.
        clear - H2 Hfrs'. subst frs'.
        set (j := 0) in *.
        assert (0 <= j) by lia. clearbody j.
        revert j k H H2 new Hfrs'; induction frs as [|[x y z]]; simpl; intros; auto.
        rewrite frames2rootpairs_cons, Zlength_app in Hfrs'.
        destruct (zeq j k); [ | destruct (zeq j 0)].
        - subst k. autorewrite with sublist. auto.
        - subst j. rewrite !sublist_0_cons by lia.
          rewrite !frames2rootpairs_cons, !Zlength_app.
          rewrite !Zlength_frame2rootpairs in *; simpl in *.
          f_equal. 
          list_solve.
          eapply IHfrs; try list_solve.
        - rewrite !sublist_pos_cons by lia.
          rewrite !Zlength_frame2rootpairs in *; simpl in *.
          eapply IHfrs; try list_solve.
        }
      clearbody frs'.
      replace s with (fr_roots (Znth k frs')) in H11 by (rewrite H8; reflexivity).
      rewrite frame_root_address_eq.
      2:{ split. rep_lia.
          apply Z.lt_le_trans 
          with (Zlength (frames2rootpairs (sublist 0 k frs')) + Zlength (fr_roots (Znth k frs'))).
          lia.
          pose proof Zlength_frames2rootpairs_sublist (k+1) frs' ltac:(lia).          
          etransitivity; [ | apply H1].
          apply Z.eq_le_incl.
          rewrite (sublist_split 0 k (k+1)) by list_solve.
          rewrite frames2rootpairs_app, Zlength_app.
          f_equal.
          rewrite (sublist_one k (k+1)) by lia.
          unfold frames2rootpairs; simpl. rewrite app_nil_r.
          rewrite Zlength_frame2rootpairs. auto.
      }
      clear - H2 H11.
      revert k H2 H11. induction frs' as [|[r a z]]; simpl; intros.
      list_solve.
      destruct (zeq k 0).
      --
        subst k.
        rewrite Znth_0_cons. autorewrite with sublist. clear H2.
        simpl in *.
        rewrite frames2rootpairs_cons.
        rewrite Znth_app1 by (autorewrite with sublist; simpl; lia).
        rewrite Znth_frame2rootpairs by auto.
        simpl. 
        rewrite Z.mul_comm. reflexivity.
      -- rewrite Znth_pos_cons by lia.
         rewrite (IHfrs' (k-1)) by list_solve; clear IHfrs'.
         rewrite Zlength_cons in *.
         rewrite Znth_pos_cons in * by lia.
         rewrite (sublist_split 0 1 k) by list_solve.
         rewrite (sublist_one 0 1) by list_solve. 
         rewrite frames2rootpairs_app.
         rewrite Zlength_app.
         rewrite Znth_0_cons.
         replace (Zlength (frames2rootpairs [{| fr_adr := r; fr_root := a; fr_roots := z |}])) 
                    with (Zlength z)
            by (unfold frames2rootpairs; simpl; rewrite app_nil_r;
                        unfold frame2rootpairs;
                        rewrite Zlength_frame2rootpairs'; auto).
          rewrite sublist_pos_cons by list_solve.
          rewrite frames2rootpairs_cons.
          autorewrite with sublist.
          rewrite Znth_app2 by (autorewrite with sublist; simpl; rep_lia).
          autorewrite with sublist. simpl.
          f_equal.
          f_equal.
          lia.
    * split.
     -- rewrite update_rootpairs_frames2rootpairs in H14; auto. 
        apply frr_Zlength in H12. rewrite Zlength_map, Zlength_app, <- H12.
        apply sc_Zlength in H. rewrite frames2roots_eq, Zlength_map, <- H, <- Hfrs', Zlength_map. 
        apply frr_Zlength in H3.
        rewrite Zlength_app, <- H3.
        cut (0 <= nr k /\ nr k <= nr k + i <= Zlength roots); [intro |].
        rewrite (sublist_split 0 (nr k) (nr k + i)) by lia.
        rewrite Zlength_app.
        rewrite !Zlength_sublist by list_solve.
        subst oldroots; cbv beta in *.
        list_solve.
        subst nr; cbv beta in *.
        split. rep_lia.
        split. lia.
        rewrite H.
        rewrite <- (sublist_same 0 (Zlength frs) frs) at 2 by auto.
        rewrite (sublist_split 0 k (Zlength frs)) by lia.
        rewrite frames2rootpairs_app.
        rewrite Zlength_app.
        apply Z.add_le_mono. lia.
        rewrite (sublist_split k (k+1)) by list_solve.
        rewrite frames2rootpairs_app, Zlength_app.
        rewrite sublist_len_1 by list_solve.
        unfold frames2rootpairs at 1. simpl concat.
        unfold frame2rootpairs.
        rewrite app_nil_r.
        rewrite Zlength_frame2rootpairs'.
        rep_lia.
     -- red. split. lia.
        apply frr_Zlength in H12.
        rewrite Zlength_app, <- H12.
        unfold oldroots.
        rewrite <- Zlength_app.
        rewrite sublist_rejoin; try list_solve.
    * Intros vret.
      destruct vret as [[g3 h3] roots3].
      simpl fst in *. simpl snd in *.
      Exists g3 h3 (sublist 0 (nr k + (i+1)) roots3).
      entailer!!.
      --
        split3; [ | | split3].
        ++  rewrite (sublist_split 0 (nr k + i)) by list_solve.
            unfold upd_roots.
            rewrite upd_Znth_app2 by list_solve.
            rewrite Znth_app2 by list_solve.
            rewrite LENroots''. rewrite Z.sub_diag.
            change (Z.to_nat 0) with O in H18.
            rewrite (sublist_one (nr k + i)) by list_solve.
            rewrite (sublist_split 0 (nr k + i) (nr k + (i+1)))
              by (unfold oldroots; list_solve).
            rewrite sublist_app1 by list_solve. rewrite sublist_app2 by list_solve.
            rewrite LENroots'', Z.sub_diag.
            rewrite (sublist_same _ _ roots'') by list_solve.
            eapply frr_app; [ eassumption | ].
            replace (_ - _) with 1 by lia.
            unfold oldroots.
            rewrite sublist_upd_Znth_lr by list_solve. rewrite Z.sub_diag.
            rewrite sublist_sublist by list_solve.
            rewrite sublist_one by list_solve.
            autorewrite with sublist.
            rewrite upd_Znth0.
            econstructor; [  | econstructor].
            replace (root2forward (Znth (nr k + i) roots))
              with  (forward_p2forward_t (inl (nr k + i)) (roots'' ++ oldroots k i) g''); auto.
            simpl. rewrite Znth_app2 by list_solve. rewrite LENroots'', Z.sub_diag.
            unfold oldroots. f_equal. list_solve.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
      -- admit.
  + Intros g3 h3 roots3. Exists (k+1, g3, h3, roots3 ). simpl fst; simpl snd.
    assert (oldroots (k+1) 0 = oldroots k (Zlength s)). {
       unfold oldroots. f_equal. unfold nr.
      rewrite (sublist_split 0 k (k+1)) by list_solve.
      rewrite Z.add_0_r.
      rewrite frames2rootpairs_app, Zlength_app.
      f_equal.
      rewrite sublist_one by lia.
      unfold frames2rootpairs; simpl; rewrite app_nil_r.
      unfold frame2rootpairs. rewrite Zlength_frame2rootpairs'.
      admit.  (* true *)
    }
    entailer!!. split3.
    * subst nr oldroots frs'; cbv beta in *. rewrite Z.add_0_r in *.
      replace (Zlength (frames2rootpairs (sublist 0 (k + 1) frs)))
       with (Zlength (frames2rootpairs (sublist 0 k frs)) + Zlength s); auto.
      rewrite (sublist_split 0 k (k+1)) by list_solve.
      eapply frr_Zlength in H3.
      pose proof Zlength_frames2rootpairs_sublist k frs ltac:(list_solve).
      apply sc_Zlength in H.
      rewrite Zlength_sublist in H3 by list_solve. rewrite Z.sub_0_r in H3.
      rewrite H3 in *.
     rewrite frames2rootpairs_app.
     rewrite Zlength_app. f_equal; auto.
     apply sc_Zlength in H13.
     apply frr_Zlength in H11.
     autorewrite with sublist in Hfrs'.
     apply sc_Zlength in H5.
     clear - H16 H15 H13 H11 Hfrs' H8 H7 H5 H3 H2 H.
     unfold frames2rootpairs.
     rewrite sublist_len_1 by lia.
     simpl.
     rewrite app_nil_r.
     unfold frame2rootpairs; rewrite Zlength_frame2rootpairs'.
     clear - H2 H8 H8 H Hfrs' H16.
     subst n.
     assert (Zlength  (map (root2val g')
           (roots' ++ sublist (Zlength roots') (Zlength roots) roots)) = Zlength roots) by 
            list_solve. 
     set (al := map _ _) in *. clearbody al.
     assert (fr_roots (Znth k (update_frames frs al)) = s). rewrite H8; reflexivity.
     subst s. rewrite H in H0. clear - H2 H0.
     revert al k H0 H2; induction frs as [|[???]]; intros.
     list_solve.
     destruct (zeq k 0).
     --
       subst k; simpl.
       rewrite Zlength_sublist; try list_solve.
       rewrite frames2rootpairs_cons, Zlength_app, Zlength_frame2rootpairs in H0. simpl in H0.
       list_solve.
     --
       rewrite !Znth_pos_cons by lia.
       rewrite <- (IHfrs (sublist (Zlength fr_roots) (Zlength al) al)); simpl; try list_solve.
     clear - H0.
     unfold frames2rootpairs in *.
     simpl in *.
     rewrite Zlength_app, Zlength_frame2rootpairs in H0. simpl in H0. list_solve.
    * eapply hr_trans; eassumption.
    * subst NEXT. subst frs'.
      apply sc_Zlength in H.
      rewrite Zlength_update_frames
       by (rewrite frames2roots_eq; list_solve).
      fold n.
      admit.  (* quite likely true *)
    * subst OTHERS.
      rewrite <- H15.
      admit. (* not implausible *)
 - 
  forward.
  assert (k=n). {
   clear - FRAMESP HRE H2.
   subst n.
   specialize (FRAMESP k).
   destruct (zeq k (Zlength frs)); auto.
   rewrite HRE in FRAMESP.
   specialize (FRAMESP ltac:(list_solve)). contradiction.
  }
  subst k.
  subst oldroots nr n.
  cbv beta in *.
  generalize H; intros [_ [? _]].
  red in H7. 
  apply (f_equal (@Zlength _)) in H7.
  autorewrite with sublist in H7.
  rewrite Z.add_0_r.
  rewrite (sublist_same 0 (Zlength frs)) in * by auto.
  rewrite <- H7 in *.
  rewrite Z.add_0_r in *.
  rewrite sublist_nil' in H5 by auto.
  rewrite !sublist_nil' by auto.
  rewrite app_nil_r in *.
  rewrite sublist_same in H3 by auto.
  Exists g' h' roots'.
  rewrite <- update_rootpairs_frames2rootpairs
     by (apply frr_Zlength in H3; rewrite frames2roots_eq; list_solve).
  entailer!!.
all:fail.
Admitted.
  
