Require Import CertiGraph.CertiGC.gc_spec.

Lemma frames_rep_ptr_or_null: forall sh frames,
  frames_rep sh frames |-- !! is_pointer_or_null (frames_p frames).
  Proof.
    destruct frames as [|[???]?]; simpl; entailer.
  Qed.

Hint Resolve frames_rep_ptr_or_null : saturate_local.

Lemma frames_rep_valid_pointer: forall sh frames, 
   sepalg.nonidentity sh ->
   frames_rep sh frames |-- valid_pointer (frames_p frames).
Proof.
  intros.
  destruct frames as [|[???]?]; simpl frames_p; simpl frames_rep; auto with valid_pointer.
Qed.
Hint Resolve frames_rep_valid_pointer: valid_pointer.

(*
Definition ti_rep (sh: share) (t_info: thread_info) p :=
  data_at sh thread_info_type (Vundef,(Vundef,(ti_heap_p t_info,
       (ti_args t_info, (ti_fp t_info, (vptrofs (ti_nalloc t_info), nullval)))))) p.
*)

Print forward_roots_relation.
(*
Definition forwarded_roots (from to: nat) (k: Z) (roots: roots_t) (g: LGraph) (roots': roots_t) (g': LGraph) :=
 

  upd_root from to g r r' 
*)

Inductive forward_roots_relation (from to: nat): forall (roots1: roots_t) (g1: LGraph) (roots2: roots_t) (g2: LGraph), Prop :=
| fwd_roots_nil: forall g, forward_roots_relation from to nil g nil g
| fwd_roots_cons: forall r roots1 g1 roots2 g2 g3,
     forward_relation from to 0 (root2forward r) g1 g2 ->
     forward_roots_relation from to roots1 g2 roots2 g3 ->
     forward_roots_relation from to (r::roots1) g1 (upd_root from to g1 r :: roots2) g3.

Lemma forward_roots_relation_snoc:
 forall from to r roots1 g1 roots2 g2 g3,
  forward_roots_relation from to roots1 g1 roots2 g2 ->
  forward_relation from to 0 (root2forward r) g2 g3 ->
  forward_roots_relation from to (roots1++[r]) g1 (roots2++[upd_root from to g2 r]) g3.
Proof.
  induction 1; intros.
  - simpl. econstructor; eauto. constructor.
  - simpl. econstructor; eauto.
Qed.

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
   rewrite <- ZtoNat_Zlength,  <- sublist_skip by rep_lia.
   unfold frames2roots in *.
   simpl in *. list_solve.
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
      rewrite (sublist_split 0 1) by list_solve.
      rewrite sublist_one by rep_lia.
      rewrite sublist_pos_cons by lia.
      autorewrite with sublist.
      simpl.

      specialize (IHfrs (k-1) ltac:(list_solve)).
      set (j := sublist _ _ _) in *. clearbody j.
      unfold frames2rootpairs in *.
      rewrite !Zlength_concat in *.
      simpl in *. lia.
Qed.

Set Nested Proofs Allowed.
Lemma frames_p_update_frames_sublist:
 forall frs roots k, 
    Zlength (frames2roots frs) = Zlength roots ->
    0 <= k <= Zlength frs ->
    frames_p (sublist k (Zlength frs) frs) = frames_p (sublist k (Zlength frs) (update_frames frs roots)).
Proof.
unfold frames2roots. 
induction frs as [|[???]?]; intros; simpl in *; auto.
rewrite <- ZtoNat_Zlength,  <- sublist_skip by rep_lia.
rewrite Zlength_app in H.
rewrite !Zlength_cons in  *.
destruct (zeq k 0).
- subst k.
 rewrite !(sublist_split 0 1 (Z.succ (Zlength frs))); try list_solve.
 rewrite Zlength_cons. rewrite Zlength_update_frames. list_solve.
 unfold frames2roots. list_solve.
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
  Search (sepcon (andp (prop _) _) _).
  rewrite sepcon_andp_prop'.
  apply derives_extract_prop; intro.
  apply prop_right.
  autorewrite with sublist.
  replace (Z.succ (Zlength frs) - 1) with (Zlength frs) by lia.
  apply H0.
  list_solve.
Qed.

Lemma roots_weak_valid_pointer:
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
rewrite <- ZtoNat_Zlength,  <- sublist_skip by rep_lia.
rewrite <- sublist_firstn.
rewrite iter_sepcon_app_sepcon.
assert (Zlength fr_roots <= Zlength roots) by admit.
destruct (zeq k 0).
- subst k. rewrite !Znth_0_cons in *. simpl in *.
  clear H2.
  apply sepcon_weak_valid_pointer1; clear IHfrs.
  rewrite iter_sepcon_frame2rootpairs'.
  2: rewrite Zlength_sublist, Z.sub_0_r; auto; try list_solve.
  rewrite Zlength_sublist, Z.sub_0_r by list_solve.
  admit.
- rewrite (Znth_pos_cons k) in * by lia. 
  simpl in *.
  apply sepcon_weak_valid_pointer2.
  apply IHfrs; clear IHfrs; auto.
  2:list_solve.
  rewrite Zlength_app in H0.
  rewrite Zlength_frame2rootpairs' in H0. list_solve.
Admitted.

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
    entailer!.
    split. constructor. apply hr_refl. 
  - Intros.
    unfold frames_rep.
    assert (LEN: Zlength (roots' ++ oldroots k 0) = Zlength (frames2rootpairs frs)). {
    destruct H as [_ [? _]]. red in H.
    destruct H5 as [_ [? _]]. red in H5.
    apply (f_equal (@Zlength val)) in H, H5.
    rewrite !Zlength_map in H,H5.
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
      change (?A::?B) with ([A]++B).
      rewrite sublist_app2 by list_solve.
      autorewrite with sublist. replace (Z.succ _ - _) with (Zlength frs) by lia.
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
     destruct H as [_ [? _]]. red in H.
     destruct H5 as [_ [H5 _]]. red in H5.
     apply (f_equal (@Zlength val)) in H, H5.
     rewrite !Zlength_map in H,H5.
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
    assert (LEN': Zlength (frames2roots frs) = Zlength (map (root2val g') (roots' ++ oldroots k 0))). {
      apply frr_Zlength in H3. autorewrite with sublist. rewrite <- H3.
      unfold oldroots. rewrite Z.add_0_r.     
      rewrite frames2roots_eq.
      destruct H as [_ [? _]]. red in H. rewrite <- H.
      rewrite Zlength_map. 
      assert (0 <= nr k <= Zlength roots); [ | list_solve].
      unfold nr. 
      pose proof (Zlength_frames2rootpairs_sublist _ _ H2). list_solve.
    }
    replace (fr_adr (Znth k frs)) with a.
    2:{
      replace a with (fr_adr (Znth k frs')) by (rewrite H8; auto).
      clear - H2 LEN'. subst n frs'.
      set (jj := map _ _) in *. clearbody jj.
      clear - LEN' H2.
      revert jj LEN' k H2; induction frs as [ | [???] ?]; simpl; intros; auto.
      destruct (zeq k 0). subst k. autorewrite with sublist; simpl; auto.
      rewrite <- ZtoNat_Zlength,  <- sublist_skip by rep_lia.
      rewrite !Znth_pos_cons by lia.
      apply IHfrs; clear IHfrs; [ | list_solve].
      unfold frames2roots in *. simpl in *.
      rewrite Zlength_app in LEN'. list_solve.
    }
    forward. forward.
    entailer!. {
       clear - H9.
       unfold field_address0.
       rewrite if_true. simpl. destruct H9, r; try contradiction; hnf; auto.
       apply arr_field_compatible0; auto. rep_lia.
    }
    forward. {
      unfold NEXT.
      simpl tc_val.
      entailer!.
      subst frs'.
      replace (Zlength _) with (Zlength frs).
      rewrite <- frames_p_update_frames_sublist by (auto; list_solve).
      destruct (zeq (k+1) (Zlength frs)).
      rewrite e. autorewrite with sublist. hnf. auto.
      apply isptr_is_pointer_or_null; apply FRAMESP; list_solve.
      rewrite Zlength_update_frames; auto.
    }
    forward_loop (EX i: Z, EX g'' : LGraph, EX h'': heap, EX roots'' : roots_t,
     PROP (0 <= i <= Zlength s;
       forward_roots_relation from to (sublist 0 (nr k + i) roots) g roots'' g'';
       heap_relation h' h'';
       super_compatible g'' h'' 
         (update_rootpairs (frames2rootpairs frs) (map (root2val g'') (roots''++oldroots k i))) 
         (roots''++oldroots k i)
         outlier;
     forward_condition g'' h'' from to)
LOCAL (temp _frame NEXT;
       temp _limit  (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB Zlength s) r);
       temp _curr (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB i) r);
      temp _from_start (gen_start g'' from);
      temp _from_limit (limit_address g'' h'' from);
      temp _next (heap_next_address hp to))
SEP (all_string_constants rsh gv;
    outlier_rep outlier;
    graph_rep g'';
    data_at sh (Tstruct _stack_frame noattr)
       (field_address0 (tarray int_or_ptr_type (Zlength s))
           (SUB Zlength s) r, (r, NEXT)) a; 
    OTHERS;
    roots_rep sh (frames2rootpairs (update_frames frs (map (root2val g'') (roots''++oldroots k i))));
    heap_rep sh h'' hp))%assert.
  + Exists 0 g' h' roots'.
    entailer!; [ split | ].
    * apply hr_refl.
    * unfold field_address0; simpl. rewrite if_true. normalize. auto with field_compatible.
    * apply derives_refl.
  + Intros i g'' h'' roots''.
    forward_if.
    *
    rewrite isptr_denote_tc_test_order
      by (unfold field_address0; rewrite if_true by auto with field_compatible;
          destruct r, H9; try contradiction; auto).
     unfold test_order_ptrs.
      replace (sameblock _ _) with true
       by (unfold field_address0; rewrite !if_true by auto with field_compatible; simpl;
        destruct r, H9; try contradiction; simpl;
        destruct (peq _ _); try contradiction; auto).
      replace r with (fr_root (Znth k frs)).
      2:{ clear - H8 LEN'.
          subst frs'. admit.
      }
      replace (Zlength s) with (Zlength (fr_roots (Znth k frs))) by admit.
      apply andp_right;
      apply sepcon_weak_valid_pointer1; repeat apply sepcon_weak_valid_pointer2;
      apply roots_weak_valid_pointer; auto; try rep_lia.
      admit. admit. admit. admit. admit.
      
    * set (rp'' := frames2rootpairs _).
      forward_call (rsh,sh,gv,g'',h'',hp,rp'',roots''++oldroots k i,outlier,from,to,0, @inl _ (VType*Z) i).
      entailer!. simpl. repeat f_equal. admit.
      rewrite update_rootpairs_frames2rootpairs in H13 by admit.
      fold rp'' in H13. split; auto.
      simpl. admit. (* ?? *)
      Intros vret.
      destruct vret as [[g3 h3] roots3].
      simpl fst in *. simpl snd in *.
      forward.
      entailer!. admit.
      Exists (i+1) g3 h3 roots3.
      entailer!.
      admit.
      admit.
    * forward.
      Exists (k+1, g'', h'', roots'').
      simpl fst. simpl snd.
      assert (i=Zlength s). {
        unfold field_address0 in H15.
        rewrite !if_true in H15 by auto with field_compatible.
        simpl in H15. destruct r; try (destruct H9; contradiction).
        unfold sem_cmp_pp in H15; simpl in H15.
        rewrite if_true in H15 by auto.
        simpl in H15.
        Search (Ptrofs.add _ _ = Ptrofs.add _ _).
        rewrite !(Ptrofs.add_commut i0) in H15.
        rewrite Ptrofs.translate_ltu in H15 by admit.
        unfold Ptrofs.ltu in H15. if_tac in H15. inv H15.
        rewrite !Ptrofs.unsigned_repr in H16 by admit. 
        lia.
      }
      subst i. clear H15 H10.
      unfold frames_rep. subst OTHERS NEXT.
      unfold oldroots in H13|-*.
      assert (NR: nr (k+1) = nr k + Zlength s) by admit.
      rewrite NR.
      entailer!.
      -- clear H20 H19 H18 H17 H16 H15.
         split; auto.
         ++ eapply hr_trans; eassumption.
         ++ Locate frames_p_update_frames.
       replace (Zlength frs') with (Zlength frs).
       apply frames_p_update_frames_sublist; [ | lia].
       admit. admit.
      -- unfold frame_shell_rep.
         rewrite prop_true_andp by auto.
         sep_apply modus_ponens_wand.
         unfold frs'. cancel.
         rewrite <- !frames_shell_rep_update; auto.
         admit.
         admit.
 - forward.
   Exists g' h' roots'.
   destruct (zeq k n). 
   2: { exfalso.
        clear - n0 H2 HRE.
        subst n.
         assert (Zlength (sublist k (Zlength frs) frs) <> 0) by list_solve.
         destruct (sublist k (Zlength frs) frs). list_solve. destruct f. simpl in HRE.
         clear - HRE.  admit.   (* this is almost but not quite a contradiction; FIXME *)
   }
   subst k.
   clear H2. subst n.
   unfold oldroots, nr in *.
   rewrite (sublist_same 0 (Zlength frs)) in * by reflexivity.
   rewrite Z.add_0_r in *.
   rewrite sublist_same in H3, H5 by admit.
   Search (sublist _ _ _ = nil).
   rewrite (sublist_nil' _ (Zlength (frames2rootpairs _))) by admit.
   rewrite app_nil_r.
   entailer!. 
   clear H10 H9 H8 H7.
   admit.
Admitted.
  
