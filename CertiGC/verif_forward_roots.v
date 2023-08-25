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
                    
Lemma body_forward_roots: semax_body Vprog Gprog f_forward_roots forward_roots_spec.
Proof.
  start_function.
  unfold thread_info_rep. Intros.
  forward.
  fold (frames_p fr).
  rename fr into frs.
  pose (n := Zlength frs).
  pose (nr k := (Zlength (frames2rootpairs (sublist 0 k frs)))).
  pose (oldroots k := sublist (nr k) (Zlength roots) roots).
  forward_while (EX k: Z,
                 EX g': LGraph, EX h': heap, EX roots': roots_t,
      PROP (0 <= k <= n;
            forward_roots_relation from to (sublist 0 (nr k) roots) g roots' g';
            heap_relation h h';
            super_compatible g' h' 
                (update_rootpairs (frames2rootpairs frs) (map (root2val g') (roots'++oldroots k))) 
                (roots'++oldroots k)
                outlier;
            forward_condition g' h' from to)
      LOCAL (temp _frame (frames_p (sublist k n frs));
             temp _from_start (gen_start g' from);
             temp _from_limit (limit_address g' h' from);
             temp _next (heap_next_address hp to))
      SEP (all_string_constants rsh gv;
           outlier_rep outlier;
           graph_rep g';
           frames_rep sh (update_frames frs (map (root2val g') (roots'++oldroots k)));
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
    rewrite <- frames_shell_rep_update.
    2:{ admit. }
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
           
     
    sep_apply (isolate_frame sh frs' k).
    admit.
   Intros.
   unfold frs' at 2.
   rewrite frame_root_address_same by admit.
   rewrite frame_root_address_eq by admit.
   forward.
  forward_loop (EX i: Z, EX g' : LGraph, EX t_info': thread_info, EX roots' : roots_t,
     PROP (forward_roots_loop from to 
              (nat_inc_list (length (frames2roots frames0) + Z.to_nat i)) roots g roots' g';
           thread_info_relation t_info t_info';
           super_compatible (g', t_info', roots') outlier;
           forward_condition g' t_info' from to)
     LOCAL (temp _frame (frames_adr frames');
            temp _curr (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB i) r);
            temp _limit  (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB Zlength s) r);
            temp _from_start (gen_start g' from);
            temp _from_limit (limit_address g' t_info' from);
            temp _next (next_address t_info' to))
     SEP (all_string_constants rsh gv;
          outlier_rep outlier;
          graph_rep g';
          ti_rep sh t_info ti;
          data_at sh (Tstruct _stack_frame noattr)
            (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB Zlength s) r,
            (r, frames_adr frames')) a;
          data_at sh (tarray int_or_ptr_type (Zlength s)) s r;
          frames_rep sh frames';
          (data_at sh (Tstruct _stack_frame noattr)
            (field_address0 (tarray int_or_ptr_type (Zlength s)) (SUB Zlength s) r,
            (r, frames_adr frames')) a
            * data_at sh (tarray int_or_ptr_type (Zlength s)) s r
            * frames_rep sh frames') -* frames_rep sh (ti_frames t_info');
          heap_struct_rep sh (map space_tri (spaces (ti_heap t_info'))) (ti_heap_p t_info);
          heap_rest_rep (ti_heap t_info')
     ))%assert.
   + Exists 0 g' t_info' roots'. entailer!.
     split. change (Z.to_nat 0) with O. rewrite Nat.add_0_r. auto.
     rewrite arr_field_address0 by (auto with field_compatible; rep_lia).
     clear - H15; destruct H15 as [? _]; destruct r; try contradiction; simpl. normalize. 
   + Intros i g'' t_info'' roots''.
     forward_if.
     *  admit.  (* true, but tedious *)
     * forward_call (rsh, sh, gv, ti, g'', t_info'', roots'', outlier, from,
         to, 0, (@inl _ (VType*Z) (Zlength (frames2roots frames0) + i))).
      --  simpl firstn. entailer!. repeat f_equal.
          admit. (* plausible *)
      -- unfold thread_info_rep.
         fold (ti_rep sh t_info'' ti).
         replace (ti_rep sh t_info'' ti) with (ti_rep sh t_info ti) by admit. (* plausible *)
         replace (ti_heap_p t_info'') with (ti_heap_p t_info) by admit. (* plausible *)
         cancel.
         eapply derives_trans; [apply modus_ponens_wand |].
         cancel.
      -- admit. (* whatever *)
      -- Intros vret.
         destruct vret as ((g3,t_info3),roots3). simpl fst in *. simpl snd in *.
         forward.
         ++ entailer!. admit. (* easy *)
         ++ Exists (i+1) g3 t_info3 roots3.
            entailer!.
            ** admit.  (* some things to prove here *)
            ** unfold thread_info_rep. fold (ti_rep sh t_info3 ti).
               replace (ti_rep sh t_info3 ti) with (ti_rep sh t_info ti) by admit. (* plausible *)
               replace (ti_heap_p t_info3) with (ti_heap_p t_info) by admit. (* plausible *)
               cancel.
               set (A := (data_at _ (Tstruct _stack_frame _) _ _ * _ * _)%logic).
               clear H11 H22 H21 H20 H19 H18 H17.
               Search (_ |-- _ * (_ -* _)).
               Search tir
               red in H16.
               Print thread_info_relation.
               admit. (* problematic *)

              
         set (B := (data_at _ (Tstruct _stack_frame _) _ _ * _ * _)%logic).
         set (C := frames_rep _ _).
         sep_apply (modus_ponens_wand B C).
         
         (B*C) (frames_rep sh frames'))

         Search spaces thread_info_relation.
     simpl.
     unfold forward_p_address, frame_root_address. simpl.
     unfold weak_valid_pointer.
     Search weak_valid_pointer.
     auto 50 with valid_pointer.
     unfold sameblock.
     simpl sameblock.
     auto 50 with valid_pointer.
     Search denote_tc_test_order.
     rewrite arr_field_address0 by (auto with field_compatible; rep_lia).

   assert (foo: environ->mpred) by admit.

     forward_if foo.
        Print heap_rest_rep.
     
     cancel.
     
     unfold limit_address.
       rewrite arr_field_address0 by (auto with field_compatible; rep_lia).
       simpl.
     unfold field_address0. rewrite if_true. simpl. clear - H15.
     auto with field_compat
     destruct H15, r; try contradiction. simpl. reflexivity. auto.
     clear - H3.

  - pose proof lri_range f_info. unfold MAX_UINT in H6. subst n; lia.
  - Exists g t_info roots. destruct H as [? [? [? ?]]]. entailer!.
    split; [|split]; try easy. unfold nat_inc_list. simpl. constructor.
    apply derives_refl.
  - unfold fun_info_rep.
    assert_PROP (force_val
                   (if Archi.ptr64 then
                      (sem_add_ptr_long tulong (offset_val 16 fi)
                                        (Vlong (Int64.repr i)))
                    else
                      (sem_add_ptr_int tuint Unsigned (offset_val 8 fi) (vint i))) =
                 field_address (tarray (if Archi.ptr64 then tulong else tuint)
                                       (Zlength
                                          (live_roots_indices f_info) + 2))
                               [ArraySubsc (i+2)] fi). {
      entailer!. simpl. unfold field_address. rewrite if_true; simpl.
      1: f_equal; lia. unfold field_compatible in *. intuition. red. split; auto.
      simpl. lia. } forward. do 2 rewrite Znth_pos_cons by lia.
    replace (i + 2 - 1 - 1) with i by lia. apply semax_if_seq. rewrite Heqn in H6.
    pose proof (fi_index_range _ _ (Znth_In _ _ H6)). forward_if.
    + forward. do 2 rewrite Znth_pos_cons by lia.
      replace (i + 2 - 1 - 1) with i by lia.
      remember (Znth i (live_roots_indices f_info)).
      replace_SEP 1 (fun_info_rep rsh f_info fi) by entailer.
      assert_PROP (force_val
                     (if Archi.ptr64 then
                        (sem_add_ptr_long
                           int_or_ptr_type (offset_val 24 ti) (Z2val z)) else
                        (sem_add_ptr_int int_or_ptr_type
                                         Unsigned (offset_val 12 ti) (Z2val z))) =
                   field_address thread_info_type
                                 [ArraySubsc z; StructField _args] ti). {
        unfold thread_info_rep. Intros. entailer!. simpl. unfold Z2val.
        first [rewrite sem_add_pi_ptr_special' |
               rewrite sem_add_pl_ptr_special] ; auto. simpl. unfold field_address.
        rewrite if_true. 1: simpl; rewrite offset_offset_val; reflexivity.
        unfold field_compatible in *. simpl. unfold in_members. simpl. intuition. }
      assert (Zlength roots' = Zlength roots) by
          (apply frl_roots_Zlength in H8; assumption).
      forward_call (rsh, sh, gv, fi, ti, g', t_info', f_info, roots', outlier, from,
                    to, 0, (@inl _ (VType*Z) i)).
      * simpl snd. apply prop_right.
        change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |})
          with int_or_ptr_type.
        change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
          with int_or_ptr_type. simpl. cbv [Archi.ptr64] in H14. rewrite H14.
        rewrite <- Heqz. clear. intuition.
      * intuition. red. rewrite H15, H5. split; assumption.
      * Intros vret. destruct vret as [[g2 t_info2] roots2]. simpl fst in *.
        simpl snd in *. simpl forward_p2forward_t in H16. Exists g2 t_info2 roots2.
        assert (thread_info_relation t_info t_info2) by (eapply tir_trans; eauto).
        assert (gen_start g' from = gen_start g2 from). {
          eapply fr_gen_start; eauto. destruct H11 as [_ [_ [? _]]].
          assumption. }
        assert (limit_address g2 t_info2 from = limit_address g' t_info' from) by
            (unfold limit_address; rewrite H22;
             rewrite (proj1 (proj2 H20)); reflexivity).
        assert (next_address t_info2 to = next_address t_info' to) by
            (unfold next_address; rewrite (proj1 H20); reflexivity).
        destruct H16 as [? [? [? ?]]]. entailer!.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by
            (rewrite Z2Nat.inj_add by lia; simpl; lia).
        rewrite nat_inc_list_S. remember (Z.to_nat i) as n.
        replace i with (Z.of_nat n) in * by (subst n;rewrite Z2Nat.id; lia).
        simpl in H18. split; [apply frl_add_tail|]; easy.
    + exfalso. try (rewrite !Int64.unsigned_repr in H13; [|rep_lia..]). rep_lia.
  - Intros g' t_info' roots'. Exists g' t_info' roots'.
    destruct H8 as [? [? [? ?]]]. entailer!. rewrite <- H5, ZtoNat_Zlength in H6.
    easy.
Qed.
