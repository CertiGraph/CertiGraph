Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_forward_roots: semax_body Vprog Gprog f_forward_roots forward_roots_spec.
Proof.
  start_function. unfold fun_info_rep.
  assert_PROP (isptr fi) by entailer.
  assert_PROP (isptr ti) by (unfold thread_info_rep; entailer).
  assert (0 <= 1 < Zlength (live_roots_indices f_info) + 2) by (split; rep_omega).
  do 3 forward. simpl align. rewrite Znth_pos_cons, Znth_0_cons by omega.
  simpl sem_binary_operation'.
  replace (force_val (sem_add_ptr_int tuint Signed fi (vint 2))) with
      (offset_val 8 fi) by (rewrite sem_add_pi_ptr_special' by auto; reflexivity).
  remember (Zlength (live_roots_indices f_info)) as n. deadvars!.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by entailer.
  assert (Zlength roots = Zlength (live_roots_indices f_info)). {
    destruct H as [_ [? _]]. red in H.
    rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H, Zlength_map.
    reflexivity. }
  forward_for_simple_bound
    n
    (EX i: Z, EX g' : LGraph, EX t_info': thread_info, EX roots' : roots_t,
     PROP (forward_roots_loop from to f_info (nat_inc_list (Z.to_nat i))
                              roots g roots' g';
           thread_info_relation t_info t_info';
           super_compatible (g', t_info', roots') f_info outlier;
           forward_condition g' t_info' from to)
     LOCAL (temp _args (offset_val 12 ti);
            temp _n (Z2val n);
            temp _roots (offset_val 8 fi);
            temp _from_start (gen_start g' from);
            temp _from_limit (limit_address g' t_info' from);
            temp _next (next_address t_info' to))
     SEP (all_string_constants rsh gv;
          fun_info_rep rsh f_info fi;
          outlier_rep outlier;
          graph_rep g';
          thread_info_rep sh t_info' ti)).
  - pose proof lri_range f_info; subst n; omega.
  - Exists g t_info roots. destruct H as [? [? [? ?]]]. entailer!.
    split; [|split]; try easy. unfold nat_inc_list. simpl. constructor.
  - unfold fun_info_rep.
    assert_PROP (force_val (sem_add_ptr_int tuint
                                            Unsigned (offset_val 8 fi) (vint i)) =
                 field_address (tarray tuint (Zlength
                                                (live_roots_indices f_info) + 2))
                               [ArraySubsc (i+2)] fi). {
      entailer!. simpl. unfold field_address. rewrite if_true; simpl.
      1: f_equal; omega. unfold field_compatible in *. intuition. red. split; auto.
      simpl. omega. } forward. do 2 rewrite Znth_pos_cons by omega.
    replace (i + 2 - 1 - 1) with i by omega. apply semax_if_seq. rewrite Heqn in H6.
    pose proof (fi_index_range _ _ (Znth_In _ _ H6)). forward_if.
    + deadvars!. forward. do 2 rewrite Znth_pos_cons by omega.
      replace (i + 2 - 1 - 1) with i by omega.
      remember (Znth i (live_roots_indices f_info)).
      replace_SEP 1 (fun_info_rep rsh f_info fi) by entailer.
      assert_PROP (force_val
                     (sem_add_ptr_int int_or_ptr_type
                                      Unsigned (offset_val 12 ti) (Z2val z)) =
                   field_address thread_info_type
                                 [ArraySubsc z; StructField _args] ti). {
        unfold thread_info_rep. Intros. entailer!. unfold Z2val.
        rewrite sem_add_pi_ptr_special'; auto. simpl. unfold field_address.
        rewrite if_true. 1: simpl; rewrite offset_offset_val; reflexivity.
        unfold field_compatible in *. simpl. unfold in_members. simpl. intuition. }
      assert (Zlength roots' = Zlength roots) by
          (apply frl_roots_Zlength in H8; assumption).
      forward_call (rsh, sh, gv, fi, ti, g', t_info', f_info, roots', outlier, from,
                    to, 0, (@inl _ (VType*Z) i)).
      * simpl snd. apply prop_right.
        change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |})
          with int_or_ptr_type. rewrite H14. rewrite <- Heqz. clear. intuition.
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
            (rewrite Z2Nat.inj_add by omega; simpl; omega).
        rewrite nat_inc_list_S. remember (Z.to_nat i) as n.
        replace i with (Z.of_nat n) in * by (subst n;rewrite Z2Nat.id; omega).
        simpl in H18. split; [apply frl_add_tail|]; easy.
    + exfalso. rep_omega.
  - Intros g' t_info' roots'. forward. Exists g' t_info' roots'.
    destruct H8 as [? [? [? ?]]]. entailer!. rewrite <- H5, ZtoNat_Zlength in H6.
    easy. 
Qed.
