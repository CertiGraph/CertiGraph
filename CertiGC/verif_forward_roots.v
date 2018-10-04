Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_forward_roots: semax_body Vprog Gprog f_forward_roots forward_roots_spec.
Proof.
  start_function.
  destruct H as [? [? [? ?]]], H0 as [? [? [? [? ?]]]].
  unfold fun_info_rep.
  assert_PROP (isptr fi) by entailer.
  assert_PROP (isptr ti) by (unfold thread_info_rep; entailer).
  assert (0 <= 1 < Zlength (live_roots_indices f_info) + 2) by (split; rep_omega).
  do 3 forward; simpl.
  rewrite Znth_pos_cons, Znth_0_cons; try omega.
  remember (Zlength (live_roots_indices f_info)) as n.
  
  forward_for_simple_bound
    n
    (EX i: Z,
     EX g' : LGraph,
     EX t_info': thread_info,
     (*EX roots' : roots_t,*)
     PROP (
         forward_roots_loop from to (sublist 0 i roots) g g';
         (*roots' = forwarded_roots from to forward_p g roots f_info;*)
         thread_info_relation t_info t_info';
         (*super_compatible (g', t_info', roots') f_info outlier;*)
         forward_condition g' t_info' from to
     )
     LOCAL (
       temp _args (offset_val 12 ti);
       temp _n (Z2val n);
       temp _roots (force_val (sem_add_ptr_int tuint Signed fi (vint 2)));
       temp _from_start (gen_start g' from);
       temp _from_limit (limit_address g' t_info' from);
       temp _next (next_address t_info' to);
       temp _fi fi;
       temp _ti ti
     )
     SEP (
       all_string_constants rsh gv;
       fun_info_rep rsh f_info fi;
       outlier_rep outlier;
       graph_rep g';
       thread_info_rep sh t_info' ti
     )
    )%assert.
  - pose proof lri_range f_info; subst n; omega.
  - Exists g t_info. autorewrite with sublist.
    entailer!; try entailer.
    split; try split; try constructor; try reflexivity.
    assumption.
    repeat (split; try assumption).
  - unfold fun_info_rep.
    assert ((force_val (sem_add_ptr_int tuint Signed fi (vint 2))) =
            offset_val (WORD_SIZE * 2) fi). {
      rewrite sem_add_pi_ptr_special'.
      3: assumption. 2: reflexivity.
      simpl. f_equal; rep_omega.
    }
    assert_PROP (force_val (sem_add_ptr_int tuint
      Unsigned (offset_val (WORD_SIZE * 2) fi) (vint i)) =
        field_address (tarray tuint (Zlength
        (live_roots_indices f_info) + 2))
        [ArraySubsc (i+2)] fi). {
      entailer!. simpl. unfold field_address.
      rewrite if_true; simpl. f_equal; rep_omega.
      unfold field_compatible in *.
      intuition. red. intuition. red. simpl. omega.
    }
    rewrite H14.
    forward.
    apply semax_if_seq.
    forward_if.
    2: { replace (i+2) with (i+1+1) in H19 by omega.
         do 2 (rewrite <- Znth_tl in H19 by rep_omega). simpl in H19.
         exfalso.
         assert (0 <= i < Zlength (live_roots_indices f_info)) by
             (rewrite <- Heqn; assumption).
         pose proof Znth_In i (live_roots_indices f_info) H20. 
         pose proof fi_index_range f_info
              (Znth i (live_roots_indices f_info)) H21.
         rewrite Int.unsigned_repr in H19; rep_omega.
    }
    forward.
    replace (i+2) with (i+1+1) by omega.
    do 2 (rewrite <- Znth_tl by rep_omega). simpl tl.
(*    
    forward_call (rsh, sh, gv, fi, ti, g', t_info', f_info, roots', outlier, from, to, 0, (@inl _ (VType*Z) i)) *)
Abort.

