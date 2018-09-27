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
     PROP (
       forward_roots_loop from to (sublist 0 i roots) g g';
       super_compatible (g', t_info', roots) f_info outlier;
       forward_condition g' t_info' from to
     )
     LOCAL (
       temp _args (offset_val 12 ti);
       temp _n (Z2val n);
       temp _roots (force_val (sem_add_ptr_int tuint Signed fi (vint 2)));
       temp _from_start (gen_start g from);
       temp _from_limit (limit_address g t_info from);
       temp _next (next_address t_info to);
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
  - admit.
  - Exists g t_info. autorewrite with sublist.
    entailer!; try entailer. split; constructor.
    assumption. repeat (split; try assumption).
  - unfold fun_info_rep.
    remember (map Z2val (fun_word_size f_info ::
      Zlength (live_roots_indices f_info) ::
      live_roots_indices f_info)) as l.
    assert (Zlength l = (Zlength (live_roots_indices f_info) + 2)) by
        (subst l; rewrite Zlength_map;
         do 2 (rewrite Zlength_cons); omega).
    rewrite <- H14.
    assert (Zlength (tl l) = Zlength l - 1) by admit.
    rewrite data_at_tarray_value_split_1_tuint. rewrite <- H15.
    rewrite data_at_tarray_value_split_1_tuint. Intros. freeze [0;1;2;4;5;6;7] FR. rewrite Heql. simpl tl.
    replace (Zlength
             (Z2val (Zlength (live_roots_indices f_info))
                    :: map Z2val (live_roots_indices f_info)) - 1) with (Zlength (map Z2val (live_roots_indices f_info))) by (rewrite Zlength_cons; omega).
    remember (map Z2val (live_roots_indices f_info)) as roots_l.
    assert ((Zlength roots_l) - i =
            Zlength (sublist i (Zlength roots_l) roots_l)) by (rewrite Heqroots_l; symmetry;
      apply Zlength_sublist_correct;
      rewrite Zlength_map; omega; omega).
    rewrite (data_at_tarray_value_tuint
               rsh
               (Zlength roots_l) i
               (offset_val WORD_SIZE (offset_val WORD_SIZE fi))
               roots_l roots_l
               (sublist 0 i roots_l)
               (sublist i (Zlength roots_l) roots_l));
      auto. rewrite H19. rewrite data_at_tarray_value_split_1_tuint.
    thaw FR; Intros. freeze [0;1;2;3;4;5;6;8;9;10] FR.



    (*assert_PROP (field_compatible tuint []
                                  (offset_val WORD_SIZE (offset_val WORD_SIZE fi))). {
      sep_apply (data_at__local_facts rsh tuint (offset_val WORD_SIZE (offset_val WORD_SIZE (offset_val WORD_SIZE fi)))).



    
    destruct (sublist i (Zlength roots_l) roots_l) eqn:?.
    1: { exfalso; subst roots_l.
         rewrite Zlength_nil in H19. rewrite Zlength_map in H19. rewrite <- Heqn in H19. omega. }
    simpl hd.
    assert_PROP (field_compatible tuint []
                                  (offset_val WORD_SIZE (offset_val WORD_SIZE fi))). {
      sep_apply (data_at__local_facts rsh tuint (offset_val WORD_SIZE (offset_val WORD_SIZE (offset_val WORD_SIZE fi)))).

      the p I need: (offset_val WORD_SIZE (offset_val WORD_SIZE fi))

      the p I have: 

                                                            (offset_val WORD_SIZE fi))).



      (field_compatible tuint [] (offset_val (4 * (i + 2)) fi)). {
      sep_apply (data_at__local_facts rsh tuint (offset_val (4 * (i + 2)) fi)).
*)

(*        field_compatible tuint []
                (offset_val (WORD_SIZE * (i + 2)) fi)). {
        (sep_apply (data_at__local_facts rsh tuint
                   (offset_val (WORD_SIZE * (i+2) fi)); entailer!). *)
    (*assert_PROP
      (force_val (sem_add_ptr_int tuint Unsigned
                                  (force_val (sem_add_ptr_int tuint Signed fi (vint 2))) (vint i)) = field_address tuint [] (offset_val WORD_SIZE (offset_val WORD_SIZE fi))).
    {
      
      unfold field_address.  entailer!.


      unfold field_address.
             rewrite if_true by assumption. simpl. rewrite offset_offset_val.
             f_equal. omega.
    }
    

    forward.

    simpl.

    
    

    constructor; try assumption.
    assu


    [constructor ; constructor | assumption].
  

 

forward_for_simple_bound
        n
        (EX i: Z,
         PROP ( )
         LOCAL (temp _h h; gvars gv)
         SEP (data_at Ews heap_type
                      (vh :: list_repeat (Z.to_nat (i - 1)) v0 ++
                          list_repeat (Z.to_nat (12 - i)) vn) h; FRZL FR))%assert.

  
  forward.



    start_function. destruct H as [? [? [? ?]]].
  destruct H0 as [? [? [? [? ?]]]].
  unfold fun_info_rep, thread_info_rep.
  assert_PROP (isptr fi) by entailer.
  assert_PROP (isptr ti) by entailer.
  assert (0 <= 1 < Zlength (live_roots_indices f_info) + 2) by (split; rep_omega).
  Intros.
  do 3 forward.

  
  
  forward.
  unfold fun_info_rep.
    
  forward.
  
  1: { entailer.*)
    Abort.