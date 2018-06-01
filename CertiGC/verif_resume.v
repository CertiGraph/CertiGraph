Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. if_tac. 1: contradiction. clear H2. Intros.
  unfold heap_struct_rep. forward. 
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by (unfold fun_info_rep; entailer!).
  forward_if True; [forward; entailer!| exfalso; destruct t_info; simpl in *; tauto|].
  destruct H as [? [? ?]]. destruct (glabel g) eqn: ?.
  1: exfalso; apply H1; rewrite <- H; reflexivity.
  remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as th.
  destruct (heap_head_cons th) as [hs [hl [? ?]]]. simpl in H2. rewrite H4 in *.
  rewrite Forall_forall in H2. assert (generation_space_compatible g (O, g0, hs)). {
    apply H2; left; reflexivity. } destruct H6 as [? [? ?]]. rewrite H5 in *.
  rewrite <- H6 in *. pose proof (start_isptr g0). forward. rewrite Znth_0_cons.
  forward. rewrite Znth_0_cons. simpl tl.
  forward_if True.
  - remember (start_address g0). destruct v0; try contradiction.
    unfold denote_tc_samebase. simpl. entailer!.
  - unfold all_string_constants. Intros.
    forward_call ((gv ___stringlit_10),
                  (map init_data2byte (gvar_init v___stringlit_10)), rsh).
    exfalso; assumption.
  - remember (start_address g0). destruct v; try contradiction.
    simpl in H10. if_tac in H10. 2: contradiction. inv_int i.
    rewrite ptrofs_add_repr, ptrofs_sub_repr, Z.add_comm, Z.add_simpl_r in H10.
    simpl in H10.
    
Abort.
