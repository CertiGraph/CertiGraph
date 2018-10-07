Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  unfold before_gc_thread_info_rep, heap_struct_rep. Intros. forward. pose proof H.
  destruct H0 as [? _]. pose proof (gt_gs_compatible _ _ H0 _ (graph_has_gen_O _)).
  destruct H1 as [? [? ?]].
  replace (heap_head (ti_heap t_info)) with (nth_space t_info 0) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H4, H5; simpl; reflexivity).
  assert (isptr (space_start (nth_space t_info 0))) by
      (rewrite <- H1; apply start_isptr). do 2 forward. deadvars!.
  rewrite upd_Znth0, sublist_1_cons, Zlength_cons, sublist_same by omega.
  fold (space_tri (nth_space t_info 0)). rewrite <- map_cons.
  replace (nth_space t_info 0 :: tl (spaces (ti_heap t_info))) with
      (spaces (ti_heap t_info)) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H5; simpl; reflexivity).
  gather_SEP 4 5 6. replace_SEP 0 (thread_info_rep sh t_info ti) by
      (unfold thread_info_rep, heap_struct_rep; entailer! ;
       do 2 (unfold_data_at 1%nat); cancel).
Abort.
