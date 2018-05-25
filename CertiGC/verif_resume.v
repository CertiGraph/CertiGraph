Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. destruct (Val.eq (ti_heap_p t_info) nullval).
  1: hnf in e; exfalso; tauto. clear n. Intros. unfold heap_struct_rep. forward. 
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by unfold fun_info_rep; entailer!.
  forward_if True; [forward; entailer!|exfalso; destruct t_info; simpl in *; tauto|].
  Intros. remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as th.
  forward; rewrite Znth_0_cons.
  - (* goal: is_pointer_or_null (space_start (heap_head (ti_heap t_info))) *)

    destruct H as [? [? ?]]. rewrite <- Heqh in *. rewrite <- Heqth in *.
    remember (glabel g) as ginfo. destruct ginfo.
    1: exfalso; apply H1; rewrite <- H; reflexivity. simpl in H2.
    admit.
  - 
Abort.
