Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  unfold forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros. hnf in H0. destruct H as [? [? [? ?]]]. hnf in H3.
    assert (Zlength roots = Zlength (live_roots_indices f_info)). {
      rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H3, Zlength_map.
      reflexivity.
    } rewrite H6 in H0. forward.
    + apply prop_right, (fi_index_range f_info), Znth_In. apply H0.
    + entailer!. pose proof (in_map (flip Znth (ti_args t_info))
                                    (live_roots_indices f_info) _ (Znth_In _ _ H0)).
      unfold flip in H13 at 1. rewrite <- H3 in H13. apply list_in_map_inv in H13.
      destruct H13 as [x [? ?]]. unfold Inhabitant_val in H13. rewrite H13.
      destruct x as [[? | ?] | ?]; simpl; auto.
      * destruct g0. simpl. exact I.
      * unfold vertex_address.
      
Abort.
