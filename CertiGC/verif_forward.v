Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  unfold forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros. hnf in H0. destruct H as [? [? [? ?]]]. hnf in H3.
    assert (Zlength roots = Zlength (live_roots_indices f_info)). {
      rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H3, Zlength_map.
      reflexivity.
    } rewrite H6 in H0.
    pose proof (in_map (flip Znth (ti_args t_info))
                       (live_roots_indices f_info) _ (Znth_In _ _ H0)).
    unfold flip in H7 at 1. rewrite <- H3 in H7. apply list_in_map_inv in H7.
    destruct H7 as [root [? ?]]. unfold Inhabitant_val in H7. forward.
    + apply prop_right, (fi_index_range f_info), Znth_In. apply H0.
    + entailer!. rewrite H7. destruct root as [[? | ?] | ?]; simpl; auto.
      * destruct g0. simpl. exact I.
      * destruct H4. unfold vertex_address. rewrite Forall_forall in H15.
        rewrite (filter_sum_right_In_iff v roots) in H8. apply H15 in H8.
        destruct H8. apply graph_has_gen_start_isptr in H8.
        remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
        simpl. exact I.
    + rewrite H7. forward_call (root2val g root).
      * destruct root as [[? | ?] | ?]; simpl.
        -- rewrite Int.unsigned_repr_eq, Zodd_mod, <- Zmod_div_mod; try rep_omega.
           ++ rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full, Z.mod_1_l by omega.
              unfold Zeq_bool. reflexivity.
           ++ unfold Int.modulus. rewrite <- Z.mod_divide by omega.
              compute. reflexivity.
        -- destruct g0. simpl. inv_int i. rewrite ptrofs_add_repr.
           replace (ofs + ofs) with (2 * ofs)%Z by omega.
           rewrite Ptrofs.unsigned_repr_eq, Zodd_mod, <- Zmod_div_mod; try rep_omega.
           ++ rewrite Z.mul_comm, Z_mod_mult. unfold Zeq_bool. reflexivity.
           ++ unfold Ptrofs.modulus. rewrite <- Z.mod_divide by omega.
              compute. reflexivity.
        --
Abort.
