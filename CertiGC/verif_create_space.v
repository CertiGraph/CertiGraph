Require Import RamifyCoq.CertiGC.gc_spec.

Local Open Scope Z_scope.

Lemma body_create_space: semax_body Vprog Gprog f_create_space create_space_spec.
Proof.
  start_function.
  forward_call (Tarray int_or_ptr_type n noattr).
  - entailer!. replace (n * 4) with (4 * n) by omega. reflexivity.
  - split; [|split].
    + simpl. destruct H. replace (Z.max 0 n) with n.
      * split. 1: omega. transitivity (4 * (Int.max_unsigned / 4)). 1: omega.
        apply Z.mul_div_le. omega.
      * symmetry. apply Z.max_r. assumption.
    + simpl; tauto.
    + compute; tauto.
  - Intros p. if_tac.
    + subst p. forward_if False.
      * unfold all_string_constants. Intros.
        forward_call ((gv ___stringlit_6),
                      (map init_data2byte (gvar_init v___stringlit_6))).
        exfalso; assumption.
      * inversion H0.
    + Intros. forward_if (
                     PROP ( )
                     LOCAL (temp _p p; temp _s s; temp _n (Vint (Int.repr n)))
                     SEP (all_string_constants gv;
                          malloc_token Tsh (Tarray int_or_ptr_type n noattr) p;
                          data_at_ Tsh (Tarray int_or_ptr_type n noattr) p;
                          data_at_ sh space_type s)).
      * contradiction.
      * forward. entailer!.
      * forward. forward. forward. forward. Exists p. unfold tarray. entailer!.
Qed.
