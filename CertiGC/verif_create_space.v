Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope Z_scope.

Lemma body_create_space: semax_body Vprog Gprog f_create_space create_space_spec.
Proof.
  start_function.
  forward_if True.
  - exfalso. rewrite MSS_eq_unsigned, Int.unsigned_repr in H0;
               [lia | apply MSS_max_unsigned_range; assumption].
  - forward. entailer!.
  - forward_call (Tarray int_or_ptr_type n noattr, gv).
    + entailer!. simpl. rewrite Z.max_r by lia. now rewrite Z.mul_comm.
    + simpl. replace (Z.max 0 n) with n. 1: apply MSS_max_4_unsigned_range, H.
      rewrite Z.max_r; [reflexivity | destruct H; assumption].
    + Intros p. if_tac.
      * subst p. forward_if False.
        -- unfold all_string_constants. Intros.
           forward_call ((gv ___stringlit_7),
                         (map init_data2byte (gvar_init v___stringlit_7)), rsh).
           exfalso; assumption.
        -- inversion H0.
      * Intros. forward_if (
                    PROP ( )
                    LOCAL (temp _p p; temp _s s; temp _n (Vint (Int.repr n)))
                    SEP (mem_mgr gv; all_string_constants rsh gv;
                         malloc_token Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ sh space_type s)).
        -- contradiction.
        -- forward. entailer!.
        -- do 3 forward. Exists p. unfold tarray. entailer!.
Qed.
