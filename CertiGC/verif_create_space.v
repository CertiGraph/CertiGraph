Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope Z_scope.

Lemma body_create_space: semax_body Vprog Gprog f_create_space create_space_spec.
Proof.
  start_function.
  unfold MSS_constant. cbv [Archi.ptr64]. forward.
  forward_if True.
  - exfalso.
    match goal with
    | H: Int64.ltu _ _ = false |- _ =>
        apply ltu64_repr_false in H; try rewrite !Int64.unsigned_repr in * by rep_lia
    | H: Int.unsigned _ >= Int.unsigned _ |- _ =>
        rewrite !Int.unsigned_repr in H
    end;
      [unfold MAX_SPACE_SIZE in *; lia | vm_compute; easy |
       now apply MSS_max_unsigned_range].                                        
  - forward. entailer!.
  - forward_call (Tarray int_or_ptr_type n noattr, gv).
    + entailer!. simpl. rewrite Z.max_r by lia. now rewrite Z.mul_comm.
    + simpl. replace (Z.max 0 n) with n. 1: apply MSS_max_wordsize_unsigned_range, H.
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
                    LOCAL (temp _p p; temp _s s;
                           temp _n (if Archi.ptr64 then Vlong (Int64.repr n)
                                    else Vint (Int.repr n)))
                    SEP (mem_mgr gv; all_string_constants rsh gv;
                         malloc_token Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ sh space_type s; MSS_constant gv)).
        -- contradiction.
        -- forward. unfold MSS_constant. entailer!.
        -- do 3 forward. Exists p. unfold tarray. entailer!.
Qed.
