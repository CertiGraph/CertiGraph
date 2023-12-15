From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.

Local Open Scope Z_scope.

Lemma body_create_space: semax_body Vprog Gprog f_create_space create_space_spec.
Proof.
  start_function.
  forward_call (Tarray int_or_ptr_type n noattr, gv).
    + entailer!. simpl. rewrite Z.max_r by lia. now rewrite Z.mul_comm.
    + simpl. rewrite Z.max_r by rep_lia.
     apply MSS_max_wordsize_unsigned_range; auto.
    + Intros p. if_tac.
      * subst p. forward_if False.
        -- unfold all_string_constants. Intros.
             forward_call.
             contradiction.
        -- first [exfalso; now apply H0 | inversion H0 ].
      * Intros. forward_if (
                    PROP ( )
                    LOCAL (temp _p p; temp _s s;
                           temp _n (if Archi.ptr64 then Vlong (Int64.repr n)
                                    else Vint (Int.repr n)))
                    SEP (mem_mgr gv; all_string_constants rsh gv;
                         malloc_token Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ Ews (Tarray int_or_ptr_type n noattr) p;
                         data_at_ sh space_type s)).
        -- contradiction.
        -- forward. entailer!.
        -- do 5 forward. Exists p. unfold tarray. entailer!.
Qed.
