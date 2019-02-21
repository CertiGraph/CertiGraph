Require Import compcert.cfrontend.ClightBigstep.
Require Export VST.veric.rmaps.
Require Export RamifyCoq.lib.List_ext.
Require Export RamifyCoq.graph.graph_model.
Require Export RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.spatial_gcgraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.
Require Export RamifyCoq.msl_ext.iter_sepcon.

Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition init_data2byte (d: init_data) : byte :=
  match d with
  | Init_int8 m => Byte.repr (Int.intval m)
  | _ => Byte.one
  end.

Definition all_string_constants (sh: share) (gv: globals) : mpred :=
  cstring sh (map init_data2byte (gvar_init v___stringlit_1)) (gv ___stringlit_1) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_2)) (gv ___stringlit_2) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_3)) (gv ___stringlit_3) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_4)) (gv ___stringlit_4) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_5)) (gv ___stringlit_5) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_6)) (gv ___stringlit_6) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_7)) (gv ___stringlit_7) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_8)) (gv ___stringlit_8) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_9)) (gv ___stringlit_9) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_10)) (gv ___stringlit_10) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_11)) (gv ___stringlit_11) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_12)) (gv ___stringlit_12) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_13)) (gv ___stringlit_13) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_14)) (gv ___stringlit_14) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_15)) (gv ___stringlit_15) *
  cstring sh (map init_data2byte (gvar_init v___stringlit_16)) (gv ___stringlit_16).

Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [ _x OF int_or_ptr_type ]
   PROP(valid_int_or_ptr x) LOCAL(temp _x x) SEP()
 POST [ tint ]
   PROP()
   LOCAL(temp ret_temp
          (Vint (Int.repr (match x with
                    | Vint _ => 1
                    | _ => 0
                    end))))
   SEP().

Definition int_or_ptr_to_int_spec :=
  DECLARE _int_or_ptr_to_int
  WITH x : val
  PRE [ _x OF int_or_ptr_type ]
    PROP(is_int I32 Signed x) LOCAL(temp _x x) SEP()
  POST [ tint ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_or_ptr_to_ptr_spec :=
  DECLARE _int_or_ptr_to_ptr
  WITH x : val
  PRE [ _x OF int_or_ptr_type ]
    PROP(isptr x) LOCAL(temp _x x) SEP()
  POST [ tptr tvoid ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_to_int_or_ptr_spec :=
  DECLARE _int_to_int_or_ptr
  WITH x : val
  PRE [ _x OF tint ]
    PROP(valid_int_or_ptr x)
    LOCAL(temp _x x) SEP()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition ptr_to_int_or_ptr_spec :=
  DECLARE _ptr_to_int_or_ptr
  WITH x : val
  PRE [ _x OF tptr tvoid ]
    PROP(valid_int_or_ptr x) LOCAL(temp _x x) SEP()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition Is_block_spec :=
  DECLARE _Is_block
  WITH x : val
  PRE [ _x OF int_or_ptr_type ]
    PROP(valid_int_or_ptr x) LOCAL(temp _x x) SEP()
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp
               (Vint (Int.repr (match x with
                                | Vptr _ _ => 1
                                | _ => 0
                                end))))
    SEP().

Definition abort_with_spec :=
  DECLARE _abort_with
  WITH s: val, str: list byte, sh: share
  PRE [ _s OF tptr tschar]
    PROP (readable_share sh) LOCAL (temp _s s) SEP (cstring sh str s)
  POST [ tvoid ]
    PROP (False) LOCAL() SEP().

Definition IS_FROM_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Definition IS_FROM_WEAK_TYPE :=
  ProdType (ProdType (ProdType (ProdType (ProdType (ConstType share) (ConstType val)) (ConstType Z)) (ConstType val)) Mpred) (ConstType Z).

(* (ProdType (ProdType (ProdType *)
(* (ProdType (ConstType share) (ConstType val)) *)
(* (ConstType Z)) (ConstType val)) Mpred) *)
(* (ConstType Z). *)

Axiom valid_pointer_bounds: forall v,
    valid_pointer v |-- !!(exists b o, v = Vptr b (Ptrofs.repr o) /\ 0 <= o <= Ptrofs.max_unsigned).

(* what's up with TYPE? *)
(* see manual for spec-writing *)
Program Definition Is_from_weak_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_WEAK_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred, m: Z
  PRE [ _from_start OF (tptr int_or_ptr_type), (* n is pos? how did we get away without this info? add? *)
        _from_limit OF (tptr int_or_ptr_type),
        _v OF (tptr int_or_ptr_type)]
    PROP (v = offset_val m start; 0 < n; sepalg.nonidentity sh; 0 <= m)
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start); temp _v v) (* weakened here -- gave ourselves the info that it's the same block, therefore is not stuck *)
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if b then 1 else 0))))
    SEP (P).
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition forward_p_address
           (p: forward_p_type) (ti: val) (f_info: fun_info) (g: LGraph) :=
  match p with
  | inl root_index => field_address
                        thread_info_type
                        [ArraySubsc (Znth root_index (live_roots_indices f_info));
                           StructField _args] ti
  | inr (v, n) => offset_val (WORD_SIZE * n) (vertex_address g v)
  end.

Definition limit_address g t_info from :=
  offset_val (WORD_SIZE * gen_size t_info from) (gen_start g from).

Definition next_address t_info to :=
  field_address heap_type
                [StructField _next;
                   ArraySubsc (Z.of_nat to); StructField _spaces] (ti_heap_p t_info).

Definition forward_spec :=
  DECLARE _forward
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, depth: Z, forward_p: forward_p_type
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _next OF (tptr (tptr int_or_ptr_type)),
        _p OF (tptr int_or_ptr_type),
        _depth OF tint]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_p_compatible forward_p roots g from;
          forward_condition g t_info from to;
          0 <= depth <= Int.max_signed;
          from <> to)
    LOCAL (temp _from_start (gen_start g from);
           temp _from_limit (limit_address g t_info from);
           temp _next (next_address t_info to);
           temp _p (forward_p_address forward_p ti f_info g);
           temp _depth (Vint (Int.repr depth)))
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          roots' = upd_roots from to forward_p g roots f_info;
          forward_relation from to (Z.to_nat depth)
                           (forward_p2forward_t forward_p roots g) g g';
          forward_condition g' t_info' from to;
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _next OF (tptr (tptr int_or_ptr_type)),
        _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to)
    LOCAL (temp _from_start (gen_start g from);
           temp _from_limit (limit_address g t_info from);
           temp _next (next_address t_info to);
           temp _fi fi; temp _ti ti)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g' : LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          forward_roots_relation from to f_info roots g roots' g';
          forward_condition g' t_info' from to;
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition do_scan_spec :=
  DECLARE _do_scan
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, to_index: nat
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _scan OF (tptr int_or_ptr_type),
        _next OF (tptr (tptr int_or_ptr_type))]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to; closure_has_index g to to_index;
          0 < gen_size t_info to; gen_unmarked g to)
    LOCAL (temp _from_start (gen_start g from);
           temp _from_limit (limit_address g t_info from);
           temp _scan (offset_val (- WORD_SIZE) (vertex_address g (to, to_index)));
           temp _next (next_address t_info to))
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info,
    PROP (super_compatible (g', t_info', roots) f_info outlier;
          forward_condition g' t_info' from to;
          do_scan_relation from to to_index g g';
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [ _from OF (tptr space_type),
        _to OF (tptr space_type),
        _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          do_generation_condition g t_info roots f_info from to;
          from <> to)
    LOCAL (temp _from (space_address t_info from);
           temp _to (space_address t_info to);
           temp _fi fi; temp _ti ti)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g' : LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          thread_info_relation t_info t_info';
          do_generation_relation from to f_info roots roots' g g')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition create_space_spec :=
  DECLARE _create_space
  WITH sh: share, s: val, n: Z, gv: globals, rsh: share
  PRE [ _s OF (tptr space_type),
        _n OF tuint]
    PROP (writable_share sh;
          readable_share rsh;
          0 <= n < MAX_SPACE_SIZE)
    LOCAL (temp _s s; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (all_string_constants rsh gv; data_at_ sh space_type s)
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP (all_string_constants rsh gv;
         malloc_token Ews (tarray int_or_ptr_type n) p;
         data_at_ Ews (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (WORD_SIZE * n) p))) s).

Definition zero_triple: (val * (val * val)) := (nullval, (nullval, nullval)).

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh) LOCAL (gvars gv) SEP (all_string_constants sh gv)
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp h)
    SEP (all_string_constants sh gv; malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh) LOCAL (gvars gv) SEP (all_string_constants sh gv)
  POST [tptr thread_info_type]
    EX t: val, EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp t)
    SEP (all_string_constants sh gv;
         malloc_token Ews thread_info_type t;
         data_at Ews thread_info_type
                 (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,
                      (h, list_repeat (Z.to_nat MAX_ARGS) Vundef))) t;
         malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition resume_spec :=
  DECLARE _resume
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          graph_thread_info_compatible g t_info;
          graph_gen_clear g O)
    LOCAL (temp _fi fi; temp _ti ti; gvars gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    PROP (fun_word_size f_info <= total_space (heap_head (ti_heap t_info)))
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti).

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          garbage_collect_condition g t_info roots f_info;
          safe_to_copy g)
    LOCAL (temp _fi fi; temp _ti ti; gvars gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti;
         ti_token_rep t_info)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          garbage_collect_relation f_info roots roots' g g';
          garbage_collect_condition g' t_info' roots' f_info;
          safe_to_copy g')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         before_gc_thread_info_rep sh t_info' ti;
         ti_token_rep t_info').

Definition reset_heap_spec :=
  DECLARE _reset_heap
  WITH h: val
  PRE [ _h OF (tptr heap_type)]
    PROP () LOCAL (temp _h h) SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition free_heap_spec :=
  DECLARE _free_heap
  WITH h: val
  PRE [ _h OF (tptr heap_type)]
    PROP () LOCAL (temp _h h) SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition Gprog: funspecs :=
  ltac:(with_library prog
                     [test_int_or_ptr_spec;
                      int_or_ptr_to_int_spec;
                      int_or_ptr_to_ptr_spec;
                      int_to_int_or_ptr_spec;
                      ptr_to_int_or_ptr_spec;
                      Is_block_spec;
                      Is_from_weak_spec;
                      abort_with_spec;
                      forward_spec;
                      forward_roots_spec;
                      do_scan_spec;
                      do_generation_spec;
                      create_space_spec;
                      create_heap_spec;
                      make_tinfo_spec;
                      resume_spec;
                      garbage_collect_spec;
                      reset_heap_spec;
                      free_heap_spec]).

Lemma body_is_from_weak: semax_body Vprog Gprog f_Is_from Is_from_weak_spec.
Proof.
  start_dep_function. simpl.
  destruct ts as [[[[[? fs] n] ?] ?] z].
  assert_PROP (isptr fs). {
    sep_apply (apply_derives m (memory_block s n fs * TT)).
    rewrite memory_block_isptr. Intros.
    entailer!. } rename H into Hp.
  forward_if
    (EX b: {v_in_range v fs n} + {~ v_in_range v fs n},
     PROP ()
    LOCAL (temp _t'1 (Vint (Int.repr (if b then 1 else 0))))
    SEP (weak_derives m (memory_block s n fs * TT) && emp;
         weak_derives m (valid_pointer v * TT) && emp; m)).
  1: {
    (* sep_apply (apply_derives m (memory_block s n fs * TT)). *)
       (* rewrite memory_block_isptr. Intros. *)
       destruct fs; try contradiction.
       simpl denote_tc_test_order.
       unfold test_order_ptrs.
       unfold sameblock.
       destruct (peq b b).
       2: { destruct n0. reflexivity. }
       simpl proj_sumbool.
       Opaque weak_derives valid_pointer.
       apply andp_right.
       2: { eapply derives_trans.
            2: apply valid_pointer_weak.
            simpl offset_val.
            sep_apply (apply_derives m (valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr z))) * TT)). entailer!.
       }
       sep_apply (apply_derives m (memory_block s n (Vptr b i) * TT)).
       sep_apply (memory_block_valid_ptr s n (Vptr b i)); [omega|].
       eapply derives_trans.
       2: apply valid_pointer_weak.
       entailer!.
  }
  - forward.
    + entailer!.
      destruct fs; try contradiction.
      simpl denote_tc_test_order.
      unfold test_order_ptrs.
      unfold sameblock.
      destruct (peq b b).
      2: { destruct n0. reflexivity. }
      simpl proj_sumbool.
      Opaque weak_derives valid_pointer.
      apply andp_right.
      2: { simpl offset_val.
           sep_apply (apply_derives m (memory_block s n (Vptr b i) * TT)).
           sep_apply (memory_block_weak_valid_pointer s n (Vptr b i) n).
           omega. auto. auto. simpl offset_val.
           apply extend_weak_valid_pointer.
      }
      simpl offset_val.
      sep_apply (apply_derives m (valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr z))) * TT)).
      sep_apply (valid_pointer_weak (Vptr b (Ptrofs.add i (Ptrofs.repr z)))). apply extend_weak_valid_pointer.

    + subst v. unfold sem_cmp_pp.
      change (Tpointer tvoid
                       {| attr_volatile := false; attr_alignas := Some 2%N |}) with int_or_ptr_type.
      destruct fs; try contradiction.
      simpl offset_val. simpl eval_binop.
      unfold sem_cmp_pp. unfold Archi.ptr64.
      simpl Val.cmpu_bool.
      unfold eq_block. destruct peq. 2: contradiction.
      inv_int i. rewrite !ptrofs_add_repr.
      unfold Ptrofs.ltu.
      assert_PROP (0 <= ofs + n <= Ptrofs.max_unsigned). {
        sep_apply (apply_derives m (memory_block s n (Vptr b (Ptrofs.repr ofs)) * TT)).
        sep_apply (memory_block_local_facts s n (Vptr b (Ptrofs.repr ofs))). Intros. red in H0.
        rewrite Ptrofs.unsigned_repr in H0. 2: rep_omega.
        apply prop_right. rep_omega. }
      assert_PROP (0 <= ofs + z <= Ptrofs.max_unsigned). {
        sep_apply (apply_derives m (valid_pointer (Vptr b (Ptrofs.repr (ofs + z))) * TT)).
        sep_apply (valid_pointer_bounds (Vptr b (Ptrofs.repr (ofs + z)))). Intros. apply prop_right.
        destruct H5 as [b0 [o [? ?]]].
        inversion H5.
        
        generalize (Ptrofs.unsigned_repr o H6); intro Hx.
        unfold Ptrofs.unsigned in Hx.
        
(* rewrite Ptrofs.unsigned_repr in H5.         *)
        admit.
      }
      rewrite !Ptrofs.unsigned_repr; auto.
      * destruct (zlt (ofs + z) (ofs + n)).
        -- simpl force_val. apply Zplus_lt_reg_l in l.
           simpl in H. rewrite ptrofs_add_repr in H.
           assert (v_in_range
                     (Vptr b (Ptrofs.repr (ofs + z))) (Vptr b (Ptrofs.repr ofs)) n). {
             exists z. simpl. rewrite ptrofs_add_repr.
             split; auto. }
           Exists (@left _ (~ v_in_range (Vptr b (Ptrofs.repr (ofs + z))) (Vptr b (Ptrofs.repr ofs)) n) H6).
           entailer!.
        -- assert (n <= z) by omega. clear g.
           simpl force_val.
           assert (~ v_in_range
                     (Vptr b (Ptrofs.repr (ofs + z))) (Vptr b (Ptrofs.repr ofs)) n). {
             intro. destruct H7 as [i [? ?]]. simpl offset_val in H8. rewrite ptrofs_add_repr in H8.
             inversion H8.
             rewrite !Ptrofs.Z_mod_modulus_eq in H10.
             rewrite !Z.mod_small in H10; [|rep_omega..].
             apply Z.add_reg_l in H10. omega. }
           Exists (@right (v_in_range (Vptr b (Ptrofs.repr (ofs + z))) (Vptr b (Ptrofs.repr ofs)) n) _ H7).
           entailer!.
  - forward. subst v. unfold sem_cmp_pp in H.
    unfold Archi.ptr64 in H. destruct fs; try contradiction.
    simpl in H. unfold eq_block in H.
    destruct peq in H. 2: contradiction.
    inv_int i. rewrite ptrofs_add_repr in H.
    unfold Ptrofs.ltu in H.
    assert_PROP (0 <= ofs + z <= Ptrofs.max_unsigned). {
      admit.
    } rewrite !Ptrofs.unsigned_repr in H; auto.
    2: rep_omega. destruct (zlt (ofs + z) ofs).
    1: exfalso; omega. simpl in H. unfold typed_false in H.
    simpl in H. inversion H.
  - Intros b. forward. Exists b. entailer.
    rewrite <- (sepcon_emp m) at 4.
    rewrite (sepcon_comm m emp).
    apply sepcon_derives.
    2: apply derives_refl.
    rewrite <- (sepcon_emp emp) at 3.
    apply sepcon_derives;
      apply andp_left2, derives_refl.
Admitted.
    
Lemma int_or_ptr_to_int_is_not_stuck: forall ge e le m id  i,
    le ! id = Some (Vint i) ->
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (talignas 2%N (tptr tvoid))) tint)
                     (Vint i).
Proof. intros; econstructor; [constructor; apply H | trivial]. Qed.

Lemma int_or_ptr_to_ptr_is_not_stuck: forall ge e le m id b o,
    le ! id = Some (Vptr b o) ->
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (talignas 2%N (tptr tvoid)))
                            (tptr tvoid))
                     (Vptr b o).
Proof. intros; econstructor; [constructor; apply H | trivial]. Qed.

Lemma int_to_int_or_ptr_is_not_stuck: forall ge e le m id i,
    le ! id = Some (Vint i) ->
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id tint) (talignas 2%N (tptr tvoid)))
                     (Vint i).
Proof. intros; econstructor; [constructor; apply H | trivial]. Qed.

Lemma ptr_to_int_or_ptr_is_not_stuck: forall ge e le m id b o,
    le ! id = Some (Vptr b o) ->
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (tptr tvoid))
                            (talignas 2%N (tptr tvoid)))
                     (Vptr b o).
Proof. intros; econstructor; [constructor; apply H | trivial]. Qed.

Lemma test_int_or_ptr_is_stuck_on_ptr: forall ge e le m v id b o,
    le ! id = Some (Vptr b o) ->
    Clight.eval_expr ge e le m
                     (Ecast (Ebinop Oand
                     (Ecast (Etempvar id
                     (talignas 2%N (tptr tvoid))) tint) (*why 2 and not 4?*)
                     (Econst_int (Int.repr 1) tint) tint) tint)
                     v -> False.  
Proof.
  intros. inversion H0; subst; [|inversion H1]; simpl in H5.
  destruct v1; inversion H5; clear H5; subst.
  + inversion H3; subst; [|inversion H1];
    inversion H7; subst; [|inversion H1];
    inversion H4; subst; [|inversion H1];
    rewrite H in H10; inversion H10; subst; clear H H10; inversion H6;
      subst; clear H6; destruct v2; inversion H9.
  + clear H;
    inversion H3; subst; [|inversion H];
    inversion H6; subst; [|inversion H];
    inversion H2; subst; [|inversion H];
    destruct v1; destruct v2; inversion H8.
Qed.

Lemma is_from_is_stuck_for_ptr: forall ge e le le2 m m2 et _from_start
                                       _from_limit _v b1 b3 o1 o3 out,
    le ! _from_start = Some (Vptr b1 o1) ->
    (* le ! _from_limit = Some (Vptr b2 o2) -> *)
    le ! _v = Some (Vptr b3 o3) ->
    (* b1 = b2 -> *)
    b1 <> b3 ->
    ClightBigstep.exec_stmt ge e le m
      (Ssequence
        (Sifthenelse (Ebinop Ole
          (Etempvar _from_start (tptr (talignas 2%N (tptr tvoid))))
          (Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) tint)
            (Sset _t'1
              (Ecast
                (Ebinop Olt (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                  (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) tint)
                tbool))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))
        (Sreturn (Some (Etempvar _t'1 tint))))
      et le2 m2 out -> False.
Proof.
  intros; inversion H2; subst;
  (clear H2 H13; inversion H8; subst;
   clear -H9 H H0 H1; inversion H9; subst; [|inversion H2];
   inversion H7; subst; [|inversion H2];
   inversion H8; subst; [|inversion H2];
   rewrite H in H5; rewrite H0 in H6;
   inversion H5; inversion H6; subst; clear H H0 H5 H6 H7 H8 H9;
   simpl in H10; unfold Cop.sem_cmp in H10; simpl in H10;
   unfold cmp_ptr in H10; simpl in H10;
   destruct (eq_block b1 b3); [contradiction|];
   destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned o1) &&
               Mem.valid_pointer m b3 (Ptrofs.unsigned o3))%bool; inversion H10).
Qed.
