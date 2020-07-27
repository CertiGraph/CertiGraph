Require Export VST.veric.rmaps.
Require Export CertiGraph.lib.List_ext.
Require Export CertiGraph.graph.graph_model.
Require Export CertiGraph.CertiGC.GCGraph.
Require Export CertiGraph.CertiGC.spatial_gcgraph.
Require Export CertiGraph.CertiGC.env_graph_gc.
Require Export CertiGraph.msl_ext.iter_sepcon.

Local Open Scope logic.

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
 PRE [int_or_ptr_type]
   PROP (valid_int_or_ptr x)
   PARAMS (x)
   GLOBALS ()
   SEP ()
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
  PRE [int_or_ptr_type ]
    PROP (is_int I32 Signed x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ tint ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_or_ptr_to_ptr_spec :=
  DECLARE _int_or_ptr_to_ptr
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (isptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_to_int_or_ptr_spec :=
  DECLARE _int_to_int_or_ptr
  WITH x : val
  PRE [tint]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition ptr_to_int_or_ptr_spec :=
  DECLARE _ptr_to_int_or_ptr
  WITH x : val
  PRE [tptr tvoid ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition Is_block_spec :=
  DECLARE _Is_block
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
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
  PRE [tptr tschar]
    PROP (readable_share sh)
    PARAMS (s)
    GLOBALS ()
    SEP (cstring sh str s)
  POST [ tvoid ]
    PROP (False) LOCAL() SEP().

Definition IS_FROM_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Program Definition Is_from_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type]
    PROP ()
    PARAMS (start; offset_val n start; v)
    GLOBALS ()
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if b then 1 else 0))))
    SEP (P).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl;
    rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  f_equal; f_equal; [|f_equal]; now rewrite derives_nonexpansive_l.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality t.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, approx_idem. reflexivity.
Qed.

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
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr int_or_ptr_type,
       tint]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_p_compatible forward_p roots g from;
          forward_condition g t_info from to;
          0 <= depth <= Int.max_signed;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           next_address t_info to;
           forward_p_address forward_p ti f_info g;
           Vint (Int.repr depth))
    GLOBALS ()
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
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr tuint,
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           next_address t_info to;
           fi; ti)
    GLOBALS (gv)
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
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to; closure_has_index g to to_index;
          0 < gen_size t_info to; gen_unmarked g to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           offset_val (- WORD_SIZE) (vertex_address g (to, to_index));
           next_address t_info to)
    GLOBALS ()
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
  PRE [tptr space_type,
       tptr space_type,
       tptr tuint,
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          do_generation_condition g t_info roots f_info from to;
          from <> to)
    PARAMS (space_address t_info from;
           space_address t_info to;
           fi; ti)
    GLOBALS (gv)
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
  PRE [tptr space_type, tuint]
    PROP (writable_share sh;
          readable_share rsh;
          0 <= n < MAX_SPACE_SIZE)
    PARAMS (s; Vint (Int.repr n))
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants rsh gv; data_at_ sh space_type s)
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP (mem_mgr gv; all_string_constants rsh gv;
         malloc_token Ews (tarray int_or_ptr_type n) p;
         data_at_ Ews (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (WORD_SIZE * n) p))) s).

Definition zero_triple: (val * (val * val)) := (nullval, (nullval, nullval)).

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv)
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp h)
    SEP (mem_mgr gv; all_string_constants sh gv; malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv)
  POST [tptr thread_info_type]
    EX t: val, EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp t)
    SEP (mem_mgr gv; all_string_constants sh gv;
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
  PRE [tptr tuint,
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          graph_thread_info_compatible g t_info;
          graph_gen_clear g O)
    PARAMS (fi; ti)
    GLOBALS (gv)
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
  PRE [tptr tuint,
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          garbage_collect_condition g t_info roots f_info;
          safe_to_copy g)
    PARAMS (fi; ti)
    GLOBALS (gv)
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
    SEP (mem_mgr gv;
         all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         before_gc_thread_info_rep sh t_info' ti;
         ti_token_rep t_info').

Definition reset_heap_spec :=
  DECLARE _reset_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP ()
    PARAMS (h)
    GLOBALS ()
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition free_heap_spec :=
  DECLARE _free_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP () PARAMS (h) GLOBALS () SEP ()
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
                      Is_from_spec;
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
