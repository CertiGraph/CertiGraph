Require Export VST.veric.rmaps.
Require Export RamifyCoq.lib.List_ext.
Require Export RamifyCoq.msl_ext.iter_sepcon.
Require Export RamifyCoq.graph.graph_model.
Require Export RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.spatial_gcgraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.

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

Definition v_in_range (v: val) (start: val) (n: Z): Prop :=
  exists i, 0 <= i < n /\ v = offset_val i start.

Definition IS_FROM_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Program Definition Is_from_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _v OF (tptr int_or_ptr_type)]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start); temp _v v)
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
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  f_equal; f_equal; [|f_equal]; rewrite derives_nonexpansive_l; reflexivity.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality t.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, approx_idem. reflexivity.
Qed.

Definition forward_p_type: Type := Z + (VType * Z).

Definition forward_p_address
           (p: forward_p_type) (ti: val) (f_info: fun_info) (g: LGraph) :=
  match p with
  | inl root_index => field_address
                        thread_info_type
                        [ArraySubsc (Znth root_index (live_roots_indices f_info));
                           StructField _args] ti
  | inr (v, n) => offset_val (WORD_SIZE * n) (vertex_address g v)
  end.

Definition forward_p2forward_t
           (p: forward_p_type) (roots: roots_t) (g: LGraph): forward_t :=
  match p with
  | inl root_index => root2forward (Znth root_index roots)
  | inr (v, n) => field2forward (Znth n (make_fields g v))
  end.

Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: LGraph): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => graph_has_v g v /\
                  0 <= n < Zlength (vlabel g v).(raw_fields) /\
                  Znth n (vlabel g v).(raw_fields) = None
  end.

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
          forward_p_compatible forward_p roots g;
          graph_has_gen g from; graph_has_gen g to)
    LOCAL (temp _from_start (gen_start g from);
           temp _from_limit
                (offset_val (WORD_SIZE * gen_size t_info from)
                            (gen_start g from));
           temp _next (field_address heap_type
              [StructField _next;
                 ArraySubsc (Z.of_nat to); StructField _spaces] (ti_heap_p t_info));
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
          forward_relation from to (Z.to_nat depth)
                           (forward_p2forward_t forward_p roots g) g g';
          graph_has_gen g' from; graph_has_gen g' to)
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH start: val, n: Z, next: val, fi: val, ti: val
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _next OF (tptr int_or_ptr_type),
        _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start);
           temp _next next; temp _fi fi; temp _ti ti)
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition do_scan_spec :=
  DECLARE _do_scan
  WITH start: val, n: Z, next: val, scan: val
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _scan OF (tptr int_or_ptr_type),
        _next OF (tptr (tptr int_or_ptr_type))]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start);
           temp _scan scan; temp _next next)
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val, from: val, to: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t
  PRE [ _from OF (tptr space_type),
        _to OF (tptr space_type),
        _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP ()
    LOCAL (temp _from from; temp _to to; temp _fi fi; temp _ti ti)
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

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
         malloc_token Tsh (tarray int_or_ptr_type n) p;
         data_at_ Tsh (tarray int_or_ptr_type n) p;
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
    SEP (all_string_constants sh gv; malloc_token Tsh heap_type h;
         data_at Tsh heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h;
         malloc_token Tsh (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Tsh (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh) LOCAL (gvars gv) SEP (all_string_constants sh gv)
  POST [tptr thread_info_type]
    EX t: val, EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp t)
    SEP (all_string_constants sh gv;
         malloc_token Tsh thread_info_type t;
         data_at Tsh thread_info_type
                 (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,
                      (h, list_repeat (Z.to_nat MAX_ARGS) Vundef))) t;
         malloc_token Tsh heap_type h;
         data_at Tsh heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h;
         malloc_token Tsh (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Tsh (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition resume_spec :=
  DECLARE _resume
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          graph_thread_info_compatible g t_info)
    LOCAL (temp _fi fi; temp _ti ti; gvars gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info,
    PROP (fun_word_size f_info <= total_space (heap_head (ti_heap t_info));
          resume_graph_relation g g';
          resume_thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier)
    LOCAL (temp _fi fi; temp _ti ti; gvars gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier)
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

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
