Require Export RamifyCoq.msl_ext.iter_sepcon.
Require Export RamifyCoq.CertiGC.env_graph_gc.
Require Export RamifyCoq.graph.graph_model.
Require Export RamifyCoq.msl_application.Graph.
Require Export RamifyCoq.CertiGC.GraphGC.
Require Export RamifyCoq.CertiGC.spatial_graph_gc.
Require Export RamifyCoq.floyd_ext.share.

Definition MAX_SPACES: Z := 12.
Lemma MAX_SPACES_eq: MAX_SPACES = 12. Proof. reflexivity. Qed.
Hint Rewrite MAX_SPACES_eq: rep_omega.
Global Opaque MAX_SPACES.

Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
Lemma NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 16. Proof. reflexivity. Qed.
Hint Rewrite NURSERY_SIZE_eq: rep_omega.
Global Opaque NURSERY_SIZE.

Definition MAX_ARGS: Z := 1024.
Lemma MAX_ARGS_eq: MAX_ARGS = 1024. Proof. reflexivity. Qed.
Hint Rewrite MAX_ARGS_eq: rep_omega.
Global Opaque MAX_ARGS.

Record fun_info : Type :=
  {
    fun_word_size: Z;
    live_roots_indices: list Z;
  }.

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  let len := Zlength (live_roots_indices fi) in
  data_at
    sh (tarray tuint (len + 2))
    (map Vint (map Int.repr (fun_word_size fi :: len :: live_roots_indices fi))) p.

Definition space_rest_rep (sp: space): mpred :=
  if (EquivDec.equiv_dec (space_start sp) nullval)
  then emp
  else data_at_ Tsh (tarray int_or_ptr_type (total_space sp - used_space sp))
                (offset_val (used_space sp) (space_start sp)).

Definition heap_rest_rep (hp: heap): mpred := iter_sepcon (spaces hp) space_rest_rep.

Definition space_reptype (sp: space): (reptype space_type) :=
  let s := space_start sp in (s, (offset_val (4 * (used_space sp)) s,
                                  offset_val (4 * (total_space sp)) s)).

Definition heap_struct_rep (hp: heap) (h: val): mpred :=
  data_at Tsh heap_type (map space_reptype (spaces hp)) h.

Record thread_info: Type :=
  {
    ti_used_space: Z;
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
  }.

Coercion Graph_LGraph: Graph >-> LGraph.
Coercion LGraph_SGraph: LGraph >-> SGraph.
Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vertices_at (sh: wshare) (P: val -> Prop) (g: Graph): mpred :=
  (@vertices_at _ _ _ _ _ _ (@PGP pPGG_VST (sPGG_VST sh)) PGA P g).
Definition whole_graph (sh: wshare) (g: Graph) := (vertices_at sh (vvalid g) g).

Definition valid_int_or_ptr (x: val) :=
 match x with
 | Vint i => Int.testbit i 0 = true
 | Vptr b z => Ptrofs.testbit z 0 = false
 | _ => False
 end.

Lemma valid_int_or_ptr_ii1:
 forall i, valid_int_or_ptr (Vint (Int.repr (i + i + 1))).
Proof.
intros.
simpl.
rewrite Int.unsigned_repr_eq.
rewrite Zodd_mod.
apply Zeq_is_eq_bool.
replace (i+i) with (2*i)%Z by omega.
rewrite <- Zmod_div_mod; try omega.
- rewrite Z.mul_comm, Z.add_comm, Z_mod_plus_full. reflexivity.
- compute; reflexivity.
- exists (Z.div Int.modulus 2). reflexivity.
Qed.

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

Definition Is_from_spec :=
  DECLARE _Is_from
  WITH sh: share, start : val, n: Z, v: val
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _v OF (tptr int_or_ptr_type)]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start); temp _v v)
    SEP (memory_block sh n start)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if b then 1 else 0))))
    SEP (memory_block sh n start).

Definition forward_spec :=
  DECLARE _forward
  WITH start: val, n: Z, next: val, p: val, depth: Z, g: Graph, sh: wshare
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _next OF (tptr int_or_ptr_type),
        _p OF (tptr int_or_ptr_type),
        _depth OF tint]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start);
           temp _next next; temp _p p; temp _depth (Vint (Int.repr depth)))
    SEP (whole_graph sh g; heap_rest_rep (glabel g))
  POST [tvoid]
  PROP () LOCAL () SEP ().

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
  WITH from: val, to: val, fi: val, ti: val
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
    PROP (writable_share sh; readable_share rsh; 0 <= n <= Int.max_unsigned / 4)
    LOCAL (temp _s s; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (all_string_constants rsh gv; data_at_ sh space_type s)
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP (all_string_constants rsh gv;
         malloc_token Tsh (tarray int_or_ptr_type n) p;
         data_at_ Tsh (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (4 * n) p))) s).

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
                 ((p, (p, (offset_val (4 * NURSERY_SIZE) p)))
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
                 (p, (offset_val (4 * NURSERY_SIZE) p,
                      (h, list_repeat (Z.to_nat MAX_ARGS) Vundef))) t;
         malloc_token Tsh heap_type h;
         data_at Tsh heap_type
                 ((p, (p, (offset_val (4 * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h; 
         malloc_token Tsh (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Tsh (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition resume_spec :=
  DECLARE _resume
  WITH fi: val, ti: val
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP () LOCAL (temp _fi fi; temp _ti ti) SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH fi: val, ti: val, rsh: rshare, f_info: fun_info
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP () LOCAL (temp _fi fi; temp _ti ti)
    SEP (fun_info_rep rsh f_info fi)
  POST [tvoid]
    PROP () LOCAL () SEP ().

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
