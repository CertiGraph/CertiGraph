Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export RamifyCoq.CertiGC.gc.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition heap_type: type := Tstruct _heap noattr.

Definition init_data2byte (d: init_data) : byte :=
  match d with
  | Init_int8 m => Byte.repr (Int.intval m)
  | _ => Byte.one
  end.

Definition all_string_constants (gv: globals) : mpred :=
  cstring (map init_data2byte (gvar_init v___stringlit_1)) (gv ___stringlit_1) *
  cstring (map init_data2byte (gvar_init v___stringlit_2)) (gv ___stringlit_2) *
  cstring (map init_data2byte (gvar_init v___stringlit_3)) (gv ___stringlit_3) *
  cstring (map init_data2byte (gvar_init v___stringlit_4)) (gv ___stringlit_4) *
  cstring (map init_data2byte (gvar_init v___stringlit_5)) (gv ___stringlit_5) *
  cstring (map init_data2byte (gvar_init v___stringlit_6)) (gv ___stringlit_6) *
  cstring (map init_data2byte (gvar_init v___stringlit_7)) (gv ___stringlit_7) *
  cstring (map init_data2byte (gvar_init v___stringlit_8)) (gv ___stringlit_8) *
  cstring (map init_data2byte (gvar_init v___stringlit_9)) (gv ___stringlit_9) *
  cstring (map init_data2byte (gvar_init v___stringlit_10)) (gv ___stringlit_10) *
  cstring (map init_data2byte (gvar_init v___stringlit_11)) (gv ___stringlit_11) *
  cstring (map init_data2byte (gvar_init v___stringlit_12)) (gv ___stringlit_12) *
  cstring (map init_data2byte (gvar_init v___stringlit_13)) (gv ___stringlit_13) *
  cstring (map init_data2byte (gvar_init v___stringlit_14)) (gv ___stringlit_14) *
  cstring (map init_data2byte (gvar_init v___stringlit_15)) (gv ___stringlit_15) *
  cstring (map init_data2byte (gvar_init v___stringlit_16)) (gv ___stringlit_16).

Definition MAX_SPACES: Z := 12.
Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
  
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
                                | Vint _ => 0
                                | _ => 1
                                end))))
    SEP().

Definition abort_with_spec :=
  DECLARE _abort_with
  WITH s: val, str: list byte
  PRE [ _s OF tptr tschar]
    PROP () LOCAL (temp _s s) SEP (cstring  str s)
  POST [ tvoid ]
    PROP (False) LOCAL() SEP().

Definition Is_from_spec :=
  DECLARE _Is_from
  WITH start : val, n: Z, v: val
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _v OF (tptr int_or_ptr_type)]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start); temp _v v)
    SEP ()
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr 0)))
    SEP ().

Definition forward_spec :=
  DECLARE _forward
  WITH start: val, n: Z, next: val, p: val, depth: Z
  PRE [ _from_start OF (tptr int_or_ptr_type),
        _from_limit OF (tptr int_or_ptr_type),
        _next OF (tptr int_or_ptr_type),
        _p OF (tptr int_or_ptr_type),
        _depth OF tint]
    PROP ()
    LOCAL (temp _from_start start; temp _from_limit (offset_val n start);
           temp _next next; temp _p p; temp _depth (Vint (Int.repr depth)))
    SEP ()
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
  WITH sh: share, s: val, n: Z, gv: globals
  PRE [ _s OF (tptr space_type),
        _n OF tuint]
    PROP (writable_share sh; 0 <= n <= Int.max_unsigned / 4)
    LOCAL (temp _s s; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (all_string_constants gv; data_at_ sh space_type s)
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP (all_string_constants gv;
         malloc_token Tsh (tarray int_or_ptr_type n) p;
         data_at_ Tsh (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (4 * n) p))) s).

Definition zero_triple: (val * (val * val)) :=
  (Vint (Int.repr 0), (Vint (Int.repr 0), Vint (Int.repr 0))).

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH gv: globals
  PRE []
    PROP () LOCAL (gvars gv) SEP (all_string_constants gv)
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp h)
    SEP (all_string_constants gv; malloc_token Tsh heap_type h;
         data_at Tsh heap_type
                 ((p, (p, (offset_val (4 * NURSERY_SIZE) p)))
                    :: list_repeat (Z.to_nat (MAX_SPACES - 1)) zero_triple) h; 
         malloc_token Tsh (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Tsh (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH u: unit
  PRE []
    PROP () LOCAL () SEP ()
  POST [tptr thread_info_type]
    EX t: val,
  PROP () LOCAL (temp ret_temp t) SEP ().

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
  WITH fi: val, ti: val
  PRE [ _fi OF (tptr tuint),
        _ti OF (tptr thread_info_type)]
    PROP () LOCAL (temp _fi fi; temp _ti ti) SEP ()
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
