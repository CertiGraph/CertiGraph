From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.11".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "prim/prim3.c".
  Definition normalized := true.
End Info.

Definition _E : ident := $"E".
Definition _Is_block : ident := $"Is_block".
Definition _Is_from : ident := $"Is_from".
Definition _MAX_EDGES : ident := $"MAX_EDGES".
Definition _MAX_SPACE_SIZE : ident := $"MAX_SPACE_SIZE".
Definition _Node : ident := $"Node".
Definition _Union : ident := $"Union".
Definition _V : ident := $"V".
Definition __139 : ident := $"_139".
Definition __140 : ident := $"_140".
Definition __213 : ident := $"_213".
Definition __214 : ident := $"_214".
Definition __215 : ident := $"_215".
Definition __Bigint : ident := $"_Bigint".
Definition ___assert_func : ident := $"__assert_func".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___cleanup : ident := $"__cleanup".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___count : ident := $"__count".
Definition ___getreent : ident := $"__getreent".
Definition ___locale_t : ident := $"__locale_t".
Definition ___sFILE64 : ident := $"__sFILE64".
Definition ___sbuf : ident := $"__sbuf".
Definition ___sdidinit : ident := $"__sdidinit".
Definition ___sf : ident := $"__sf".
Definition ___sglue : ident := $"__sglue".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_11 : ident := $"__stringlit_11".
Definition ___stringlit_12 : ident := $"__stringlit_12".
Definition ___stringlit_13 : ident := $"__stringlit_13".
Definition ___stringlit_14 : ident := $"__stringlit_14".
Definition ___stringlit_15 : ident := $"__stringlit_15".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition ___tm : ident := $"__tm".
Definition ___tm_hour : ident := $"__tm_hour".
Definition ___tm_isdst : ident := $"__tm_isdst".
Definition ___tm_mday : ident := $"__tm_mday".
Definition ___tm_min : ident := $"__tm_min".
Definition ___tm_mon : ident := $"__tm_mon".
Definition ___tm_sec : ident := $"__tm_sec".
Definition ___tm_wday : ident := $"__tm_wday".
Definition ___tm_yday : ident := $"__tm_yday".
Definition ___tm_year : ident := $"__tm_year".
Definition ___value : ident := $"__value".
Definition ___wch : ident := $"__wch".
Definition ___wchb : ident := $"__wchb".
Definition __add : ident := $"_add".
Definition __asctime_buf : ident := $"_asctime_buf".
Definition __atexit : ident := $"_atexit".
Definition __atexit0 : ident := $"_atexit0".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __cvtbuf : ident := $"_cvtbuf".
Definition __cvtlen : ident := $"_cvtlen".
Definition __data : ident := $"_data".
Definition __dso_handle : ident := $"_dso_handle".
Definition __emergency : ident := $"_emergency".
Definition __errno : ident := $"_errno".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __fnargs : ident := $"_fnargs".
Definition __fns : ident := $"_fns".
Definition __fntypes : ident := $"_fntypes".
Definition __freelist : ident := $"_freelist".
Definition __gamma_signgam : ident := $"_gamma_signgam".
Definition __getdate_err : ident := $"_getdate_err".
Definition __glue : ident := $"_glue".
Definition __h_errno : ident := $"_h_errno".
Definition __inc : ident := $"_inc".
Definition __ind : ident := $"_ind".
Definition __iobs : ident := $"_iobs".
Definition __is_cxa : ident := $"_is_cxa".
Definition __k : ident := $"_k".
Definition __l64a_buf : ident := $"_l64a_buf".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __locale : ident := $"_locale".
Definition __localtime_buf : ident := $"_localtime_buf".
Definition __lock : ident := $"_lock".
Definition __maxwds : ident := $"_maxwds".
Definition __mblen_state : ident := $"_mblen_state".
Definition __mbrlen_state : ident := $"_mbrlen_state".
Definition __mbrtowc_state : ident := $"_mbrtowc_state".
Definition __mbsrtowcs_state : ident := $"_mbsrtowcs_state".
Definition __mbstate : ident := $"_mbstate".
Definition __mbtowc_state : ident := $"_mbtowc_state".
Definition __mult : ident := $"_mult".
Definition __nbuf : ident := $"_nbuf".
Definition __new : ident := $"_new".
Definition __next : ident := $"_next".
Definition __nextf : ident := $"_nextf".
Definition __niobs : ident := $"_niobs".
Definition __nmalloc : ident := $"_nmalloc".
Definition __offset : ident := $"_offset".
Definition __on_exit_args : ident := $"_on_exit_args".
Definition __p : ident := $"_p".
Definition __p5s : ident := $"_p5s".
Definition __r : ident := $"_r".
Definition __r48 : ident := $"_r48".
Definition __rand48 : ident := $"_rand48".
Definition __rand_next : ident := $"_rand_next".
Definition __read : ident := $"_read".
Definition __reent : ident := $"_reent".
Definition __result : ident := $"_result".
Definition __result_k : ident := $"_result_k".
Definition __seed : ident := $"_seed".
Definition __seek : ident := $"_seek".
Definition __seek64 : ident := $"_seek64".
Definition __sig_func : ident := $"_sig_func".
Definition __sign : ident := $"_sign".
Definition __signal_buf : ident := $"_signal_buf".
Definition __size : ident := $"_size".
Definition __stderr : ident := $"_stderr".
Definition __stdin : ident := $"_stdin".
Definition __stdout : ident := $"_stdout".
Definition __strtok_last : ident := $"_strtok_last".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __unspecified_locale_info : ident := $"_unspecified_locale_info".
Definition __unused : ident := $"_unused".
Definition __unused_rand : ident := $"_unused_rand".
Definition __up : ident := $"_up".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __wcrtomb_state : ident := $"_wcrtomb_state".
Definition __wcsrtombs_state : ident := $"_wcsrtombs_state".
Definition __wctomb_state : ident := $"_wctomb_state".
Definition __wds : ident := $"_wds".
Definition __write : ident := $"_write".
Definition __x : ident := $"_x".
Definition _a : ident := $"a".
Definition _abort_with : ident := $"abort_with".
Definition _active : ident := $"active".
Definition _adjustWeight : ident := $"adjustWeight".
Definition _alloc : ident := $"alloc".
Definition _append : ident := $"append".
Definition _args : ident := $"args".
Definition _arr : ident := $"arr".
Definition _build_heap : ident := $"build_heap".
Definition _capacity : ident := $"capacity".
Definition _cells : ident := $"cells".
Definition _check_symmetric_matrix : ident := $"check_symmetric_matrix".
Definition _cost : ident := $"cost".
Definition _create_heap : ident := $"create_heap".
Definition _create_space : ident := $"create_space".
Definition _data : ident := $"data".
Definition _depth : ident := $"depth".
Definition _do_generation : ident := $"do_generation".
Definition _do_scan : ident := $"do_scan".
Definition _dst : ident := $"dst".
Definition _edge : ident := $"edge".
Definition _edge_list : ident := $"edge_list".
Definition _empty_graph : ident := $"empty_graph".
Definition _exch : ident := $"exch".
Definition _exit : ident := $"exit".
Definition _fa : ident := $"fa".
Definition _fi : ident := $"fi".
Definition _fill_edge : ident := $"fill_edge".
Definition _find : ident := $"find".
Definition _first_available : ident := $"first_available".
Definition _forward : ident := $"forward".
Definition _forward_roots : ident := $"forward_roots".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _freeN : ident := $"freeN".
Definition _freePQ : ident := $"freePQ".
Definition _freeSet : ident := $"freeSet".
Definition _free_graph : ident := $"free_graph".
Definition _free_heap : ident := $"free_heap".
Definition _from : ident := $"from".
Definition _from_limit : ident := $"from_limit".
Definition _from_start : ident := $"from_start".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _getCell : ident := $"getCell".
Definition _graph : ident := $"graph".
Definition _graph_E : ident := $"graph_E".
Definition _graph_V : ident := $"graph_V".
Definition _graph__1 : ident := $"graph__1".
Definition _greater : ident := $"greater".
Definition _h : ident := $"h".
Definition _hd : ident := $"hd".
Definition _head : ident := $"head".
Definition _heap : ident := $"heap".
Definition _heap_cells : ident := $"heap_cells".
Definition _heapify : ident := $"heapify".
Definition _heapsort : ident := $"heapsort".
Definition _heapsort_rev : ident := $"heapsort_rev".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _inf : ident := $"inf".
Definition _init : ident := $"init".
Definition _init_empty_graph : ident := $"init_empty_graph".
Definition _initialise_list : ident := $"initialise_list".
Definition _initialise_matrix : ident := $"initialise_matrix".
Definition _insert : ident := $"insert".
Definition _insert_nc : ident := $"insert_nc".
Definition _int_or_ptr_to_int : ident := $"int_or_ptr_to_int".
Definition _int_or_ptr_to_ptr : ident := $"int_or_ptr_to_ptr".
Definition _int_to_int_or_ptr : ident := $"int_to_int_or_ptr".
Definition _item : ident := $"item".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _key : ident := $"key".
Definition _key1 : ident := $"key1".
Definition _key2 : ident := $"key2".
Definition _key_table : ident := $"key_table".
Definition _kruskal : ident := $"kruskal".
Definition _l : ident := $"l".
Definition _less : ident := $"less".
Definition _limit : ident := $"limit".
Definition _list : ident := $"list".
Definition _lo : ident := $"lo".
Definition _lookup : ident := $"lookup".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _make : ident := $"make".
Definition _makeSet : ident := $"makeSet".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _malloc : ident := $"malloc".
Definition _mallocK : ident := $"mallocK".
Definition _mallocN : ident := $"mallocN".
Definition _mark : ident := $"mark".
Definition _mst : ident := $"mst".
Definition _n : ident := $"n".
Definition _new : ident := $"new".
Definition _newpri : ident := $"newpri".
Definition _next : ident := $"next".
Definition _num_allocs : ident := $"num_allocs".
Definition _oldpri : ident := $"oldpri".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _p0 : ident := $"p0".
Definition _parent : ident := $"parent".
Definition _popMin : ident := $"popMin".
Definition _pq : ident := $"pq".
Definition _pq_edit_priority : ident := $"pq_edit_priority".
Definition _pq_emp : ident := $"pq_emp".
Definition _pq_free : ident := $"pq_free".
Definition _pq_insert : ident := $"pq_insert".
Definition _pq_insert_nc : ident := $"pq_insert_nc".
Definition _pq_make : ident := $"pq_make".
Definition _pq_remove_min : ident := $"pq_remove_min".
Definition _pq_remove_min_nc : ident := $"pq_remove_min_nc".
Definition _pq_size : ident := $"pq_size".
Definition _prim : ident := $"prim".
Definition _priority : ident := $"priority".
Definition _ptr_to_int_or_ptr : ident := $"ptr_to_int_or_ptr".
Definition _push : ident := $"push".
Definition _r : ident := $"r".
Definition _rank : ident := $"rank".
Definition _remove_min : ident := $"remove_min".
Definition _remove_min_nc : ident := $"remove_min_nc".
Definition _reset_heap : ident := $"reset_heap".
Definition _resume : ident := $"resume".
Definition _root_mark : ident := $"root_mark".
Definition _roots : ident := $"roots".
Definition _s : ident := $"s".
Definition _scan : ident := $"scan".
Definition _sink : ident := $"sink".
Definition _size : ident := $"size".
Definition _size__1 : ident := $"size__1".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _src : ident := $"src".
Definition _start : ident := $"start".
Definition _structItem : ident := $"structItem".
Definition _structPQ : ident := $"structPQ".
Definition _subset : ident := $"subset".
Definition _subsets : ident := $"subsets".
Definition _summatrix : ident := $"summatrix".
Definition _swim : ident := $"swim".
Definition _sz : ident := $"sz".
Definition _t : ident := $"t".
Definition _table : ident := $"table".
Definition _tag : ident := $"tag".
Definition _tail : ident := $"tail".
Definition _target : ident := $"target".
Definition _test_int_or_ptr : ident := $"test_int_or_ptr".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _tinfo : ident := $"tinfo".
Definition _tmp : ident := $"tmp".
Definition _to : ident := $"to".
Definition _twobytwo : ident := $"twobytwo".
Definition _u : ident := $"u".
Definition _ufind : ident := $"ufind".
Definition _unionS : ident := $"unionS".
Definition _v : ident := $"v".
Definition _v__1 : ident := $"v__1".
Definition _va : ident := $"va".
Definition _vfind : ident := $"vfind".
Definition _w : ident := $"w".
Definition _wedge : ident := $"wedge".
Definition _weight : ident := $"weight".
Definition _x : ident := $"x".
Definition _xRank : ident := $"xRank".
Definition _xRoot : ident := $"xRoot".
Definition _xroot : ident := $"xroot".
Definition _y : ident := $"y".
Definition _yRank : ident := $"yRank".
Definition _yRoot : ident := $"yRoot".
Definition _yroot : ident := $"yroot".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.

Definition f_check_symmetric_matrix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 8) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _j (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _i tint)
                             tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Ederef
                        (Ebinop Oadd (Etempvar _graph (tptr (tarray tint 8)))
                          (Etempvar _i tint) (tptr (tarray tint 8)))
                        (tarray tint 8)) (Etempvar _j tint) (tptr tint))
                    tint))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _graph (tptr (tarray tint 8)))
                            (Etempvar _j tint) (tptr (tarray tint 8)))
                          (tarray tint 8)) (Etempvar _i tint) (tptr tint))
                      tint))
                  (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                                 (Etempvar _t'2 tint) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_initialise_matrix := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: (_a, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 8) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _j (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                           (Econst_int (Int.repr 8) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Ederef
                    (Ebinop Oadd (Etempvar _graph (tptr (tarray tint 8)))
                      (Etempvar _i tint) (tptr (tarray tint 8)))
                    (tarray tint 8)) (Etempvar _j tint) (tptr tint)) tint)
              (Etempvar _a tint)))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
              tint)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_initialise_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_list, (tptr tint)) :: (_a, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 8) tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _list (tptr tint)) (Etempvar _i tint)
            (tptr tint)) tint) (Etempvar _a tint)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_getCell := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: (_u, tint) ::
                (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd
        (Ederef
          (Ebinop Oadd (Etempvar _graph (tptr (tarray tint 8)))
            (Etempvar _u tint) (tptr (tarray tint 8))) (tarray tint 8))
        (Etempvar _i tint) (tptr tint)) tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_prim := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: (_r, tint) ::
                (_parent, (tptr tint)) :: nil);
  fn_vars := ((_key, (tarray tint 8)) :: (_out, (tarray tint 8)) :: nil);
  fn_temps := ((_cost, tint) :: (_pq, (tptr tint)) :: (_v, tint) ::
               (_u, tint) :: (_v__1, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr tint)) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _initialise_list (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                             tvoid cc_default))
    ((Evar _key (tarray tint 8)) ::
     (Econst_int (Int.repr 2147483646) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _initialise_list (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                               tvoid cc_default))
      ((Etempvar _parent (tptr tint)) :: (Econst_int (Int.repr 8) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _initialise_list (Tfunction
                                 (Tcons (tptr tint) (Tcons tint Tnil)) tvoid
                                 cc_default))
        ((Evar _out (tarray tint 8)) :: (Econst_int (Int.repr 0) tint) ::
         nil))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _key (tarray tint 8)) (Etempvar _r tint)
              (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _init (Tfunction (Tcons tint Tnil) (tptr tint)
                            cc_default))
              ((Econst_int (Int.repr 8) tint) :: nil))
            (Sset _pq (Etempvar _t'1 (tptr tint))))
          (Ssequence
            (Ssequence
              (Sset _v (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _v tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'8
                      (Ederef
                        (Ebinop Oadd (Evar _key (tarray tint 8))
                          (Etempvar _v tint) (tptr tint)) tint))
                    (Scall None
                      (Evar _push (Tfunction
                                    (Tcons tint
                                      (Tcons tint (Tcons (tptr tint) Tnil)))
                                    tvoid cc_default))
                      ((Etempvar _v tint) :: (Etempvar _t'8 tint) ::
                       (Etempvar _pq (tptr tint)) :: nil))))
                (Sset _v
                  (Ebinop Oadd (Etempvar _v tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _pq_emp (Tfunction
                                      (Tcons tint
                                        (Tcons tint (Tcons (tptr tint) Tnil)))
                                      tint cc_default))
                      ((Econst_int (Int.repr 8) tint) ::
                       (Econst_int (Int.repr 2147483646) tint) ::
                       (Etempvar _pq (tptr tint)) :: nil))
                    (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _popMin (Tfunction
                                        (Tcons tint
                                          (Tcons tint
                                            (Tcons (tptr tint) Tnil))) tint
                                        cc_default))
                        ((Econst_int (Int.repr 8) tint) ::
                         (Econst_int (Int.repr 2147483646) tint) ::
                         (Etempvar _pq (tptr tint)) :: nil))
                      (Sset _u (Etempvar _t'3 tint)))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _out (tarray tint 8))
                            (Etempvar _u tint) (tptr tint)) tint)
                        (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _v__1 (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _v__1 tint)
                                           (Econst_int (Int.repr 8) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'5
                                (Ederef
                                  (Ebinop Oadd (Evar _out (tarray tint 8))
                                    (Etempvar _v__1 tint) (tptr tint)) tint))
                              (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'4)
                                      (Evar _getCell (Tfunction
                                                       (Tcons
                                                         (tptr (tarray tint 8))
                                                         (Tcons tint
                                                           (Tcons tint Tnil)))
                                                       tint cc_default))
                                      ((Etempvar _graph (tptr (tarray tint 8))) ::
                                       (Etempvar _u tint) ::
                                       (Etempvar _v__1 tint) :: nil))
                                    (Sset _cost (Etempvar _t'4 tint)))
                                  (Ssequence
                                    (Sset _t'6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _key (tarray tint 8))
                                          (Etempvar _v__1 tint) (tptr tint))
                                        tint))
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _cost tint)
                                                   (Etempvar _t'6 tint) tint)
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _parent (tptr tint))
                                              (Etempvar _v__1 tint)
                                              (tptr tint)) tint)
                                          (Etempvar _u tint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _key (tarray tint 8))
                                                (Etempvar _v__1 tint)
                                                (tptr tint)) tint)
                                            (Etempvar _cost tint))
                                          (Ssequence
                                            (Sset _t'7
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _key (tarray tint 8))
                                                  (Etempvar _v__1 tint)
                                                  (tptr tint)) tint))
                                            (Scall None
                                              (Evar _adjustWeight (Tfunction
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _v__1 tint) ::
                                               (Etempvar _t'7 tint) ::
                                               (Etempvar _pq (tptr tint)) ::
                                               nil)))))
                                      Sskip)))
                                Sskip)))
                          (Sset _v__1
                            (Ebinop Oadd (Etempvar _v__1 tint)
                              (Econst_int (Int.repr 1) tint) tint)))))))
                Sskip)
              (Ssequence
                (Scall None
                  (Evar _freePQ (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                  ((Etempvar _pq (tptr tint)) :: nil))
                (Sreturn None)))))))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_init,
   Gfun(External (EF_external "init"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tint Tnil) (tptr tint) cc_default)) ::
 (_push,
   Gfun(External (EF_external "push"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tvoid cc_default)) ::
 (_popMin,
   Gfun(External (EF_external "popMin"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tint cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tint cc_default)) ::
 (_adjustWeight,
   Gfun(External (EF_external "adjustWeight"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tvoid cc_default)) ::
 (_pq_emp,
   Gfun(External (EF_external "pq_emp"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tint cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tint cc_default)) ::
 (_freePQ,
   Gfun(External (EF_external "freePQ"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_check_symmetric_matrix, Gfun(Internal f_check_symmetric_matrix)) ::
 (_initialise_matrix, Gfun(Internal f_initialise_matrix)) ::
 (_initialise_list, Gfun(Internal f_initialise_list)) ::
 (_getCell, Gfun(Internal f_getCell)) :: (_prim, Gfun(Internal f_prim)) ::
 nil).

Definition public_idents : list ident :=
(_prim :: _getCell :: _initialise_list :: _initialise_matrix ::
 _check_symmetric_matrix :: _freePQ :: _pq_emp :: _adjustWeight :: _popMin ::
 _push :: _init :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


