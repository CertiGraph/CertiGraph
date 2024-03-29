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
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "CertiGC/gc.c".
  Definition normalized := true.
End Info.

Definition _Is_block : ident := $"Is_block".
Definition _Is_from : ident := $"Is_from".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
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
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
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
Definition ___sFILE : ident := $"__sFILE".
Definition ___sFILEX : ident := $"__sFILEX".
Definition ___sbuf : ident := $"__sbuf".
Definition ___stderrp : ident := $"__stderrp".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_11 : ident := $"__stringlit_11".
Definition ___stringlit_12 : ident := $"__stringlit_12".
Definition ___stringlit_13 : ident := $"__stringlit_13".
Definition ___stringlit_14 : ident := $"__stringlit_14".
Definition ___stringlit_15 : ident := $"__stringlit_15".
Definition ___stringlit_16 : ident := $"__stringlit_16".
Definition ___stringlit_17 : ident := $"__stringlit_17".
Definition ___stringlit_18 : ident := $"__stringlit_18".
Definition ___stringlit_19 : ident := $"__stringlit_19".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_20 : ident := $"__stringlit_20".
Definition ___stringlit_21 : ident := $"__stringlit_21".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __extra : ident := $"_extra".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __nbuf : ident := $"_nbuf".
Definition __offset : ident := $"_offset".
Definition __p : ident := $"_p".
Definition __r : ident := $"_r".
Definition __read : ident := $"_read".
Definition __seek : ident := $"_seek".
Definition __size : ident := $"_size".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __write : ident := $"_write".
Definition _abort : ident := $"abort".
Definition _abort_with : ident := $"abort_with".
Definition _alloc : ident := $"alloc".
Definition _allocated : ident := $"allocated".
Definition _args : ident := $"args".
Definition _certicoq_modify : ident := $"certicoq_modify".
Definition _create_heap : ident := $"create_heap".
Definition _create_space : ident := $"create_space".
Definition _curr : ident := $"curr".
Definition _depth : ident := $"depth".
Definition _do_generation : ident := $"do_generation".
Definition _do_scan : ident := $"do_scan".
Definition _exit : ident := $"exit".
Definition _export : ident := $"export".
Definition _fake_sp : ident := $"fake_sp".
Definition _forward : ident := $"forward".
Definition _forward_remset : ident := $"forward_remset".
Definition _forward_roots : ident := $"forward_roots".
Definition _fp : ident := $"fp".
Definition _fprintf : ident := $"fprintf".
Definition _frame : ident := $"frame".
Definition _free : ident := $"free".
Definition _free_heap : ident := $"free_heap".
Definition _from : ident := $"from".
Definition _from_limit : ident := $"from_limit".
Definition _from_rem_limit : ident := $"from_rem_limit".
Definition _from_start : ident := $"from_start".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _garbage_collect_all : ident := $"garbage_collect_all".
Definition _gen_level : ident := $"gen_level".
Definition _h : ident := $"h".
Definition _hd : ident := $"hd".
Definition _heap : ident := $"heap".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _int_or_ptr_to_int : ident := $"int_or_ptr_to_int".
Definition _int_or_ptr_to_ptr : ident := $"int_or_ptr_to_ptr".
Definition _int_to_int_or_ptr : ident := $"int_to_int_or_ptr".
Definition _j : ident := $"j".
Definition _limit : ident := $"limit".
Definition _lo : ident := $"lo".
Definition _main : ident := $"main".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _nalloc : ident := $"nalloc".
Definition _new : ident := $"new".
Definition _newp : ident := $"newp".
Definition _next : ident := $"next".
Definition _num_allocs : ident := $"num_allocs".
Definition _odata : ident := $"odata".
Definition _oldp : ident := $"oldp".
Definition _p : ident := $"p".
Definition _p_cell : ident := $"p_cell".
Definition _p_val : ident := $"p_val".
Definition _prev : ident := $"prev".
Definition _print_heapsize : ident := $"print_heapsize".
Definition _printf : ident := $"printf".
Definition _ptr_to_int_or_ptr : ident := $"ptr_to_int_or_ptr".
Definition _q : ident := $"q".
Definition _rem_limit : ident := $"rem_limit".
Definition _remembered : ident := $"remembered".
Definition _reset_heap : ident := $"reset_heap".
Definition _result_block : ident := $"result_block".
Definition _resume : ident := $"resume".
Definition _root : ident := $"root".
Definition _roots : ident := $"roots".
Definition _s : ident := $"s".
Definition _scan : ident := $"scan".
Definition _sp : ident := $"sp".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _stack_frame : ident := $"stack_frame".
Definition _start : ident := $"start".
Definition _sz : ident := $"sz".
Definition _tag : ident := $"tag".
Definition _test_int_or_ptr : ident := $"test_int_or_ptr".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _tinfo : ident := $"tinfo".
Definition _to : ident := $"to".
Definition _v : ident := $"v".
Definition _value_sp : ident := $"value_sp".
Definition _w : ident := $"w".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 48);
  gvar_init := (Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 75);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 43) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := (tarray tschar 12);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 49);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stderrp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_test_int_or_ptr := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand
                   (Ecast (Etempvar _x (talignas 3%N (tptr tvoid))) tlong)
                   (Econst_int (Int.repr 1) tint) tlong) tint)))
|}.

Definition f_int_or_ptr_to_int := {|
  fn_return := tlong;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 3%N (tptr tvoid))) tlong)))
|}.

Definition f_int_or_ptr_to_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 3%N (tptr tvoid))) (tptr tvoid))))
|}.

Definition f_int_to_int_or_ptr := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, tlong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x tlong) (talignas 3%N (tptr tvoid)))))
|}.

Definition f_ptr_to_int_or_ptr := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) (talignas 3%N (tptr tvoid)))))
|}.

Definition f_Is_block := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _test_int_or_ptr (Tfunction
                             (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint
                             cc_default))
    ((Etempvar _x (talignas 3%N (tptr tvoid))) :: nil))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint))))
|}.

Definition f_abort_with := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct ___sFILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
       (Evar ___stringlit_1 (tarray tschar 3)) ::
       (Etempvar _s (tptr tschar)) :: nil)))
  (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
    ((Econst_int (Int.repr 1) tint) :: nil)))
|}.

Definition f_Is_from := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_v, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole
                 (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid))))
                 (Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Olt (Etempvar _v (tptr (talignas 3%N (tptr tvoid))))
          (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) tint)
        tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_forward := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                (_p, (tptr (talignas 3%N (tptr tvoid)))) :: (_depth, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_v, (talignas 3%N (tptr tvoid))) :: (_hd, tulong) ::
               (_i, tint) :: (_sz, tint) ::
               (_new, (tptr (talignas 3%N (tptr tvoid)))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _v
    (Ederef (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
      (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _Is_block (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                        tint cc_default))
      ((Etempvar _v (talignas 3%N (tptr tvoid))) :: nil))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _Is_from (Tfunction
                           (Tcons (tptr (talignas 3%N (tptr tvoid)))
                             (Tcons (tptr (talignas 3%N (tptr tvoid)))
                               (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                 Tnil))) tint cc_default))
          ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
           (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
           (Etempvar _v (talignas 3%N (tptr tvoid))) :: nil))
        (Sifthenelse (Etempvar _t'1 tint)
          (Ssequence
            (Sset _hd
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _v (talignas 3%N (tptr tvoid)))
                    (tptr tulong))
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                  (tptr tulong)) tulong))
            (Sifthenelse (Ebinop Oeq (Etempvar _hd tulong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _v (talignas 3%N (tptr tvoid)))
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (talignas 3%N (tptr tvoid))))
                    (talignas 3%N (tptr tvoid))))
                (Sassign
                  (Ederef (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                    (talignas 3%N (tptr tvoid)))
                  (Etempvar _t'5 (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Sset _sz
                  (Ecast
                    (Ecast
                      (Ebinop Oshr (Etempvar _hd tulong)
                        (Econst_int (Int.repr 10) tint) tulong) tulong) tint))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Sset _new
                      (Ebinop Oadd
                        (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                        (Econst_int (Int.repr 1) tint)
                        (tptr (talignas 3%N (tptr tvoid))))))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Ebinop Oadd
                        (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
                        (Etempvar _sz tint)
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Ssequence
                      (Sifthenelse (Ebinop Ogt (Etempvar _sz tint)
                                     (Econst_int (Int.repr 50) tint) tint)
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint
                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_2 (tarray tschar 45)) ::
                           (Ecast (Etempvar _v (talignas 3%N (tptr tvoid)))
                             (tptr tvoid)) :: (Etempvar _hd tulong) ::
                           (Etempvar _sz tint) :: nil))
                        Sskip)
                      (Ssequence
                        (Ssequence
                          (Sset _i
                            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                             (Etempvar _sz tint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _t'3
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ecast
                                        (Etempvar _v (talignas 3%N (tptr tvoid)))
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Etempvar _i tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid))))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ecast
                                        (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Etempvar _i tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))
                                  (Etempvar _t'3 (talignas 3%N (tptr tvoid))))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Ecast
                                  (Etempvar _v (talignas 3%N (tptr tvoid)))
                                  (tptr tulong))
                                (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                  tint) (tptr tulong)) tulong)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Ecast
                                    (Etempvar _v (talignas 3%N (tptr tvoid)))
                                    (tptr (talignas 3%N (tptr tvoid))))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))
                              (Ecast
                                (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid))))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid)))
                                (Ecast
                                  (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid))))
                              (Sifthenelse (Ebinop Ogt (Etempvar _depth tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _i (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tint)
                                                     (Etempvar _sz tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Scall None
                                        (Evar _forward (Tfunction
                                                         (Tcons
                                                           (tptr (talignas 3%N (tptr tvoid)))
                                                           (Tcons
                                                             (tptr (talignas 3%N (tptr tvoid)))
                                                             (Tcons
                                                               (tptr (tptr (talignas 3%N (tptr tvoid))))
                                                               (Tcons
                                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                                 (Tcons tint
                                                                   Tnil)))))
                                                         tvoid cc_default))
                                        ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
                                         (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
                                         (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                                         (Ebinop Oadd
                                           (Ecast
                                             (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
                                             (tptr (talignas 3%N (tptr tvoid))))
                                           (Etempvar _i tint)
                                           (tptr (talignas 3%N (tptr tvoid)))) ::
                                         (Ebinop Osub (Etempvar _depth tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) :: nil)))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint))))
                                Sskip)))))))))))
          Sskip))
      Sskip)))
|}.

Definition f_forward_remset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil);
  fn_vars := nil;
  fn_temps := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_from_rem_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_q, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_oldp, (talignas 3%N (tptr tvoid))) ::
               (_newp, (talignas 3%N (tptr tvoid))) :: (_t'2, tint) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _from_start
    (Efield
      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _start (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sset _from_limit
      (Efield
        (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
          (Tstruct _space noattr)) _limit (tptr (talignas 3%N (tptr tvoid)))))
    (Ssequence
      (Sset _from_rem_limit
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _rem_limit
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _q (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _start
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sifthenelse (Ebinop Ole
                             (Ebinop Osub
                               (Etempvar _from_rem_limit (tptr (talignas 3%N (tptr tvoid))))
                               (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid))))
                               tlong)
                             (Ebinop Osub
                               (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                               (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                               tlong) tint)
                Sskip
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_5 (tarray tschar 30)) ::
                     (Evar ___stringlit_4 (tarray tschar 5)) ::
                     (Econst_int (Int.repr 214) tint) ::
                     (Evar ___stringlit_3 (tarray tschar 49)) :: nil))
                  (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default))
                    nil)))))
          (Swhile
            (Ebinop One (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _from_rem_limit (tptr (talignas 3%N (tptr tvoid))))
              tint)
            (Ssequence
              (Sset _p
                (Ederef
                  (Ecast (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                    (tptr (tptr (talignas 3%N (tptr tvoid)))))
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Ole
                                 (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid))))
                                 (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                                 tint)
                    (Sset _t'2
                      (Ecast
                        (Ebinop Olt
                          (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                          (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid))))
                          tint) tbool))
                    (Sset _t'2 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                    (Ssequence
                      (Sset _oldp
                        (Ederef
                          (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                          (talignas 3%N (tptr tvoid))))
                      (Ssequence
                        (Scall None
                          (Evar _forward (Tfunction
                                           (Tcons
                                             (tptr (talignas 3%N (tptr tvoid)))
                                             (Tcons
                                               (tptr (talignas 3%N (tptr tvoid)))
                                               (Tcons
                                                 (tptr (tptr (talignas 3%N (tptr tvoid))))
                                                 (Tcons
                                                   (tptr (talignas 3%N (tptr tvoid)))
                                                   (Tcons tint Tnil)))))
                                           tvoid cc_default))
                          ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
                           (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
                           (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                           (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))) ::
                           (Econst_int (Int.repr 0) tint) :: nil))
                        (Ssequence
                          (Sset _newp
                            (Ederef
                              (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                              (talignas 3%N (tptr tvoid))))
                          (Sifthenelse (Ebinop One
                                         (Etempvar _oldp (talignas 3%N (tptr tvoid)))
                                         (Etempvar _newp (talignas 3%N (tptr tvoid)))
                                         tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'3
                                    (Efield
                                      (Ederef
                                        (Etempvar _to (tptr (Tstruct _space noattr)))
                                        (Tstruct _space noattr)) _limit
                                      (tptr (talignas 3%N (tptr tvoid)))))
                                  (Sset _t'1
                                    (Ecast
                                      (Ebinop Osub
                                        (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (tptr (talignas 3%N (tptr tvoid))))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _to (tptr (Tstruct _space noattr)))
                                      (Tstruct _space noattr)) _limit
                                    (tptr (talignas 3%N (tptr tvoid))))
                                  (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))
                              (Sassign
                                (Ederef
                                  (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid)))
                                (Ecast
                                  (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid)))))
                            Sskip))))
                    Sskip))
                (Sset _q
                  (Ebinop Oadd
                    (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                    (Econst_int (Int.repr 1) tint)
                    (tptr (talignas 3%N (tptr tvoid)))))))))))))
|}.

Definition f_forward_roots := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_frame, (tptr (Tstruct _stack_frame noattr))) ::
               (_curr, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_limit, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _frame
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _fp
      (tptr (Tstruct _stack_frame noattr))))
  (Swhile
    (Ebinop One (Etempvar _frame (tptr (Tstruct _stack_frame noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sset _curr
        (Efield
          (Ederef (Etempvar _frame (tptr (Tstruct _stack_frame noattr)))
            (Tstruct _stack_frame noattr)) _root
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _limit
          (Efield
            (Ederef (Etempvar _frame (tptr (Tstruct _stack_frame noattr)))
              (Tstruct _stack_frame noattr)) _next
            (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Ssequence
            (Sset _curr
              (Efield
                (Ederef
                  (Etempvar _frame (tptr (Tstruct _stack_frame noattr)))
                  (Tstruct _stack_frame noattr)) _root
                (tptr (talignas 3%N (tptr tvoid)))))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt
                               (Etempvar _curr (tptr (talignas 3%N (tptr tvoid))))
                               (Etempvar _limit (tptr (talignas 3%N (tptr tvoid))))
                               tint)
                  Sskip
                  Sbreak)
                (Scall None
                  (Evar _forward (Tfunction
                                   (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 3%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 3%N (tptr tvoid))))
                                         (Tcons
                                           (tptr (talignas 3%N (tptr tvoid)))
                                           (Tcons tint Tnil))))) tvoid
                                   cc_default))
                  ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
                   (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
                   (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                   (Etempvar _curr (tptr (talignas 3%N (tptr tvoid)))) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Sset _curr
                (Ebinop Oadd
                  (Etempvar _curr (tptr (talignas 3%N (tptr tvoid))))
                  (Econst_int (Int.repr 1) tint)
                  (tptr (talignas 3%N (tptr tvoid)))))))
          (Sset _frame
            (Efield
              (Ederef (Etempvar _frame (tptr (Tstruct _stack_frame noattr)))
                (Tstruct _stack_frame noattr)) _prev
              (tptr (Tstruct _stack_frame noattr)))))))))
|}.

Definition f_do_scan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_scan, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr (talignas 3%N (tptr tvoid)))) :: (_hd, tulong) ::
               (_sz, tulong) :: (_tag, tint) :: (_j, tlong) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Etempvar _scan (tptr (talignas 3%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Ederef (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
            (tptr (talignas 3%N (tptr tvoid)))))
        (Sifthenelse (Ebinop Olt
                       (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
                       (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ederef (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
              (talignas 3%N (tptr tvoid))))
          (Sset _hd
            (Ecast (Etempvar _t'1 (talignas 3%N (tptr tvoid))) tulong)))
        (Ssequence
          (Sset _sz
            (Ecast
              (Ebinop Oshr (Etempvar _hd tulong)
                (Econst_int (Int.repr 10) tint) tulong) tulong))
          (Ssequence
            (Sset _tag
              (Ecast
                (Ebinop Oand (Etempvar _hd tulong)
                  (Econst_int (Int.repr 255) tint) tulong) tuint))
            (Ssequence
              (Sifthenelse (Eunop Onotbool
                             (Ebinop Oge (Etempvar _tag tint)
                               (Econst_int (Int.repr 251) tint) tint) tint)
                (Ssequence
                  (Sset _j (Ecast (Econst_int (Int.repr 1) tint) tlong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _j tlong)
                                     (Etempvar _sz tulong) tint)
                        Sskip
                        Sbreak)
                      (Scall None
                        (Evar _forward (Tfunction
                                         (Tcons
                                           (tptr (talignas 3%N (tptr tvoid)))
                                           (Tcons
                                             (tptr (talignas 3%N (tptr tvoid)))
                                             (Tcons
                                               (tptr (tptr (talignas 3%N (tptr tvoid))))
                                               (Tcons
                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                 (Tcons tint Tnil))))) tvoid
                                         cc_default))
                        ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
                         (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
                         (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                         (Ebinop Oadd
                           (Ecast
                             (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
                             (tptr (talignas 3%N (tptr tvoid))))
                           (Etempvar _j tlong)
                           (tptr (talignas 3%N (tptr tvoid)))) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tlong)
                        (Econst_int (Int.repr 1) tint) tlong))))
                Sskip)
              (Sset _s
                (Ebinop Oadd (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
                  (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                    (Etempvar _sz tulong) tulong)
                  (tptr (talignas 3%N (tptr tvoid))))))))))
    Sskip))
|}.

Definition f_do_generation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'12, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'11, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'10, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'9, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _next (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _next
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _rem_limit
              (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _next
                    (tptr (talignas 3%N (tptr tvoid)))))
                (Sifthenelse (Ebinop Ole
                               (Ebinop Osub
                                 (Ebinop Oadd
                                   (Ebinop Osub
                                     (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                                     (Etempvar _t'8 (tptr (talignas 3%N (tptr tvoid))))
                                     tlong)
                                   (Etempvar _t'9 (tptr (talignas 3%N (tptr tvoid))))
                                   (tptr (talignas 3%N (tptr tvoid))))
                                 (Etempvar _t'10 (tptr (talignas 3%N (tptr tvoid))))
                                 tlong)
                               (Ebinop Osub
                                 (Etempvar _t'11 (tptr (talignas 3%N (tptr tvoid))))
                                 (Etempvar _t'12 (tptr (talignas 3%N (tptr tvoid))))
                                 tlong) tint)
                  Sskip
                  (Ssequence
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                      ((Evar ___stringlit_5 (tarray tschar 30)) ::
                       (Evar ___stringlit_4 (tarray tschar 5)) ::
                       (Econst_int (Int.repr 281) tint) ::
                       (Evar ___stringlit_6 (tarray tschar 75)) :: nil))
                    (Scall None
                      (Evar _abort (Tfunction Tnil tvoid cc_default)) nil)))))))))
    (Ssequence
      (Scall None
        (Evar _forward_remset (Tfunction
                                (Tcons (tptr (Tstruct _space noattr))
                                  (Tcons (tptr (Tstruct _space noattr))
                                    (Tcons
                                      (tptr (tptr (talignas 3%N (tptr tvoid))))
                                      Tnil))) tvoid cc_default))
        ((Etempvar _from (tptr (Tstruct _space noattr))) ::
         (Etempvar _to (tptr (Tstruct _space noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
               (Tstruct _space noattr)) _next
             (tptr (talignas 3%N (tptr tvoid))))
           (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _start
              (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid)))))
            (Scall None
              (Evar _forward_roots (Tfunction
                                     (Tcons
                                       (tptr (talignas 3%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (talignas 3%N (tptr tvoid)))
                                         (Tcons
                                           (tptr (tptr (talignas 3%N (tptr tvoid))))
                                           (Tcons
                                             (tptr (Tstruct _thread_info noattr))
                                             Tnil)))) tvoid cc_default))
              ((Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid)))) ::
               (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid)))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                     (Tstruct _space noattr)) _next
                   (tptr (talignas 3%N (tptr tvoid))))
                 (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
               (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _start
                (tptr (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Scall None
                (Evar _do_scan (Tfunction
                                 (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                   (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 3%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 3%N (tptr tvoid))))
                                         Tnil)))) tvoid cc_default))
                ((Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid)))) ::
                 (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid)))) ::
                 (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))) ::
                 (Eaddrof
                   (Efield
                     (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                       (Tstruct _space noattr)) _next
                     (tptr (talignas 3%N (tptr tvoid))))
                   (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _start
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _next
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))))
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _rem_limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))))))))
|}.

Definition f_create_space := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _space noattr))) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _n tulong)
         (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (talignas 3%N (tptr tvoid))))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                            cc_default))
        ((Evar ___stringlit_7 (tarray tschar 38)) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _start
          (tptr (talignas 3%N (tptr tvoid))))
        (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _next
            (tptr (talignas 3%N (tptr tvoid))))
          (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 3%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _n tulong) (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _rem_limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_create_heap := {|
  fn_return := (tptr (Tstruct _heap noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_h, (tptr (Tstruct _heap noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _heap noattr) tulong) :: nil))
    (Sset _h
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                            cc_default))
        ((Evar ___stringlit_8 (tarray tschar 27)) :: nil))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _create_space (Tfunction
                              (Tcons (tptr (Tstruct _space noattr))
                                (Tcons tulong Tnil)) tvoid cc_default))
        ((Ebinop Oadd
           (Efield
             (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
               (Tstruct _heap noattr)) _spaces
             (tarray (Tstruct _space noattr) 45))
           (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr))) ::
         (Ebinop Oshl (Econst_int (Int.repr 1) tint)
           (Econst_int (Int.repr 16) tint) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 1) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Ebinop Osub
                               (Ebinop Omul (Econst_int (Int.repr 8) tint)
                                 (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                                 tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                                 (Econst_int (Int.repr 16) tint) tint)
                               tulong) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                            (Tstruct _heap noattr)) _spaces
                          (tarray (Tstruct _space noattr) 45))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 3%N (tptr tvoid))))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 45))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _next
                      (tptr (talignas 3%N (tptr tvoid))))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 45))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 45))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _rem_limit
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _h (tptr (Tstruct _heap noattr)))))))))
|}.

Definition f_make_tinfo := {|
  fn_return := (tptr (Tstruct _thread_info noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_tinfo, (tptr (Tstruct _thread_info noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _heap noattr))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _create_heap (Tfunction Tnil (tptr (Tstruct _heap noattr))
                           cc_default)) nil)
    (Sset _h (Etempvar _t'1 (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _thread_info noattr) tulong) :: nil))
      (Sset _tinfo
        (Ecast (Etempvar _t'2 (tptr tvoid))
          (tptr (Tstruct _thread_info noattr)))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                     tint)
        (Scall None
          (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                              cc_default))
          ((Evar ___stringlit_9 (tarray tschar 39)) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _heap
            (tptr (Tstruct _heap noattr)))
          (Etempvar _h (tptr (Tstruct _heap noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                        (Tstruct _heap noattr)) _spaces
                      (tarray (Tstruct _space noattr) 45))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _start (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 45))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _fp
                  (tptr (Tstruct _stack_frame noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _nalloc tulong)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                        (Tstruct _thread_info noattr)) _odata (tptr tvoid))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Sreturn (Some (Etempvar _tinfo (tptr (Tstruct _thread_info noattr))))))))))))))
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_lo, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_hi, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_num_allocs, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sset _num_allocs
      (Efield
        (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
          (Tstruct _thread_info noattr)) _nalloc tulong))
    (Ssequence
      (Sifthenelse (Etempvar _h (tptr (Tstruct _heap noattr)))
        Sskip
        (Ssequence
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_5 (tarray tschar 30)) ::
             (Evar ___stringlit_4 (tarray tschar 5)) ::
             (Econst_int (Int.repr 377) tint) ::
             (Evar ___stringlit_10 (tarray tschar 2)) :: nil))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil)))
      (Ssequence
        (Sset _lo
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                    (Tstruct _heap noattr)) _spaces
                  (tarray (Tstruct _space noattr) 45))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
            _start (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sset _hi
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 45))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Osub
                             (Etempvar _hi (tptr (talignas 3%N (tptr tvoid))))
                             (Etempvar _lo (tptr (talignas 3%N (tptr tvoid))))
                             tlong) (Etempvar _num_allocs tulong) tint)
              (Scall None
                (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                                    cc_default))
                ((Evar ___stringlit_11 (tarray tschar 48)) :: nil))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _lo (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _hi (tptr (talignas 3%N (tptr tvoid))))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_w, tint) :: (_t'1, (tptr (Tstruct _heap noattr))) ::
               (_t'10, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'9, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _create_heap (Tfunction Tnil (tptr (Tstruct _heap noattr))
                                 cc_default)) nil)
          (Sset _h (Etempvar _t'1 (tptr (Tstruct _heap noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _heap
              (tptr (Tstruct _heap noattr)))
            (Etempvar _h (tptr (Tstruct _heap noattr))))
          (Ssequence
            (Scall None
              (Evar _resume (Tfunction
                              (Tcons (tptr (Tstruct _thread_info noattr))
                                Tnil) tvoid cc_default))
              ((Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))
            (Sreturn None))))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _limit
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 45))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _t'10 (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                        (Tstruct _heap noattr)) _spaces
                      (tarray (Tstruct _space noattr) 45))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _next (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'9 (tptr (talignas 3%N (tptr tvoid))))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Ebinop Osub
                                   (Ebinop Osub
                                     (Ebinop Omul
                                       (Econst_int (Int.repr 8) tint)
                                       (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                                       tulong)
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 3) tint)
                                       (Econst_int (Int.repr 16) tint) tint)
                                     tulong) (Econst_int (Int.repr 1) tint)
                                   tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 45))
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _start
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid))))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _h (tptr (Tstruct _heap noattr)))
                                        (Tstruct _heap noattr)) _spaces
                                      (tarray (Tstruct _space noattr) 45))
                                    (Etempvar _i tint)
                                    (tptr (Tstruct _space noattr)))
                                  (Tstruct _space noattr)) _rem_limit
                                (tptr (talignas 3%N (tptr tvoid)))))
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _heap noattr)))
                                          (Tstruct _heap noattr)) _spaces
                                        (tarray (Tstruct _space noattr) 45))
                                      (Etempvar _i tint)
                                      (tptr (Tstruct _space noattr)))
                                    (Tstruct _space noattr)) _start
                                  (tptr (talignas 3%N (tptr tvoid)))))
                              (Sset _w
                                (Ecast
                                  (Ebinop Osub
                                    (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                                    (Etempvar _t'8 (tptr (talignas 3%N (tptr tvoid))))
                                    tlong) tint))))
                          (Scall None
                            (Evar _create_space (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _space noattr))
                                                    (Tcons tulong Tnil))
                                                  tvoid cc_default))
                            ((Ebinop Oadd
                               (Efield
                                 (Ederef
                                   (Etempvar _h (tptr (Tstruct _heap noattr)))
                                   (Tstruct _heap noattr)) _spaces
                                 (tarray (Tstruct _space noattr) 45))
                               (Ebinop Oadd (Etempvar _i tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                               (tptr (Tstruct _space noattr))) ::
                             (Ebinop Omul (Econst_int (Int.repr 2) tint)
                               (Etempvar _w tint) tint) :: nil)))
                        Sskip))
                    (Ssequence
                      (Scall None
                        (Evar _do_generation (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _space noattr))
                                                 (Tcons
                                                   (tptr (Tstruct _space noattr))
                                                   (Tcons
                                                     (tptr (Tstruct _thread_info noattr))
                                                     Tnil))) tvoid
                                               cc_default))
                        ((Ebinop Oadd
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _heap noattr)))
                               (Tstruct _heap noattr)) _spaces
                             (tarray (Tstruct _space noattr) 45))
                           (Etempvar _i tint) (tptr (Tstruct _space noattr))) ::
                         (Ebinop Oadd
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _heap noattr)))
                               (Tstruct _heap noattr)) _spaces
                             (tarray (Tstruct _space noattr) 45))
                           (Ebinop Oadd (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint)
                           (tptr (Tstruct _space noattr))) ::
                         (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                         nil))
                      (Ssequence
                        (Sset _t'2
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _h (tptr (Tstruct _heap noattr)))
                                    (Tstruct _heap noattr)) _spaces
                                  (tarray (Tstruct _space noattr) 45))
                                (Etempvar _i tint)
                                (tptr (Tstruct _space noattr)))
                              (Tstruct _space noattr)) _rem_limit
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Ssequence
                          (Sset _t'3
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _heap noattr)))
                                      (Tstruct _heap noattr)) _spaces
                                    (tarray (Tstruct _space noattr) 45))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _space noattr)))
                                (Tstruct _space noattr)) _start
                              (tptr (talignas 3%N (tptr tvoid)))))
                          (Ssequence
                            (Sset _t'4
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _h (tptr (Tstruct _heap noattr)))
                                        (Tstruct _heap noattr)) _spaces
                                      (tarray (Tstruct _space noattr) 45))
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr (Tstruct _space noattr)))
                                  (Tstruct _space noattr)) _limit
                                (tptr (talignas 3%N (tptr tvoid)))))
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _heap noattr)))
                                          (Tstruct _heap noattr)) _spaces
                                        (tarray (Tstruct _space noattr) 45))
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr (Tstruct _space noattr)))
                                    (Tstruct _space noattr)) _next
                                  (tptr (talignas 3%N (tptr tvoid)))))
                              (Sifthenelse (Ebinop Ole
                                             (Ebinop Osub
                                               (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                                               (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                                               tlong)
                                             (Ebinop Osub
                                               (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                                               (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                                               tlong) tint)
                                (Ssequence
                                  (Scall None
                                    (Evar _resume (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _thread_info noattr))
                                                      Tnil) tvoid cc_default))
                                    ((Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                                     nil))
                                  (Sreturn None))
                                Sskip))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Osub
                               (Ebinop Omul (Econst_int (Int.repr 8) tint)
                                 (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                                 tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                                 (Econst_int (Int.repr 16) tint) tint)
                               tulong) (Etempvar _i tint) tint)
                Sskip
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_5 (tarray tschar 30)) ::
                     (Evar ___stringlit_4 (tarray tschar 5)) ::
                     (Econst_int (Int.repr 432) tint) ::
                     (Evar ___stringlit_12 (tarray tschar 16)) :: nil))
                  (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default))
                    nil)))
              (Scall None
                (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                                    cc_default))
                ((Evar ___stringlit_13 (tarray tschar 24)) :: nil)))))))
    (Ssequence
      (Scall None
        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
        ((Evar ___stringlit_5 (tarray tschar 30)) ::
         (Evar ___stringlit_4 (tarray tschar 5)) ::
         (Econst_int (Int.repr 436) tint) ::
         (Evar ___stringlit_14 (tarray tschar 2)) :: nil))
      (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, (tptr (Tstruct ___sFILE noattr))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct ___sFILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'2 (tptr (Tstruct ___sFILE noattr))) ::
       (Evar ___stringlit_15 (tarray tschar 22)) :: nil)))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Ebinop Osub
                         (Ebinop Omul (Econst_int (Int.repr 8) tint)
                           (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                           tulong)
                         (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                           (Econst_int (Int.repr 16) tint) tint) tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 45)) (Etempvar _i tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 45)) (Etempvar _i tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct ___sFILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
       (Evar ___stringlit_16 (tarray tschar 21)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Ebinop Osub
                           (Ebinop Omul (Econst_int (Int.repr 8) tint)
                             (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                             tulong)
                           (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                             (Econst_int (Int.repr 16) tint) tint) tulong)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _p
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                        (Tstruct _heap noattr)) _spaces
                      (tarray (Tstruct _space noattr) 45)) (Etempvar _i tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _start (tptr (talignas 3%N (tptr tvoid)))))
            (Sifthenelse (Ebinop One
                           (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _p (tptr (talignas 3%N (tptr tvoid)))) :: nil))
              Sskip)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))))
|}.

Definition f_garbage_collect_all := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _heap noattr))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _create_heap (Tfunction Tnil (tptr (Tstruct _heap noattr))
                                 cc_default)) nil)
          (Sset _h (Etempvar _t'1 (tptr (Tstruct _heap noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _heap
            (tptr (Tstruct _heap noattr)))
          (Etempvar _h (tptr (Tstruct _heap noattr)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _limit
            (tptr (talignas 3%N (tptr tvoid)))))
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                    (Tstruct _heap noattr)) _spaces
                  (tarray (Tstruct _space noattr) 45))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
            _limit (tptr (talignas 3%N (tptr tvoid))))
          (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 45))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Ebinop Osub
                                   (Ebinop Osub
                                     (Ebinop Omul
                                       (Econst_int (Int.repr 8) tint)
                                       (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                                       tulong)
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 3) tint)
                                       (Econst_int (Int.repr 16) tint) tint)
                                     tulong) (Econst_int (Int.repr 1) tint)
                                   tulong) tint)
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 45))
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _start
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Sset _t'2
                        (Ecast
                          (Ebinop One
                            (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)) tint) tbool)))
                    (Sset _t'2 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
                (Scall None
                  (Evar _do_generation (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _space noattr))
                                           (Tcons
                                             (tptr (Tstruct _space noattr))
                                             (Tcons
                                               (tptr (Tstruct _thread_info noattr))
                                               Tnil))) tvoid cc_default))
                  ((Ebinop Oadd
                     (Efield
                       (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                         (Tstruct _heap noattr)) _spaces
                       (tarray (Tstruct _space noattr) 45))
                     (Etempvar _i tint) (tptr (Tstruct _space noattr))) ::
                   (Ebinop Oadd
                     (Efield
                       (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                         (Tstruct _heap noattr)) _spaces
                       (tarray (Tstruct _space noattr) 45))
                     (Ebinop Oadd (Etempvar _i tint)
                       (Econst_int (Int.repr 1) tint) tint)
                     (tptr (Tstruct _space noattr))) ::
                   (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                   nil)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Sreturn (Some (Etempvar _i tint))))))))
|}.

Definition f_export := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_root, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((_frame, (Tstruct _stack_frame noattr)) ::
              (_roots, (tarray (talignas 3%N (tptr tvoid)) 1)) :: nil);
  fn_temps := ((_gen_level, tint) :: (_sp, (tptr (Tstruct _space noattr))) ::
               (_fake_sp, (tptr (Tstruct _space noattr))) ::
               (_value_sp, (tptr (Tstruct _space noattr))) ::
               (_result_block, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'11, (tptr (Tstruct _heap noattr))) ::
               (_t'10, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'9, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Evar _roots (tarray (talignas 3%N (tptr tvoid)) 1))
        (Econst_int (Int.repr 0) tint) (tptr (talignas 3%N (tptr tvoid))))
      (talignas 3%N (tptr tvoid)))
    (Etempvar _root (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield (Evar _frame (Tstruct _stack_frame noattr)) _root
        (tptr (talignas 3%N (tptr tvoid))))
      (Evar _roots (tarray (talignas 3%N (tptr tvoid)) 1)))
    (Ssequence
      (Sassign
        (Efield (Evar _frame (Tstruct _stack_frame noattr)) _next
          (tptr (talignas 3%N (tptr tvoid))))
        (Ebinop Oadd (Evar _roots (tarray (talignas 3%N (tptr tvoid)) 1))
          (Econst_int (Int.repr 1) tint) (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sassign
          (Efield (Evar _frame (Tstruct _stack_frame noattr)) _prev
            (tptr (Tstruct _stack_frame noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _fp
              (tptr (Tstruct _stack_frame noattr)))
            (Eaddrof (Evar _frame (Tstruct _stack_frame noattr))
              (tptr (Tstruct _stack_frame noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _Is_block (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  tint cc_default))
                ((Etempvar _root (talignas 3%N (tptr tvoid))) :: nil))
              (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
                (Sreturn (Some (Ecast
                                 (Etempvar _root (talignas 3%N (tptr tvoid)))
                                 (tptr tvoid))))
                Sskip))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _garbage_collect_all (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _thread_info noattr))
                                                 Tnil) tint cc_default))
                  ((Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                   nil))
                (Sset _gen_level (Etempvar _t'2 tint)))
              (Ssequence
                (Ssequence
                  (Sset _t'11
                    (Efield
                      (Ederef
                        (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                        (Tstruct _thread_info noattr)) _heap
                      (tptr (Tstruct _heap noattr))))
                  (Sset _sp
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _t'11 (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 45))
                      (Etempvar _gen_level tint)
                      (tptr (Tstruct _space noattr)))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                      (tptr tvoid) cc_default))
                      ((Esizeof (Tstruct _space noattr) tulong) :: nil))
                    (Sset _fake_sp
                      (Ecast (Etempvar _t'3 (tptr tvoid))
                        (tptr (Tstruct _space noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Etempvar _sp (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _next
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Ssequence
                        (Sset _t'10
                          (Efield
                            (Ederef
                              (Etempvar _sp (tptr (Tstruct _space noattr)))
                              (Tstruct _space noattr)) _start
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Scall None
                          (Evar _create_space (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _space noattr))
                                                  (Tcons tulong Tnil)) tvoid
                                                cc_default))
                          ((Etempvar _fake_sp (tptr (Tstruct _space noattr))) ::
                           (Ebinop Osub
                             (Etempvar _t'9 (tptr (talignas 3%N (tptr tvoid))))
                             (Etempvar _t'10 (tptr (talignas 3%N (tptr tvoid))))
                             tlong) :: nil))))
                    (Ssequence
                      (Scall None
                        (Evar _do_generation (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _space noattr))
                                                 (Tcons
                                                   (tptr (Tstruct _space noattr))
                                                   (Tcons
                                                     (tptr (Tstruct _thread_info noattr))
                                                     Tnil))) tvoid
                                               cc_default))
                        ((Etempvar _sp (tptr (Tstruct _space noattr))) ::
                         (Etempvar _fake_sp (tptr (Tstruct _space noattr))) ::
                         (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                            (tptr tvoid) cc_default))
                            ((Esizeof (Tstruct _space noattr) tulong) :: nil))
                          (Sset _value_sp
                            (Ecast (Etempvar _t'4 (tptr tvoid))
                              (tptr (Tstruct _space noattr)))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _fake_sp (tptr (Tstruct _space noattr)))
                                  (Tstruct _space noattr)) _next
                                (tptr (talignas 3%N (tptr tvoid)))))
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Etempvar _fake_sp (tptr (Tstruct _space noattr)))
                                    (Tstruct _space noattr)) _start
                                  (tptr (talignas 3%N (tptr tvoid)))))
                              (Scall None
                                (Evar _create_space (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _space noattr))
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                                ((Etempvar _value_sp (tptr (Tstruct _space noattr))) ::
                                 (Ebinop Osub
                                   (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                                   (Etempvar _t'8 (tptr (talignas 3%N (tptr tvoid))))
                                   tlong) :: nil))))
                          (Ssequence
                            (Scall None
                              (Evar _do_generation (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _space noattr))
                                                       (Tcons
                                                         (tptr (Tstruct _space noattr))
                                                         (Tcons
                                                           (tptr (Tstruct _thread_info noattr))
                                                           Tnil))) tvoid
                                                     cc_default))
                              ((Etempvar _fake_sp (tptr (Tstruct _space noattr))) ::
                               (Etempvar _value_sp (tptr (Tstruct _space noattr))) ::
                               (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                               nil))
                            (Ssequence
                              (Ssequence
                                (Sset _t'6
                                  (Efield
                                    (Ederef
                                      (Etempvar _value_sp (tptr (Tstruct _space noattr)))
                                      (Tstruct _space noattr)) _start
                                    (tptr (talignas 3%N (tptr tvoid)))))
                                (Sset _result_block
                                  (Ecast
                                    (Ebinop Oadd
                                      (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid))))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (tptr tvoid))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5
                                    (Efield
                                      (Ederef
                                        (Etempvar _fake_sp (tptr (Tstruct _space noattr)))
                                        (Tstruct _space noattr)) _start
                                      (tptr (talignas 3%N (tptr tvoid)))))
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid)))) ::
                                     nil)))
                                (Ssequence
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _fake_sp (tptr (Tstruct _space noattr))) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _free (Tfunction
                                                    (Tcons (tptr tvoid) Tnil)
                                                    tvoid cc_default))
                                      ((Etempvar _value_sp (tptr (Tstruct _space noattr))) ::
                                       nil))
                                    (Sreturn (Some (Etempvar _result_block (tptr tvoid))))))))))))))))))))))
|}.

Definition f_certicoq_modify := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_p_cell, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_p_val, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
          (Tstruct _thread_info noattr)) _alloc
        (tptr (talignas 3%N (tptr tvoid)))))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit
          (tptr (talignas 3%N (tptr tvoid)))))
      (Sifthenelse (Ebinop Olt
                     (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                     (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid)))) tint)
        Sskip
        (Ssequence
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_5 (tarray tschar 30)) ::
             (Evar ___stringlit_4 (tarray tschar 5)) ::
             (Econst_int (Int.repr 524) tint) ::
             (Evar ___stringlit_17 (tarray tschar 22)) :: nil))
          (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil)))))
  (Ssequence
    (Sassign
      (Ederef (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid))))
        (talignas 3%N (tptr tvoid)))
      (Etempvar _p_val (talignas 3%N (tptr tvoid))))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Is_block (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                          tint cc_default))
        ((Etempvar _p_val (talignas 3%N (tptr tvoid))) :: nil))
      (Sifthenelse (Etempvar _t'2 tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sset _t'1
                (Ecast
                  (Ebinop Osub
                    (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                    (Econst_int (Int.repr 1) tint)
                    (tptr (talignas 3%N (tptr tvoid))))
                  (tptr (talignas 3%N (tptr tvoid))))))
            (Sassign
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))
          (Sassign
            (Ederef
              (Ecast (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                (tptr (tptr (talignas 3%N (tptr tvoid)))))
              (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid))))))
        Sskip))))
|}.

Definition f_print_heapsize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_allocated, tint) :: (_remembered, tint) ::
               (_t'1, tint) :: (_t'13, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'12, (tptr (Tstruct _heap noattr))) ::
               (_t'11, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'10, (tptr (Tstruct _heap noattr))) ::
               (_t'9, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'8, (tptr (Tstruct _heap noattr))) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (Tstruct _heap noattr))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (Tstruct _heap noattr))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (Tstruct _heap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Ebinop Osub
                       (Ebinop Omul (Econst_int (Int.repr 8) tint)
                         (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                       (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                         (Econst_int (Int.repr 16) tint) tint) tulong) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _heap
              (tptr (Tstruct _heap noattr))))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _t'10 (tptr (Tstruct _heap noattr)))
                        (Tstruct _heap noattr)) _spaces
                      (tarray (Tstruct _space noattr) 45)) (Etempvar _i tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _next (tptr (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _heap
                  (tptr (Tstruct _heap noattr))))
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _t'12 (tptr (Tstruct _heap noattr)))
                            (Tstruct _heap noattr)) _spaces
                          (tarray (Tstruct _space noattr) 45))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 3%N (tptr tvoid)))))
                (Sset _allocated
                  (Ecast
                    (Ebinop Osub
                      (Etempvar _t'11 (tptr (talignas 3%N (tptr tvoid))))
                      (Etempvar _t'13 (tptr (talignas 3%N (tptr tvoid))))
                      tlong) tint))))))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _heap
                (tptr (Tstruct _heap noattr))))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _t'6 (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 45))
                      (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _rem_limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _heap
                    (tptr (Tstruct _heap noattr))))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _t'8 (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 45))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit
                      (tptr (talignas 3%N (tptr tvoid)))))
                  (Sset _remembered
                    (Ecast
                      (Ebinop Osub
                        (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                        (Etempvar _t'9 (tptr (talignas 3%N (tptr tvoid))))
                        tlong) tint))))))
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _allocated tint)
                (Sset _t'1 (Econst_int (Int.repr 1) tint))
                (Sset _t'1 (Ecast (Etempvar _remembered tint) tbool)))
              (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
                Scontinue
                Sskip))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_18 (tarray tschar 16)) ::
                 (Etempvar _i tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                        (Tstruct _thread_info noattr)) _heap
                      (tptr (Tstruct _heap noattr))))
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _t'2 (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 45))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _rem_limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                            (Tstruct _thread_info noattr)) _heap
                          (tptr (Tstruct _heap noattr))))
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _t'4 (tptr (Tstruct _heap noattr)))
                                    (Tstruct _heap noattr)) _spaces
                                  (tarray (Tstruct _space noattr) 45))
                                (Etempvar _i tint)
                                (tptr (Tstruct _space noattr)))
                              (Tstruct _space noattr)) _start
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint
                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_19 (tarray tschar 12)) ::
                           (Ecast
                             (Ebinop Osub
                               (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                               (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                               tlong) tint) :: nil))))))
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_20 (tarray tschar 17)) ::
                     (Etempvar _allocated tint) :: nil))
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_21 (tarray tschar 18)) ::
                     (Etempvar _remembered tint) :: nil)))))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___sbuf Struct
   (Member_plain __base (tptr tuchar) :: Member_plain __size tint :: nil)
   noattr ::
 Composite ___sFILE Struct
   (Member_plain __p (tptr tuchar) :: Member_plain __r tint ::
    Member_plain __w tint :: Member_plain __flags tshort ::
    Member_plain __file tshort ::
    Member_plain __bf (Tstruct ___sbuf noattr) ::
    Member_plain __lbfsize tint :: Member_plain __cookie (tptr tvoid) ::
    Member_plain __close
      (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default)) ::
    Member_plain __read
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __seek
      (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))
              tlong cc_default)) ::
    Member_plain __write
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __ub (Tstruct ___sbuf noattr) ::
    Member_plain __extra (tptr (Tstruct ___sFILEX noattr)) ::
    Member_plain __ur tint :: Member_plain __ubuf (tarray tuchar 3) ::
    Member_plain __nbuf (tarray tuchar 1) ::
    Member_plain __lb (Tstruct ___sbuf noattr) ::
    Member_plain __blksize tint :: Member_plain __offset tlong :: nil)
   noattr ::
 Composite _stack_frame Struct
   (Member_plain _next (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _root (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _prev (tptr (Tstruct _stack_frame noattr)) :: nil)
   noattr ::
 Composite _thread_info Struct
   (Member_plain _alloc (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _limit (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _heap (tptr (Tstruct _heap noattr)) ::
    Member_plain _args (tarray (talignas 3%N (tptr tvoid)) 1024) ::
    Member_plain _fp (tptr (Tstruct _stack_frame noattr)) ::
    Member_plain _nalloc tulong :: Member_plain _odata (tptr tvoid) :: nil)
   noattr ::
 Composite _space Struct
   (Member_plain _start (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _next (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _limit (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _rem_limit (tptr (talignas 3%N (tptr tvoid))) :: nil)
   noattr ::
 Composite _heap Struct
   (Member_plain _spaces (tarray (Tstruct _space noattr) 45) :: nil)
   noattr :: nil).

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
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
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
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
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
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (___stderrp, Gvar v___stderrp) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE noattr)) (Tcons (tptr tschar) Tnil)) tint
     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil AST.Tvoid cc_default))
     Tnil tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_test_int_or_ptr, Gfun(Internal f_test_int_or_ptr)) ::
 (_int_or_ptr_to_int, Gfun(Internal f_int_or_ptr_to_int)) ::
 (_int_or_ptr_to_ptr, Gfun(Internal f_int_or_ptr_to_ptr)) ::
 (_int_to_int_or_ptr, Gfun(Internal f_int_to_int_or_ptr)) ::
 (_ptr_to_int_or_ptr, Gfun(Internal f_ptr_to_int_or_ptr)) ::
 (_Is_block, Gfun(Internal f_Is_block)) ::
 (_abort_with, Gfun(Internal f_abort_with)) ::
 (_Is_from, Gfun(Internal f_Is_from)) ::
 (_forward, Gfun(Internal f_forward)) ::
 (_forward_remset, Gfun(Internal f_forward_remset)) ::
 (_forward_roots, Gfun(Internal f_forward_roots)) ::
 (_do_scan, Gfun(Internal f_do_scan)) ::
 (_do_generation, Gfun(Internal f_do_generation)) ::
 (_create_space, Gfun(Internal f_create_space)) ::
 (_create_heap, Gfun(Internal f_create_heap)) ::
 (_make_tinfo, Gfun(Internal f_make_tinfo)) ::
 (_resume, Gfun(Internal f_resume)) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) ::
 (_free_heap, Gfun(Internal f_free_heap)) ::
 (_garbage_collect_all, Gfun(Internal f_garbage_collect_all)) ::
 (_export, Gfun(Internal f_export)) ::
 (_certicoq_modify, Gfun(Internal f_certicoq_modify)) ::
 (_print_heapsize, Gfun(Internal f_print_heapsize)) :: nil).

Definition public_idents : list ident :=
(_print_heapsize :: _certicoq_modify :: _export :: _garbage_collect_all ::
 _free_heap :: _reset_heap :: _garbage_collect :: _resume :: _make_tinfo ::
 _create_heap :: _create_space :: _do_generation :: _do_scan ::
 _forward_roots :: _forward_remset :: _forward :: _Is_from :: _abort_with ::
 _Is_block :: _ptr_to_int_or_ptr :: _int_to_int_or_ptr ::
 _int_or_ptr_to_ptr :: _int_or_ptr_to_int :: _test_int_or_ptr :: _printf ::
 _abort :: _fprintf :: ___stderrp :: _exit :: _free :: _malloc ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
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


