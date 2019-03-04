From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "gc.c"%string.
  Definition normalized := true.
End Info.

Definition _Is_block : ident := 99%positive.
Definition _Is_from : ident := 105%positive.
Definition ___builtin_annot : ident := 41%positive.
Definition ___builtin_annot_intval : ident := 42%positive.
Definition ___builtin_bswap : ident := 35%positive.
Definition ___builtin_bswap16 : ident := 37%positive.
Definition ___builtin_bswap32 : ident := 36%positive.
Definition ___builtin_bswap64 : ident := 67%positive.
Definition ___builtin_clz : ident := 68%positive.
Definition ___builtin_clzl : ident := 69%positive.
Definition ___builtin_clzll : ident := 70%positive.
Definition ___builtin_ctz : ident := 71%positive.
Definition ___builtin_ctzl : ident := 72%positive.
Definition ___builtin_ctzll : ident := 73%positive.
Definition ___builtin_debug : ident := 85%positive.
Definition ___builtin_fabs : ident := 38%positive.
Definition ___builtin_fmadd : ident := 76%positive.
Definition ___builtin_fmax : ident := 74%positive.
Definition ___builtin_fmin : ident := 75%positive.
Definition ___builtin_fmsub : ident := 77%positive.
Definition ___builtin_fnmadd : ident := 78%positive.
Definition ___builtin_fnmsub : ident := 79%positive.
Definition ___builtin_fsqrt : ident := 39%positive.
Definition ___builtin_membar : ident := 43%positive.
Definition ___builtin_memcpy_aligned : ident := 40%positive.
Definition ___builtin_nop : ident := 84%positive.
Definition ___builtin_read16_reversed : ident := 80%positive.
Definition ___builtin_read32_reversed : ident := 81%positive.
Definition ___builtin_va_arg : ident := 45%positive.
Definition ___builtin_va_copy : ident := 46%positive.
Definition ___builtin_va_end : ident := 47%positive.
Definition ___builtin_va_start : ident := 44%positive.
Definition ___builtin_write16_reversed : ident := 82%positive.
Definition ___builtin_write32_reversed : ident := 83%positive.
Definition ___compcert_i64_dtos : ident := 52%positive.
Definition ___compcert_i64_dtou : ident := 53%positive.
Definition ___compcert_i64_sar : ident := 64%positive.
Definition ___compcert_i64_sdiv : ident := 58%positive.
Definition ___compcert_i64_shl : ident := 62%positive.
Definition ___compcert_i64_shr : ident := 63%positive.
Definition ___compcert_i64_smod : ident := 60%positive.
Definition ___compcert_i64_smulh : ident := 65%positive.
Definition ___compcert_i64_stod : ident := 54%positive.
Definition ___compcert_i64_stof : ident := 56%positive.
Definition ___compcert_i64_udiv : ident := 59%positive.
Definition ___compcert_i64_umod : ident := 61%positive.
Definition ___compcert_i64_umulh : ident := 66%positive.
Definition ___compcert_i64_utod : ident := 55%positive.
Definition ___compcert_i64_utof : ident := 57%positive.
Definition ___compcert_va_composite : ident := 51%positive.
Definition ___compcert_va_float64 : ident := 50%positive.
Definition ___compcert_va_int32 : ident := 48%positive.
Definition ___compcert_va_int64 : ident := 49%positive.
Definition ___sFILE : ident := 25%positive.
Definition ___sFILEX : ident := 17%positive.
Definition ___sbuf : ident := 3%positive.
Definition ___stderrp : ident := 89%positive.
Definition ___stringlit_1 : ident := 118%positive.
Definition ___stringlit_10 : ident := 143%positive.
Definition ___stringlit_11 : ident := 144%positive.
Definition ___stringlit_12 : ident := 147%positive.
Definition ___stringlit_13 : ident := 148%positive.
Definition ___stringlit_14 : ident := 149%positive.
Definition ___stringlit_15 : ident := 151%positive.
Definition ___stringlit_16 : ident := 153%positive.
Definition ___stringlit_2 : ident := 119%positive.
Definition ___stringlit_3 : ident := 120%positive.
Definition ___stringlit_4 : ident := 128%positive.
Definition ___stringlit_5 : ident := 129%positive.
Definition ___stringlit_6 : ident := 131%positive.
Definition ___stringlit_7 : ident := 132%positive.
Definition ___stringlit_8 : ident := 135%positive.
Definition ___stringlit_9 : ident := 138%positive.
Definition __base : ident := 1%positive.
Definition __bf : ident := 9%positive.
Definition __blksize : ident := 23%positive.
Definition __close : ident := 12%positive.
Definition __cookie : ident := 11%positive.
Definition __extra : ident := 18%positive.
Definition __file : ident := 8%positive.
Definition __flags : ident := 7%positive.
Definition __lb : ident := 22%positive.
Definition __lbfsize : ident := 10%positive.
Definition __nbuf : ident := 21%positive.
Definition __offset : ident := 24%positive.
Definition __p : ident := 4%positive.
Definition __r : ident := 5%positive.
Definition __read : ident := 13%positive.
Definition __seek : ident := 14%positive.
Definition __size : ident := 2%positive.
Definition __ub : ident := 16%positive.
Definition __ubuf : ident := 20%positive.
Definition __ur : ident := 19%positive.
Definition __w : ident := 6%positive.
Definition __write : ident := 15%positive.
Definition _abort : ident := 91%positive.
Definition _abort_with : ident := 101%positive.
Definition _alloc : ident := 26%positive.
Definition _args : ident := 29%positive.
Definition _create_heap : ident := 136%positive.
Definition _create_space : ident := 133%positive.
Definition _depth : ident := 107%positive.
Definition _do_generation : ident := 130%positive.
Definition _do_scan : ident := 125%positive.
Definition _exit : ident := 88%positive.
Definition _fi : ident := 114%positive.
Definition _forward : ident := 113%positive.
Definition _forward_roots : ident := 121%positive.
Definition _fprintf : ident := 90%positive.
Definition _free : ident := 87%positive.
Definition _free_heap : ident := 154%positive.
Definition _from : ident := 126%positive.
Definition _from_limit : ident := 103%positive.
Definition _from_start : ident := 102%positive.
Definition _garbage_collect : ident := 150%positive.
Definition _h : ident := 134%positive.
Definition _hd : ident := 109%positive.
Definition _heap : ident := 28%positive.
Definition _hi : ident := 141%positive.
Definition _i : ident := 110%positive.
Definition _int_or_ptr_to_int : ident := 95%positive.
Definition _int_or_ptr_to_ptr : ident := 96%positive.
Definition _int_to_int_or_ptr : ident := 97%positive.
Definition _j : ident := 124%positive.
Definition _limit : ident := 27%positive.
Definition _lo : ident := 140%positive.
Definition _main : ident := 155%positive.
Definition _make_tinfo : ident := 139%positive.
Definition _malloc : ident := 86%positive.
Definition _n : ident := 116%positive.
Definition _new : ident := 112%positive.
Definition _next : ident := 32%positive.
Definition _num_allocs : ident := 142%positive.
Definition _p : ident := 106%positive.
Definition _printf : ident := 92%positive.
Definition _ptr_to_int_or_ptr : ident := 98%positive.
Definition _reset_heap : ident := 152%positive.
Definition _resume : ident := 145%positive.
Definition _roots : ident := 117%positive.
Definition _s : ident := 100%positive.
Definition _scan : ident := 122%positive.
Definition _space : ident := 33%positive.
Definition _spaces : ident := 34%positive.
Definition _start : ident := 31%positive.
Definition _sz : ident := 111%positive.
Definition _tag : ident := 123%positive.
Definition _test_int_or_ptr : ident := 94%positive.
Definition _thread_info : ident := 30%positive.
Definition _ti : ident := 115%positive.
Definition _tinfo : ident := 137%positive.
Definition _to : ident := 127%positive.
Definition _v : ident := 104%positive.
Definition _va : ident := 108%positive.
Definition _w : ident := 146%positive.
Definition _x : ident := 93%positive.
Definition _t'1 : ident := 156%positive.
Definition _t'10 : ident := 165%positive.
Definition _t'11 : ident := 166%positive.
Definition _t'12 : ident := 167%positive.
Definition _t'13 : ident := 168%positive.
Definition _t'14 : ident := 169%positive.
Definition _t'2 : ident := 157%positive.
Definition _t'3 : ident := 158%positive.
Definition _t'4 : ident := 159%positive.
Definition _t'5 : ident := 160%positive.
Definition _t'6 : ident := 161%positive.
Definition _t'7 : ident := 162%positive.
Definition _t'8 : ident := 163%positive.
Definition _t'9 : ident := 164%positive.

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
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
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

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 91) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 43);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
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
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 10) ::
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

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 45);
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

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
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
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand
                   (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) tint)
                   (Econst_int (Int.repr 1) tint) tint) tint)))
|}.

Definition f_int_or_ptr_to_int := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) tint)))
|}.

Definition f_int_or_ptr_to_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) (tptr tvoid))))
|}.

Definition f_int_to_int_or_ptr := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x tint) (talignas 2%N (tptr tvoid)))))
|}.

Definition f_ptr_to_int_or_ptr := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) (talignas 2%N (tptr tvoid)))))
|}.

Definition f_Is_block := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _test_int_or_ptr (Tfunction
                             (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint
                             cc_default))
    ((Etempvar _x (talignas 2%N (tptr tvoid))) :: nil))
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
                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
       (Etempvar _s (tptr tschar)) :: nil)))
  (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
    ((Econst_int (Int.repr 1) tint) :: nil)))
|}.

Definition f_Is_from := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_v, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
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
|}.

Definition f_forward := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                (_p, (tptr (talignas 2%N (tptr tvoid)))) :: (_depth, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_v, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_va, (talignas 2%N (tptr tvoid))) :: (_hd, tuint) ::
               (_i, tint) :: (_sz, tint) ::
               (_new, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (talignas 2%N (tptr tvoid))) ::
               (_t'2, (talignas 2%N (tptr tvoid))) :: (_t'1, (tptr tvoid)) ::
               (_t'8, (talignas 2%N (tptr tvoid))) ::
               (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (talignas 2%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _va
    (Ederef (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
      (talignas 2%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'5)
      (Evar _Is_block (Tfunction (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                        tint cc_default))
      ((Etempvar _va (talignas 2%N (tptr tvoid))) :: nil))
    (Sifthenelse (Etempvar _t'5 tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _int_or_ptr_to_ptr (Tfunction
                                       (Tcons (talignas 2%N (tptr tvoid))
                                         Tnil) (tptr tvoid) cc_default))
            ((Etempvar _va (talignas 2%N (tptr tvoid))) :: nil))
          (Sset _v
            (Ecast (Etempvar _t'1 (tptr tvoid))
              (tptr (talignas 2%N (tptr tvoid))))))
        (Ssequence
          (Scall (Some _t'4)
            (Evar _Is_from (Tfunction
                             (Tcons (tptr (talignas 2%N (tptr tvoid)))
                               (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                 (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                   Tnil))) tint cc_default))
            ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) :: nil))
          (Sifthenelse (Etempvar _t'4 tint)
            (Ssequence
              (Sset _hd
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                      (tptr tuint))
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                    (tptr tuint)) tuint))
              (Sifthenelse (Ebinop Oeq (Etempvar _hd tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _t'8
                    (Ederef
                      (Ebinop Oadd
                        (Ecast
                          (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                          (tptr (talignas 2%N (tptr tvoid))))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (talignas 2%N (tptr tvoid))))
                      (talignas 2%N (tptr tvoid))))
                  (Sassign
                    (Ederef (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                      (talignas 2%N (tptr tvoid)))
                    (Etempvar _t'8 (talignas 2%N (tptr tvoid)))))
                (Ssequence
                  (Sset _sz
                    (Ecast
                      (Ebinop Oshr (Etempvar _hd tuint)
                        (Econst_int (Int.repr 10) tint) tuint) tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Sset _new
                        (Ebinop Oadd
                          (Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid))))
                          (Econst_int (Int.repr 1) tint)
                          (tptr (talignas 2%N (tptr tvoid))))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
                          (tptr (talignas 2%N (tptr tvoid))))
                        (Ebinop Oadd
                          (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                          (Etempvar _sz tint)
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Ecast
                                (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                                (tptr tuint))
                              (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                tint) (tptr tuint)) tuint)
                          (Etempvar _hd tuint))
                        (Ssequence
                          (Ssequence
                            (Sset _i (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Etempvar _sz tint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _t'6
                                    (Ederef
                                      (Ebinop Oadd
                                        (Ecast
                                          (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                                          (tptr (talignas 2%N (tptr tvoid))))
                                        (Etempvar _i tint)
                                        (tptr (talignas 2%N (tptr tvoid))))
                                      (talignas 2%N (tptr tvoid))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Ecast
                                          (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                                          (tptr (talignas 2%N (tptr tvoid))))
                                        (Etempvar _i tint)
                                        (tptr (talignas 2%N (tptr tvoid))))
                                      (talignas 2%N (tptr tvoid)))
                                    (Etempvar _t'6 (talignas 2%N (tptr tvoid))))))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Ecast
                                    (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                                    (tptr tuint))
                                  (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                    tint) (tptr tuint)) tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'2)
                                  (Evar _ptr_to_int_or_ptr (Tfunction
                                                             (Tcons
                                                               (tptr tvoid)
                                                               Tnil)
                                                             (talignas 2%N (tptr tvoid))
                                                             cc_default))
                                  ((Ecast
                                     (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                                     (tptr tvoid)) :: nil))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ecast
                                        (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
                                        (tptr (talignas 2%N (tptr tvoid))))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (talignas 2%N (tptr tvoid))))
                                    (talignas 2%N (tptr tvoid)))
                                  (Etempvar _t'2 (talignas 2%N (tptr tvoid)))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'3)
                                    (Evar _ptr_to_int_or_ptr (Tfunction
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil)
                                                               (talignas 2%N (tptr tvoid))
                                                               cc_default))
                                    ((Ecast
                                       (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                                       (tptr tvoid)) :: nil))
                                  (Sassign
                                    (Ederef
                                      (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                                      (talignas 2%N (tptr tvoid)))
                                    (Etempvar _t'3 (talignas 2%N (tptr tvoid)))))
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _depth tint)
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
                                                             (tptr (talignas 2%N (tptr tvoid)))
                                                             (Tcons
                                                               (tptr (talignas 2%N (tptr tvoid)))
                                                               (Tcons
                                                                 (tptr (tptr (talignas 2%N (tptr tvoid))))
                                                                 (Tcons
                                                                   (tptr (talignas 2%N (tptr tvoid)))
                                                                   (Tcons
                                                                    tint
                                                                    Tnil)))))
                                                           tvoid cc_default))
                                          ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                                           (Ebinop Oadd
                                             (Ecast
                                               (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                                               (tptr (talignas 2%N (tptr tvoid))))
                                             (Etempvar _i tint)
                                             (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Ebinop Osub
                                             (Etempvar _depth tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint) :: nil)))
                                      (Sset _i
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))))
                                  Sskip)))))))))))
            Sskip)))
      Sskip)))
|}.

Definition f_forward_roots := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_args, (tptr (talignas 2%N (tptr tvoid)))) :: (_n, tint) ::
               (_i, tuint) :: (_roots, (tptr tuint)) :: (_t'1, tint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _roots
    (Ebinop Oadd (Etempvar _fi (tptr tuint)) (Econst_int (Int.repr 2) tint)
      (tptr tuint)))
  (Ssequence
    (Sset _n
      (Ederef
        (Ebinop Oadd (Etempvar _fi (tptr tuint))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _args
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _args
          (tarray (talignas 2%N (tptr tvoid)) 1024)))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _roots (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 1024) tint) tint)
                  Sskip
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                      ((Evar ___stringlit_3 (tarray tschar 30)) ::
                       (Evar ___stringlit_2 (tarray tschar 5)) ::
                       (Econst_int (Int.repr 210) tint) ::
                       (Evar ___stringlit_1 (tarray tschar 20)) :: nil))
                    (Scall None
                      (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))))
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _roots (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Scall None
                  (Evar _forward (Tfunction
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 2%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 2%N (tptr tvoid))))
                                         (Tcons
                                           (tptr (talignas 2%N (tptr tvoid)))
                                           (Tcons tint Tnil))))) tvoid
                                   cc_default))
                  ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                   (Ebinop Oadd
                     (Etempvar _args (tptr (talignas 2%N (tptr tvoid))))
                     (Etempvar _t'2 tuint)
                     (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))))
|}.

Definition f_do_scan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_scan, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr (talignas 2%N (tptr tvoid)))) :: (_hd, tuint) ::
               (_sz, tuint) :: (_tag, tint) :: (_j, tint) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Etempvar _scan (tptr (talignas 2%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Ederef (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
            (tptr (talignas 2%N (tptr tvoid)))))
        (Sifthenelse (Ebinop Olt
                       (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
                       (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid))))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Sset _hd
          (Ederef
            (Ecast (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _sz
            (Ecast
              (Ebinop Oshr (Etempvar _hd tuint)
                (Econst_int (Int.repr 10) tint) tuint) tuint))
          (Ssequence
            (Sset _tag
              (Ecast
                (Ebinop Oand (Etempvar _hd tuint)
                  (Econst_int (Int.repr 255) tint) tuint) tuint))
            (Ssequence
              (Sifthenelse (Eunop Onotbool
                             (Ebinop Oge (Etempvar _tag tint)
                               (Econst_int (Int.repr 251) tint) tint) tint)
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 1) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _j tint)
                                     (Etempvar _sz tuint) tint)
                        Sskip
                        Sbreak)
                      (Scall None
                        (Evar _forward (Tfunction
                                         (Tcons
                                           (tptr (talignas 2%N (tptr tvoid)))
                                           (Tcons
                                             (tptr (talignas 2%N (tptr tvoid)))
                                             (Tcons
                                               (tptr (tptr (talignas 2%N (tptr tvoid))))
                                               (Tcons
                                                 (tptr (talignas 2%N (tptr tvoid)))
                                                 (Tcons tint Tnil))))) tvoid
                                         cc_default))
                        ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                         (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                         (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                         (Ebinop Oadd
                           (Ecast
                             (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
                             (tptr (talignas 2%N (tptr tvoid))))
                           (Etempvar _j tint)
                           (tptr (talignas 2%N (tptr tvoid)))) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                Sskip)
              (Sset _s
                (Ebinop Oadd (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
                  (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                    (Etempvar _sz tuint) tuint)
                  (tptr (talignas 2%N (tptr tvoid))))))))))
    Sskip))
|}.

Definition f_do_generation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'1, tint) ::
               (_t'14, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'13, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'12, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'11, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'10, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'9, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (Tstruct ___sFILE noattr))) ::
               (_t'2, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _next (tptr (talignas 2%N (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _next
          (tptr (talignas 2%N (tptr tvoid)))))
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'14
              (Efield
                (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _next
                (tptr (talignas 2%N (tptr tvoid)))))
            (Sifthenelse (Ebinop Ole
                           (Ebinop Osub
                             (Etempvar _t'11 (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _t'12 (tptr (talignas 2%N (tptr tvoid))))
                             tint)
                           (Ebinop Osub
                             (Etempvar _t'13 (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _t'14 (tptr (talignas 2%N (tptr tvoid))))
                             tint) tint)
              Sskip
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_3 (tarray tschar 30)) ::
                   (Evar ___stringlit_2 (tarray tschar 5)) ::
                   (Econst_int (Int.repr 251) tint) ::
                   (Evar ___stringlit_4 (tarray tschar 45)) :: nil))
                (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default))
                  nil)))))))
    (Ssequence
      (Ssequence
        (Sset _t'9
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 2%N (tptr tvoid)))))
          (Scall None
            (Evar _forward_roots (Tfunction
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 2%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 2%N (tptr tvoid))))
                                         (Tcons (tptr tuint)
                                           (Tcons
                                             (tptr (Tstruct _thread_info noattr))
                                             Tnil))))) tvoid cc_default))
            ((Etempvar _t'9 (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _t'10 (tptr (talignas 2%N (tptr tvoid)))) ::
             (Eaddrof
               (Efield
                 (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                   (Tstruct _space noattr)) _next
                 (tptr (talignas 2%N (tptr tvoid))))
               (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
             (Etempvar _fi (tptr tuint)) ::
             (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _start
              (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 2%N (tptr tvoid)))))
            (Scall None
              (Evar _do_scan (Tfunction
                               (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                 (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (tptr (talignas 2%N (tptr tvoid))))
                                       Tnil)))) tvoid cc_default))
              ((Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid)))) ::
               (Etempvar _t'8 (tptr (talignas 2%N (tptr tvoid)))) ::
               (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                     (Tstruct _space noattr)) _next
                   (tptr (talignas 2%N (tptr tvoid))))
                 (tptr (tptr (talignas 2%N (tptr tvoid))))) :: nil))))
        (Ssequence
          (Sifthenelse (Econst_int (Int.repr 0) tint)
            (Ssequence
              (Sset _t'3 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _next
                    (tptr (talignas 2%N (tptr tvoid)))))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _next
                      (tptr (talignas 2%N (tptr tvoid)))))
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Etempvar _from (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _start
                        (tptr (talignas 2%N (tptr tvoid)))))
                    (Scall None
                      (Evar _fprintf (Tfunction
                                       (Tcons
                                         (tptr (Tstruct ___sFILE noattr))
                                         (Tcons (tptr tschar) Tnil)) tint
                                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                      ((Etempvar _t'3 (tptr (Tstruct ___sFILE noattr))) ::
                       (Evar ___stringlit_5 (tarray tschar 19)) ::
                       (Ebinop Odiv
                         (Ebinop Osub
                           (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))
                           (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                           tint)
                         (Ecast
                           (Ebinop Osub
                             (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _t'6 (tptr (talignas 2%N (tptr tvoid))))
                             tint) tdouble) tdouble) :: nil))))))
            Sskip)
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _start
                (tptr (talignas 2%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _next
                (tptr (talignas 2%N (tptr tvoid))))
              (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid)))))))))))
|}.

Definition f_create_space := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _space noattr))) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oge (Etempvar _n tuint)
                 (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                   (Econst_int (Int.repr 29) tint) tint) tint)
    (Scall None
      (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                          cc_default))
      ((Evar ___stringlit_6 (tarray tschar 43)) :: nil))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Etempvar _n tuint)
           (Esizeof (talignas 2%N (tptr tvoid)) tuint) tuint) :: nil))
      (Sset _p
        (Ecast (Etempvar _t'1 (tptr tvoid))
          (tptr (talignas 2%N (tptr tvoid))))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
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
            (tptr (talignas 2%N (tptr tvoid))))
          (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _next
              (tptr (talignas 2%N (tptr tvoid))))
            (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 2%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
              (Etempvar _n tuint) (tptr (talignas 2%N (tptr tvoid))))))))))
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
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _heap noattr) tuint) :: nil))
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
                                (Tcons tuint Tnil)) tvoid cc_default))
        ((Ebinop Oadd
           (Efield
             (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
               (Tstruct _heap noattr)) _spaces
             (tarray (Tstruct _space noattr) 12))
           (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr))) ::
         (Ebinop Oshl (Econst_int (Int.repr 1) tint)
           (Econst_int (Int.repr 16) tint) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 1) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 12) tint) tint)
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
                          (tarray (Tstruct _space noattr) 12))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 2%N (tptr tvoid))))
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
                            (tarray (Tstruct _space noattr) 12))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _next
                      (tptr (talignas 2%N (tptr tvoid))))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 12))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit
                      (tptr (talignas 2%N (tptr tvoid))))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
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
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
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
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _thread_info noattr) tuint) :: nil))
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
                      (tarray (Tstruct _space noattr) 12))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _start (tptr (talignas 2%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 2%N (tptr tvoid))))
              (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 12))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid))))))
            (Sreturn (Some (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))))))))))
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_lo, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_hi, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_num_allocs, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sset _num_allocs
      (Ederef
        (Ebinop Oadd (Etempvar _fi (tptr tuint))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sifthenelse (Etempvar _h (tptr (Tstruct _heap noattr)))
        Sskip
        (Ssequence
          (Scall (Some _t'1)
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_3 (tarray tschar 30)) ::
             (Evar ___stringlit_2 (tarray tschar 5)) ::
             (Econst_int (Int.repr 343) tint) ::
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
                  (tarray (Tstruct _space noattr) 12))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
            _start (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sset _hi
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Osub
                             (Etempvar _hi (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _lo (tptr (talignas 2%N (tptr tvoid))))
                             tint) (Etempvar _num_allocs tuint) tint)
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
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _lo (tptr (talignas 2%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _hi (tptr (talignas 2%N (tptr tvoid))))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_w, tint) :: (_t'1, tint) ::
               (_t'10, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'9, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (tptr (Tstruct ___sFILE noattr))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _alloc
          (tptr (talignas 2%N (tptr tvoid)))))
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _spaces
                (tarray (Tstruct _space noattr) 12))
              (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _next
          (tptr (talignas 2%N (tptr tvoid))))
        (Etempvar _t'10 (tptr (talignas 2%N (tptr tvoid))))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Ebinop Osub (Econst_int (Int.repr 12) tint)
                             (Econst_int (Int.repr 1) tint) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                            (Tstruct _heap noattr)) _spaces
                          (tarray (Tstruct _space noattr) 12))
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint)
                        (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 2%N (tptr tvoid)))))
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid))))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'8
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 12))
                              (Etempvar _i tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _limit
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _h (tptr (Tstruct _heap noattr)))
                                    (Tstruct _heap noattr)) _spaces
                                  (tarray (Tstruct _space noattr) 12))
                                (Etempvar _i tint)
                                (tptr (Tstruct _space noattr)))
                              (Tstruct _space noattr)) _start
                            (tptr (talignas 2%N (tptr tvoid)))))
                        (Sset _w
                          (Ebinop Osub
                            (Etempvar _t'8 (tptr (talignas 2%N (tptr tvoid))))
                            (Etempvar _t'9 (tptr (talignas 2%N (tptr tvoid))))
                            tint))))
                    (Scall None
                      (Evar _create_space (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _space noattr))
                                              (Tcons tuint Tnil)) tvoid
                                            cc_default))
                      ((Ebinop Oadd
                         (Efield
                           (Ederef
                             (Etempvar _h (tptr (Tstruct _heap noattr)))
                             (Tstruct _heap noattr)) _spaces
                           (tarray (Tstruct _space noattr) 12))
                         (Ebinop Oadd (Etempvar _i tint)
                           (Econst_int (Int.repr 1) tint) tint)
                         (tptr (Tstruct _space noattr))) ::
                       (Ebinop Omul (Econst_int (Int.repr 2) tint)
                         (Etempvar _w tint) tint) :: nil)))
                  Sskip))
              (Ssequence
                (Sifthenelse (Econst_int (Int.repr 0) tint)
                  (Ssequence
                    (Sset _t'6
                      (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
                    (Scall None
                      (Evar _fprintf (Tfunction
                                       (Tcons
                                         (tptr (Tstruct ___sFILE noattr))
                                         (Tcons (tptr tschar) Tnil)) tint
                                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                      ((Etempvar _t'6 (tptr (Tstruct ___sFILE noattr))) ::
                       (Evar ___stringlit_12 (tarray tschar 17)) ::
                       (Etempvar _i tint) :: nil)))
                  Sskip)
                (Ssequence
                  (Scall None
                    (Evar _do_generation (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _space noattr))
                                             (Tcons
                                               (tptr (Tstruct _space noattr))
                                               (Tcons (tptr tuint)
                                                 (Tcons
                                                   (tptr (Tstruct _thread_info noattr))
                                                   Tnil)))) tvoid cc_default))
                    ((Ebinop Oadd
                       (Efield
                         (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                           (Tstruct _heap noattr)) _spaces
                         (tarray (Tstruct _space noattr) 12))
                       (Etempvar _i tint) (tptr (Tstruct _space noattr))) ::
                     (Ebinop Oadd
                       (Efield
                         (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                           (Tstruct _heap noattr)) _spaces
                         (tarray (Tstruct _space noattr) 12))
                       (Ebinop Oadd (Etempvar _i tint)
                         (Econst_int (Int.repr 1) tint) tint)
                       (tptr (Tstruct _space noattr))) ::
                     (Etempvar _fi (tptr tuint)) ::
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
                              (tarray (Tstruct _space noattr) 12))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 2%N (tptr tvoid)))))
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 12))
                              (Etempvar _i tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _start
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Ssequence
                        (Sset _t'4
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _h (tptr (Tstruct _heap noattr)))
                                    (Tstruct _heap noattr)) _spaces
                                  (tarray (Tstruct _space noattr) 12))
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (tptr (Tstruct _space noattr)))
                              (Tstruct _space noattr)) _limit
                            (tptr (talignas 2%N (tptr tvoid)))))
                        (Ssequence
                          (Sset _t'5
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _heap noattr)))
                                      (Tstruct _heap noattr)) _spaces
                                    (tarray (Tstruct _space noattr) 12))
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr (Tstruct _space noattr)))
                                (Tstruct _space noattr)) _next
                              (tptr (talignas 2%N (tptr tvoid)))))
                          (Sifthenelse (Ebinop Ole
                                         (Ebinop Osub
                                           (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid))))
                                           (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid))))
                                           tint)
                                         (Ebinop Osub
                                           (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))
                                           (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid))))
                                           tint) tint)
                            (Ssequence
                              (Scall None
                                (Evar _resume (Tfunction
                                                (Tcons (tptr tuint)
                                                  (Tcons
                                                    (tptr (Tstruct _thread_info noattr))
                                                    Tnil)) tvoid cc_default))
                                ((Etempvar _fi (tptr tuint)) ::
                                 (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                                 nil))
                              (Sreturn None))
                            Sskip)))))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Scall None
          (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                              cc_default))
          ((Evar ___stringlit_13 (tarray tschar 24)) :: nil))
        (Sifthenelse (Econst_int (Int.repr 0) tint)
          Sskip
          (Ssequence
            (Scall (Some _t'1)
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_3 (tarray tschar 30)) ::
               (Evar ___stringlit_2 (tarray tschar 5)) ::
               (Econst_int (Int.repr 386) tint) ::
               (Evar ___stringlit_14 (tarray tschar 2)) :: nil))
            (Scall None (Evar _abort (Tfunction Tnil tvoid cc_default)) nil)))))))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, (tptr (Tstruct ___sFILE noattr))) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct ___sFILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'2 (tptr (Tstruct ___sFILE noattr))) ::
       (Evar ___stringlit_15 (tarray tschar 22)) :: nil)))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 12) tint) tint)
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
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 2%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr (talignas 2%N (tptr tvoid))))
            (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct ___sFILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
       (Evar ___stringlit_16 (tarray tschar 21)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 12) tint) tint)
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
                      (tarray (Tstruct _space noattr) 12)) (Etempvar _i tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _start (tptr (talignas 2%N (tptr tvoid)))))
            (Sifthenelse (Ebinop One
                           (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _p (tptr (talignas 2%N (tptr tvoid)))) :: nil))
              Sskip)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))))
|}.

Definition composites : list composite_definition :=
(Composite ___sbuf Struct
   ((__base, (tptr tuchar)) :: (__size, tint) :: nil)
   noattr ::
 Composite ___sFILE Struct
   ((__p, (tptr tuchar)) :: (__r, tint) :: (__w, tint) ::
    (__flags, tshort) :: (__file, tshort) ::
    (__bf, (Tstruct ___sbuf noattr)) :: (__lbfsize, tint) ::
    (__cookie, (tptr tvoid)) ::
    (__close, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))) ::
    (__read,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
             tint cc_default))) ::
    (__seek,
     (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))
             tlong cc_default))) ::
    (__write,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
             tint cc_default))) :: (__ub, (Tstruct ___sbuf noattr)) ::
    (__extra, (tptr (Tstruct ___sFILEX noattr))) :: (__ur, tint) ::
    (__ubuf, (tarray tuchar 3)) :: (__nbuf, (tarray tuchar 1)) ::
    (__lb, (Tstruct ___sbuf noattr)) :: (__blksize, tint) ::
    (__offset, tlong) :: nil)
   noattr ::
 Composite _thread_info Struct
   ((_alloc, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray (talignas 2%N (tptr tvoid)) 1024)) :: nil)
   noattr ::
 Composite _space Struct
   ((_start, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_next, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) :: nil)
   noattr ::
 Composite _heap Struct
   ((_spaces, (tarray (Tstruct _space noattr) 12)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (___stderrp, Gvar v___stderrp) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE noattr)) (Tcons (tptr tschar) Tnil)) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil None cc_default)) Tnil
     tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_test_int_or_ptr, Gfun(Internal f_test_int_or_ptr)) ::
 (_int_or_ptr_to_int, Gfun(Internal f_int_or_ptr_to_int)) ::
 (_int_or_ptr_to_ptr, Gfun(Internal f_int_or_ptr_to_ptr)) ::
 (_int_to_int_or_ptr, Gfun(Internal f_int_to_int_or_ptr)) ::
 (_ptr_to_int_or_ptr, Gfun(Internal f_ptr_to_int_or_ptr)) ::
 (_Is_block, Gfun(Internal f_Is_block)) ::
 (_abort_with, Gfun(Internal f_abort_with)) ::
 (_Is_from, Gfun(Internal f_Is_from)) ::
 (_forward, Gfun(Internal f_forward)) ::
 (_forward_roots, Gfun(Internal f_forward_roots)) ::
 (_do_scan, Gfun(Internal f_do_scan)) ::
 (_do_generation, Gfun(Internal f_do_generation)) ::
 (_create_space, Gfun(Internal f_create_space)) ::
 (_create_heap, Gfun(Internal f_create_heap)) ::
 (_make_tinfo, Gfun(Internal f_make_tinfo)) ::
 (_resume, Gfun(Internal f_resume)) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) ::
 (_free_heap, Gfun(Internal f_free_heap)) :: nil).

Definition public_idents : list ident :=
(_free_heap :: _reset_heap :: _garbage_collect :: _resume :: _make_tinfo ::
 _create_heap :: _create_space :: _do_generation :: _do_scan ::
 _forward_roots :: _forward :: _Is_from :: _abort_with :: _Is_block ::
 _ptr_to_int_or_ptr :: _int_to_int_or_ptr :: _int_or_ptr_to_ptr ::
 _int_or_ptr_to_int :: _test_int_or_ptr :: _printf :: _abort :: _fprintf ::
 ___stderrp :: _exit :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


