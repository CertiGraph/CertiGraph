From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "dijkstra/dijkstra3.c".
  Definition normalized := true.
End Info.

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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition _argc : ident := $"argc".
Definition _argv : ident := $"argv".
Definition _capacity : ident := $"capacity".
Definition _cost : ident := $"cost".
Definition _curr : ident := $"curr".
Definition _data : ident := $"data".
Definition _dijkstra : ident := $"dijkstra".
Definition _dist : ident := $"dist".
Definition _first_available : ident := $"first_available".
Definition _free : ident := $"free".
Definition _freeN : ident := $"freeN".
Definition _getCell : ident := $"getCell".
Definition _getPaths : ident := $"getPaths".
Definition _graph : ident := $"graph".
Definition _heap_cells : ident := $"heap_cells".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key_table : ident := $"key_table".
Definition _keys : ident := $"keys".
Definition _main : ident := $"main".
Definition _mallocN : ident := $"mallocN".
Definition _pq : ident := $"pq".
Definition _pq_edit_priority : ident := $"pq_edit_priority".
Definition _pq_free : ident := $"pq_free".
Definition _pq_insert_nc : ident := $"pq_insert_nc".
Definition _pq_make : ident := $"pq_make".
Definition _pq_remove_min_nc : ident := $"pq_remove_min_nc".
Definition _pq_size : ident := $"pq_size".
Definition _prev : ident := $"prev".
Definition _printPath : ident := $"printPath".
Definition _print_graph : ident := $"print_graph".
Definition _printf : ident := $"printf".
Definition _priority : ident := $"priority".
Definition _rand : ident := $"rand".
Definition _random : ident := $"random".
Definition _setup : ident := $"setup".
Definition _srand : ident := $"srand".
Definition _src : ident := $"src".
Definition _structItem : ident := $"structItem".
Definition _structPQ : ident := $"structPQ".
Definition _temp : ident := $"temp".
Definition _time : ident := $"time".
Definition _u : ident := $"u".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_setup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_random, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _time (Tfunction (Tcons (tptr tlong) Tnil) tlong cc_default))
      ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
    (Scall None (Evar _srand (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Ecast (Etempvar _t'1 tlong) tuint) :: nil)))
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
              (Sifthenelse (Ebinop Ole (Etempvar _j tint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _rand (Tfunction Tnil tint cc_default)) nil)
                  (Sset _random
                    (Ebinop Omod (Etempvar _t'2 tint)
                      (Ebinop Omul (Econst_int (Int.repr 3) tint)
                        (Econst_int (Int.repr 50) tint) tint) tint)))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _i tint)
                                 (Etempvar _j tint) tint)
                    (Sset _t'3 (Ecast (Econst_int (Int.repr 0) tint) tint))
                    (Sifthenelse (Ebinop Ogt (Etempvar _random tint)
                                   (Econst_int (Int.repr 50) tint) tint)
                      (Ssequence
                        (Sset _t'4
                          (Ecast (Econst_int (Int.repr 2147483647) tint)
                            tint))
                        (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))
                      (Ssequence
                        (Sset _t'4 (Ecast (Etempvar _random tint) tint))
                        (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _graph (tptr (tarray tint 8)))
                            (Etempvar _i tint) (tptr (tarray tint 8)))
                          (tarray tint 8)) (Etempvar _j tint) (tptr tint))
                      tint) (Etempvar _t'3 tint)))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_print_graph := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: (_src, tint) :: nil);
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
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 8) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _graph (tptr (tarray tint 8)))
                            (Etempvar _i tint) (tptr (tarray tint 8)))
                          (tarray tint 8)) (Etempvar _j tint) (tptr tint))
                      tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                                 (Econst_int (Int.repr 2147483647) tint)
                                 tint)
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                      ((Evar ___stringlit_2 (tarray tschar 3)) :: nil))
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _graph (tptr (tarray tint 8)))
                                (Etempvar _i tint) (tptr (tarray tint 8)))
                              (tarray tint 8)) (Etempvar _j tint)
                            (tptr tint)) tint))
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_1 (tarray tschar 4)) ::
                         (Etempvar _t'2 tint) :: nil))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_3 (tarray tschar 2)) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_4 (tarray tschar 22)) ::
     (Econst_int (Int.repr 8) tint) :: (Etempvar _src tint) :: nil)))
|}.

Definition f_printPath := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_curr, tint) :: (_src, tint) :: (_prev, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _curr tint) (Etempvar _src tint) tint)
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_1 (tarray tschar 4)) :: (Etempvar _curr tint) :: nil))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd (Etempvar _prev (tptr tint)) (Etempvar _curr tint)
            (tptr tint)) tint))
      (Scall None
        (Evar _printPath (Tfunction
                           (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil)))
                           tvoid cc_default))
        ((Etempvar _t'1 tint) :: (Etempvar _src tint) ::
         (Etempvar _prev (tptr tint)) :: nil)))
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_1 (tarray tschar 4)) :: (Etempvar _curr tint) ::
       nil))))
|}.

Definition f_getPaths := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_src, tint) :: (_dist, (tptr tint)) ::
                (_prev, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tint) :: (_t'3, tint) :: (_t'2, tint) ::
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
          (Sifthenelse (Ebinop One (Etempvar _i tint) (Etempvar _src tint)
                         tint)
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _dist (tptr tint))
                    (Etempvar _i tint) (tptr tint)) tint))
              (Sset _t'1
                (Ecast
                  (Ebinop Olt (Etempvar _t'3 tint)
                    (Econst_int (Int.repr 2147483647) tint) tint) tbool)))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'1 tint)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _dist (tptr tint))
                      (Etempvar _i tint) (tptr tint)) tint))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_5 (tarray tschar 39)) ::
                   (Etempvar _src tint) :: (Etempvar _i tint) ::
                   (Etempvar _t'2 tint) :: nil)))
              (Scall None
                (Evar _printPath (Tfunction
                                   (Tcons tint
                                     (Tcons tint (Tcons (tptr tint) Tnil)))
                                   tvoid cc_default))
                ((Etempvar _i tint) :: (Etempvar _src tint) ::
                 (Etempvar _prev (tptr tint)) :: nil)))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_6 (tarray tschar 28)) :: nil)))
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

Definition f_dijkstra := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tarray tint 8))) :: (_src, tint) ::
                (_dist, (tptr tint)) :: (_prev, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_temp, (tptr (Tstruct _structItem noattr))) ::
               (_keys, (tptr tint)) ::
               (_pq, (tptr (Tstruct _structPQ noattr))) :: (_i, tint) ::
               (_j, tint) :: (_u, tint) :: (_cost, tint) :: (_t'6, tint) ::
               (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _structPQ noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _structItem noattr) tulong) :: nil))
    (Sset _temp
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _structItem noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Econst_int (Int.repr 8) tint) (Esizeof tint tulong)
           tulong) :: nil))
      (Sset _keys (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _pq_make (Tfunction (Tcons tuint Tnil)
                           (tptr (Tstruct _structPQ noattr)) cc_default))
          ((Econst_int (Int.repr 8) tint) :: nil))
        (Sset _pq (Etempvar _t'3 (tptr (Tstruct _structPQ noattr)))))
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
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _dist (tptr tint))
                      (Etempvar _i tint) (tptr tint)) tint)
                  (Econst_int (Int.repr 2147483647) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _prev (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint)
                    (Econst_int (Int.repr 2147483647) tint))
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _pq_insert_nc (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _structPQ noattr))
                                              (Tcons tint (Tcons tint Tnil)))
                                            tuint cc_default))
                      ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                       (Econst_int (Int.repr 2147483647) tint) ::
                       (Etempvar _i tint) :: nil))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _keys (tptr tint))
                          (Etempvar _i tint) (tptr tint)) tint)
                      (Etempvar _t'4 tuint))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dist (tptr tint)) (Etempvar _src tint)
                (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _prev (tptr tint))
                  (Etempvar _src tint) (tptr tint)) tint)
              (Etempvar _src tint))
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Ederef
                    (Ebinop Oadd (Etempvar _keys (tptr tint))
                      (Etempvar _src tint) (tptr tint)) tint))
                (Scall None
                  (Evar _pq_edit_priority (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _structPQ noattr))
                                              (Tcons tint (Tcons tint Tnil)))
                                            tvoid cc_default))
                  ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                   (Etempvar _t'12 tint) :: (Econst_int (Int.repr 0) tint) ::
                   nil)))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _pq_size (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _structPQ noattr))
                                           Tnil) tuint cc_default))
                        ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                         nil))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'5 tuint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Scall None
                        (Evar _pq_remove_min_nc (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _structPQ noattr))
                                                    (Tcons
                                                      (tptr (Tstruct _structItem noattr))
                                                      Tnil)) tvoid
                                                  cc_default))
                        ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                         (Etempvar _temp (tptr (Tstruct _structItem noattr))) ::
                         nil))
                      (Ssequence
                        (Sset _u
                          (Efield
                            (Ederef
                              (Etempvar _temp (tptr (Tstruct _structItem noattr)))
                              (Tstruct _structItem noattr)) _data tint))
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                             (Econst_int (Int.repr 8) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _getCell (Tfunction
                                                     (Tcons
                                                       (tptr (tarray tint 8))
                                                       (Tcons tint
                                                         (Tcons tint Tnil)))
                                                     tint cc_default))
                                    ((Etempvar _graph (tptr (tarray tint 8))) ::
                                     (Etempvar _u tint) ::
                                     (Etempvar _i tint) :: nil))
                                  (Sset _cost (Etempvar _t'6 tint)))
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _cost tint)
                                               (Econst_int (Int.repr 2147483647) tint)
                                               tint)
                                  (Ssequence
                                    (Sset _t'7
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _dist (tptr tint))
                                          (Etempvar _i tint) (tptr tint))
                                        tint))
                                    (Ssequence
                                      (Sset _t'8
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _dist (tptr tint))
                                            (Etempvar _u tint) (tptr tint))
                                          tint))
                                      (Sifthenelse (Ebinop Ogt
                                                     (Etempvar _t'7 tint)
                                                     (Ebinop Oadd
                                                       (Etempvar _t'8 tint)
                                                       (Etempvar _cost tint)
                                                       tint) tint)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'11
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _dist (tptr tint))
                                                  (Etempvar _u tint)
                                                  (tptr tint)) tint))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _dist (tptr tint))
                                                  (Etempvar _i tint)
                                                  (tptr tint)) tint)
                                              (Ebinop Oadd
                                                (Etempvar _t'11 tint)
                                                (Etempvar _cost tint) tint)))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _prev (tptr tint))
                                                  (Etempvar _i tint)
                                                  (tptr tint)) tint)
                                              (Etempvar _u tint))
                                            (Ssequence
                                              (Sset _t'9
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _keys (tptr tint))
                                                    (Etempvar _i tint)
                                                    (tptr tint)) tint))
                                              (Ssequence
                                                (Sset _t'10
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _dist (tptr tint))
                                                      (Etempvar _i tint)
                                                      (tptr tint)) tint))
                                                (Scall None
                                                  (Evar _pq_edit_priority 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _structPQ noattr))
                                                      (Tcons tint
                                                        (Tcons tint Tnil)))
                                                    tvoid cc_default))
                                                  ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                                                   (Etempvar _t'9 tint) ::
                                                   (Etempvar _t'10 tint) ::
                                                   nil))))))
                                        Sskip)))
                                  Sskip)))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint)))))))
                  Sskip)
                (Ssequence
                  (Scall None
                    (Evar _freeN (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                    ((Etempvar _temp (tptr (Tstruct _structItem noattr))) ::
                     nil))
                  (Ssequence
                    (Scall None
                      (Evar _pq_free (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _structPQ noattr))
                                         Tnil) tvoid cc_default))
                      ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _freeN (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                        ((Etempvar _keys (tptr tint)) :: nil))
                      (Sreturn None))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_argc, tint) :: (_argv, (tptr (tptr tschar))) :: nil);
  fn_vars := ((_graph, (tarray (tarray tint 8) 8)) :: nil);
  fn_temps := ((_src, tint) :: (_prev, (tptr tint)) ::
               (_dist, (tptr tint)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tint) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _time (Tfunction (Tcons (tptr tlong) Tnil) tlong cc_default))
        ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
      (Scall None
        (Evar _srand (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Ecast (Etempvar _t'1 tlong) tuint) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2) (Evar _rand (Tfunction Tnil tint cc_default)) nil)
        (Sset _src
          (Ebinop Omod (Etempvar _t'2 tint) (Econst_int (Int.repr 8) tint)
            tint)))
      (Ssequence
        (Scall None
          (Evar _setup (Tfunction (Tcons (tptr (tarray tint 8)) Tnil) tvoid
                         cc_default))
          ((Evar _graph (tarray (tarray tint 8) 8)) :: nil))
        (Ssequence
          (Scall None
            (Evar _print_graph (Tfunction
                                 (Tcons (tptr (tarray tint 8))
                                   (Tcons tint Tnil)) tvoid cc_default))
            ((Evar _graph (tarray (tarray tint 8) 8)) ::
             (Etempvar _src tint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                 cc_default))
                ((Ebinop Omul (Econst_int (Int.repr 8) tint)
                   (Esizeof tint tulong) tulong) :: nil))
              (Sset _prev (Etempvar _t'3 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                   cc_default))
                  ((Ebinop Omul (Econst_int (Int.repr 8) tint)
                     (Esizeof tint tulong) tulong) :: nil))
                (Sset _dist (Etempvar _t'4 (tptr tvoid))))
              (Ssequence
                (Scall None
                  (Evar _dijkstra (Tfunction
                                    (Tcons (tptr (tarray tint 8))
                                      (Tcons tint
                                        (Tcons (tptr tint)
                                          (Tcons (tptr tint) Tnil)))) tvoid
                                    cc_default))
                  ((Evar _graph (tarray (tarray tint 8) 8)) ::
                   (Etempvar _src tint) :: (Etempvar _dist (tptr tint)) ::
                   (Etempvar _prev (tptr tint)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _getPaths (Tfunction
                                      (Tcons tint
                                        (Tcons (tptr tint)
                                          (Tcons (tptr tint) Tnil))) tvoid
                                      cc_default))
                    ((Etempvar _src tint) :: (Etempvar _dist (tptr tint)) ::
                     (Etempvar _prev (tptr tint)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _prev (tptr tint)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _dist (tptr tint)) :: nil))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _structItem Struct
   (Member_plain _key tuint :: Member_plain _priority tint ::
    Member_plain _data tint :: nil)
   noattr ::
 Composite _structPQ Struct
   (Member_plain _capacity tuint :: Member_plain _first_available tuint ::
    Member_plain _heap_cells (tptr (Tstruct _structItem noattr)) ::
    Member_plain _key_table (tptr tuint) :: nil)
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
     cc_default)) :: (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_rand,
   Gfun(External (EF_external "rand" (mksignature nil AST.Tint cc_default))
     Tnil tint cc_default)) ::
 (_srand,
   Gfun(External (EF_external "srand"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tuint Tnil) tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_time,
   Gfun(External (EF_external "time"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tlong) Tnil) tlong cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_pq_remove_min_nc,
   Gfun(External (EF_external "pq_remove_min_nc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr))
       (Tcons (tptr (Tstruct _structItem noattr)) Tnil)) tvoid cc_default)) ::
 (_pq_insert_nc,
   Gfun(External (EF_external "pq_insert_nc"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) (Tcons tint (Tcons tint Tnil)))
     tuint cc_default)) ::
 (_pq_edit_priority,
   Gfun(External (EF_external "pq_edit_priority"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) (Tcons tint (Tcons tint Tnil)))
     tvoid cc_default)) ::
 (_pq_size,
   Gfun(External (EF_external "pq_size"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) Tnil) tuint cc_default)) ::
 (_pq_make,
   Gfun(External (EF_external "pq_make"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tuint Tnil) (tptr (Tstruct _structPQ noattr)) cc_default)) ::
 (_pq_free,
   Gfun(External (EF_external "pq_free"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) Tnil) tvoid cc_default)) ::
 (_setup, Gfun(Internal f_setup)) ::
 (_print_graph, Gfun(Internal f_print_graph)) ::
 (_printPath, Gfun(Internal f_printPath)) ::
 (_getPaths, Gfun(Internal f_getPaths)) ::
 (_getCell, Gfun(Internal f_getCell)) ::
 (_dijkstra, Gfun(Internal f_dijkstra)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _dijkstra :: _getCell :: _getPaths :: _printPath :: _print_graph ::
 _setup :: _pq_free :: _pq_make :: _pq_size :: _pq_edit_priority ::
 _pq_insert_nc :: _pq_remove_min_nc :: _freeN :: _mallocN :: _time ::
 _printf :: _srand :: _rand :: _free :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


