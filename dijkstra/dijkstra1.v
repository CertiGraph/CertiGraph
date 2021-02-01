From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "dijkstra/dijkstra1.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 18%positive.
Definition ___builtin_annot_intval : ident := 19%positive.
Definition ___builtin_bswap : ident := 11%positive.
Definition ___builtin_bswap16 : ident := 13%positive.
Definition ___builtin_bswap32 : ident := 12%positive.
Definition ___builtin_bswap64 : ident := 10%positive.
Definition ___builtin_clz : ident := 44%positive.
Definition ___builtin_clzl : ident := 45%positive.
Definition ___builtin_clzll : ident := 46%positive.
Definition ___builtin_ctz : ident := 47%positive.
Definition ___builtin_ctzl : ident := 48%positive.
Definition ___builtin_ctzll : ident := 49%positive.
Definition ___builtin_debug : ident := 60%positive.
Definition ___builtin_fabs : ident := 14%positive.
Definition ___builtin_fmadd : ident := 52%positive.
Definition ___builtin_fmax : ident := 50%positive.
Definition ___builtin_fmin : ident := 51%positive.
Definition ___builtin_fmsub : ident := 53%positive.
Definition ___builtin_fnmadd : ident := 54%positive.
Definition ___builtin_fnmsub : ident := 55%positive.
Definition ___builtin_fsqrt : ident := 15%positive.
Definition ___builtin_membar : ident := 20%positive.
Definition ___builtin_memcpy_aligned : ident := 16%positive.
Definition ___builtin_read16_reversed : ident := 56%positive.
Definition ___builtin_read32_reversed : ident := 57%positive.
Definition ___builtin_sel : ident := 17%positive.
Definition ___builtin_va_arg : ident := 22%positive.
Definition ___builtin_va_copy : ident := 23%positive.
Definition ___builtin_va_end : ident := 24%positive.
Definition ___builtin_va_start : ident := 21%positive.
Definition ___builtin_write16_reversed : ident := 58%positive.
Definition ___builtin_write32_reversed : ident := 59%positive.
Definition ___compcert_i64_dtos : ident := 29%positive.
Definition ___compcert_i64_dtou : ident := 30%positive.
Definition ___compcert_i64_sar : ident := 41%positive.
Definition ___compcert_i64_sdiv : ident := 35%positive.
Definition ___compcert_i64_shl : ident := 39%positive.
Definition ___compcert_i64_shr : ident := 40%positive.
Definition ___compcert_i64_smod : ident := 37%positive.
Definition ___compcert_i64_smulh : ident := 42%positive.
Definition ___compcert_i64_stod : ident := 31%positive.
Definition ___compcert_i64_stof : ident := 33%positive.
Definition ___compcert_i64_udiv : ident := 36%positive.
Definition ___compcert_i64_umod : ident := 38%positive.
Definition ___compcert_i64_umulh : ident := 43%positive.
Definition ___compcert_i64_utod : ident := 32%positive.
Definition ___compcert_i64_utof : ident := 34%positive.
Definition ___compcert_va_composite : ident := 28%positive.
Definition ___compcert_va_float64 : ident := 27%positive.
Definition ___compcert_va_int32 : ident := 25%positive.
Definition ___compcert_va_int64 : ident := 26%positive.
Definition ___stringlit_1 : ident := 103%positive.
Definition ___stringlit_2 : ident := 104%positive.
Definition ___stringlit_3 : ident := 105%positive.
Definition ___stringlit_4 : ident := 106%positive.
Definition ___stringlit_5 : ident := 112%positive.
Definition ___stringlit_6 : ident := 113%positive.
Definition _argc : ident := 121%positive.
Definition _argv : ident := 122%positive.
Definition _arr : ident := 66%positive.
Definition _capacity : ident := 5%positive.
Definition _cells : ident := 77%positive.
Definition _cost : ident := 119%positive.
Definition _curr : ident := 108%positive.
Definition _data : ident := 3%positive.
Definition _dijkstra : ident := 120%positive.
Definition _dist : ident := 111%positive.
Definition _exch : ident := 70%positive.
Definition _fa : ident := 76%positive.
Definition _first_available : ident := 6%positive.
Definition _free : ident := 93%positive.
Definition _freeN : ident := 63%positive.
Definition _getCell : ident := 116%positive.
Definition _getPaths : ident := 114%positive.
Definition _graph : ident := 98%positive.
Definition _heap_cells : ident := 7%positive.
Definition _i : ident := 89%positive.
Definition _inf : ident := 99%positive.
Definition _item : ident := 84%positive.
Definition _j : ident := 64%positive.
Definition _k : ident := 65%positive.
Definition _key : ident := 1%positive.
Definition _key1 : ident := 68%positive.
Definition _key2 : ident := 69%positive.
Definition _key_table : ident := 8%positive.
Definition _keys : ident := 118%positive.
Definition _less : ident := 73%positive.
Definition _lookup : ident := 67%positive.
Definition _main : ident := 92%positive.
Definition _malloc : ident := 61%positive.
Definition _mallocN : ident := 62%positive.
Definition _newpri : ident := 79%positive.
Definition _oldpri : ident := 82%positive.
Definition _pq : ident := 71%positive.
Definition _pq_edit_priority : ident := 83%positive.
Definition _pq_free : ident := 91%positive.
Definition _pq_insert : ident := 86%positive.
Definition _pq_insert_nc : ident := 78%positive.
Definition _pq_make : ident := 90%positive.
Definition _pq_remove_min : ident := 87%positive.
Definition _pq_remove_min_nc : ident := 85%positive.
Definition _pq_size : ident := 72%positive.
Definition _prev : ident := 109%positive.
Definition _printPath : ident := 110%positive.
Definition _print_graph : ident := 107%positive.
Definition _printf : ident := 96%positive.
Definition _priority : ident := 2%positive.
Definition _rand : ident := 94%positive.
Definition _random : ident := 100%positive.
Definition _setup : ident := 101%positive.
Definition _sink : ident := 75%positive.
Definition _size : ident := 88%positive.
Definition _srand : ident := 95%positive.
Definition _src : ident := 102%positive.
Definition _structItem : ident := 4%positive.
Definition _structPQ : ident := 9%positive.
Definition _swim : ident := 74%positive.
Definition _table : ident := 80%positive.
Definition _target : ident := 81%positive.
Definition _temp : ident := 117%positive.
Definition _time : ident := 97%positive.
Definition _u : ident := 115%positive.
Definition _t'1 : ident := 123%positive.
Definition _t'10 : ident := 132%positive.
Definition _t'11 : ident := 133%positive.
Definition _t'12 : ident := 134%positive.
Definition _t'2 : ident := 124%positive.
Definition _t'3 : ident := 125%positive.
Definition _t'4 : ident := 126%positive.
Definition _t'5 : ident := 127%positive.
Definition _t'6 : ident := 128%positive.
Definition _t'7 : ident := 129%positive.
Definition _t'8 : ident := 130%positive.
Definition _t'9 : ident := 131%positive.

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
  fn_params := ((_graph, (tptr (tptr tint))) :: (_size, tint) ::
                (_inf, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_random, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'5, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _time (Tfunction (Tcons (tptr tint) Tnil) tint cc_default))
      ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
    (Scall None (Evar _srand (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Ecast (Etempvar _t'1 tint) tuint) :: nil)))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _size tint)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _j (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _j tint)
                             (Etempvar _size tint) tint)
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
                        (Sset _t'4 (Ecast (Etempvar _inf tint) tint))
                        (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))
                      (Ssequence
                        (Sset _t'4 (Ecast (Etempvar _random tint) tint))
                        (Sset _t'3 (Ecast (Etempvar _t'4 tint) tint)))))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Etempvar _graph (tptr (tptr tint)))
                          (Etempvar _i tint) (tptr (tptr tint))) (tptr tint)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                          (Etempvar _j tint) (tptr tint)) tint)
                      (Etempvar _t'3 tint))))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_print_graph := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tptr tint))) :: (_size, tint) ::
                (_inf, tint) :: (_src, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'4, tint) ::
               (_t'3, (tptr tint)) :: (_t'2, tint) :: (_t'1, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _size tint)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Etempvar _size tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _graph (tptr (tptr tint)))
                        (Etempvar _i tint) (tptr (tptr tint))) (tptr tint)))
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                          (Etempvar _j tint) (tptr tint)) tint))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                                   (Etempvar _inf tint) tint)
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_2 (tarray tschar 3)) :: nil))
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Etempvar _graph (tptr (tptr tint)))
                              (Etempvar _i tint) (tptr (tptr tint)))
                            (tptr tint)))
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd (Etempvar _t'3 (tptr tint))
                                (Etempvar _j tint) (tptr tint)) tint))
                          (Scall None
                            (Evar _printf (Tfunction
                                            (Tcons (tptr tschar) Tnil) tint
                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                            ((Evar ___stringlit_1 (tarray tschar 4)) ::
                             (Etempvar _t'4 tint) :: nil))))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_3 (tarray tschar 2)) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_4 (tarray tschar 22)) :: (Etempvar _size tint) ::
     (Etempvar _src tint) :: nil)))
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
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_1 (tarray tschar 4)) :: (Etempvar _curr tint) ::
       nil))))
|}.

Definition f_getPaths := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_src, tint) :: (_dist, (tptr tint)) ::
                (_prev, (tptr tint)) :: (_size, tint) :: (_inf, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _size tint)
                       tint)
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
                  (Ebinop Olt (Etempvar _t'3 tint) (Etempvar _inf tint) tint)
                  tbool)))
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
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_6 (tarray tschar 28)) :: nil)))
|}.

Definition f_getCell := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tptr tint))) :: (_u, tint) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _graph (tptr (tptr tint))) (Etempvar _u tint)
        (tptr (tptr tint))) (tptr tint)))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Etempvar _i tint)
          (tptr tint)) tint))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition f_dijkstra := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (tptr tint))) :: (_src, tint) ::
                (_dist, (tptr tint)) :: (_prev, (tptr tint)) ::
                (_size, tint) :: (_inf, tint) :: nil);
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
      ((Esizeof (Tstruct _structItem noattr) tuint) :: nil))
    (Sset _temp
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _structItem noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Etempvar _size tint) (Esizeof tint tuint) tuint) ::
         nil))
      (Sset _keys (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _pq_make (Tfunction (Tcons tuint Tnil)
                           (tptr (Tstruct _structPQ noattr)) cc_default))
          ((Etempvar _size tint) :: nil))
        (Sset _pq (Etempvar _t'3 (tptr (Tstruct _structPQ noattr)))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _size tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _dist (tptr tint))
                      (Etempvar _i tint) (tptr tint)) tint)
                  (Etempvar _inf tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _prev (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint)
                    (Etempvar _inf tint))
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _pq_insert_nc (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _structPQ noattr))
                                              (Tcons tint (Tcons tint Tnil)))
                                            tuint cc_default))
                      ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
                       (Etempvar _inf tint) :: (Etempvar _i tint) :: nil))
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
                                             (Etempvar _size tint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _getCell (Tfunction
                                                     (Tcons
                                                       (tptr (tptr tint))
                                                       (Tcons tint
                                                         (Tcons tint Tnil)))
                                                     tint cc_default))
                                    ((Etempvar _graph (tptr (tptr tint))) ::
                                     (Etempvar _u tint) ::
                                     (Etempvar _i tint) :: nil))
                                  (Sset _cost (Etempvar _t'6 tint)))
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _cost tint)
                                               (Etempvar _inf tint) tint)
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
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_size, tint) :: (_inf, tint) :: (_src, tint) ::
               (_graph, (tptr (tptr tint))) :: (_prev, (tptr tint)) ::
               (_dist, (tptr tint)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'8, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _time (Tfunction (Tcons (tptr tint) Tnil) tint cc_default))
        ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
      (Scall None
        (Evar _srand (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Ecast (Etempvar _t'1 tint) tuint) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2) (Evar _rand (Tfunction Tnil tint cc_default)) nil)
        (Sset _size
          (Ebinop Oadd (Econst_int (Int.repr 1) tint)
            (Ebinop Omod (Etempvar _t'2 tint) (Econst_int (Int.repr 20) tint)
              tint) tint)))
      (Ssequence
        (Sset _inf
          (Ebinop Osub (Econst_int (Int.repr 2147483647) tint)
            (Ebinop Odiv (Econst_int (Int.repr 2147483647) tint)
              (Etempvar _size tint) tint) tint))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3) (Evar _rand (Tfunction Tnil tint cc_default))
              nil)
            (Sset _src
              (Ebinop Omod (Etempvar _t'3 tint) (Etempvar _size tint) tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default))
                ((Ebinop Omul (Etempvar _size tint)
                   (Esizeof (tptr tint) tuint) tuint) :: nil))
              (Sset _graph (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                   (Etempvar _size tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                        (tptr tvoid) cc_default))
                        ((Ebinop Omul (Etempvar _size tint)
                           (Esizeof tint tuint) tuint) :: nil))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _graph (tptr (tptr tint)))
                            (Etempvar _i tint) (tptr (tptr tint)))
                          (tptr tint)) (Etempvar _t'5 (tptr tvoid)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Scall None
                  (Evar _setup (Tfunction
                                 (Tcons (tptr (tptr tint))
                                   (Tcons tint (Tcons tint Tnil))) tvoid
                                 cc_default))
                  ((Etempvar _graph (tptr (tptr tint))) ::
                   (Etempvar _size tint) :: (Etempvar _inf tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _print_graph (Tfunction
                                         (Tcons (tptr (tptr tint))
                                           (Tcons tint
                                             (Tcons tint (Tcons tint Tnil))))
                                         tvoid cc_default))
                    ((Etempvar _graph (tptr (tptr tint))) ::
                     (Etempvar _size tint) :: (Etempvar _inf tint) ::
                     (Etempvar _src tint) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                        (tptr tvoid) cc_default))
                        ((Ebinop Omul (Etempvar _size tint)
                           (Esizeof tint tuint) tuint) :: nil))
                      (Sset _prev (Etempvar _t'6 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                          (tptr tvoid) cc_default))
                          ((Ebinop Omul (Etempvar _size tint)
                             (Esizeof tint tuint) tuint) :: nil))
                        (Sset _dist (Etempvar _t'7 (tptr tvoid))))
                      (Ssequence
                        (Scall None
                          (Evar _dijkstra (Tfunction
                                            (Tcons (tptr (tptr tint))
                                              (Tcons tint
                                                (Tcons (tptr tint)
                                                  (Tcons (tptr tint)
                                                    (Tcons tint
                                                      (Tcons tint Tnil))))))
                                            tvoid cc_default))
                          ((Etempvar _graph (tptr (tptr tint))) ::
                           (Etempvar _src tint) ::
                           (Etempvar _dist (tptr tint)) ::
                           (Etempvar _prev (tptr tint)) ::
                           (Etempvar _size tint) :: (Etempvar _inf tint) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _getPaths (Tfunction
                                              (Tcons tint
                                                (Tcons (tptr tint)
                                                  (Tcons (tptr tint)
                                                    (Tcons tint
                                                      (Tcons tint Tnil)))))
                                              tvoid cc_default))
                            ((Etempvar _src tint) ::
                             (Etempvar _dist (tptr tint)) ::
                             (Etempvar _prev (tptr tint)) ::
                             (Etempvar _size tint) :: (Etempvar _inf tint) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _free (Tfunction
                                            (Tcons (tptr tvoid) Tnil) tvoid
                                            cc_default))
                              ((Etempvar _prev (tptr tint)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _free (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                                ((Etempvar _dist (tptr tint)) :: nil))
                              (Ssequence
                                (Ssequence
                                  (Sset _i (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tint)
                                                     (Etempvar _size tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _graph (tptr (tptr tint)))
                                              (Etempvar _i tint)
                                              (tptr (tptr tint)))
                                            (tptr tint)))
                                        (Scall None
                                          (Evar _free (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                          ((Etempvar _t'8 (tptr tint)) ::
                                           nil))))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint))))
                                (Ssequence
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _graph (tptr (tptr tint))) ::
                                     nil))
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _structItem Struct
   ((_key, tuint) :: (_priority, tint) :: (_data, tint) :: nil)
   noattr ::
 Composite _structPQ Struct
   ((_capacity, tuint) :: (_first_available, tuint) ::
    (_heap_cells, (tptr (Tstruct _structItem noattr))) ::
    (_key_table, (tptr tuint)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_4, Gvar v___stringlit_4) ::
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
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
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_time,
   Gfun(External (EF_external "time"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tint) Tnil) tint cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_pq_remove_min_nc,
   Gfun(External (EF_external "pq_remove_min_nc"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr))
       (Tcons (tptr (Tstruct _structItem noattr)) Tnil)) tvoid cc_default)) ::
 (_pq_insert_nc,
   Gfun(External (EF_external "pq_insert_nc"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) (Tcons tint (Tcons tint Tnil)))
     tuint cc_default)) ::
 (_pq_edit_priority,
   Gfun(External (EF_external "pq_edit_priority"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) (Tcons tint (Tcons tint Tnil)))
     tvoid cc_default)) ::
 (_pq_size,
   Gfun(External (EF_external "pq_size"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _structPQ noattr)) Tnil) tuint cc_default)) ::
 (_pq_make,
   Gfun(External (EF_external "pq_make"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) (tptr (Tstruct _structPQ noattr)) cc_default)) ::
 (_pq_free,
   Gfun(External (EF_external "pq_free"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
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
 _printf :: _srand :: _rand :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


