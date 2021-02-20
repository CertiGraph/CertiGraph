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
  Definition source_file := "prim/prim2.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 9%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 1%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 43%positive.
Definition ___builtin_fmax : ident := 41%positive.
Definition ___builtin_fmin : ident := 42%positive.
Definition ___builtin_fmsub : ident := 44%positive.
Definition ___builtin_fnmadd : ident := 45%positive.
Definition ___builtin_fnmsub : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 6%positive.
Definition ___builtin_membar : ident := 11%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_read16_reversed : ident := 47%positive.
Definition ___builtin_read32_reversed : ident := 48%positive.
Definition ___builtin_sel : ident := 8%positive.
Definition ___builtin_va_arg : ident := 13%positive.
Definition ___builtin_va_copy : ident := 14%positive.
Definition ___builtin_va_end : ident := 15%positive.
Definition ___builtin_va_start : ident := 12%positive.
Definition ___builtin_write16_reversed : ident := 49%positive.
Definition ___builtin_write32_reversed : ident := 50%positive.
Definition ___compcert_i64_dtos : ident := 20%positive.
Definition ___compcert_i64_dtou : ident := 21%positive.
Definition ___compcert_i64_sar : ident := 32%positive.
Definition ___compcert_i64_sdiv : ident := 26%positive.
Definition ___compcert_i64_shl : ident := 30%positive.
Definition ___compcert_i64_shr : ident := 31%positive.
Definition ___compcert_i64_smod : ident := 28%positive.
Definition ___compcert_i64_smulh : ident := 33%positive.
Definition ___compcert_i64_stod : ident := 22%positive.
Definition ___compcert_i64_stof : ident := 24%positive.
Definition ___compcert_i64_udiv : ident := 27%positive.
Definition ___compcert_i64_umod : ident := 29%positive.
Definition ___compcert_i64_umulh : ident := 34%positive.
Definition ___compcert_i64_utod : ident := 23%positive.
Definition ___compcert_i64_utof : ident := 25%positive.
Definition ___compcert_va_composite : ident := 19%positive.
Definition ___compcert_va_float64 : ident := 18%positive.
Definition ___compcert_va_int32 : ident := 16%positive.
Definition ___compcert_va_int64 : ident := 17%positive.
Definition _a : ident := 74%positive.
Definition _adjustWeight : ident := 66%positive.
Definition _check_symmetric_matrix : ident := 73%positive.
Definition _cost : ident := 82%positive.
Definition _free : ident := 52%positive.
Definition _freeN : ident := 70%positive.
Definition _freePQ : ident := 68%positive.
Definition _getCell : ident := 79%positive.
Definition _graph : ident := 71%positive.
Definition _i : ident := 63%positive.
Definition _inf : ident := 60%positive.
Definition _init : ident := 56%positive.
Definition _initialise_list : ident := 77%positive.
Definition _initialise_matrix : ident := 75%positive.
Definition _j : ident := 72%positive.
Definition _key : ident := 83%positive.
Definition _list : ident := 76%positive.
Definition _main : ident := 69%positive.
Definition _mallocN : ident := 53%positive.
Definition _minVertex : ident := 61%positive.
Definition _minWeight : ident := 62%positive.
Definition _newWeight : ident := 65%positive.
Definition _out : ident := 84%positive.
Definition _parent : ident := 81%positive.
Definition _popMin : ident := 64%positive.
Definition _pq : ident := 55%positive.
Definition _pq_emp : ident := 67%positive.
Definition _prim : ident := 87%positive.
Definition _push : ident := 59%positive.
Definition _r : ident := 80%positive.
Definition _size : ident := 54%positive.
Definition _u : ident := 78%positive.
Definition _v : ident := 85%positive.
Definition _v__1 : ident := 86%positive.
Definition _vertex : ident := 57%positive.
Definition _weight : ident := 58%positive.
Definition _t'1 : ident := 88%positive.
Definition _t'2 : ident := 89%positive.
Definition _t'3 : ident := 90%positive.
Definition _t'4 : ident := 91%positive.
Definition _t'5 : ident := 92%positive.
Definition _t'6 : ident := 93%positive.
Definition _t'7 : ident := 94%positive.
Definition _t'8 : ident := 95%positive.

Definition f_check_symmetric_matrix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr tint)) :: nil);
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
                    (Ebinop Oadd (Etempvar _graph (tptr tint))
                      (Ebinop Oadd
                        (Ebinop Omul (Etempvar _i tint)
                          (Econst_int (Int.repr 8) tint) tint)
                        (Etempvar _j tint) tint) (tptr tint)) tint))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _graph (tptr tint))
                        (Ebinop Oadd
                          (Ebinop Omul (Etempvar _j tint)
                            (Econst_int (Int.repr 8) tint) tint)
                          (Etempvar _i tint) tint) (tptr tint)) tint))
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
  fn_params := ((_graph, (tptr tint)) :: (_a, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Ebinop Omul (Econst_int (Int.repr 8) tint)
                       (Econst_int (Int.repr 8) tint) tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _graph (tptr tint)) (Etempvar _i tint)
            (tptr tint)) tint) (Etempvar _a tint)))
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
  fn_params := ((_graph, (tptr tint)) :: (_u, tint) :: (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _graph (tptr tint))
        (Ebinop Oadd
          (Ebinop Omul (Etempvar _u tint) (Econst_int (Int.repr 8) tint)
            tint) (Etempvar _i tint) tint) (tptr tint)) tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_prim := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr tint)) :: (_r, tint) ::
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
                                                       (Tcons (tptr tint)
                                                         (Tcons tint
                                                           (Tcons tint Tnil)))
                                                       tint cc_default))
                                      ((Etempvar _graph (tptr tint)) ::
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
((___builtin_bswap64,
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
 (_init,
   Gfun(External (EF_external "init"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tint) cc_default)) ::
 (_push,
   Gfun(External (EF_external "push"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tvoid cc_default)) ::
 (_popMin,
   Gfun(External (EF_external "popMin"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tint cc_default)) ::
 (_adjustWeight,
   Gfun(External (EF_external "adjustWeight"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tvoid cc_default)) ::
 (_pq_emp,
   Gfun(External (EF_external "pq_emp"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tint cc_default)) ::
 (_freePQ,
   Gfun(External (EF_external "freePQ"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
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
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


