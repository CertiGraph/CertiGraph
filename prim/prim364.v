From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "prim/prim3.c".
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
Definition _a : ident := $"a".
Definition _adjustWeight : ident := $"adjustWeight".
Definition _check_symmetric_matrix : ident := $"check_symmetric_matrix".
Definition _cost : ident := $"cost".
Definition _freePQ : ident := $"freePQ".
Definition _getCell : ident := $"getCell".
Definition _graph : ident := $"graph".
Definition _i : ident := $"i".
Definition _init : ident := $"init".
Definition _initialise_list : ident := $"initialise_list".
Definition _initialise_matrix : ident := $"initialise_matrix".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _list : ident := $"list".
Definition _main : ident := $"main".
Definition _out : ident := $"out".
Definition _parent : ident := $"parent".
Definition _popMin : ident := $"popMin".
Definition _pq : ident := $"pq".
Definition _pq_emp : ident := $"pq_emp".
Definition _prim : ident := $"prim".
Definition _push : ident := $"push".
Definition _r : ident := $"r".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _v__1 : ident := $"v__1".
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
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
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
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


