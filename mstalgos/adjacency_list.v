From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "verif/adjacency_list.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 10%positive.
Definition ___builtin_annot : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 20%positive.
Definition ___builtin_bswap : ident := 12%positive.
Definition ___builtin_bswap16 : ident := 14%positive.
Definition ___builtin_bswap32 : ident := 13%positive.
Definition ___builtin_bswap64 : ident := 11%positive.
Definition ___builtin_clz : ident := 45%positive.
Definition ___builtin_clzl : ident := 46%positive.
Definition ___builtin_clzll : ident := 47%positive.
Definition ___builtin_ctz : ident := 48%positive.
Definition ___builtin_ctzl : ident := 49%positive.
Definition ___builtin_ctzll : ident := 50%positive.
Definition ___builtin_debug : ident := 61%positive.
Definition ___builtin_fabs : ident := 15%positive.
Definition ___builtin_fmadd : ident := 53%positive.
Definition ___builtin_fmax : ident := 51%positive.
Definition ___builtin_fmin : ident := 52%positive.
Definition ___builtin_fmsub : ident := 54%positive.
Definition ___builtin_fnmadd : ident := 55%positive.
Definition ___builtin_fnmsub : ident := 56%positive.
Definition ___builtin_fsqrt : ident := 16%positive.
Definition ___builtin_membar : ident := 21%positive.
Definition ___builtin_memcpy_aligned : ident := 17%positive.
Definition ___builtin_read16_reversed : ident := 57%positive.
Definition ___builtin_read32_reversed : ident := 58%positive.
Definition ___builtin_sel : ident := 18%positive.
Definition ___builtin_va_arg : ident := 23%positive.
Definition ___builtin_va_copy : ident := 24%positive.
Definition ___builtin_va_end : ident := 25%positive.
Definition ___builtin_va_start : ident := 22%positive.
Definition ___builtin_write16_reversed : ident := 59%positive.
Definition ___builtin_write32_reversed : ident := 60%positive.
Definition ___compcert_i64_dtos : ident := 30%positive.
Definition ___compcert_i64_dtou : ident := 31%positive.
Definition ___compcert_i64_sar : ident := 42%positive.
Definition ___compcert_i64_sdiv : ident := 36%positive.
Definition ___compcert_i64_shl : ident := 40%positive.
Definition ___compcert_i64_shr : ident := 41%positive.
Definition ___compcert_i64_smod : ident := 38%positive.
Definition ___compcert_i64_smulh : ident := 43%positive.
Definition ___compcert_i64_stod : ident := 32%positive.
Definition ___compcert_i64_stof : ident := 34%positive.
Definition ___compcert_i64_udiv : ident := 37%positive.
Definition ___compcert_i64_umod : ident := 39%positive.
Definition ___compcert_i64_umulh : ident := 44%positive.
Definition ___compcert_i64_utod : ident := 33%positive.
Definition ___compcert_i64_utof : ident := 35%positive.
Definition ___compcert_va_composite : ident := 29%positive.
Definition ___compcert_va_float64 : ident := 28%positive.
Definition ___compcert_va_int32 : ident := 26%positive.
Definition ___compcert_va_int64 : ident := 27%positive.
Definition _adjlist_create_graph : ident := 70%positive.
Definition _adjlist_free_graph : ident := 71%positive.
Definition _adjlist_graph : ident := 9%positive.
Definition _adjlist_insert_edge : ident := 75%positive.
Definition _edgelist : ident := 69%positive.
Definition _edgelists : ident := 8%positive.
Definition _elem : ident := 3%positive.
Definition _free_pqueue : ident := 63%positive.
Definition _graph : ident := 67%positive.
Definition _head : ident := 5%positive.
Definition _i : ident := 68%positive.
Definition _key : ident := 2%positive.
Definition _main : ident := 76%positive.
Definition _maybe_free : ident := 66%positive.
Definition _next : ident := 4%positive.
Definition _num_vertices : ident := 7%positive.
Definition _pqueue : ident := 6%positive.
Definition _pqueue_insert : ident := 64%positive.
Definition _pqueue_new : ident := 62%positive.
Definition _surely_malloc : ident := 65%positive.
Definition _u : ident := 72%positive.
Definition _v : ident := 73%positive.
Definition _val : ident := 1%positive.
Definition _weight : ident := 74%positive.
Definition _t'1 : ident := 77%positive.
Definition _t'2 : ident := 78%positive.
Definition _t'3 : ident := 79%positive.

Definition f_adjlist_create_graph := {|
  fn_return := (tptr (Tstruct _adjlist_graph noattr));
  fn_callconv := cc_default;
  fn_params := ((_num_vertices, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_graph, (tptr (Tstruct _adjlist_graph noattr))) ::
               (_edgelists, (tptr (tptr (Tstruct _pqueue noattr)))) ::
               (_i, tint) :: (_edgelist, (tptr (Tstruct _pqueue noattr))) ::
               (_t'3, (tptr (Tstruct _pqueue noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _adjlist_graph noattr) tuint) :: nil))
    (Sset _graph
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _adjlist_graph noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof (tptr (Tstruct _pqueue noattr)) tuint)
           (Etempvar _num_vertices tint) tuint) :: nil))
      (Sset _edgelists
        (Ecast (Etempvar _t'2 (tptr tvoid))
          (tptr (tptr (Tstruct _pqueue noattr))))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Etempvar _num_vertices tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _pqueue_new (Tfunction Tnil
                                      (tptr (Tstruct _pqueue noattr))
                                      cc_default)) nil)
                (Sset _edgelist
                  (Etempvar _t'3 (tptr (Tstruct _pqueue noattr)))))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _edgelists (tptr (tptr (Tstruct _pqueue noattr))))
                    (Etempvar _i tint)
                    (tptr (tptr (Tstruct _pqueue noattr))))
                  (tptr (Tstruct _pqueue noattr)))
                (Etempvar _edgelist (tptr (Tstruct _pqueue noattr))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
              (Tstruct _adjlist_graph noattr)) _num_vertices tint)
          (Etempvar _num_vertices tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
                (Tstruct _adjlist_graph noattr)) _edgelists
              (tptr (tptr (Tstruct _pqueue noattr))))
            (Etempvar _edgelists (tptr (tptr (Tstruct _pqueue noattr)))))
          (Sreturn (Some (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr))))))))))
|}.

Definition f_adjlist_free_graph := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (Tstruct _adjlist_graph noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_edgelist, (tptr (Tstruct _pqueue noattr))) ::
               (_t'2, tint) ::
               (_t'1, (tptr (tptr (Tstruct _pqueue noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
                (Tstruct _adjlist_graph noattr)) _num_vertices tint))
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _t'2 tint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
                  (Tstruct _adjlist_graph noattr)) _edgelists
                (tptr (tptr (Tstruct _pqueue noattr)))))
            (Sset _edgelist
              (Ederef
                (Ebinop Oadd
                  (Etempvar _t'1 (tptr (tptr (Tstruct _pqueue noattr))))
                  (Etempvar _i tint) (tptr (tptr (Tstruct _pqueue noattr))))
                (tptr (Tstruct _pqueue noattr)))))
          (Scall None
            (Evar _free_pqueue (Tfunction
                                 (Tcons (tptr (Tstruct _pqueue noattr)) Tnil)
                                 tvoid cc_default))
            ((Etempvar _edgelist (tptr (Tstruct _pqueue noattr))) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _maybe_free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _graph (tptr (Tstruct _adjlist_graph noattr))) :: nil)))
|}.

Definition f_adjlist_insert_edge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph, (tptr (Tstruct _adjlist_graph noattr))) ::
                (_u, tint) :: (_v, tint) :: (_weight, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_edgelist, (tptr (Tstruct _pqueue noattr))) ::
               (_t'2, (tptr (tptr (Tstruct _pqueue noattr)))) ::
               (_t'1, (tptr (tptr (Tstruct _pqueue noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
          (Tstruct _adjlist_graph noattr)) _edgelists
        (tptr (tptr (Tstruct _pqueue noattr)))))
    (Sset _edgelist
      (Ederef
        (Ebinop Oadd (Etempvar _t'2 (tptr (tptr (Tstruct _pqueue noattr))))
          (Etempvar _u tint) (tptr (tptr (Tstruct _pqueue noattr))))
        (tptr (Tstruct _pqueue noattr)))))
  (Ssequence
    (Scall None
      (Evar _pqueue_insert (Tfunction
                             (Tcons (tptr (Tstruct _pqueue noattr))
                               (Tcons tint (Tcons tint Tnil))) tvoid
                             cc_default))
      ((Etempvar _edgelist (tptr (Tstruct _pqueue noattr))) ::
       (Etempvar _v tint) :: (Etempvar _weight tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _graph (tptr (Tstruct _adjlist_graph noattr)))
              (Tstruct _adjlist_graph noattr)) _edgelists
            (tptr (tptr (Tstruct _pqueue noattr)))))
        (Sset _edgelist
          (Ederef
            (Ebinop Oadd
              (Etempvar _t'1 (tptr (tptr (Tstruct _pqueue noattr))))
              (Etempvar _v tint) (tptr (tptr (Tstruct _pqueue noattr))))
            (tptr (Tstruct _pqueue noattr)))))
      (Scall None
        (Evar _pqueue_insert (Tfunction
                               (Tcons (tptr (Tstruct _pqueue noattr))
                                 (Tcons tint (Tcons tint Tnil))) tvoid
                               cc_default))
        ((Etempvar _edgelist (tptr (Tstruct _pqueue noattr))) ::
         (Etempvar _u tint) :: (Etempvar _weight tint) :: nil)))))
|}.

Definition composites : list composite_definition :=
(Composite _elem Struct
   ((_val, tint) :: (_key, tint) :: (_next, (tptr (Tstruct _elem noattr))) ::
    nil)
   noattr ::
 Composite _pqueue Struct
   ((_head, (tptr (Tstruct _elem noattr))) :: nil)
   noattr ::
 Composite _adjlist_graph Struct
   ((_num_vertices, tint) ::
    (_edgelists, (tptr (tptr (Tstruct _pqueue noattr)))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
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
 (_pqueue_new,
   Gfun(External (EF_external "pqueue_new"
                   (mksignature nil AST.Tint cc_default)) Tnil
     (tptr (Tstruct _pqueue noattr)) cc_default)) ::
 (_free_pqueue,
   Gfun(External (EF_external "free_pqueue"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _pqueue noattr)) Tnil) tvoid cc_default)) ::
 (_pqueue_insert,
   Gfun(External (EF_external "pqueue_insert"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _pqueue noattr)) (Tcons tint (Tcons tint Tnil)))
     tvoid cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_maybe_free,
   Gfun(External (EF_external "maybe_free"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_adjlist_create_graph, Gfun(Internal f_adjlist_create_graph)) ::
 (_adjlist_free_graph, Gfun(Internal f_adjlist_free_graph)) ::
 (_adjlist_insert_edge, Gfun(Internal f_adjlist_insert_edge)) :: nil).

Definition public_idents : list ident :=
(_adjlist_insert_edge :: _adjlist_free_graph :: _adjlist_create_graph ::
 _maybe_free :: _surely_malloc :: _pqueue_insert :: _free_pqueue ::
 _pqueue_new :: ___builtin_debug :: ___builtin_write32_reversed ::
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
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


