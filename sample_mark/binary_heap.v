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
  Definition source_file := "binary_heap.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 16%positive.
Definition ___builtin_annot_intval : ident := 17%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 8%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 58%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fmadd : ident := 50%positive.
Definition ___builtin_fmax : ident := 48%positive.
Definition ___builtin_fmin : ident := 49%positive.
Definition ___builtin_fmsub : ident := 51%positive.
Definition ___builtin_fnmadd : ident := 52%positive.
Definition ___builtin_fnmsub : ident := 53%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 18%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_read16_reversed : ident := 54%positive.
Definition ___builtin_read32_reversed : ident := 55%positive.
Definition ___builtin_sel : ident := 15%positive.
Definition ___builtin_va_arg : ident := 20%positive.
Definition ___builtin_va_copy : ident := 21%positive.
Definition ___builtin_va_end : ident := 22%positive.
Definition ___builtin_va_start : ident := 19%positive.
Definition ___builtin_write16_reversed : ident := 56%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 27%positive.
Definition ___compcert_i64_dtou : ident := 28%positive.
Definition ___compcert_i64_sar : ident := 39%positive.
Definition ___compcert_i64_sdiv : ident := 33%positive.
Definition ___compcert_i64_shl : ident := 37%positive.
Definition ___compcert_i64_shr : ident := 38%positive.
Definition ___compcert_i64_smod : ident := 35%positive.
Definition ___compcert_i64_smulh : ident := 40%positive.
Definition ___compcert_i64_stod : ident := 29%positive.
Definition ___compcert_i64_stof : ident := 31%positive.
Definition ___compcert_i64_udiv : ident := 34%positive.
Definition ___compcert_i64_umod : ident := 36%positive.
Definition ___compcert_i64_umulh : ident := 41%positive.
Definition ___compcert_i64_utod : ident := 30%positive.
Definition ___compcert_i64_utof : ident := 32%positive.
Definition ___compcert_va_composite : ident := 26%positive.
Definition ___compcert_va_float64 : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 23%positive.
Definition ___compcert_va_int64 : ident := 24%positive.
Definition ___compound : ident := 82%positive.
Definition __res : ident := 78%positive.
Definition __res__1 : ident := 79%positive.
Definition _arr : ident := 62%positive.
Definition _capacity : ident := 4%positive.
Definition _data : ident := 2%positive.
Definition _exch : ident := 64%positive.
Definition _first_available : ident := 5%positive.
Definition _heap_cells : ident := 6%positive.
Definition _insert : ident := 76%positive.
Definition _item : ident := 77%positive.
Definition _j : ident := 60%positive.
Definition _k : ident := 61%positive.
Definition _last_used : ident := 67%positive.
Definition _less : ident := 65%positive.
Definition _main : ident := 84%positive.
Definition _make : ident := 83%positive.
Definition _mallocN : ident := 59%positive.
Definition _pq : ident := 69%positive.
Definition _pq__1 : ident := 70%positive.
Definition _pq__2 : ident := 71%positive.
Definition _pq__3 : ident := 75%positive.
Definition _priority : ident := 1%positive.
Definition _remove_min : ident := 80%positive.
Definition _sink : ident := 68%positive.
Definition _size : ident := 81%positive.
Definition _structItem : ident := 3%positive.
Definition _structPQ : ident := 7%positive.
Definition _swim : ident := 66%positive.
Definition _t : ident := 63%positive.
Definition _x : ident := 72%positive.
Definition _x__1 : ident := 73%positive.
Definition _x__2 : ident := 74%positive.
Definition _t'1 : ident := 85%positive.
Definition _t'10 : ident := 94%positive.
Definition _t'11 : ident := 95%positive.
Definition _t'2 : ident := 86%positive.
Definition _t'3 : ident := 87%positive.
Definition _t'4 : ident := 88%positive.
Definition _t'5 : ident := 89%positive.
Definition _t'6 : ident := 90%positive.
Definition _t'7 : ident := 91%positive.
Definition _t'8 : ident := 92%positive.
Definition _t'9 : ident := 93%positive.

Definition f_exch := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_j, tuint) :: (_k, tuint) ::
                (_arr, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_vars := ((_t, (Tstruct _structItem noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _t (Tstruct _structItem noattr))
    (Ederef
      (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
        (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
      (Tstruct _structItem noattr)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr))
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr)))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr)) (Evar _t (Tstruct _structItem noattr)))))
|}.

Definition f_less := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_j, tuint) :: (_k, tuint) ::
                (_arr, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr)) _priority tint))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef
          (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
            (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
          (Tstruct _structItem noattr)) _priority tint))
    (Sreturn (Some (Ebinop Ole (Etempvar _t'1 tint) (Etempvar _t'2 tint)
                     tint)))))
|}.

Definition f_swim := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, tuint) :: (_arr, (tptr (Tstruct _structItem noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _k tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _less (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil))) tint cc_default))
            ((Ebinop Odiv
               (Ebinop Osub (Etempvar _k tuint)
                 (Econst_int (Int.repr 1) tint) tuint)
               (Econst_int (Int.repr 2) tint) tuint) ::
             (Etempvar _k tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
          (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
    (Ssequence
      (Scall None
        (Evar _exch (Tfunction
                      (Tcons tuint
                        (Tcons tuint
                          (Tcons (tptr (Tstruct _structItem noattr)) Tnil)))
                      tvoid cc_default))
        ((Etempvar _k tuint) ::
         (Ebinop Odiv
           (Ebinop Osub (Etempvar _k tuint) (Econst_int (Int.repr 1) tint)
             tuint) (Econst_int (Int.repr 2) tint) tuint) ::
         (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
      (Sset _k
        (Ebinop Odiv
          (Ebinop Osub (Etempvar _k tuint) (Econst_int (Int.repr 1) tint)
            tuint) (Econst_int (Int.repr 2) tint) tuint))))
  Sskip)
|}.

Definition f_sink := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, tuint) :: (_arr, (tptr (Tstruct _structItem noattr))) ::
                (_last_used, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tuint) :: (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Swhile
  (Ebinop Ole
    (Ebinop Oadd
      (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _k tuint) tuint)
      (Econst_int (Int.repr 1) tint) tuint) (Etempvar _last_used tuint) tint)
  (Ssequence
    (Sset _j
      (Ebinop Oadd
        (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _k tuint)
          tuint) (Econst_int (Int.repr 1) tint) tuint))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                       (Etempvar _last_used tuint) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _less (Tfunction
                            (Tcons tuint
                              (Tcons tuint
                                (Tcons (tptr (Tstruct _structItem noattr))
                                  Tnil))) tint cc_default))
              ((Ebinop Oadd (Etempvar _j tuint)
                 (Econst_int (Int.repr 1) tint) tuint) ::
               (Etempvar _j tuint) ::
               (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
            (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
          (Sset _t'1 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sset _j
            (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          Sskip))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _less (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil))) tint cc_default))
            ((Etempvar _j tuint) :: (Etempvar _k tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
          (Sifthenelse (Etempvar _t'3 tint) Sbreak Sskip))
        (Ssequence
          (Scall None
            (Evar _exch (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil))) tvoid cc_default))
            ((Etempvar _k tuint) :: (Etempvar _j tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
          (Sset _k (Etempvar _j tuint)))))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pq, tuint) :: (_pq__1, tuint) :: (_pq__2, tuint) ::
                (_x, tuint) :: (_x__1, tuint) :: nil);
  fn_vars := ((_x__2, (tarray tuint 2)) :: (_pq__3, (tarray tuint 3)) :: nil);
  fn_temps := ((_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _structItem noattr))) ::
               (_t'3, (tptr (Tstruct _structItem noattr))) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _pq tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
        (Etempvar _pq__1 tuint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
              (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
          (Etempvar _pq__2 tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _x__2 (tarray tuint 2))
                (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
            (Etempvar _x tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _x__2 (tarray tuint 2))
                (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
            (Etempvar _x__1 tuint))))))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef
            (Ecast
              (Eaddrof (Evar _pq__3 (tarray tuint 3))
                (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _first_available tuint))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef
              (Ecast
                (Eaddrof (Evar _pq__3 (tarray tuint 3))
                  (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
              (Tstruct _structPQ noattr)) _capacity tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint) (Etempvar _t'7 tuint)
                       tint)
          (Sreturn None)
          Sskip)))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef
              (Ecast
                (Eaddrof (Evar _pq__3 (tarray tuint 3))
                  (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
              (Tstruct _structPQ noattr)) _heap_cells
            (tptr (Tstruct _structItem noattr))))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Ecast
                  (Eaddrof (Evar _pq__3 (tarray tuint 3))
                    (tptr (tarray tuint 3)))
                  (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Etempvar _t'4 (tptr (Tstruct _structItem noattr)))
                (Etempvar _t'5 tuint) (tptr (Tstruct _structItem noattr)))
              (Tstruct _structItem noattr))
            (Ederef
              (Ecast
                (Eaddrof (Evar _x__2 (tarray tuint 2))
                  (tptr (tarray tuint 2)))
                (tptr (Tstruct _structItem noattr)))
              (Tstruct _structItem noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Ecast
                  (Eaddrof (Evar _pq__3 (tarray tuint 3))
                    (tptr (tarray tuint 3)))
                  (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Ecast
                    (Eaddrof (Evar _pq__3 (tarray tuint 3))
                      (tptr (tarray tuint 3)))
                    (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _heap_cells
                (tptr (Tstruct _structItem noattr))))
            (Scall None
              (Evar _swim (Tfunction
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil)) tvoid cc_default))
              ((Etempvar _t'2 tuint) ::
               (Etempvar _t'3 (tptr (Tstruct _structItem noattr))) :: nil))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Ecast
                  (Eaddrof (Evar _pq__3 (tarray tuint 3))
                    (tptr (tarray tuint 3)))
                  (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint))
          (Sassign
            (Efield
              (Ederef
                (Ecast
                  (Eaddrof (Evar _pq__3 (tarray tuint 3))
                    (tptr (tarray tuint 3)))
                  (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint)
            (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))))
|}.

Definition f_remove_min := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_pq, tuint) :: (_pq__1, tuint) :: (_pq__2, tuint) :: nil);
  fn_vars := ((_item, (Tstruct _structItem noattr)) ::
              (_pq__3, (tarray tuint 3)) :: nil);
  fn_temps := ((__res, (tptr tuchar)) :: (__res__1, (tptr tuchar)) ::
               (_t'11, tuint) ::
               (_t'10, (tptr (Tstruct _structItem noattr))) ::
               (_t'9, tulong) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _structItem noattr))) ::
               (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _structItem noattr))) ::
               (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _structItem noattr))) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _pq tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
        (Etempvar _pq__1 tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Etempvar _pq__2 tuint))))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef
            (Ecast
              (Eaddrof (Evar _pq__3 (tarray tuint 3))
                (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _first_available tuint))
      (Sassign
        (Efield
          (Ederef
            (Ecast
              (Eaddrof (Evar _pq__3 (tarray tuint 3))
                (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _first_available tuint)
        (Ebinop Osub (Etempvar _t'11 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef
              (Ecast
                (Eaddrof (Evar _pq__3 (tarray tuint 3))
                  (tptr (tarray tuint 3))) (tptr (Tstruct _structPQ noattr)))
              (Tstruct _structPQ noattr)) _first_available tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Ecast
                      (Eaddrof (Evar _pq__3 (tarray tuint 3))
                        (tptr (tarray tuint 3)))
                      (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _heap_cells
                  (tptr (Tstruct _structItem noattr))))
              (Sset __res__1
                (Ecast
                  (Ebinop Oadd
                    (Etempvar _t'10 (tptr (Tstruct _structItem noattr)))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _structItem noattr))) (tptr tuchar))))
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ecast (Etempvar __res__1 (tptr tuchar)) (tptr tulong))
                  tulong))
              (Sreturn (Some (Etempvar _t'9 tulong)))))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef
                (Ecast
                  (Eaddrof (Evar _pq__3 (tarray tuint 3))
                    (tptr (tarray tuint 3)))
                  (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef
                  (Ecast
                    (Eaddrof (Evar _pq__3 (tarray tuint 3))
                      (tptr (tarray tuint 3)))
                    (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _heap_cells
                (tptr (Tstruct _structItem noattr))))
            (Scall None
              (Evar _exch (Tfunction
                            (Tcons tuint
                              (Tcons tuint
                                (Tcons (tptr (Tstruct _structItem noattr))
                                  Tnil))) tvoid cc_default))
              ((Econst_int (Int.repr 0) tint) :: (Etempvar _t'6 tuint) ::
               (Etempvar _t'7 (tptr (Tstruct _structItem noattr))) :: nil))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Ecast
                    (Eaddrof (Evar _pq__3 (tarray tuint 3))
                      (tptr (tarray tuint 3)))
                    (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _heap_cells
                (tptr (Tstruct _structItem noattr))))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef
                    (Ecast
                      (Eaddrof (Evar _pq__3 (tarray tuint 3))
                        (tptr (tarray tuint 3)))
                      (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _first_available tuint))
              (Sassign (Evar _item (Tstruct _structItem noattr))
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _t'4 (tptr (Tstruct _structItem noattr)))
                    (Etempvar _t'5 tuint)
                    (tptr (Tstruct _structItem noattr)))
                  (Tstruct _structItem noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef
                    (Ecast
                      (Eaddrof (Evar _pq__3 (tarray tuint 3))
                        (tptr (tarray tuint 3)))
                      (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _heap_cells
                  (tptr (Tstruct _structItem noattr))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Ecast
                        (Eaddrof (Evar _pq__3 (tarray tuint 3))
                          (tptr (tarray tuint 3)))
                        (tptr (Tstruct _structPQ noattr)))
                      (Tstruct _structPQ noattr)) _first_available tuint))
                (Scall None
                  (Evar _sink (Tfunction
                                (Tcons tuint
                                  (Tcons (tptr (Tstruct _structItem noattr))
                                    (Tcons tuint Tnil))) tvoid cc_default))
                  ((Econst_int (Int.repr 0) tint) ::
                   (Etempvar _t'2 (tptr (Tstruct _structItem noattr))) ::
                   (Ebinop Osub (Etempvar _t'3 tuint)
                     (Econst_int (Int.repr 1) tint) tuint) :: nil))))
            (Ssequence
              (Sset __res
                (Ecast
                  (Eaddrof (Evar _item (Tstruct _structItem noattr))
                    (tptr (Tstruct _structItem noattr))) (tptr tuchar)))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ecast (Etempvar __res (tptr tuchar)) (tptr tulong))
                    tulong))
                (Sreturn (Some (Etempvar _t'1 tulong)))))))))))
|}.

Definition f_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, tuint) :: (_pq__1, tuint) :: (_pq__2, tuint) :: nil);
  fn_vars := ((_pq__3, (tarray tuint 3)) :: nil);
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _pq tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
        (Etempvar _pq__1 tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Etempvar _pq__2 tuint))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef
          (Ecast
            (Eaddrof (Evar _pq__3 (tarray tuint 3)) (tptr (tarray tuint 3)))
            (tptr (Tstruct _structPQ noattr))) (Tstruct _structPQ noattr))
        _first_available tuint))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_capacity := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, tuint) :: (_pq__1, tuint) :: (_pq__2, tuint) :: nil);
  fn_vars := ((_pq__3, (tarray tuint 3)) :: nil);
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _pq tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
        (Etempvar _pq__1 tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _pq__3 (tarray tuint 3))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Etempvar _pq__2 tuint))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef
          (Ecast
            (Eaddrof (Evar _pq__3 (tarray tuint 3)) (tptr (tarray tuint 3)))
            (tptr (Tstruct _structPQ noattr))) (Tstruct _structPQ noattr))
        _capacity tuint))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_make := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _structPQ noattr))) :: nil);
  fn_vars := ((___compound, (Tstruct _structPQ noattr)) :: nil);
  fn_temps := ((_arr, (tptr (Tstruct _structItem noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Esizeof (Tstruct _structItem noattr) tuint)
         (Econst_int (Int.repr 8) tint) tuint) :: nil))
    (Sset _arr
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _structItem noattr)))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sassign
            (Efield (Evar ___compound (Tstruct _structPQ noattr)) _capacity
              tuint) (Econst_int (Int.repr 8) tint))
          (Sassign
            (Efield (Evar ___compound (Tstruct _structPQ noattr))
              _first_available tuint) (Econst_int (Int.repr 0) tint)))
        (Sassign
          (Efield (Evar ___compound (Tstruct _structPQ noattr)) _heap_cells
            (tptr (Tstruct _structItem noattr)))
          (Etempvar _arr (tptr (Tstruct _structItem noattr)))))
      (Sassign
        (Ederef (Etempvar __res (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr))
        (Evar ___compound (Tstruct _structPQ noattr))))
    (Sreturn None)))
|}.

Definition composites : list composite_definition :=
(Composite _structItem Struct
   ((_priority, tint) :: (_data, (tptr tvoid)) :: nil)
   noattr ::
 Composite _structPQ Struct
   ((_capacity, tuint) :: (_first_available, tuint) ::
    (_heap_cells, (tptr (Tstruct _structItem noattr))) :: nil)
   noattr :: nil).

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
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_exch, Gfun(Internal f_exch)) :: (_less, Gfun(Internal f_less)) ::
 (_swim, Gfun(Internal f_swim)) :: (_sink, Gfun(Internal f_sink)) ::
 (_insert, Gfun(Internal f_insert)) ::
 (_remove_min, Gfun(Internal f_remove_min)) ::
 (_size, Gfun(Internal f_size)) :: (_capacity, Gfun(Internal f_capacity)) ::
 (_make, Gfun(Internal f_make)) :: nil).

Definition public_idents : list ident :=
(_make :: _capacity :: _size :: _remove_min :: _insert :: _sink :: _swim ::
 _less :: _exch :: _mallocN :: ___builtin_debug ::
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

