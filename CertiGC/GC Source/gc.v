
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 13%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_bswap : ident := 37%positive.
Definition ___builtin_bswap16 : ident := 39%positive.
Definition ___builtin_bswap32 : ident := 38%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 58%positive.
Definition ___builtin_fabs : ident := 11%positive.
Definition ___builtin_fmadd : ident := 49%positive.
Definition ___builtin_fmax : ident := 47%positive.
Definition ___builtin_fmin : ident := 48%positive.
Definition ___builtin_fmsub : ident := 50%positive.
Definition ___builtin_fnmadd : ident := 51%positive.
Definition ___builtin_fnmsub : ident := 52%positive.
Definition ___builtin_fsqrt : ident := 46%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_nop : ident := 57%positive.
Definition ___builtin_read16_reversed : ident := 53%positive.
Definition ___builtin_read32_reversed : ident := 54%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_write16_reversed : ident := 55%positive.
Definition ___builtin_write32_reversed : ident := 56%positive.
Definition ___compcert_va_composite : ident := 23%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___compcert_va_int32 : ident := 20%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition ___i64_dtos : ident := 24%positive.
Definition ___i64_dtou : ident := 25%positive.
Definition ___i64_sar : ident := 36%positive.
Definition ___i64_sdiv : ident := 30%positive.
Definition ___i64_shl : ident := 34%positive.
Definition ___i64_shr : ident := 35%positive.
Definition ___i64_smod : ident := 32%positive.
Definition ___i64_stod : ident := 26%positive.
Definition ___i64_stof : ident := 28%positive.
Definition ___i64_udiv : ident := 31%positive.
Definition ___i64_umod : ident := 33%positive.
Definition ___i64_utod : ident := 27%positive.
Definition ___i64_utof : ident := 29%positive.
Definition ___stringlit_1 : ident := 84%positive.
Definition ___stringlit_2 : ident := 88%positive.
Definition ___stringlit_3 : ident := 93%positive.
Definition ___stringlit_4 : ident := 96%positive.
Definition _abort_with : ident := 85%positive.
Definition _alloc : ident := 3%positive.
Definition _argc : ident := 2%positive.
Definition _args : ident := 1%positive.
Definition _assert : ident := 81%positive.
Definition _create_heap : ident := 89%positive.
Definition _create_space : ident := 86%positive.
Definition _depth : ident := 62%positive.
Definition _do_generation : ident := 82%positive.
Definition _do_scan : ident := 78%positive.
Definition _fi : ident := 69%positive.
Definition _forward : ident := 68%positive.
Definition _forward_roots : ident := 73%positive.
Definition _free : ident := 99%positive.
Definition _free_heap : ident := 100%positive.
Definition _from : ident := 79%positive.
Definition _from_limit : ident := 60%positive.
Definition _from_start : ident := 59%positive.
Definition _garbage_collect : ident := 97%positive.
Definition _h : ident := 87%positive.
Definition _hd : ident := 64%positive.
Definition _heap : ident := 5%positive.
Definition _hi : ident := 91%positive.
Definition _i : ident := 65%positive.
Definition _j : ident := 77%positive.
Definition _limit : ident := 4%positive.
Definition _lo : ident := 90%positive.
Definition _main : ident := 101%positive.
Definition _malloc : ident := 83%positive.
Definition _n : ident := 71%positive.
Definition _new : ident := 67%positive.
Definition _next : ident := 8%positive.
Definition _num_allocs : ident := 92%positive.
Definition _p : ident := 61%positive.
Definition _reset_heap : ident := 98%positive.
Definition _resume : ident := 94%positive.
Definition _roots : ident := 72%positive.
Definition _s : ident := 75%positive.
Definition _scan : ident := 74%positive.
Definition _space : ident := 9%positive.
Definition _spaces : ident := 10%positive.
Definition _start : ident := 7%positive.
Definition _sz : ident := 66%positive.
Definition _tag : ident := 76%positive.
Definition _thread_info : ident := 6%positive.
Definition _ti : ident := 70%positive.
Definition _to : ident := 80%positive.
Definition _v : ident := 63%positive.
Definition _w : ident := 95%positive.
Definition _t'1 : ident := 102%positive.

Definition v___stringlit_3 := {|
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

Definition v___stringlit_1 := {|
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

Definition v___stringlit_2 := {|
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

Definition v___stringlit_4 := {|
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

Definition f_forward := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr tint)) :: (_from_limit, (tptr tint)) ::
                (_next, (tptr (tptr tint))) :: (_p, (tptr tint)) ::
                (_depth, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_v, tint) :: (_hd, tuint) :: (_i, tint) :: (_sz, tint) ::
               (_new, (tptr tint)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _v (Ederef (Etempvar _p (tptr tint)) tint))
  (Sifthenelse (Ebinop Oeq
                 (Ebinop Oand (Etempvar _v tint)
                   (Econst_int (Int.repr 1) tint) tint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _from_start (tptr tint))
                     (Ecast (Etempvar _v tint) (tptr tint)) tint)
        (Sset _t'1
          (Ecast
            (Ebinop Olt (Ecast (Etempvar _v tint) (tptr tint))
              (Etempvar _from_limit (tptr tint)) tint) tbool))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _hd
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _v tint) (tptr tuint))
                (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                (tptr tuint)) tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _hd tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _v tint) (tptr tint))
                  (Econst_int (Int.repr 0) tint) (tptr tint)) tint))
            (Ssequence
              (Sset _sz
                (Ecast
                  (Ebinop Oshr (Etempvar _hd tuint)
                    (Econst_int (Int.repr 10) tint) tuint) tuint))
              (Ssequence
                (Sset _new
                  (Ebinop Oadd
                    (Ederef (Etempvar _next (tptr (tptr tint))) (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint)))
                (Ssequence
                  (Sassign
                    (Ederef (Etempvar _next (tptr (tptr tint))) (tptr tint))
                    (Ebinop Oadd (Etempvar _new (tptr tint))
                      (Etempvar _sz tint) (tptr tint)))
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
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Ecast (Etempvar _new (tptr tint))
                                  (tptr tint)) (Etempvar _i tint)
                                (tptr tint)) tint)
                            (Ederef
                              (Ebinop Oadd
                                (Ecast (Etempvar _v tint) (tptr tint))
                                (Etempvar _i tint) (tptr tint)) tint)))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _v tint) (tptr tuint))
                            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                            (tptr tuint)) tuint)
                        (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Ecast (Etempvar _v tint) (tptr tint))
                              (Econst_int (Int.repr 0) tint) (tptr tint))
                            tint) (Ecast (Etempvar _new (tptr tint)) tint))
                        (Ssequence
                          (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
                            (Ecast (Etempvar _new (tptr tint)) tint))
                          (Sifthenelse (Ebinop Ogt (Etempvar _depth tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Sset _i (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                                 (Etempvar _sz tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Scall None
                                    (Evar _forward (Tfunction
                                                     (Tcons (tptr tint)
                                                       (Tcons (tptr tint)
                                                         (Tcons
                                                           (tptr (tptr tint))
                                                           (Tcons (tptr tint)
                                                             (Tcons tint
                                                               Tnil)))))
                                                     tvoid cc_default))
                                    ((Etempvar _from_start (tptr tint)) ::
                                     (Etempvar _from_limit (tptr tint)) ::
                                     (Etempvar _next (tptr (tptr tint))) ::
                                     (Eaddrof
                                       (Ederef
                                         (Ebinop Oadd
                                           (Ecast (Etempvar _new (tptr tint))
                                             (tptr tint)) (Etempvar _i tint)
                                           (tptr tint)) tint) (tptr tint)) ::
                                     (Ebinop Osub (Etempvar _depth tint)
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     nil)))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            Sskip))))))))))
        Sskip))
    Sskip))
|}.

Definition f_forward_roots := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr tint)) :: (_from_limit, (tptr tint)) ::
                (_next, (tptr (tptr tint))) :: (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_args, (tptr tint)) :: (_n, tint) :: (_i, tuint) ::
               (_roots, (tptr tuint)) :: nil);
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
            (Tstruct _thread_info noattr)) _args (tptr tint)))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tint)
                           tint)
              Sskip
              Sbreak)
            (Scall None
              (Evar _forward (Tfunction
                               (Tcons (tptr tint)
                                 (Tcons (tptr tint)
                                   (Tcons (tptr (tptr tint))
                                     (Tcons (tptr tint) (Tcons tint Tnil)))))
                               tvoid cc_default))
              ((Etempvar _from_start (tptr tint)) ::
               (Etempvar _from_limit (tptr tint)) ::
               (Etempvar _next (tptr (tptr tint))) ::
               (Ebinop Oadd (Etempvar _args (tptr tint))
                 (Ederef
                   (Ebinop Oadd (Etempvar _roots (tptr tuint))
                     (Etempvar _i tuint) (tptr tuint)) tuint) (tptr tint)) ::
               (Econst_int (Int.repr 0) tint) :: nil)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))))
|}.

Definition f_do_scan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr tint)) :: (_from_limit, (tptr tint)) ::
                (_scan, (tptr tint)) :: (_next, (tptr (tptr tint))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr tint)) :: (_hd, tuint) :: (_sz, tuint) ::
               (_tag, tint) :: (_j, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Etempvar _scan (tptr tint)))
  (Swhile
    (Ebinop Olt (Etempvar _s (tptr tint))
      (Ederef (Etempvar _next (tptr (tptr tint))) (tptr tint)) tint)
    (Ssequence
      (Sset _hd (Ederef (Etempvar _s (tptr tint)) tint))
      (Ssequence
        (Sset _sz
          (Ecast
            (Ebinop Oshr (Etempvar _hd tuint) (Econst_int (Int.repr 10) tint)
              tuint) tuint))
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
                                       (Tcons (tptr tint)
                                         (Tcons (tptr tint)
                                           (Tcons (tptr (tptr tint))
                                             (Tcons (tptr tint)
                                               (Tcons tint Tnil))))) tvoid
                                       cc_default))
                      ((Etempvar _from_start (tptr tint)) ::
                       (Etempvar _from_limit (tptr tint)) ::
                       (Etempvar _next (tptr (tptr tint))) ::
                       (Eaddrof
                         (Ederef
                           (Ebinop Oadd
                             (Ecast (Etempvar _s (tptr tint)) (tptr tint))
                             (Etempvar _j tint) (tptr tint)) tint)
                         (tptr tint)) :: (Econst_int (Int.repr 0) tint) ::
                       nil)))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              Sskip)
            (Sset _s
              (Ebinop Oadd (Etempvar _s (tptr tint))
                (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                  (Etempvar _sz tuint) tuint) (tptr tint)))))))))
|}.

Definition f_do_generation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _assert (Tfunction Tnil tint
                    {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
    ((Ebinop Ole
       (Ebinop Osub
         (Efield
           (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _next (tptr tint))
         (Efield
           (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _start (tptr tint)) tint)
       (Ebinop Osub
         (Efield
           (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _limit (tptr tint))
         (Efield
           (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _next (tptr tint)) tint) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _forward_roots (Tfunction
                             (Tcons (tptr tint)
                               (Tcons (tptr tint)
                                 (Tcons (tptr (tptr tint))
                                   (Tcons (tptr tuint)
                                     (Tcons
                                       (tptr (Tstruct _thread_info noattr))
                                       Tnil))))) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
           (Tstruct _space noattr)) _start (tptr tint)) ::
       (Efield
         (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
           (Tstruct _space noattr)) _limit (tptr tint)) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _next (tptr tint)) (tptr (tptr tint))) ::
       (Etempvar _fi (tptr tuint)) ::
       (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))
    (Ssequence
      (Scall None
        (Evar _do_scan (Tfunction
                         (Tcons (tptr tint)
                           (Tcons (tptr tint)
                             (Tcons (tptr tint)
                               (Tcons (tptr (tptr tint)) Tnil)))) tvoid
                         cc_default))
        ((Efield
           (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _start (tptr tint)) ::
         (Efield
           (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _limit (tptr tint)) ::
         (Efield
           (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
             (Tstruct _space noattr)) _start (tptr tint)) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
               (Tstruct _space noattr)) _next (tptr tint))
           (tptr (tptr tint))) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _next (tptr tint))
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _start (tptr tint))))))
|}.

Definition f_create_space := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _space noattr))) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tint)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction Tnil tint
                      {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
      ((Ebinop Omul (Etempvar _n tuint) (Esizeof tint tuint) tuint) :: nil))
    (Sset _p (Ecast (Etempvar _t'1 tint) (tptr tint))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tint))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _abort_with (Tfunction Tnil tint
                            {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
        ((Evar ___stringlit_1 (tarray tschar 38)) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _start (tptr tint))
        (Etempvar _p (tptr tint)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _next (tptr tint))
          (Etempvar _p (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _limit (tptr tint))
          (Ebinop Oadd (Etempvar _p (tptr tint)) (Etempvar _n tuint)
            (tptr tint)))))))
|}.

Definition f_create_heap := {|
  fn_return := (tptr (Tstruct _heap noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_h, (tptr (Tstruct _heap noattr))) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction Tnil tint
                      {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
      ((Esizeof (Tstruct _heap noattr) tuint) :: nil))
    (Sset _h (Ecast (Etempvar _t'1 tint) (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _abort_with (Tfunction Tnil tint
                            {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
        ((Evar ___stringlit_2 (tarray tschar 27)) :: nil))
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
             (tarray (Tstruct _space noattr) 10))
           (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr))) ::
         (Ebinop Odiv
           (Ebinop Oshl (Econst_int (Int.repr 1) tint)
             (Econst_int (Int.repr 21) tint) tint) (Esizeof tint tuint)
           tuint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 1) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 10) tint) tint)
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
                          (tarray (Tstruct _space noattr) 10))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start (tptr tint))
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 10))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _next (tptr tint))
                    (Econst_int (Int.repr 0) tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 10))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit (tptr tint))
                    (Econst_int (Int.repr 0) tint)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _h (tptr (Tstruct _heap noattr)))))))))
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_lo, (tptr tint)) ::
               (_hi, (tptr tint)) :: (_num_allocs, tuint) :: nil);
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
      (Scall None
        (Evar _assert (Tfunction Tnil tint
                        {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
        ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))
      (Ssequence
        (Sset _lo
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                    (Tstruct _heap noattr)) _spaces
                  (tarray (Tstruct _space noattr) 10))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
            _start (tptr tint)))
        (Ssequence
          (Sset _hi
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 10))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr tint)))
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Osub (Etempvar _hi (tptr tint))
                             (Etempvar _lo (tptr tint)) tint)
                           (Etempvar _num_allocs tuint) tint)
              (Scall None
                (Evar _abort_with (Tfunction Tnil tint
                                    {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
                ((Evar ___stringlit_3 (tarray tschar 48)) :: nil))
              Sskip)
            (Ssequence
              (Sassign
                (Ederef
                  (Efield
                    (Ederef
                      (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _alloc
                    (tptr (tptr tint))) (tptr tint))
                (Etempvar _lo (tptr tint)))
              (Sassign
                (Ederef
                  (Efield
                    (Ederef
                      (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _limit
                    (tptr (tptr tint))) (tptr tint))
                (Etempvar _hi (tptr tint))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_w, tint) :: (_t'1, (tptr (Tstruct _heap noattr))) :: nil);
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
                              (Tcons (tptr tuint)
                                (Tcons (tptr (Tstruct _thread_info noattr))
                                  Tnil)) tvoid cc_default))
              ((Etempvar _fi (tptr tuint)) ::
               (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))
            (Sreturn None))))
      (Ssequence
        (Scall None
          (Evar _assert (Tfunction Tnil tint
                          {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
          ((Ebinop Oeq
             (Efield
               (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                       (Tstruct _heap noattr)) _spaces
                     (tarray (Tstruct _space noattr) 10))
                   (Econst_int (Int.repr 0) tint)
                   (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
               _limit (tptr tint))
             (Ederef
               (Efield
                 (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                   (Tstruct _thread_info noattr)) _limit (tptr (tptr tint)))
               (tptr tint)) tint) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 10))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr tint))
            (Ederef
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc (tptr (tptr tint)))
              (tptr tint)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Ebinop Osub (Econst_int (Int.repr 10) tint)
                                   (Econst_int (Int.repr 1) tint) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq
                                   (Efield
                                     (Ederef
                                       (Ebinop Oadd
                                         (Efield
                                           (Ederef
                                             (Etempvar _h (tptr (Tstruct _heap noattr)))
                                             (Tstruct _heap noattr)) _spaces
                                           (tarray (Tstruct _space noattr) 10))
                                         (Ebinop Oadd (Etempvar _i tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                                         (tptr (Tstruct _space noattr)))
                                       (Tstruct _space noattr)) _start
                                     (tptr tint))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Ssequence
                        (Sset _w
                          (Ebinop Osub
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _heap noattr)))
                                      (Tstruct _heap noattr)) _spaces
                                    (tarray (Tstruct _space noattr) 10))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _space noattr)))
                                (Tstruct _space noattr)) _limit (tptr tint))
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _heap noattr)))
                                      (Tstruct _heap noattr)) _spaces
                                    (tarray (Tstruct _space noattr) 10))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _space noattr)))
                                (Tstruct _space noattr)) _start (tptr tint))
                            tint))
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
                               (tarray (Tstruct _space noattr) 10))
                             (Ebinop Oadd (Etempvar _i tint)
                               (Econst_int (Int.repr 1) tint) tint)
                             (tptr (Tstruct _space noattr))) ::
                           (Ebinop Omul (Econst_int (Int.repr 2) tint)
                             (Etempvar _w tint) tint) :: nil)))
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
                                                       Tnil)))) tvoid
                                               cc_default))
                        ((Ebinop Oadd
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _heap noattr)))
                               (Tstruct _heap noattr)) _spaces
                             (tarray (Tstruct _space noattr) 10))
                           (Etempvar _i tint) (tptr (Tstruct _space noattr))) ::
                         (Ebinop Oadd
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _heap noattr)))
                               (Tstruct _heap noattr)) _spaces
                             (tarray (Tstruct _space noattr) 10))
                           (Ebinop Oadd (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint)
                           (tptr (Tstruct _space noattr))) ::
                         (Etempvar _fi (tptr tuint)) ::
                         (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                         nil))
                      (Sifthenelse (Ebinop Ole
                                     (Ebinop Osub
                                       (Efield
                                         (Ederef
                                           (Ebinop Oadd
                                             (Efield
                                               (Ederef
                                                 (Etempvar _h (tptr (Tstruct _heap noattr)))
                                                 (Tstruct _heap noattr))
                                               _spaces
                                               (tarray (Tstruct _space noattr) 10))
                                             (Etempvar _i tint)
                                             (tptr (Tstruct _space noattr)))
                                           (Tstruct _space noattr)) _limit
                                         (tptr tint))
                                       (Efield
                                         (Ederef
                                           (Ebinop Oadd
                                             (Efield
                                               (Ederef
                                                 (Etempvar _h (tptr (Tstruct _heap noattr)))
                                                 (Tstruct _heap noattr))
                                               _spaces
                                               (tarray (Tstruct _space noattr) 10))
                                             (Etempvar _i tint)
                                             (tptr (Tstruct _space noattr)))
                                           (Tstruct _space noattr)) _start
                                         (tptr tint)) tint)
                                     (Ebinop Osub
                                       (Efield
                                         (Ederef
                                           (Ebinop Oadd
                                             (Efield
                                               (Ederef
                                                 (Etempvar _h (tptr (Tstruct _heap noattr)))
                                                 (Tstruct _heap noattr))
                                               _spaces
                                               (tarray (Tstruct _space noattr) 10))
                                             (Ebinop Oadd (Etempvar _i tint)
                                               (Econst_int (Int.repr 1) tint)
                                               tint)
                                             (tptr (Tstruct _space noattr)))
                                           (Tstruct _space noattr)) _limit
                                         (tptr tint))
                                       (Efield
                                         (Ederef
                                           (Ebinop Oadd
                                             (Efield
                                               (Ederef
                                                 (Etempvar _h (tptr (Tstruct _heap noattr)))
                                                 (Tstruct _heap noattr))
                                               _spaces
                                               (tarray (Tstruct _space noattr) 10))
                                             (Ebinop Oadd (Etempvar _i tint)
                                               (Econst_int (Int.repr 1) tint)
                                               tint)
                                             (tptr (Tstruct _space noattr)))
                                           (Tstruct _space noattr)) _next
                                         (tptr tint)) tint) tint)
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
                        Sskip))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Scall None
              (Evar _abort_with (Tfunction Tnil tint
                                  {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
              ((Evar ___stringlit_4 (tarray tschar 24)) :: nil))))))
    (Scall None
      (Evar _assert (Tfunction Tnil tint
                      {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
      ((Econst_int (Int.repr 0) tint) :: nil))))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 10) tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _spaces
                (tarray (Tstruct _space noattr) 10)) (Etempvar _i tint)
              (tptr (Tstruct _space noattr))) (Tstruct _space noattr)) _next
          (tptr tint))
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _spaces
                (tarray (Tstruct _space noattr) 10)) (Etempvar _i tint)
              (tptr (Tstruct _space noattr))) (Tstruct _space noattr)) _start
          (tptr tint))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 10) tint) tint)
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
                    (tarray (Tstruct _space noattr) 10)) (Etempvar _i tint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr tint)))
          (Sifthenelse (Ebinop One (Etempvar _p (tptr tint))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Scall None
              (Evar _free (Tfunction Tnil tint
                            {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
              ((Etempvar _p (tptr tint)) :: nil))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Scall None
    (Evar _free (Tfunction Tnil tint
                  {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
    ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite _thread_info Struct
   ((_args, (tptr tint)) :: (_argc, tint) :: (_alloc, (tptr (tptr tint))) ::
    (_limit, (tptr (tptr tint))) :: (_heap, (tptr (Tstruct _heap noattr))) ::
    nil)
   noattr ::
 Composite _space Struct
   ((_start, (tptr tint)) :: (_next, (tptr tint)) :: (_limit, (tptr tint)) ::
    nil)
   noattr ::
 Composite _heap Struct
   ((_spaces, (tarray (Tstruct _space noattr) 10)) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
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
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
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
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
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
 (_forward, Gfun(Internal f_forward)) ::
 (_forward_roots, Gfun(Internal f_forward_roots)) ::
 (_do_scan, Gfun(Internal f_do_scan)) ::
 (_do_generation, Gfun(Internal f_do_generation)) ::
 (_create_space, Gfun(Internal f_create_space)) ::
 (_malloc,
   Gfun(External EF_malloc Tnil tint
     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_create_heap, Gfun(Internal f_create_heap)) ::
 (_resume, Gfun(Internal f_resume)) ::
 (_abort_with,
   Gfun(External (EF_external "abort_with"
                   (mksignature nil (Some AST.Tint)
                     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_assert,
   Gfun(External (EF_external "assert"
                   (mksignature nil (Some AST.Tint)
                     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) ::
 (_free,
   Gfun(External EF_free Tnil tint
     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_free_heap, Gfun(Internal f_free_heap)) :: nil);
prog_public :=
(_free_heap :: _free :: _reset_heap :: _garbage_collect :: _assert ::
 _abort_with :: _resume :: _create_heap :: _malloc :: _create_space ::
 _do_generation :: _do_scan :: _forward_roots :: _forward ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

