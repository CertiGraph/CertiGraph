Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.CertiGC.GCGraph.
Require Import VST.concurrency.conclib.
Require Export CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.msl_ext.iter_sepcon.

Local Open Scope logic.

Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition init_data2byte (d: init_data) : byte :=
  match d with
  | Init_int8 m => Byte.repr (Int.intval m)
  | _ => Byte.one
  end.

Definition is_string_constant (d: ident * globdef Clight.fundef type) : bool :=
  match d with 
  | (_, Gvar {| gvar_info := Tarray (Tint I8 _ _) _ _;
             gvar_init := _; gvar_readonly := true; gvar_volatile := _ |})
     => true
  | _ => false
  end.

Definition sep_of_string_constant sh gv (d: ident * globdef Clight.fundef type) : mpred :=
  match d with
  | (i, Gvar v) => cstring sh (map init_data2byte (gvar_init v)) (gv i)
  | _ => emp
  end.

Definition all_string_constants' (sh: share) (gv: globals) : mpred :=
 fold_left sepcon
  (map (sep_of_string_constant sh gv) (filter is_string_constant gc_stack.global_definitions))
  emp.

Definition all_string_constants (sh: share) (gv: globals) : mpred := 
  ltac:(
   let x := constr:(all_string_constants' sh gv) in
   let x := eval hnf in x in
   let x := eval unfold sep_of_string_constant in x in
   match x with ?S ?A ?B => exact (sepcon A B) end).

Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [int_or_ptr_type]
   PROP (valid_int_or_ptr x)
   PARAMS (x)
   GLOBALS ()
   SEP ()
 POST [ tint ]
   PROP()
   RETURN(Vint (Int.repr (match x with
                           | Vint _ => if Archi.ptr64 then 0 else 1
                           | Vlong _ => if Archi.ptr64 then 1 else 0
                           | _ => 0
                           end)))
   SEP().

Definition int_or_ptr_to_int_spec :=
  DECLARE _int_or_ptr_to_int
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (is_int I32 Signed x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ (if Archi.ptr64 then tlong else tint) ]
    PROP() RETURN (x) SEP().

Definition int_or_ptr_to_ptr_spec :=
  DECLARE _int_or_ptr_to_ptr
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (isptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    PROP() RETURN (x) SEP().

Definition int_to_int_or_ptr_spec :=
  DECLARE _int_to_int_or_ptr
  WITH x : val
  PRE [ (if Archi.ptr64 then tlong else tint) ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ int_or_ptr_type ]
    PROP() RETURN (x) SEP().

Definition ptr_to_int_or_ptr_spec :=
  DECLARE _ptr_to_int_or_ptr
  WITH x : val
  PRE [tptr tvoid ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ int_or_ptr_type ]
    PROP() RETURN (x) SEP().

Definition is_ptr_spec :=
  DECLARE _is_ptr
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ tint ]
    PROP()
    RETURN(Vint (Int.repr (match x with
                                | Vptr _ _ => 1
                                | _ => 0
                                end)))
    SEP().

Definition abort_with_spec :=
  DECLARE _abort_with
  WITH s: val, str: list byte, sh: share
  PRE [tptr tschar]
    PROP (readable_share sh)
    PARAMS (s)
    GLOBALS ()
    SEP (cstring sh str s)
  POST [ tvoid ]
    PROP (False) RETURN() SEP().

Definition IS_FROM_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Program Definition Is_from_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type]
    PROP ()
    PARAMS (start; offset_val n start; v)
    GLOBALS ()
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    RETURN (Vint (Int.repr (if b then 1 else 0)))
    SEP (P).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl;
    rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  f_equal; f_equal; [|f_equal]; now rewrite derives_nonexpansive_l.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality t.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, approx_idem. reflexivity.
Qed.

Definition forward_spec :=
  DECLARE _forward
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: heap, hp: val, rootpairs: list rootpair,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, depth: Z, forward_p: forward_p_type
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr int_or_ptr_type,
       tint]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g h rootpairs roots outlier;
          forward_p_compatible forward_p roots g from;
          forward_condition g h from to;
          0 <= depth <= Int.max_signed;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g h from;
           heap_next_address hp to;
           forward_p_address' forward_p rootpairs g;
           Vint (Int.repr depth))
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         roots_rep sh rootpairs;
         heap_rep sh h hp)
  POST [tvoid]
    EX g': LGraph, EX h': heap, EX roots': roots_t,
    PROP (super_compatible g' h' (update_rootpairs rootpairs (map (root2val g') roots'))  roots' outlier;
          roots' = upd_roots from to forward_p g roots;
          forward_relation from to (Z.to_nat depth)
                           (forward_p2forward_t forward_p roots g) g g';
          forward_condition g' h' from to;
          heap_relation h h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         roots_rep sh (update_rootpairs rootpairs (map (root2val g') roots'));
         heap_rep sh h' hp).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: heap, hp: val, fr: list frame,
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr (Tstruct _stack_frame noattr)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g h (frames2rootpairs fr) roots outlier;
          forward_condition g h from to;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g h from;
           heap_next_address hp to;
           frames_p fr)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         frames_rep sh fr;
         heap_rep sh h hp)
  POST [tvoid]
    EX g' : LGraph, EX h': heap, EX roots': roots_t,
    PROP (super_compatible g' h' (frames2rootpairs (update_frames fr (map (root2val g') roots'))) roots' outlier;
          forward_roots_relation from to roots g roots' g';
          forward_condition g' h' from to;
          heap_relation h h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         frames_rep sh (update_frames fr (map (root2val g') roots'));
         heap_rep sh h' hp).

Definition forward_remset_spec :=
  DECLARE _forward_remset
  WITH sh: share, h: heap, hp: val, from: nat, to: nat, next: val
  PRE [ tptr space_type, tptr space_type, tptr (tptr int_or_ptr_type) ]
     PROP (readable_share sh)
     PARAMS ( space_address hp from ; space_address hp to; next )
     SEP (heap_rep sh h hp)
  POST [ tvoid ]
     PROP()
     RETURN ()
     SEP(heap_rep sh h hp).

Definition do_scan_spec :=
  DECLARE _do_scan
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: heap, hp: val, rootpairs: list rootpair,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, to_index: nat
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g h rootpairs roots outlier;
          forward_condition g h from to;
          from <> to; closure_has_index g to to_index;
          0 < gen_size h to; gen_unmarked g to)
    PARAMS (gen_start g from;
           limit_address g h from;
           offset_val (- WORD_SIZE) (vertex_address g (to, to_index));
           heap_next_address hp to)
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         roots_rep sh rootpairs;
         heap_rep sh h hp)
  POST [tvoid]
    EX g': LGraph, EX h': heap,
    PROP (super_compatible g' h' rootpairs roots outlier;
          forward_condition g' h' from to;
          do_scan_relation from to to_index g g';
          heap_relation h h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         roots_rep sh rootpairs;
         heap_rep sh h' hp).

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: heap, hp: val, fr: list frame, 
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [tptr space_type,
       tptr space_type,
       tptr (Tstruct _stack_frame noattr)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g h (frames2rootpairs fr) roots outlier;
          do_generation_condition g h from to;
          from <> to)
    PARAMS (space_address hp from;
           space_address hp to;
           frames_p fr)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         frames_rep sh fr;
         heap_rep sh h hp)
  POST [tvoid]
    EX g' : LGraph, EX h': heap, EX roots': roots_t,
    PROP (super_compatible g' h' (frames2rootpairs (update_frames fr (map (root2val g') roots'))) roots' outlier;
          heap_relation h h';
          do_generation_relation from to roots roots' g g')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         frames_rep sh (update_frames fr (map (root2val g') roots'));
         heap_rep sh h' hp).

Definition create_space_spec :=
  DECLARE _create_space
  WITH sh: share, s: val, n: Z, gv: globals, rsh: share
  PRE [tptr space_type, if Archi.ptr64 then tulong else tuint]
    PROP (writable_share sh;
          readable_share rsh;
          0 <= n <= MAX_SPACE_SIZE)
    PARAMS (s; if Archi.ptr64 then Vlong (Int64.repr n) else Vint (Int.repr n))
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants rsh gv; data_at_ sh space_type s)
  POST [tvoid]
    EX p: val,
    PROP () RETURN ()
    SEP (mem_mgr gv; all_string_constants rsh gv;
         malloc_token Ews (tarray int_or_ptr_type n) p;
         data_at_ Ews (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (WORD_SIZE * n) p,offset_val (WORD_SIZE * n) p))) s).

Definition zero_triple: (val * (val * (val*val))) := (nullval, (nullval, (nullval,nullval))).

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv)
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () RETURN (h)
    SEP (mem_mgr gv; all_string_constants sh gv;
        malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: repeat zero_triple (Z.to_nat (MAX_SPACES - 1))) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv)
  POST [tptr thread_info_type]
    EX t: val, EX h: val, EX p: val,
    PROP () RETURN (t)
    SEP (mem_mgr gv; all_string_constants sh gv;
         malloc_token Ews thread_info_type t;
         data_at Ews thread_info_type
                 (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,
                      (h, (repeat Vundef (Z.to_nat MAX_ARGS), (nullval,(vptrofs 0,nullval)))))) t;
         malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: repeat zero_triple (Z.to_nat (MAX_SPACES - 1))) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition resume_spec :=
  DECLARE _resume
  WITH rsh: share, sh: share, gv: globals, ti: val,
       g: LGraph, t_info: thread_info,
       roots : roots_t
  PRE [tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          graph_heap_compatible g (ti_heap t_info);
          graph_gen_clear g O)
    PARAMS (ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    PROP (Ptrofs.unsigned (ti_nalloc t_info) <= 
           total_space (heap_head (ti_heap t_info))
          - used_space (heap_head (ti_heap t_info)))
    RETURN ()
    SEP (all_string_constants rsh gv;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti).

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH rsh: share, sh: share, gv: globals, ti: val,
       g: LGraph, t_info: thread_info,
       roots : roots_t, outlier: outlier_t
  PRE [tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g (ti_heap t_info) (frames2rootpairs (ti_frames t_info)) roots outlier;
          garbage_collect_condition g (ti_heap t_info);
          safe_to_copy g)
    PARAMS (ti)
    GLOBALS (gv)
    SEP (mem_mgr gv;
         all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti;
         ti_token_rep (ti_heap t_info) (ti_heap_p t_info))
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible g' (ti_heap t_info') (frames2rootpairs (ti_frames t_info')) roots' outlier;
          garbage_collect_relation roots roots' g g';
          garbage_collect_condition g' (ti_heap t_info');
          safe_to_copy g';
          frame_shells_eq (ti_frames t_info) (ti_frames t_info');
          Ptrofs.unsigned (ti_nalloc t_info) <= 
                 total_space (heap_head (ti_heap t_info'))
                    - used_space (heap_head (ti_heap t_info')))
    RETURN ()
    SEP (mem_mgr gv;
         all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         before_gc_thread_info_rep sh t_info' ti;
         ti_token_rep (ti_heap t_info') (ti_heap_p t_info')).

(*
Definition reset_heap_spec :=
   (* THIS IS A PLACEHOLDER AND NOT CORRECT *)
  DECLARE _reset_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP ()
    PARAMS (h)
    GLOBALS ()
    SEP ()
  POST [tvoid]
  PROP () RETURN () SEP ().

Definition free_heap_spec :=
   (* THIS IS A PLACEHOLDER AND NOT CORRECT *)
  DECLARE _free_heap
  WITH h: heap, p: val, rsh: share, gv: globals
  PRE [tptr heap_type]
    PROP (readable_share rsh) PARAMS (p) GLOBALS (gv) 
    SEP (heap_rep Ews h p; ti_token_rep h p; 
         mem_mgr gv; all_string_constants rsh gv)
  POST [tvoid]
  PROP () RETURN () 
  SEP (mem_mgr gv; all_string_constants rsh gv).
*)

Definition Gprog: funspecs :=
  ltac:(with_library prog
                     [test_int_or_ptr_spec;
                      int_or_ptr_to_int_spec;
                      int_or_ptr_to_ptr_spec;
                      int_to_int_or_ptr_spec;
                      ptr_to_int_or_ptr_spec;
                      is_ptr_spec;
                      Is_from_spec;
                      abort_with_spec;
                      forward_spec;
                      forward_roots_spec;
                      forward_remset_spec;
                      do_scan_spec;
                      do_generation_spec;
                      create_space_spec;
                      create_heap_spec;
                      make_tinfo_spec;
                      resume_spec;
                      garbage_collect_spec]).
