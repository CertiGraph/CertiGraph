Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.CertiGC.GCGraph.
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
       g: LGraph, h: part_heap, hp: val, outlier: outlier_t,
       from: nat, to: nat, depth: Z, forward_p: forward_p_type,
       fwd_addr: forward_addr_type
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr int_or_ptr_type,
       tint]
    PROP (readable_share rsh; writable_share sh;
          graph_heap_compatible g h;
          outlier_compatible g outlier;
          forward_p_compatible forward_p outlier g from;
          forward_p_addr_match forward_p fwd_addr;
          forward_condition g h from to;
          0 <= depth <= Int.max_signed;
          from <> to)
    PARAMS (gen_start g from;
            limit_address g h from;
            heap_next_address hp to;
            forward_p_address forward_p fwd_addr g;
            Vint (Int.repr depth))
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         forward_p_rep sh forward_p fwd_addr g;
         graph_rep g;
         heap_rep sh h hp)
  POST [tvoid]
    EX g': LGraph, EX h': part_heap,
    PROP ((g', h') = forward_graph_and_heap from to (Z.to_nat depth)
                           (forward_p2forward_t forward_p g) g h)
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         forward_p_rep sh (upd_fwd from to g forward_p) fwd_addr g';
         graph_rep g';
         heap_rep sh h' hp).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: part_heap, hp: val, fr: list frame,
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
    EX g' : LGraph, EX h': part_heap, EX roots': roots_t,
    PROP (super_compatible g' h' (frames2rootpairs (update_frames fr (map (exterior2val g') roots'))) roots' outlier;
          forward_roots_relation from to roots g roots' g';
          forward_condition g' h' from to;
          heap_relation h h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         frames_rep sh (update_frames fr (map (exterior2val g') roots'));
         heap_rep sh h' hp).

Definition forward_remset_spec :=
  DECLARE _forward_remset
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: part_heap, hp: val, outlier: outlier_t,
       rh: remset_heap, rmst: remset, from: nat, to: nat
  PRE [ tptr space_type, tptr space_type, tptr (tptr int_or_ptr_type) ]
     PROP (readable_share rsh; writable_share sh;
           graph_heap_compatible g h;
           outlier_compatible g outlier;
           forward_remset_condition g h from to;
           remset_graph_outlier_compatible g outlier rmst;
           remset_heap_compatible g from rmst rh h;
           from <> to)
     PARAMS (space_address hp from;
             space_address hp to;
             heap_next_address hp to)
     SEP (all_string_constants rsh gv;
          outlier_rep outlier;
          graph_rep g;
          heap_rep sh h hp;
          heap_remset_rep g h rh;
          remset_rep sh g rmst)
  POST [ tvoid ]
     EX g': LGraph, EX h': part_heap, EX rh': remset_heap, EX rmst': remset,
     PROP ((g', h', rh', rmst') = forward_remset_gh from to g h rh rmst)
     RETURN ()
     SEP(all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         heap_rep sh h' hp;
         heap_remset_rep g' h' rh';
         remset_rep sh g' rmst').

Definition DO_SCAN_TYPE :=
  ProdType (ProdType (ProdType (ProdType (ProdType
    (ProdType (ProdType (ProdType (ProdType (ProdType
      (ConstType share) (ConstType share))
      (ConstType globals)) (ConstType LGraph)) (ConstType part_heap))
      (ConstType val)) (ConstType outlier_t)) (ConstType nat))
      (ConstType nat)) (ConstType nat)) Mpred.

Program Definition do_scan_spec :=
  DECLARE _do_scan
  TYPE DO_SCAN_TYPE
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: part_heap, hp: val, outlier: outlier_t,
       from: nat, to: nat, to_index: nat, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type)]
    PROP (readable_share rsh; writable_share sh;
          graph_heap_compatible g h;
          outlier_compatible g outlier;
          forward_condition g h from to;
          from <> to; closure_has_index g to to_index;
          gen_unmarked g to)
    PARAMS (gen_start g from;
           limit_address g h from;
           offset_val (- WORD_SIZE) (vertex_address g (to, to_index));
           heap_next_address hp to)
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         heap_rep sh h hp;
         if zlt 0 (available_size h to) then emp
         else weak_derives P (weak_valid_pointer (gen_start g to) * TT) && emp;
         P)
  POST [tvoid]
    EX g': LGraph, EX h': part_heap,
    PROP (graph_heap_compatible g' h';
          outlier_compatible g' outlier;
          forward_condition g' h' from to;
          do_scan_relation from to to_index g g';
          heap_relation h h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         heap_rep sh h' hp;
         if zlt 0 (available_size h' to) then emp
         else weak_derives P (weak_valid_pointer (gen_start g' to) * TT) && emp;
         P).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
  rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  destruct (zlt 0 (available_size _ _)); [reflexivity|].
  rewrite !approx_andp. rewrite derives_nonexpansive_l. reflexivity.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality g'.
  rewrite !approx_exp. apply f_equal; extensionality h'.
  unfold PROPx, LOCALx, SEPx; simpl.
  rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  destruct (zlt 0 (available_size h' _)); [reflexivity|].
  rewrite !approx_andp. rewrite derives_nonexpansive_l. reflexivity.
Qed.

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH rsh: share, sh: share, gv: globals,
       g: LGraph, h: part_heap, hp: val, fr: list frame,
       roots: roots_t, outlier: outlier_t,
       rh: remset_heap, rmst: remset, from: nat, to: nat
  PRE [tptr space_type,
       tptr space_type,
       tptr (Tstruct _stack_frame noattr)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g h (frames2rootpairs fr) roots outlier;
          remset_compatible g outlier from rmst rh h;
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
         heap_rep sh h hp;
         heap_remset_rep g h rh;
         remset_rep sh g rmst)
  POST [tvoid]
    EX g_rem: LGraph, EX h_rem: part_heap,
    EX rh': remset_heap, EX rmst': remset,
    EX g' : LGraph, EX h': part_heap, EX roots': roots_t,
    PROP (super_compatible g' h' (frames2rootpairs (update_frames fr (map (exterior2val g') roots'))) roots' outlier;
          weak_heap_relation h h';
          do_generation_relation from to roots roots' g h rh rmst
            g_rem h_rem rh' rmst' g' h')
    RETURN ()
    SEP (all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         frames_rep sh (update_frames fr (map (exterior2val g') roots'));
         heap_rep sh h' hp;
         heap_remset_rep_except g_rem h_rem rh' from;
         remset_rep sh g_rem rmst').

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
                      (h, (repeat Vundef (Z.to_nat MAX_ARGS), (nullval,(Vptrofs (Ptrofs.repr 0),nullval)))))) t;
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
          graph_heap_compatible g (ti_heap t_info).(pt_heap);
          graph_gen_clear g O)
    PARAMS (ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    PROP (Ptrofs.unsigned (ti_nalloc t_info) <=
           available_space (heap_head (ti_heap t_info).(pt_heap))
          - used_space (heap_head (ti_heap t_info).(pt_heap)))
    RETURN ()
    SEP (all_string_constants rsh gv;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti).

(* TODO *)
Definition decr_info_nursery (ti: thread_info) (x: val): thread_info :=
  if isptr_dec x then ti else ti.
    (* Build_thread_info (ti_heap_p ti) (incr_remset_heap (ti_heap ti).(pt_heap) 0) *)
    (*   (ti_args ti) (arg_size ti) (ti_frames ti) (ti_nalloc ti). *)

Definition mtb_upd_remset_heap (x: val) (item: remset_space_item) (rh: remset_heap) : remset_heap :=
  if isptr_dec x then upd_remset_heap item rh O else rh.

Definition info_recordable (ti: thread_info): Prop := True.

Definition ext_mutable_update_spec :=
  DECLARE _mutable_update
    WITH ti: val, p: val, v: exterior_t, t_info: thread_info, sh: share,
         g: LGraph, outlier: outlier_t, rh: remset_heap
  PRE [tptr thread_info_type, tptr int_or_ptr_type, int_or_ptr_type]
  PROP (writable_share sh;
        info_recordable t_info;
        outlier_compatible g outlier;
        exterior_compatible g outlier v)
    PARAMS (ti; p; exterior2val g v)
    GLOBALS ()
    SEP (graph_rep g;
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info ti;
         data_at_ sh int_or_ptr_type p;
         heap_remset_rep g (ti_heap t_info).(pt_heap) rh)
  POST [tvoid]
    EX t_info': thread_info, EX rh': remset_heap,
    PROP (t_info' = decr_info_nursery t_info (exterior2val g v);
          rh' = mtb_upd_remset_heap (exterior2val g v) (RemSetExterior p) rh)
    RETURN ()
    SEP (graph_rep g;
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info' ti;
         data_at sh int_or_ptr_type (exterior2val g v) p;
         heap_remset_rep g (ti_heap t_info').(pt_heap) rh').

(* Maybe exterior_t could be renamed into root_t *)

Lemma upd_rvb_range: forall rvb pos rf,
    0 < Zlength (upd_Znth pos (raw_fields rvb) rf) < two_p (WORD_SIZE * 8 - 10).
Proof.
  intros rvb pos rf. pose proof raw_fields_range rvb. rewrite Zlength_upd_Znth. assumption.
Qed.

(*

Definition upd_rvb (rvb: raw_vertex_block) (pos: Z) (rf: raw_field) : raw_vertex_block :=
  Build_raw_vertex_block
    (raw_mark rvb) (copied_vertex rvb) (upd_Znth pos (raw_fields rvb) rf)
    (raw_color rvb) (raw_tag rvb) (raw_tag_range rvb)
    (raw_color_range rvb) (upd_rvb_range rvb pos rf) (tag_no_scan rvb).

Definition mtb_upd_graph (g: LGraph) (it: interior_t) (v: exterior_t) : LGraph :=
  match it with
  | InteriorVertexPos v pos =>
      match Znth pos (raw_fields (vlabel g v)) with
      | RawInternal => match v with
                       | ExteriorUnboxed z =>
                       | ExteriorOutlier p =>
                       | ExteriorVertex vtx =>
                       end
      | RawUnboxed _
      | RawOutlier _ => match v with
                       | ExteriorUnboxed z =>
                       | ExteriorOutlier p =>
                       | ExteriorVertex vtx =>
                       end
  end

*)

Definition int_mutable_update_spec :=
  DECLARE _mutable_update
    WITH ti: val, v: exterior_t, t_info: thread_info, sh: share, g: LGraph,
         it: interior_t, outlier: outlier_t, rh: remset_heap
  PRE [tptr thread_info_type, tptr int_or_ptr_type, int_or_ptr_type]
  PROP (writable_share sh;
        info_recordable t_info;
        outlier_compatible g outlier;
        exterior_compatible g outlier v;
        interior_compatible g O it)
    PARAMS (ti; interior_address it g; exterior2val g v)
    GLOBALS ()
    SEP (graph_rep g;
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info ti;
         heap_remset_rep g (ti_heap t_info).(pt_heap) rh)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX rh': remset_heap,
    PROP (t_info' = decr_info_nursery t_info (exterior2val g v);
          rh' = mtb_upd_remset_heap (exterior2val g v) (RemSetInterior it) rh
          (* relation or function about g and g' *))
    RETURN ()
    SEP (graph_rep g';
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info' ti;
         heap_remset_rep g' (ti_heap t_info').(pt_heap) rh').

(* Change before_gc_thread_info_rep *)
(* Define a new heap_management to hide details in
   before_gc_thread_info_rep *)
(* combine heap and remset_heap *)

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH rsh: share, sh: share, gv: globals, ti: val,
       g: LGraph, t_info: thread_info,
       roots : roots_t, outlier: outlier_t,
       rh: remset_heap, rmst: remset
  PRE [tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible g (ti_heap t_info).(pt_heap) (frames2rootpairs (ti_frames t_info)) roots outlier;
          garbage_collect_condition g (ti_heap t_info).(pt_heap);
          safe_to_copy_heap g (ti_heap t_info).(pt_heap);
          remset_compatible g outlier O rmst rh (ti_heap t_info).(pt_heap);
          remset_generation_compatible O rmst rh)
    PARAMS (ti)
    GLOBALS (gv)
    SEP (mem_mgr gv;
         all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g;
         heap_remset_rep g (ti_heap t_info).(pt_heap) rh;
         remset_rep sh g rmst;
         before_gc_thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    EX rh': remset_heap, EX rmst': remset,
    PROP (super_compatible g' (ti_heap t_info').(pt_heap) (frames2rootpairs (ti_frames t_info')) roots' outlier;
          garbage_collect_relation roots roots'
            g (ti_heap t_info).(pt_heap) rh rmst
            g' (ti_heap t_info').(pt_heap) rh' rmst';
          garbage_collect_condition g' (ti_heap t_info').(pt_heap);
          safe_to_copy_heap g' (ti_heap t_info').(pt_heap);
          frame_shells_eq (ti_frames t_info) (ti_frames t_info');
          Ptrofs.unsigned (ti_nalloc t_info) <=
                 available_space (heap_head (ti_heap t_info').(pt_heap))
                    - used_space (heap_head (ti_heap t_info').(pt_heap)))
    RETURN ()
    SEP (mem_mgr gv;
         all_string_constants rsh gv;
         outlier_rep outlier;
         graph_rep g';
         heap_remset_rep g' (ti_heap t_info').(pt_heap) rh';
         remset_rep sh g' rmst';
         before_gc_thread_info_rep sh t_info' ti).

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
