Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  data_at sh tint (Vint (Int.repr header)) (offset_val (- WORD_SIZE) p) *
  data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p.

Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred :=
  vertex_at sh (vertex_address g v) (make_header g v) (make_fields g v).

Definition generation_rep (sh: share) (g: LGraph) (gen_and_num: nat * nat): mpred :=
  match gen_and_num with
  | pair gen num =>
    iter_sepcon (map (fun x => (gen, x)) (nat_inc_list num)) (vertex_rep sh g)
  end.

Definition graph_rep (sh: share) (g: LGraph): mpred :=
  let up := map number_of_vertices g.(glabel) in 
  iter_sepcon (combine (nat_inc_list (length up)) up) (generation_rep sh g).

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  let len := Zlength (live_roots_indices fi) in
  data_at
    sh (tarray tuint (len + 2))
    (map Vint (map Int.repr (fun_word_size fi :: len :: live_roots_indices fi))) p.

Definition space_rest_rep (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ Tsh (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val sp.(used_space) sp.(space_start)).

Definition heap_rest_rep (hp: heap): mpred := iter_sepcon hp.(spaces) space_rest_rep.

Definition space_rep (sp: space): (reptype space_type) :=
  let s := sp.(space_start) in (s, (offset_val (WORD_SIZE * sp.(used_space)) s,
                                    offset_val (WORD_SIZE * sp.(total_space)) s)).

Definition heap_struct_rep (sp_reps: list (reptype space_type)) (h: val): mpred :=
  data_at Tsh heap_type sp_reps h.

Definition thread_info_rep (ti: thread_info) (t: val) :=
  if Val.eq ti.(ti_heap_p) nullval
  then data_at Tsh thread_info_type
               (Vundef, (Vundef, (nullval, list_repeat (Z.to_nat MAX_ARGS) Vundef))) t
  else let nursery := heap_head ti.(ti_heap) in
       let p := nursery.(space_start) in
       let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
       data_at Tsh thread_info_type
               (offset_val (WORD_SIZE * nursery.(used_space)) p,
                (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
       heap_struct_rep
         ((p, (Vundef, n_lim))
            :: map space_rep (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
       heap_rest_rep ti.(ti_heap).

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map (compose valid_pointer GC_Pointer2val) outlier).
