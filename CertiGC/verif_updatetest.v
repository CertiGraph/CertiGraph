From CertiGraph.CertiGC Require Import env_graph_gc spatial_gcgraph gc_spec gc_correct.
Import graph_model.
From Stdlib Require Import ZArith Psatz.

Existing Instance CompSpecs.

Definition tail_pointer (g: LGraph) (v: VType) (w: exterior_t) : Prop :=
 graph_has_v g v /\
 raw_mark(vlabel g v) = false /\
 raw_tag (vlabel g v) = 2 /\
 match (vlabel g v).(raw_fields) with     
  | [ _ ; RawUnboxed i ] => w = ExteriorUnboxed i
  | [ _ ; RawInternal ] => 
          match get_edges g v with
           | [(w',1%nat)] => w = ExteriorVertex w'
           | _ => False
           end
  | _ => False
 end.

Inductive graph_represents_list (g: LGraph) : exterior_t -> list Z -> Prop :=
| GRL_nil: graph_represents_list g (ExteriorUnboxed 0) nil
| GRL_cons: forall (v: VType) (w: exterior_t) (h: Z) (t: list Z),
                    graph_has_v g v ->
                    tail_pointer g v w ->
                    graph_represents_list g w t ->
                    graph_represents_list g (ExteriorVertex v) (h::t).

Definition headroom_decrease_at_most_one (t_info t_info': thread_info) := 
  exists v: val,  t_info' = decr_info_nursery t_info v.

Inductive pointer_not_in_list (g: LGraph) (p: exterior_t) : exterior_t -> Prop :=
| PNI_nil: pointer_not_in_list g p (ExteriorUnboxed 0)
| PNI_cons: forall v w,
    tail_pointer g v w ->
    w <> p ->
    pointer_not_in_list g p w ->
    pointer_not_in_list g p (ExteriorVertex v).

Definition assign_it_spec : funspec :=
    WITH ti: val, t_info: thread_info, sh: share, g: LGraph, outlier: outlier_t, rh: remset_heap,
               p: exterior_t, a: Z, al: list Z,  q: exterior_t, bl: list Z
  PRE [tptr thread_info_type, tptr int_or_ptr_type, int_or_ptr_type]
     PROP (writable_share sh;
                graph_represents_list g p (a::al);
                graph_represents_list g q bl;
                pointer_not_in_list g p q;
                1 <= headroom t_info;
        graph_heap_compatible g (ti_heap t_info).(pt_heap);
        remset_heap_and_heap_compatible rh (ti_heap t_info).(pt_heap))
    PARAMS (ti; offset_val WORD_SIZE (exterior2val g p); exterior2val g q)
    GLOBALS ()
    SEP (graph_rep g;
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info ti;
         heap_remset_rep g (ti_heap t_info).(pt_heap) rh)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX rh': remset_heap,
    PROP (graph_represents_list g' p (a::bl);
                  graph_represents_list g' q bl;
                  headroom_decrease_at_most_one t_info t_info';
                  remset_heap_and_heap_compatible rh' (ti_heap t_info').(pt_heap))
    RETURN ()
    SEP (graph_rep g';
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info' ti;
         heap_remset_rep g' (ti_heap t_info').(pt_heap) rh').

Lemma assign_it_works: funspec_sub (snd int_mutable_update_spec) assign_it_spec.
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[[[[[[[[[ti t_info] sh] g] outlier]  rh] p] a] al] q] bl] [? ?].
assert_PROP (exists p' : VType, p = ExteriorVertex p'). {
  normalize.
  unfold_for_go_lower; normalize; simpl; entailer!!.
  inv H1. eauto.
}
destruct H as [p' H].
Exists (ti, q, t_info, sh, g, InteriorVertexPos p' 1, outlier, rh) emp.
normalize.
unfold_for_go_lower; normalize.
simpl; entailer!; intros.
clear H0.
split.
-
entailer!.
clear rho' H.
rename x into g'.
Exists g'.
set (t_info' := decr_info_nursery _ _).
set (rh' :=  mtb_upd_remset_heap _ (RemSetInterior (InteriorVertexPos p' 1)) rh).
Exists t_info' rh'.
entailer!!.
split; [ | split3].
+
inv H2.
apply GRL_cons with q; auto.
* admit.
* admit.
* admit.
+
admit.
+
admit.
+
admit.
-
inv H2.
split; [split; [ | split3] | ].
+
auto.
+
destruct H10 as [? [? [? ?]]].
destruct (raw_fields (vlabel g p')); try contradiction.
destruct l; try contradiction.
list_solve.
+
destruct H10 as [? [? [? ?]]]; auto.
+
destruct H10 as [? [? [? ?]]].
rewrite H2.
with_strategy transparent [NO_SCAN_TAG] unfold NO_SCAN_TAG. lia.
+
red.
inv H3; auto.
Admitted.
