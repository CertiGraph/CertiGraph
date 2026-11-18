From CertiGraph.CertiGC Require Import env_graph_gc spatial_gcgraph gc_spec gc_correct.
Import graph_model.
From Stdlib Require Import ZArith Psatz.

Existing Instance CompSpecs.

Definition cons_pointer (g: LGraph) (v: VType) (z: Z) (w: exterior_t) : Prop :=
 graph_has_v g v /\
 raw_mark(vlabel g v) = false /\
 raw_tag (vlabel g v) = 2 /\
 match (vlabel g v).(raw_fields) with
  | [ RawUnboxed z' ; RawUnboxed i ] => w = ExteriorUnboxed i /\ z = z'
  | [ RawUnboxed z' ; RawInternal ] =>
          match get_edges g v with
           | [(src,1%nat)] => w = ExteriorVertex (dst g (src,1%nat)) /\ z = z'
           | _ => False
           end
  | _ => False
 end.

Inductive graph_contains_list (g: LGraph) : exterior_t -> list Z -> Prop :=
| GRL_nil: graph_contains_list g (ExteriorUnboxed 0) nil
| GRL_cons: forall (v: VType) (w: exterior_t) (h: Z) (t: list Z),
                    graph_has_v g v ->
                    cons_pointer g v h w ->
                    graph_contains_list g w t ->
                    graph_contains_list g (ExteriorVertex v) (h::t).

Definition headroom_decrease_at_most_one (t_info t_info': thread_info) :=
  exists v: val,  t_info' = decr_info_nursery t_info v.

Inductive pointer_not_in_list (g: LGraph) (p: exterior_t) : exterior_t -> Prop :=
| PNI_nil: pointer_not_in_list g p (ExteriorUnboxed 0)
| PNI_cons: forall v h w,
    cons_pointer g v h w ->
    ExteriorVertex v <> p ->
    pointer_not_in_list g p w ->
    pointer_not_in_list g p (ExteriorVertex v).

Definition assign_it_spec : funspec :=
    WITH ti: val, t_info: thread_info, sh: share, g: LGraph, outlier: outlier_t, rh: remset_heap,
               p: exterior_t, a: Z, al: list Z,  q: exterior_t, bl: list Z
  PRE [tptr thread_info_type, tptr int_or_ptr_type, int_or_ptr_type]
     PROP (writable_share sh;
                graph_contains_list g p (a::al);
                graph_contains_list g q bl;
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
    PROP (graph_contains_list g' p (a::bl);
                  graph_contains_list g' q bl;
                  headroom_decrease_at_most_one t_info t_info';
                  remset_heap_and_heap_compatible rh' (ti_heap t_info').(pt_heap))
    RETURN ()
    SEP (graph_rep g';
         outlier_rep outlier;
         before_gc_thread_info_rep sh t_info' ti;
         heap_remset_rep g' (ti_heap t_info').(pt_heap) rh').

#[local] Lemma cons_pointer_fields g v a w :
  cons_pointer g v a w ->
  exists tail, raw_fields (vlabel g v) = [RawUnboxed a; tail].
Proof.
  intros [_ [_ [_ H]]].
  destruct (raw_fields (vlabel g v)) as [|[|n|n] [|[|m|m] [|k l]]] eqn:E;
    try contradiction.
  - unfold get_edges, make_fields in H. rewrite E in H. simpl in H.
    destruct H as [_ ->]. eauto.
  - destruct H as [_ ->]. eauto.
Qed.

#[local] Lemma cons_tail_location g v a w :
  cons_pointer g v a w -> mutable_location_compatible g (InteriorVertexPos v 1).
Proof.
  intros H. destruct (cons_pointer_fields _ _ _ _ H) as [tail Hfields].
  destruct H as [Hv [Hm [Ht _]]]. cbn. rewrite Hfields, Ht.
  with_strategy transparent [NO_SCAN_TAG] unfold NO_SCAN_TAG.
  split; [exact Hv|]. split; [change (0 <= 1 < 2); lia|].
  split; [exact Hm|lia].
Qed.

#[local] Lemma cons_update_other g g' src v new a w :
  v <> src ->
  mutable_location_compatible g (InteriorVertexPos src 1) ->
  mutable_graph_update g (InteriorVertexPos src 1) new g' ->
  cons_pointer g v a w ->
  cons_pointer g' v a w.
Proof.
  intros Hneq Hloc Hupd. unfold cons_pointer, get_edges, make_fields.
  rewrite (mutable_graph_update_graph_has_v _ _ _ _ _ Hloc Hupd).
  rewrite (mutable_graph_update_vlabel_other _ _ _ _ _ _ Hneq Hloc Hupd).
  intros [Hv [Hm [Ht H]]]. split; [exact Hv|]. split; [exact Hm|]. split; [exact Ht|].
  destruct (raw_fields (vlabel g v)) as [|[|n|n] [|[|m|m] [|k l]]]; try contradiction; auto.
  simpl in H |- *. rewrite (mutable_graph_update_dst_neq g src 1 new g' (v, 1%nat));
    auto; congruence.
Qed.

#[local] Lemma cons_tail_deterministic g v a b w w' :
  cons_pointer g v a w -> cons_pointer g v b w' -> w = w'.
Proof.
  intros [_ [_ [_ H]]] [_ [_ [_ H']]].
  destruct (raw_fields (vlabel g v)) as [|[|n|n] [|[|m|m] [|k l]]]; try contradiction.
  - destruct (get_edges g v) as [|[x [|[|i]]] [|e es]]; intuition congruence.
  - intuition congruence.
Qed.

#[local] Lemma graph_contains_list_update_other g g' src new :
  mutable_location_compatible g (InteriorVertexPos src 1) ->
  mutable_graph_update g (InteriorVertexPos src 1) new g' ->
  forall q bl, graph_contains_list g q bl ->
    pointer_not_in_list g (ExteriorVertex src) q ->
    graph_contains_list g' q bl.
Proof.
  intros Hloc Hupd q bl Hl. induction Hl as [|v w h t Hv Hcons Ht IH]; intros Hnot.
  - constructor.
  - inversion Hnot as [|v' h' w' Hcons' Hneq' Hnot']; subst.
    assert (w = w') by (eapply cons_tail_deterministic; eassumption). subst w'.
    apply GRL_cons with w.
    + eapply (proj2 (mutable_graph_update_graph_has_v _ _ _ _ _ Hloc Hupd)); eauto.
    + eapply cons_update_other; eauto; congruence.
    + auto.
Qed.

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
simpl; unfold mutable_update_pre, mutable_update_post, mutator_sep; entailer!; intros.
clear H0.
inversion H2 as [|src old h t Hv Hcell Htail]; subst.
pose proof (cons_tail_location _ _ _ _ Hcell) as Hloc.
split.
2: { split; [exact Hloc | inversion H3; subst; simpl; auto]. }
entailer!.
clear rho' H.
rename x into g'.
assert (Hupd : mutable_graph_update g (InteriorVertexPos p' 1) q g') by assumption.
Exists g'.
set (t_info' := decr_info_nursery _ _).
set (rh' := mtb_upd_remset_heap _ (RemSetInterior (InteriorVertexPos p' 1)) rh).
Exists t_info' rh'.
entailer!!.
pose proof (graph_contains_list_update_other _ _ _ _ Hloc Hupd q bl H3 H4) as Hq'.
split; [ | split3].
- apply GRL_cons with q; [ | | exact Hq'].
  + apply (proj2 (mutable_graph_update_graph_has_v _ _ _ _ _ Hloc Hupd)); exact Hv.
  + destruct (cons_pointer_fields _ _ _ _ Hcell) as [tail Hfields].
    destruct Hcell as [_ [Hm [Ht _]]].
    destruct (mutable_graph_update_vlabel_src _ _ _ _ _ Hloc Hupd)
      as [Hf [Hm' [_ [_ Ht']]]].
    unfold cons_pointer, get_edges, make_fields.
    rewrite (mutable_graph_update_graph_has_v _ _ _ _ _ Hloc Hupd), Hm', Ht', Hf, Hfields.
    split; [exact Hv|]. split; [exact Hm|]. split; [exact Ht|].
    destruct q as [z | ptr | v]; [split; reflexivity | inversion H3 | ].
    change (ExteriorVertex v = ExteriorVertex (dst g' (p', Z.to_nat 1)) /\ a = a).
    rewrite (mutable_graph_update_dst_new _ _ _ _ _ Hloc Hupd). split; reflexivity.
- exact Hq'.
- eexists; reflexivity.
- unfold rh', t_info', mtb_upd_remset_heap, decr_info_nursery.
  destruct (isptr_dec (exterior2val g q)); [ | exact H7].
  simpl pt_heap. eapply upd_incr_remset_heap_rhhc with (g := g) (gen := O);
    [exact H6 | apply graph_has_gen_O | | exact H7].
  rewrite <- heap_head_nth_space_O.
  apply (proj1 (info_recordable_iff_used_lt_available t_info)); exact H5.
Qed.
