Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.kruskal.WeightedEdgeListGraph.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.kruskal.env_kruskal_edgelist.

Local Open Scope logic.

Definition wedge_to_cdata (wedge : LE*EType) : reptype t_struct_edge :=
  (Vint (Int.repr (fst wedge)),
    (Vint (Int.repr (fst (snd wedge))),
      Vint (Int.repr (snd (snd wedge)))
    )
  ).

Lemma wedge_to_cdata_wedgerep:
  forall w, Int.min_signed <= fst w <= Int.max_signed ->
            Int.min_signed <= fst (snd w) <= Int.max_signed ->
            Int.min_signed <= snd (snd w) <= Int.max_signed ->
            def_wedgerep (wedge_to_cdata w).
Proof.
  intros. unfold wedge_to_cdata; unfold def_wedgerep; simpl. lia.
Qed.

Lemma map_local_functions_eq:
  forall (A B: Type) (f f': A -> B) (l: list A),
  (forall x: A, In x l -> f x = f' x) -> map f l = map f' l.
Proof.
induction l; intros. auto.
simpl. rewrite (H a). rewrite IHl. auto.
intros. apply H. right; auto. left; auto.
Qed.

Lemma list_inj_map_NoDup:
  forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y : A, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
induction l; intros. simpl. apply NoDup_nil.
simpl. apply NoDup_cons. unfold not; intros.
apply NoDup_cons_iff in H0; destruct H0.
apply list_in_map_inv in H1. destruct H1. destruct H1. apply H in H1. subst a. contradiction.
left; auto. right; auto.
apply IHl. intros. apply H. right; auto. right; auto. auto. apply NoDup_cons_iff in H0. apply H0.
Qed.

Lemma sound_wedge_to_cdata_inj:
forall size (g: @EdgeListGG size),
(forall x y : LE * EType,
In x (graph_to_wedgelist g) ->
In y (graph_to_wedgelist g) -> wedge_to_cdata x = wedge_to_cdata y -> x = y).
Proof.
intros. unfold graph_to_wedgelist in H, H0. apply list_in_map_inv in H. destruct H.
apply list_in_map_inv in H0. destruct H0. destruct H. destruct H0. unfold edge_to_wedge in H. unfold edge_to_wedge in H0.
subst x. subst y.
apply EList_evalid in H2. apply EList_evalid in H3.
assert (Hvvalid_x0: vvalid g (fst x0) /\ vvalid g (snd x0)). {
  rewrite <- (src_fst g), <- (dst_snd g) by auto. apply edge_valid; auto.
}
destruct Hvvalid_x0 as [Hx0_1 Hx0_2].
assert (Hvvalid_x1: vvalid g (fst x1) /\ vvalid g (snd x1)). {
  rewrite <- (src_fst g), <- (dst_snd g) by auto. apply edge_valid; auto.
}
destruct Hvvalid_x1 as [Hx1_1 Hx1_2].
unfold wedge_to_cdata in H1; simpl in H1.
apply pair_equal_spec in H1. destruct H1. apply pair_equal_spec in H0. destruct H0.
apply Vint_injective in H. apply Vint_injective in H0. apply Vint_injective in H1.
apply repr_inj_signed in H. rewrite H.
2: unfold repable_signed; apply (weight_valid g); auto.
2: unfold repable_signed; apply (weight_valid g); auto.
replace x0 with (fst x0, snd x0). 2: destruct x0; auto.
replace x1 with (fst x1, snd x1). 2: destruct x1; auto.
apply repr_inj_signed in H0. rewrite H0.
apply repr_inj_signed in H1. rewrite H1. auto.
all: unfold repable_signed.
apply (@vertex_representable size) in Hx0_2. lia. apply (size_bound g).
apply (@vertex_representable size) in Hx1_2. lia. apply (size_bound g).
apply (@vertex_representable size) in Hx0_1. lia. apply (size_bound g).
apply (@vertex_representable size) in Hx1_1. lia. apply (size_bound g).
Qed.

Lemma wedge_to_cdata_NoDup:
forall size (g: @EdgeListGG size),
  NoDup (map wedge_to_cdata (graph_to_wedgelist g)).
Proof.
intros. pose proof (NoDup_g2wedgelist g). apply list_inj_map_NoDup. 2: auto.
apply sound_wedge_to_cdata_inj.
Qed.

Definition c_connected_by_path size (g: @EdgeListGG size) p u v :=
match u, v with
| Vint u', Vint v' => connected_by_path g p (Int.signed u') (Int.signed v')
| _, _ => False
end.

Lemma def_wedgerep_map_w2c:
  forall size (g: @EdgeListGG size),
    Forall def_wedgerep (map wedge_to_cdata (graph_to_wedgelist g)).
Proof.
  intros.
  rewrite Forall_forall; intros.
  apply list_in_map_inv in H.
  destruct H as [? [? _]].
  unfold wedge_to_cdata in H.
  unfold def_wedgerep.
  rewrite (surjective_pairing x) in *.
  inversion H; clear H.
  destruct x.
  rewrite (surjective_pairing c) in *.
  simpl fst in *; simpl snd in *.
  inversion H2; clear H2.
  rewrite H1, H0, H3. split3; trivial.
Qed.

(*Warning, this is a BAD definition. It's only because the place it's used in has
Forall def_wedgerep, so the second will never happen*)
Definition cdata_to_wedge (cwedge: reptype t_struct_edge) : (LE*EType) :=
match cwedge with
| (Vint w, (Vint x, Vint y)) => (Int.signed w,(Int.signed x,Int.signed y))
| _ => (0, (0,0))
end.

Lemma w2c2w:
  forall w, Int.min_signed <= fst w <= Int.max_signed ->
            Int.min_signed <= fst (snd w) <= Int.max_signed ->
            Int.min_signed <= snd (snd w) <= Int.max_signed ->
            cdata_to_wedge (wedge_to_cdata w) = w.
Proof.
unfold wedge_to_cdata; unfold cdata_to_wedge; intros.
repeat rewrite Int.signed_repr by auto. destruct w; destruct p; simpl; auto.
Qed.

Lemma cons_eq:
  forall {A: Type} (l l': list A) (a: A), l = l' -> a::l = a::l'.
Proof. intros. rewrite H. auto. Qed.

Lemma w2c2w_map:
  forall l,
  (forall w, In w l -> Int.min_signed <= fst w <= Int.max_signed /\
            Int.min_signed <= fst (snd w) <= Int.max_signed /\
            Int.min_signed <= snd (snd w) <= Int.max_signed) ->
            map cdata_to_wedge (map wedge_to_cdata l) = l.
Proof.
intros. induction l. simpl; auto.
rewrite map_cons. rewrite map_cons.
assert (In a (a::l)) by (left;auto). apply H in H0. destruct H0 as [? [? ?]].
rewrite w2c2w; auto. apply cons_eq. apply IHl. intros. apply H. right; auto.
Qed.

Lemma c2w2c:
  forall wedgerep, def_wedgerep wedgerep ->
  wedge_to_cdata (cdata_to_wedge wedgerep) = wedgerep.
Proof.
  unfold def_wedgerep; intros. destruct H as [? [? ?]].
  destruct (fst wedgerep) eqn:Hw; try contradiction.
  destruct (fst (snd wedgerep)) eqn:Hu; try contradiction.
  destruct (snd (snd wedgerep)) eqn:Hv; try contradiction.
  replace wedgerep with (Vint i, (Vint i0, Vint i1)).
  2: { rewrite <- Hw; rewrite <- Hu; rewrite <- Hv. destruct wedgerep as [? [? ?]]; auto. }
  unfold wedge_to_cdata; unfold cdata_to_wedge; simpl.
  repeat rewrite Int.repr_signed; auto.
Qed.

Lemma c2w2c_map:
  forall (l: list (reptype t_struct_edge)),
  Forall def_wedgerep l ->
  map wedge_to_cdata (map cdata_to_wedge l) = l.
Proof.
induction l; intros. simpl; auto.
rewrite map_cons. rewrite map_cons. rewrite c2w2c.
apply cons_eq. apply IHl. apply Forall_inv_tail in H. auto.
apply Forall_inv in H; auto.
Qed.

Definition Vundef_cwedges (n: Z): list (reptype t_struct_edge) :=
    repeat (Vundef, (Vundef, Vundef)) (Z.to_nat n).

Lemma Vundef_cwedges_Zlength:
  forall n: Z, 0 <= n -> Zlength (Vundef_cwedges n) = n.
Proof.
intros. unfold Vundef_cwedges. apply Zlength_repeat. auto.
Qed.
