(*Described a pure undirected graph that can be represented by an adjacency matrix*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Section MATRIXUGRAPH.

Instance V_EqDec: EqDec V eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec E eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec z z0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Context {inf: Z} {size: Z}.

Class AdjMatUSoundness (g: LabeledGraph V E DV DE DG) := {
  size_rep: 0 <= size <= Int.max_signed;
  inf_rep: 0 <= inf <= Int.max_signed; 
  vert_representable: forall v, vvalid g v <-> 0 <= v < size;
  edge_strong_evalid: forall e, evalid g e -> vvalid g (src g e) /\ vvalid g (dst g e);
  edge_weight_representable: forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed;
  edge_weight_not_inf: forall e, evalid g e -> elabel g e < inf; (*no reason to have <>*)
  invalid_edge_weight: forall e, ~ evalid g e -> elabel g e = inf;
  src_fst: forall e, evalid g e -> src g e = fst e;
  dst_snd: forall e, evalid g e -> dst g e = snd e;
  fin: FiniteGraph g;
  undirected_edge_rep: forall e, evalid g e -> src g e <= dst g e;
}.

(*Hm, was wondering if I could incorporate "soundness" in*)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => AdjMatUSoundness g)).

Definition sound_MatrixUGraph (g: MatrixUGraph) := (@sound_gg _ _ _ _ _ _ _ _ g).

Instance Finite_MatrixUPGraph (g: MatrixUGraph): FiniteGraph g.
Proof. apply (@fin g (sound_MatrixUGraph g)). Qed.

Lemma vert_bound:
forall (g: MatrixUGraph) v, vvalid g v <-> 0 <= v < size.
Proof.
intros. apply (@vert_representable g (sound_MatrixUGraph g)).
Qed.

Lemma MatrixUGraph_VList:
forall (g: MatrixUGraph), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite vert_bound.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

Lemma evalid_strong_evalid:
forall (g: MatrixUGraph) e, evalid g e -> strong_evalid g e.
Proof.
intros; split. auto. apply (@edge_strong_evalid _ (sound_MatrixUGraph g) e); auto.
Qed.

Lemma evalid_inf_iff:
forall (g: MatrixUGraph) e, evalid g e <-> elabel g e < inf.
Proof.
intros; split; intros. apply (@edge_weight_not_inf _ (sound_MatrixUGraph g)); auto.
destruct (evalid_dec g e). auto. apply (@invalid_edge_weight _ (sound_MatrixUGraph g)) in n. lia.
Qed.

Lemma weight_representable:
forall (g: MatrixUGraph) e, Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
intros. destruct (evalid_dec g e).
apply (@edge_weight_representable g (sound_MatrixUGraph g) e). auto.
apply (@invalid_edge_weight g (sound_MatrixUGraph g) e) in n. rewrite n.
pose proof (@inf_rep g (sound_MatrixUGraph g)). split.
set (i:=Int.min_signed); compute in i; subst i. lia.
apply H.
Qed.

Lemma weight_inf_bound:
forall (g: MatrixUGraph) e, elabel g e <= inf.
Proof.
intros. destruct (evalid_dec g e).
apply Z.lt_le_incl. apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e). auto.
apply (@invalid_edge_weight g (sound_MatrixUGraph g)) in n. lia.
Qed.

Lemma adj_edge_form:
forall (g: MatrixUGraph) u v a b, adj_edge g (u,v) a b -> a <= b -> (u = a /\ v = b).
Proof.
intros. destruct H. assert (src g (u,v) <= dst g (u,v)).
apply (@undirected_edge_rep g (sound_MatrixUGraph g)). apply H.
rewrite (@src_fst g (sound_MatrixUGraph g)), (@dst_snd g (sound_MatrixUGraph g)) in *.
simpl in *. destruct H1. auto. destruct H1; subst u; subst v. lia.
all: apply H.
Qed.

(****************Edgeless graph again*****************)

Section EDGELESS_MUGRAPH.

Context {inf_bound: 0 <= inf <= Int.max_signed}.
Context {size_bound: 0 <= size < Int.max_signed}.

Definition edgeless_lgraph: LabeledGraph V E DV DE DG :=
@Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
  (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
  (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)

Instance AdjMatUSound_edgeless:
  AdjMatUSoundness edgeless_lgraph.
Proof.
constructor.
all: simpl; intros; try contradiction.
+lia.
+lia.
+lia.
+auto.
+constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_graph: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    edgeless_lgraph (AdjMatUSound_edgeless).

Lemma edgeless_graph_vvalid:
  forall k, vvalid edgeless_graph k <-> 0 <= k < size.
Proof. simpl. intros; split; intros; auto. Qed.

Lemma edgeless_graph_evalid:
  forall e, ~ evalid edgeless_graph e.
Proof.
intros. unfold edgeless_graph; simpl. auto.
Qed.

Lemma edgeless_graph_EList:
  EList edgeless_graph = nil.
Proof.
  intros. unfold edgeless_graph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Lemma edgeless_partial_lgraph:
  forall (g: MatrixUGraph), is_partial_lgraph edgeless_graph g.
Proof.
intros. split. unfold is_partial_graph.
split. intros. simpl. simpl in H. rewrite vert_bound. auto.
split. intros. pose proof (edgeless_graph_evalid e). contradiction.
split. intros. pose proof (edgeless_graph_evalid e). contradiction.
intros. pose proof (edgeless_graph_evalid e). contradiction.
split. unfold preserve_vlabel; intros. destruct vlabel; destruct vlabel. auto.
unfold preserve_elabel; intros. pose proof (edgeless_graph_evalid e). contradiction.
Qed.

Lemma uforest'_edgeless_graph:
  uforest' edgeless_graph.
Proof.
split; intros.
(*no self-loops*)
apply edgeless_graph_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_graph_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_graph_evalid in H; contradiction.
(*main forest definition*)
unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

Lemma edgeless_graph_disconnected:
forall u v, u <> v -> ~ connected edgeless_graph u v.
Proof.
unfold not; intros.
destruct H0 as [p [? [? ?]]].
destruct p. inversion H1.
destruct p. inversion H1; inversion H2. subst u; subst v. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0.
pose proof (edgeless_graph_evalid x). contradiction.
Qed.

End EDGELESS_MUGRAPH.

(**************ADDING AN EDGE****************)

Section ADD_EDGE_MUGRAPH.

Context {g: MatrixUGraph}.
Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
Context {w: DE} {w_rep: Int.min_signed <= w < inf}.

Definition MatrixUGraph_adde':=
  labeledgraph_add_edge g (u,v) u v w.

Instance Fin_MatrixUGraph_adde':
  FiniteGraph (MatrixUGraph_adde').
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
(*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc. destruct (in_dec E_EqDec (u,v) (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists ((u,v)::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Instance AdjMatUSound_adde':
  AdjMatUSoundness MatrixUGraph_adde'.
Proof.
constructor; simpl.
+apply (@size_rep g (sound_MatrixUGraph g)).
+apply (@inf_rep g (sound_MatrixUGraph g)).
+apply (@vert_representable g (sound_MatrixUGraph g)).
+unfold addValidFunc, updateEdgeFunc; intros. unfold equiv_dec. destruct (E_EqDec (u,v) e).
  split; auto.
  unfold complement, equiv in c. destruct H. apply (@edge_strong_evalid g (sound_MatrixUGraph g) e H).
  symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  pose proof (@inf_rep g (sound_MatrixUGraph g)). lia.
  unfold complement, equiv in c. destruct H. apply (@edge_weight_representable g (sound_MatrixUGraph g) e H).
  symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. lia.
  destruct H. apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c. symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0. exfalso; apply H; auto.
  destruct (evalid_dec g e). exfalso; apply H; auto. apply (@invalid_edge_weight g (sound_MatrixUGraph g) e n).
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  destruct H. apply (@src_fst g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c; symmetry in H; contradiction.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  destruct H. apply (@dst_snd g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c; symmetry in H; contradiction.
+apply Fin_MatrixUGraph_adde'.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  lia. destruct H. apply (@undirected_edge_rep g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c. symmetry in H; contradiction.
Qed.

Definition MatrixUGraph_adde: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    MatrixUGraph_adde' (AdjMatUSound_adde').

Lemma adde_vvalid:
  vvalid g v <-> vvalid MatrixUGraph_adde v.
Proof.
intros. simpl. split; auto.
Qed.

Lemma adde_evalid_new:
  evalid MatrixUGraph_adde (u,v).
Proof. intros. apply add_edge_evalid. Qed.

Lemma adde_evalid_old:
  forall e, evalid g e -> evalid MatrixUGraph_adde e.
Proof. intros. apply add_edge_preserves_evalid; auto. Qed.

Lemma adde_evalid_rev:
  forall e, e <> (u,v) -> evalid MatrixUGraph_adde e -> evalid g e.
Proof. intros. apply add_edge_preserves_evalid' in H0; auto. Qed.

Lemma adde_evalid_or:
  forall e, evalid MatrixUGraph_adde e <-> (evalid g e \/ e = (u,v)).
Proof. unfold MatrixUGraph_adde; simpl; unfold addValidFunc. intros; split; auto. Qed.

(*all the Elist stuff are useless by themselves, because (@fin .. sound_matrx) clashes with Fin for some reason*)
Lemma adde_EList_new:
  ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList MatrixUGraph_adde).
Proof.
intros. apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
intros; split; intros. rewrite EList_evalid, adde_evalid_or. destruct H0.
right; symmetry; auto. left; rewrite EList_evalid in H0; auto.
rewrite EList_evalid, adde_evalid_or in H0. destruct H0. right; rewrite EList_evalid; auto. left; symmetry; auto.
Qed.

Lemma adde_EList_old:
  forall e, In e (EList g) -> In e (EList MatrixUGraph_adde).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
apply H1. rewrite adde_evalid_or. left; rewrite <- EList_evalid; apply H.
Qed.

Lemma adde_EList_rev:
  forall l, ~ evalid g (u,v) ->
    Permutation ((u,v)::l) (EList MatrixUGraph_adde) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList MatrixUGraph_adde)).
apply (Permutation_in (l:=(u,v)::l)). auto. right; auto.
apply EList_evalid in H2. apply adde_evalid_or in H2. destruct H2.
rewrite EList_evalid; auto.
subst x. assert (NoDup ((u,v)::l)). apply NoDup_Perm_EList in H0; auto.
apply NoDup_cons_2 in H2. contradiction.
destruct (E_EqDec x (u,v)). unfold equiv in e. subst x. apply EList_evalid in H1; contradiction.
unfold complement, equiv in c.
apply adde_EList_old in H1.
apply (Permutation_in (l':=(u,v)::l)) in H1. destruct H1. symmetry in H1; contradiction. auto.
apply Permutation_sym; auto.
Qed.

Lemma adde_src_new:
  src MatrixUGraph_adde (u,v) = u.
Proof.
apply (@src_fst _ (sound_MatrixUGraph _)). apply adde_evalid_new.
Qed.

Lemma adde_dst_new:
  dst MatrixUGraph_adde (u,v) = v.
Proof.
apply (@dst_snd _ (sound_MatrixUGraph _)). apply adde_evalid_new.
Qed.

Lemma adde_src_old:
  forall e', (u,v) <> e' -> src MatrixUGraph_adde e' = src g e'.
Proof.
unfold MatrixUGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e; contradiction. auto.
Qed.

Lemma adde_src:
  forall e', evalid g e' -> src MatrixUGraph_adde e' = src g e'.
Proof.
intros. rewrite (@src_fst _ (sound_MatrixUGraph _)). rewrite (@src_fst _ (sound_MatrixUGraph _)). auto.
auto. apply adde_evalid_old; auto.
Qed.

Lemma adde_dst_old:
  forall e', (u,v) <> e' -> dst MatrixUGraph_adde e' = dst g e'.
Proof.
unfold MatrixUGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e; contradiction. auto.
Qed.

Lemma adde_dst:
  forall e', evalid g e' -> dst MatrixUGraph_adde e' = dst g e'.
Proof.
intros. rewrite (@dst_snd _ (sound_MatrixUGraph _)). rewrite (@dst_snd _ (sound_MatrixUGraph _)). auto.
auto. apply adde_evalid_old; auto.
Qed.

Corollary adde_strong_evalid_new:
  strong_evalid MatrixUGraph_adde (u,v).
Proof.
split. apply adde_evalid_new. rewrite adde_src_new, adde_dst_new. simpl; auto.
Qed.

Lemma adde_strong_evalid_old:
  forall e', (u,v) <> e' ->
  evalid g e' ->
  strong_evalid MatrixUGraph_adde e'.
Proof.
intros. split. apply adde_evalid_old. apply H0.
apply (@edge_strong_evalid _ (sound_MatrixUGraph _)). apply adde_evalid_old. apply H0.
Qed.

Lemma adde_strong_evalid_rev:
  forall e', (u,v) <> e' ->
  strong_evalid MatrixUGraph_adde e' -> strong_evalid g e'.
Proof.
intros. destruct H0. destruct H1.
split. apply adde_evalid_rev in H0; auto.
split. rewrite adde_src_old in H1; auto.
rewrite adde_dst_old in H2; auto.
Qed.

Lemma adde_elabel_new:
  elabel MatrixUGraph_adde (u,v) = w.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec. auto.
unfold complement, equiv in c. contradiction.
Qed.

Lemma adde_elabel_old:
  forall e, e <> (u,v) -> elabel MatrixUGraph_adde e = elabel g e.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0; contradiction.
auto.
Qed.

Lemma adde_partial_graph:
  forall (g': MatrixUGraph), is_partial_graph g g' -> evalid g' (u,v) -> is_partial_graph MatrixUGraph_adde g'.
Proof.
intros. destruct H as [? [? [? ?]]].
split. intros. simpl. apply H. auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
apply H1; auto. subst e; auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H2. apply adde_src. auto. auto. rewrite adde_src in H5 by auto. simpl in H5; auto.
subst e. rewrite (@src_fst _ (sound_MatrixUGraph g')).
rewrite (@src_fst _ (sound_MatrixUGraph MatrixUGraph_adde)). auto.
apply adde_evalid_new. auto.
intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H3. apply adde_dst. auto. auto. rewrite adde_dst in H5 by auto. simpl in H5; auto.
subst e. rewrite (@dst_snd _ (sound_MatrixUGraph g')).
rewrite (@dst_snd _ (sound_MatrixUGraph MatrixUGraph_adde)). auto.
apply adde_evalid_new. auto.
Qed.

Lemma adde_partial_lgraph:
  forall (g': MatrixUGraph), is_partial_lgraph g g' -> evalid g' (u,v) -> w = elabel g' (u,v) -> is_partial_lgraph MatrixUGraph_adde g'.
Proof.
intros. split. apply adde_partial_graph. apply H. auto.
split. unfold preserve_vlabel; intros.
destruct vlabel. destruct vlabel. auto.
unfold preserve_elabel; intros.
destruct H. destruct H3. unfold preserve_elabel in H4.
destruct (E_EqDec e (u,v)).
unfold equiv in e0. subst e. rewrite adde_elabel_new. rewrite H1. auto.
unfold complement, equiv in c. apply adde_evalid_rev in H2. rewrite adde_elabel_old.
rewrite <- H4. all: auto.
Qed.

(****connectedness****)

Lemma adde_adj_edge_new:
  adj_edge MatrixUGraph_adde (u,v) u v.
Proof.
unfold adj_edge; intros. split. apply adde_strong_evalid_new; auto.
left. rewrite adde_src_new, adde_dst_new. auto.
Qed.

Lemma adde_adj_edge_old:
  forall e a b, adj_edge g e a b -> adj_edge MatrixUGraph_adde e a b.
Proof.
unfold adj_edge; intros. destruct H.
rewrite (@src_fst g (sound_MatrixUGraph g)) in H0. 2: apply H.
rewrite (@dst_snd g (sound_MatrixUGraph g)) in H0. 2: apply H.
destruct (E_EqDec (u,v) e).
+(*(u,v) = e*) unfold equiv in e0. subst e.
split. apply adde_strong_evalid_new. rewrite adde_src_new, adde_dst_new. apply H0.
+unfold complement, equiv in c. split. apply adde_strong_evalid_old. auto. apply H.
rewrite adde_src_old, adde_dst_old; auto.
rewrite (@src_fst g (sound_MatrixUGraph g)), (@dst_snd g (sound_MatrixUGraph g)). apply H0.
all: apply H.
Qed.

Lemma adde_adj_edge_rev:
forall e a b, (u,v) <> e -> adj_edge MatrixUGraph_adde e a b -> adj_edge g e a b.
Proof.
unfold adj_edge; intros. destruct H0.
split.
apply adde_strong_evalid_rev in H0; auto.
rewrite adde_src_old, adde_dst_old in H1; auto.
Qed.

Lemma adde_valid_upath:
  forall p, valid_upath g p -> valid_upath MatrixUGraph_adde p.
Proof.
induction p; intros. auto.
destruct p. auto.
split. destruct H. destruct H. exists x.
apply adde_adj_edge_old; auto.
apply IHp. auto. apply H.
Qed.

Lemma adde_connected_by_path:
  forall p a b, connected_by_path g p a b -> connected_by_path MatrixUGraph_adde p a b.
Proof.
unfold connected_by_path; intros. split. apply adde_valid_upath. apply H. apply H.
Qed.

Corollary adde_connected:
  forall a b, connected g a b -> connected MatrixUGraph_adde a b.
Proof.
intros. destruct H as [p ?]. exists p. apply adde_connected_by_path; auto.
Qed.

Lemma adde_fits_upath:
  forall p l, fits_upath g l p -> fits_upath MatrixUGraph_adde l p.
Proof.
induction p; intros. destruct l; auto.
destruct l. auto. destruct p. auto.
split. destruct H. apply adde_adj_edge_old; auto.
apply IHp. apply H.
Qed.

Lemma adde_fits_upath_rev:
  forall p l, fits_upath MatrixUGraph_adde l p -> ~ In (u,v) l -> fits_upath g l p.
Proof.
intros. apply add_edge_fits_upath_rev in H; auto.
Qed.

End ADD_EDGE_MUGRAPH.

(**************MST****************)
(*copy...*)
Definition sum_LE (g: MatrixUGraph) : DE :=
  fold_left Z.add (DEList g) 0.

Definition minimum_spanning_forest (t g: MatrixUGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': MatrixUGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv:
  forall (g: MatrixUGraph) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

End MATRIXUGRAPH.
