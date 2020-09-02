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

(* I suggest using AdjMat's soundess and adding 
   your further restrictions to it.
   See MathDijkGraph for an example 
 *)
Class AdjMatUSoundness (g: LabeledGraph V E DV DE DG) := {
  size_rep: 0 <= size <= Int.max_signed;
  inf_rep: 0 <= inf <= Int.max_signed; 
  vert_representable: forall v, vvalid g v <-> 0 <= v < size;
  (* so essentially evalid and strong_evalid have been collapsed *)
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
(* done? *)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => AdjMatUSoundness g)).


Definition sound_MatrixUGraph (g: MatrixUGraph) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* There is already a whole set of such getters in
   AdjMatGraph. I suggest just using those.
   Add more getters for any custom restictions
   you place. If your lemmas are provable
   from AdjMat's soundless, you can move them up 
   to that file.
 *)
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

Lemma evalid_form: (*useful for a = (u,v) etc*)
forall (g: MatrixUGraph) e, evalid g e -> e = (src g e, dst g e).
Proof.
intros. rewrite (@src_fst _ (sound_MatrixUGraph g) e) by auto.
rewrite (@dst_snd _ (sound_MatrixUGraph g) e) by auto.
destruct e; simpl; auto.
Qed.

Lemma evalid_strong_evalid:
forall (g: MatrixUGraph) e, evalid g e -> strong_evalid g e.
Proof.
intros; split. auto. apply (@edge_strong_evalid _ (sound_MatrixUGraph g) e); auto.
Qed.

Lemma evalid_vvalid:
forall (g: MatrixUGraph) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply evalid_strong_evalid in H. destruct H.
rewrite (@src_fst _ (sound_MatrixUGraph _)), (@dst_snd _ (sound_MatrixUGraph _)) in H0 by auto.
simpl in H0; auto.
Qed.

Lemma evalid_adjacent:
forall (g: MatrixUGraph) u v, evalid g (u,v) -> adjacent g u v.
Proof.
intros. exists (u,v); split. apply evalid_strong_evalid; auto.
rewrite (@src_fst _ (sound_MatrixUGraph _)), (@dst_snd _ (sound_MatrixUGraph _)) by auto.
left; simpl; auto.
Qed.

(*derp, remove if possible*)
Lemma evalid_fstsnd:
forall (g: MatrixUGraph) e, evalid g e -> evalid g (fst e, snd e).
Proof.
intros. destruct e; simpl; auto.
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
Context {size_bound: 0 <= size <= Int.max_signed}.

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

(*putting this here instead of undirected_graph, so I don't have to deal with strong evalid
*)
Lemma adde_valid_edge_fits_upath:
  forall p l (g': MatrixUGraph), is_partial_graph g g' -> evalid g' (u,v) ->
    fits_upath MatrixUGraph_adde l p -> fits_upath g' l p.
Proof.
induction p; intros. destruct l. auto. simpl in H1. contradiction.
destruct p. destruct l. simpl. simpl in H1. auto. simpl in H1. apply H. auto. contradiction.
destruct l. simpl in H1; contradiction.
destruct H1. destruct (E_EqDec e (u,v)).
+hnf in e0. subst e. split. destruct H1. destruct H1. destruct H4.
rewrite (@src_fst _ (sound_MatrixUGraph _)) in H3, H4 by auto.
rewrite (@dst_snd _ (sound_MatrixUGraph _)) in H3, H5 by auto.
split. apply evalid_strong_evalid; auto.
rewrite (@src_fst _ (sound_MatrixUGraph _)) by auto.
rewrite (@dst_snd _ (sound_MatrixUGraph _)) by auto.
apply H3.
apply IHp; auto.
+unfold complement, equiv in c. split.
apply adde_adj_edge_rev in H1; auto.
apply (is_partial_graph_adj_edge g); auto.
apply IHp; auto.
Qed.

Corollary adde_valid_edge_still_connected:
  forall (g': MatrixUGraph) a b, is_partial_graph g g' -> evalid g' (u,v) ->
    connected MatrixUGraph_adde a b -> connected g' a b.
Proof.
intros. destruct H1 as [p ?]. exists p.
assert (exists l : list E, fits_upath MatrixUGraph_adde l p).
apply connected_exists_list_edges in H1; auto. destruct H2 as [l ?].
apply connected_exists_list_edges'.
intros. apply (valid_upath_vvalid MatrixUGraph_adde) in H3. rewrite vert_bound. rewrite vert_bound in H3. lia. apply H1.
exists l. apply adde_valid_edge_fits_upath; auto.
apply H1. apply H1.
Qed.

End ADD_EDGE_MUGRAPH.

Section REMOVE_EDGE_MUGRAPH.

Context {g: MatrixUGraph}.
Context {e: E} {evalid_e: evalid g e}.

Definition MatrixUGraph_eremove':=
  @Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG (pregraph_remove_edge g e)
  (vlabel g)
  (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
  (glabel g).

Instance Fin_MatrixUGraph_eremove':
  FiniteGraph (MatrixUGraph_eremove').
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
(*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
(*case e already inside*)
exists (remove E_EqDec e (EList g)). split. apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff, EList_evalid; auto. split; auto.
Qed.

Instance AdjMatUSound_eremove':
  AdjMatUSoundness MatrixUGraph_eremove'.
Proof.
constructor; simpl.
++apply (@size_rep g (sound_MatrixUGraph g)).
++apply (@inf_rep g (sound_MatrixUGraph g)).
++apply (@vert_representable g (sound_MatrixUGraph g)).
++unfold removeValidFunc; intros. destruct H. apply evalid_strong_evalid in H. apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). auto.
  pose proof (@inf_rep _ (sound_MatrixUGraph g)). split. apply (Z.le_trans _ 0).
  pose proof Int.min_signed_neg. lia. lia. lia.
  apply (@edge_weight_representable g (sound_MatrixUGraph g) e0). apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). destruct H. hnf in e1. contradiction.
  apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e0). apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). auto.
  apply (@invalid_edge_weight g (sound_MatrixUGraph g) e0). unfold not; intros; apply H. split; auto.
++unfold removeValidFunc; intros. destruct H.
  apply (@src_fst g (sound_MatrixUGraph g) e0 H).
++unfold removeValidFunc; intros. destruct H.
  apply (@dst_snd g (sound_MatrixUGraph g) e0 H).
++apply Fin_MatrixUGraph_eremove'.
++unfold removeValidFunc; intros. destruct H.
  apply (@undirected_edge_rep g (sound_MatrixUGraph g) e0 H).
Qed.

Definition MatrixUGraph_eremove: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    MatrixUGraph_eremove' (AdjMatUSound_eremove').

Lemma eremove_EList:
  forall l, Permutation (e::l) (EList g) -> Permutation l (EList MatrixUGraph_eremove).
Proof.
intros. assert (Hel: NoDup (e::l)). apply NoDup_Perm_EList in H; auto.
apply NoDup_Permutation.
apply NoDup_cons_1 in Hel; auto.
apply NoDup_EList.
intros. rewrite EList_evalid. simpl. unfold removeValidFunc. rewrite <- EList_evalid. split; intros.
split. apply (Permutation_in (l:=(e::l))). apply H. right; auto.
unfold not; intros. subst e. apply NoDup_cons_2 in Hel. contradiction.
destruct H0. apply Permutation_sym in H. apply (Permutation_in (l':=(e::l))) in H0. 2: auto.
destruct H0. symmetry in H0; contradiction. auto.
Qed.

Lemma eremove_EList_rev:
  forall l, evalid g e -> Permutation l (EList (MatrixUGraph_eremove)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList MatrixUGraph_eremove)).
rewrite EList_evalid. simpl. unfold removeValidFunc, not; intros. destruct H1. contradiction.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList MatrixUGraph_eremove))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList MatrixUGraph_eremove))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid MatrixUGraph_eremove x).
simpl. unfold removeValidFunc. rewrite EList_evalid in H3. split; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList MatrixUGraph_eremove))). apply Permutation_sym; auto. apply H4.
Qed.

End REMOVE_EDGE_MUGRAPH.

(**************MST****************)

Definition minimum_spanning_forest (t g: MatrixUGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': MatrixUGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

Lemma partial_lgraph_spanning_equiv:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> labeled_spanning_uforest t2 g -> Permutation (EList t1) (EList t2).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_EList. apply NoDup_EList.
intros. repeat rewrite EList_evalid. split; intros.
apply H. auto.
destruct (evalid_dec t1 x). auto. exfalso.
pose proof (trivial_path1 t2 x (evalid_strong_evalid t2 x H2)). destruct H3.
assert (connected t1 (src t2 x) (dst t2 x)).
apply H0. apply H1. exists (src t2 x :: dst t2 x :: nil); auto.
destruct H5 as [p ?].
apply connected_by_upath_exists_simple_upath in H5. clear p.
destruct H5 as [p [? ?]].
assert (exists l, fits_upath t1 l p). apply connected_exists_list_edges in H5; auto.
destruct H7 as [l ?].
assert (~ In x l). unfold not; intros. apply (fits_upath_evalid t1 p l) in H8; auto.
assert (fits_upath t2 l p).
apply (fits_upath_transfer' p l t1 t2) in H7; auto.
  intros; split; intros. apply H. auto. rewrite vert_bound in *; auto.
  intros. apply H. apply (fits_upath_evalid t1 p l); auto.
  intros. apply H. auto. apply evalid_strong_evalid; auto.
  intros. apply H. auto. apply evalid_strong_evalid; auto.
assert (p = (src t2 x :: dst t2 x :: nil)). assert (unique_simple_upath t2). apply H1.
unfold unique_simple_upath in H10. apply (H10 (src t2 x) (dst t2 x)).
split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
apply connected_exists_list_edges'. intros. rewrite vert_bound. apply (valid_upath_vvalid t1) in H11.
rewrite vert_bound in H11; auto. apply H6.
exists l. auto.
apply H5. apply H5.
split. apply H3. apply NoDup_cons.
unfold not; intros. destruct H11. 2: contradiction.
symmetry in H11. assert (src t2 x <> dst t2 x). apply H1. auto. contradiction.
apply NoDup_cons. unfold not; intros; contradiction. apply NoDup_nil.
apply H3.
assert (x :: nil = l). apply (uforest'_unique_lpath p (x::nil) l t2).
apply H1. split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
rewrite H10; auto. auto.
rewrite <- H11 in H8. apply H8. left; auto.
Qed.

Corollary partial_lgraph_spanning_sum_LE:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> labeled_spanning_uforest t2 g -> sum_DE Z.add t1 0 = sum_DE Z.add t2 0.
Proof.
intros. assert (Permutation (EList t1) (EList t2)).
apply (partial_lgraph_spanning_equiv t1 t2 g); auto.
unfold sum_DE. apply fold_left_comm.
intros. lia.
unfold DEList.
replace (map (elabel t1) (EList t1)) with (map (elabel g) (EList t1)).
replace (map (elabel t2) (EList t2)) with (map (elabel g) (EList t2)).
apply Permutation_map; auto.
apply map_ext_in. intros. symmetry; apply H1. rewrite EList_evalid in H3; auto.
apply map_ext_in. intros. symmetry; apply H0. rewrite EList_evalid in H3; auto.
Qed.

Corollary partial_lgraph_spanning_mst:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> minimum_spanning_forest t2 g -> minimum_spanning_forest t1 g.
Proof.
intros. split. auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t2 0) _ ).
apply Z.eq_le_incl. apply (partial_lgraph_spanning_sum_LE t1 t2 g); auto. apply H1.
apply H1; auto.
Qed.

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_DE_equiv:
  forall (g: MatrixUGraph) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

(*
Lemma msf_swap_edges:
forall (t g: MatrixUGraph) (a b: E), minimum_spanning_forest t g -> evalid g a -> ~evalid t a ->
  evalid t b -> elabel g a <= elabel g b
  -> minimum_spanning_uforest MatrixUGraph_adde (MatrixUGraph_eremove b) a) g.
*)

Lemma connected_dec:
forall (g: MatrixUGraph) u v, connected g u v \/ ~ connected g u v.
Proof.
intros. tauto.
Qed.

Lemma exists_labeled_spanning_uforest_pre:
forall (l: list E) (g: MatrixUGraph), Permutation l (EList g) -> exists (t: MatrixUGraph), labeled_spanning_uforest t g.
Proof.
induction l; intros.
(*nil case*)
exists (@edgeless_graph (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g))).
split. split. apply edgeless_partial_lgraph. split. apply uforest'_edgeless_graph.
unfold spanning; intros. destruct (V_EqDec u v).
hnf in e. subst v. split; intros; apply connected_refl.
apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
unfold complement, equiv in c. split; intros. exfalso. destruct H0.
unfold connected_by_path in H0. destruct H0. destruct H1. destruct x. inversion H1.
destruct x. inversion H1. inversion H2. subst v0. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0.
rewrite <- EList_evalid in H0. rewrite <- H in H0. contradiction.
pose proof (@edgeless_graph_disconnected (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g)) u v c).
contradiction.
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel. destruct vlabel. auto.
pose proof (@edgeless_graph_evalid (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g)) e).
contradiction.
(*inductive step*)
set (u:=src g a). set (v:=dst g a).
assert (connected g u v). apply adjacent_connected. exists a.
unfold u; unfold v; apply strong_evalid_adj_edge.
apply evalid_strong_evalid. rewrite <- EList_evalid, <- H. left; auto.
set (remove_a:=(@MatrixUGraph_eremove g a)).
assert (Ha_evalid: evalid g a). { rewrite <- EList_evalid. apply (Permutation_in (l:=(a::l))).
  apply H. left; auto. }
specialize IHl with remove_a.
destruct IHl as [t ?]. {
unfold remove_a. pose proof (@eremove_EList g a Ha_evalid l H).
apply NoDup_Permutation. assert (NoDup (a::l)). apply (Permutation_NoDup (l:=EList g)).
apply Permutation_sym; auto. apply NoDup_EList. apply NoDup_cons_1 in H2; auto.
apply NoDup_EList.
intros. rewrite EList_evalid. split; intros.
pose proof (Permutation_in (l:=l) (l':=_) x H1 H2). rewrite EList_evalid in H3; auto.
apply Permutation_sym in H1.
apply (Permutation_in (l:=_) (l':=l) x H1). rewrite EList_evalid; auto.
}
assert (Htg: is_partial_lgraph t g). {
  destruct H1. destruct H2. destruct H1. destruct H4. split.
  split. intros. apply H1 in H6. auto.
  split. intros. destruct H1. destruct H7. apply H7. auto.
  split. intros. apply H1 in H7. simpl in H7. auto. auto.
  intros. apply H1 in H7. simpl in H7. auto. auto.
  unfold preserve_vlabel, preserve_elabel; split; intros.
  destruct vlabel. destruct vlabel. auto.
  rewrite H3 by auto. simpl. destruct (E_EqDec e a). unfold equiv in e0.
  subst e. assert (evalid remove_a a). apply H1; auto.
  simpl in H7. unfold removeValidFunc in H7. destruct H7; contradiction.
  auto.
}
destruct (connected_dec remove_a u v).
(*already connected*)
++
exists t. destruct H1.  destruct H3. destruct H1. destruct H5.
split. split.
(*partial_graph*)
apply Htg.
(*uforest*)
split. auto.
(*spanning*)
unfold spanning in *. intros. rewrite <- H6. (*
destruct (V_EqDec u u0). hnf in e. subst u0.
destruct (V_EqDec v v0). hnf in e. subst v0.
split; intros; auto.*)
admit.
(*labels*)
apply Htg.
++
assert (vvalid g u /\ vvalid g v). apply connected_vvalid in H0; auto. destruct H3.
assert (u <= v). apply (@undirected_edge_rep g (sound_MatrixUGraph g)). auto.
set (w:= elabel g a).
assert (Int.min_signed <= w < inf). split.
unfold w; apply (@edge_weight_representable g (sound_MatrixUGraph g)). auto.
unfold w; apply (@edge_weight_not_inf g (sound_MatrixUGraph g)). auto.
rewrite vert_bound in H3, H4. rewrite <- (vert_bound t) in H3, H4.
assert (Ha: a = (u,v)). unfold u, v; apply evalid_form; auto. rewrite Ha in *.
set (adde_a:=@MatrixUGraph_adde t u v H3 H4 H5 w H6).
exists adde_a. split. split.
apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto.
split.
(*uforest*)
apply add_edge_uforest'; auto. apply H1.
unfold not; intros.
apply (is_partial_lgraph_connected t remove_a) in H7. contradiction.
split. apply H1. apply H1.
(*spanning*)
admit.
(*labels*)
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel; destruct vlabel; auto.
simpl. unfold update_elabel, equiv_dec.
destruct (E_EqDec (u,v) e). hnf in e0. subst e. unfold w; rewrite Ha; auto.
apply Htg. simpl in H7. unfold addValidFunc in H7. destruct H7. apply H7.
unfold complement, equiv in c. symmetry in H7; contradiction.
Abort.

(*Either:
-Prove a pure MST algorithm
-If I can solve the above (not impossible, but very tedious), and if we can show that
    "for any finite graph (with strong evalid edges?), the set of partial graphs is finite",
  then we can say "the set of spanning trees, which is a subset, is also finite"
  and "it is also nonempty, therefore it can be sorted by sum_DE and then take the first in the sorted list"
*)
Lemma exists_msf:
forall (g: MatrixUGraph), exists (t: MatrixUGraph), minimum_spanning_forest t g.
Proof. admit. Admitted.

Lemma msf_if_le_msf:
forall (t g: MatrixUGraph), labeled_spanning_uforest t g ->
  (forall t', minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
  minimum_spanning_forest t g.
Proof.
intros. unfold minimum_spanning_forest. split. auto.
intros. destruct (exists_msf g) as [msf ?].
apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
apply H2. auto.
Qed.

Corollary msf_if_le_msf':
forall (t t' g: MatrixUGraph), labeled_spanning_uforest t g ->
  minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
  minimum_spanning_forest t g.
Proof.
intros. apply msf_if_le_msf; auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
apply H0. apply H2.
Qed.

End MATRIXUGRAPH.
