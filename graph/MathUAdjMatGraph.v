Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Export CertiGraph.lib.find_lemmas.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Export CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.MathAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section Mathematical_Undirected_AdjMat_Model.
  
Context {size: Z} {inf: Z}.

Definition UAdjMatLG := AdjMatLG.

(* We just add a further constraint to AdjMat's soundness *)
Class SoundUAdjMat (g: UAdjMatLG) := {
  sadjmat: @SoundAdjMat size inf g;
  uer: forall e, evalid g e -> src g e <= dst g e;
  em: (* evalid_meaning *)
    forall e, evalid g e <-> 
              Int.min_signed <= elabel g e <= Int.max_signed /\
              elabel g e < inf;
}.

Definition UAdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundUAdjMat g)).

(* Some handy coercions: *)
Identity Coercion AdjMatLG_UAdjMatLG: UAdjMatLG >-> AdjMatLG.
Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

Definition SoundUAdjMat_UAdjMatGG (g: UAdjMatGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* We can always drag out SoundAdjMat *)
Definition SoundAdjMat_UAdjMatGG (g: UAdjMatGG) :=
  @sadjmat g (SoundUAdjMat_UAdjMatGG g).

(* A UAdjMatGG can be weakened into an AdjMatGG *)
Definition AdjMatGG_UAdjMatGG (g: UAdjMatGG) : AdjMatGG :=
  Build_GeneralGraph DV DE DG SoundAdjMat g (SoundAdjMat_UAdjMatGG g).

Coercion AdjMatGG_UAdjMatGG: UAdjMatGG >-> AdjMatGG.

(* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a UAdjMatGG. The coercion will be seamless. 
 *)

(* For the two new UAdjMat-specific plugins, we create getters *)
Definition undirected_edge_rep (g: UAdjMatGG) :=
  @uer g (SoundUAdjMat_UAdjMatGG g).

Definition evalid_meaning (g: UAdjMatGG) :=
  @em g ((@sound_gg _ _ _ _ _ _ _ _ g)).

(* 
   A nice-to-do future step:
   Move any known lemmas that depend only on
   AdjMatSoundness + the above soundness plugin
   to this file instead of leaving it down below.
 *)

(* Downstream, we will need a little utility to
   reorder our vertices for the purposes of representation *)
Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

(* Some lemmas about eformat *)

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
Proof.
  intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
Qed.

Lemma eformat_eq:
  forall u v a b, eformat (u,v) = eformat (a,b) -> ((u=a /\ v=b) \/ (u=b /\ v=a)).
Proof.
  intros. destruct (Z.le_ge_cases u v); destruct (Z.le_ge_cases a b).
  rewrite eformat1, eformat1 in H. apply pair_equal_spec in H. left; auto. simpl; auto. simpl; auto. simpl; auto.
  rewrite eformat1, eformat2 in H. simpl in H. apply pair_equal_spec in H. right; auto. simpl; auto. simpl; auto.
  rewrite eformat2, eformat1 in H. simpl in H. apply pair_equal_spec in H. right; split; apply H. simpl; auto. simpl; auto.
  rewrite eformat2, eformat2 in H. simpl in H. apply pair_equal_spec in H. left; split; apply H. simpl; auto. simpl; auto.
Qed.

Lemma eformat_symm:
  forall u v, eformat (u,v) = eformat (v,u).
Proof.
  intros. destruct (Z.lt_trichotomy u v).
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  destruct H.
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  rewrite eformat2'. rewrite eformat1. simpl; auto. simpl; lia. simpl; lia.
Qed.

Instance Finite_UAdjMatGG (g: UAdjMatGG):
  FiniteGraph g.
Proof. apply (finGraph g). Qed.

Lemma vert_bound:
forall (g: UAdjMatGG) v, vvalid g v <-> 0 <= v < size.
Proof.
intros. apply (vvalid_meaning g).
Qed.

Lemma UAdjMatGG_VList:
  forall (g: UAdjMatGG), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite vert_bound.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

Lemma evalid_form: (*useful for a = (u,v) etc*)
forall (g: UAdjMatGG) e, evalid g e -> e = (src g e, dst g e).
Proof.
  intros.
  rewrite (edge_src_fst g).
  rewrite (edge_dst_snd g).
  destruct e; simpl; auto.
Qed.

Lemma evalid_vvalid:
forall (g: UAdjMatGG) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply (evalid_strong_evalid g) in H. destruct H.
rewrite (edge_src_fst g), (edge_dst_snd g) in H0 by auto.
simpl in H0; auto.
Qed.

Lemma evalid_adjacent:
forall (g: UAdjMatGG) u v, evalid g (u,v) -> adjacent g u v.
Proof.
intros. exists (u,v); split. apply (evalid_strong_evalid g); auto.
rewrite (edge_src_fst g), (edge_dst_snd g) by auto. left; simpl; auto.
Qed.

Lemma evalid_inf_iff:
forall (g: UAdjMatGG) e, evalid g e <-> elabel g e < inf.
Proof.
  intros; split; intros.
  apply (evalid_meaning g); auto.
destruct (evalid_dec g e). 
auto. exfalso.
rewrite (invalid_edge_weight g) in n.
replace (elabel g e) with inf in * by trivial.
lia.
Qed.

Lemma weight_representable:
forall (g: UAdjMatGG) e, Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
  intros. destruct (evalid_dec g e).
apply (evalid_meaning g e); auto.
rewrite (invalid_edge_weight g) in n.
replace (elabel g e) with inf in * by trivial.
pose proof (inf_representable g). rep_lia. 
Qed.

Lemma weight_inf_bound:
forall (g: UAdjMatGG) e, elabel g e <= inf.
Proof.
intros. destruct (evalid_dec g e).
apply Z.lt_le_incl. apply (evalid_meaning  g e). auto.
apply (invalid_edge_weight g) in n.
replace (elabel g e) with inf in * by trivial. lia.
Qed.

Lemma adj_edge_form:
forall (g: UAdjMatGG) u v a b, adj_edge g (u,v) a b -> a <= b -> (u = a /\ v = b).
Proof.
intros. destruct H. assert (src g (u,v) <= dst g (u,v)).
apply (undirected_edge_rep g). apply H.
rewrite (edge_src_fst g), (edge_dst_snd g) in *.
simpl in *. destruct H1. auto. destruct H1; subst u; subst v. lia.
all: apply H.
Qed.

Lemma eformat_evalid_vvalid:
forall (g: UAdjMatGG) u v, evalid g (eformat (u,v)) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply (evalid_strong_evalid g) in H.
destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H. destruct H.
rewrite (edge_src_fst g), (edge_dst_snd g) in H1; auto. simpl; lia.
destruct H0.
subst u. rewrite eformat1 in H. destruct H.
rewrite (edge_src_fst g), (edge_dst_snd g) in H0; auto. simpl; lia.
rewrite eformat2 in H. simpl in H; destruct H.
rewrite (edge_src_fst g), (edge_dst_snd g) in H1; auto. simpl in H1.
split; apply H1. simpl; lia.
Qed.

Lemma eformat_adj': forall (g : UAdjMatGG) u v, evalid g (eformat (u,v)) -> adj_edge g (eformat (u,v)) u v.
Proof.
intros. split. apply (evalid_strong_evalid g); auto.
destruct (Z.le_ge_cases u v).
rewrite eformat1 in *. left. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
rewrite eformat2 in *. right. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
Qed.

Lemma eformat_adj: forall (g: UAdjMatGG) u v, adjacent g u v <-> evalid g (eformat (u,v)).
Proof.
intros. split. intros.
+
destruct H. destruct H. destruct H.
destruct H0; destruct H0. assert (x = (u,v)). {
  rewrite (edge_src_fst g) in H0.
  rewrite (edge_dst_snd g) in H2. rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat1; auto. simpl.
rewrite <- H0. rewrite <- H2 at 2. apply (undirected_edge_rep g); auto.
assert (x = (v,u)). {
  rewrite (edge_src_fst g) in H0; rewrite (edge_dst_snd g) in H2.
  rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat2. simpl. auto. simpl. rewrite <- H0. rewrite <- H2 at 2.
apply (undirected_edge_rep g); auto.
+intros. destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply (evalid_strong_evalid g); auto. left.
rewrite (edge_src_fst g), (edge_dst_snd g); auto.
(*equal, repeat*)
destruct H0. rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply (evalid_strong_evalid g); auto. left.
rewrite (edge_src_fst g), (edge_dst_snd g); auto.
rewrite eformat2 in H. 2: simpl; lia. simpl in H.
assert (evalid g (v,u)). auto.
exists (v,u). split. apply (evalid_strong_evalid g); auto.
rewrite (edge_src_fst g), (edge_dst_snd g); auto.
Qed.

Corollary eformat_adj_elabel: forall (g: UAdjMatGG) u v, adjacent g u v <-> elabel g (eformat (u,v)) < inf.
Proof.
intros. rewrite eformat_adj. apply evalid_inf_iff.
Qed.

Section EDGELESS_UADJMATGRAPH.

Context {inf_bound: 0 < inf <= Int.max_signed}.
Context {size_bound: 0 < size <= Int.max_signed}.

Definition edgeless_lgraph : UAdjMatLG :=
  @Build_LabeledGraph V E V_EqDec E_EqDec unit Z unit
    (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
    (fun v => tt) (fun e => inf) tt. 

Instance SoundUAdjMat_edgeless:
  SoundUAdjMat edgeless_lgraph.
Proof. 
constructor.
all: simpl; intros; try contradiction.
- constructor. 
  auto. auto. 
  all: simpl; intros; try auto; try contradiction.
  split; intros; lia. 
  split; intros; trivial.
  split; intros. contradiction. destruct H.
  destruct H; apply H0; reflexivity.
  split; intros. trivial. unfold not. inversion 1.
  constructor; unfold EnumEnsembles.Enumerable.
  (*vertices*)
  exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
  simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
  destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
  destruct H. rewrite H. unfold Z.max; simpl. split; lia.
  rewrite Z.max_l by lia. split; auto.
  (*edges*)
  exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
- split. inversion 1. intros.
  destruct H.
  apply Zaux.Zgt_not_eq in H0.
  apply H0; reflexivity.
Qed.

Definition edgeless_graph: UAdjMatGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
    edgeless_lgraph SoundUAdjMat_edgeless.

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
  forall (g: UAdjMatGG), is_partial_lgraph edgeless_graph g.
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

End EDGELESS_UADJMATGRAPH.

Section ADD_EDGE_UADJMATGRAPH.

Context {g: UAdjMatGG}.
Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
Context {w: Z} {w_rep: Int.min_signed <= w < inf}.

Definition UAdjMatGG_adde':=
  labeledgraph_add_edge g (u,v) u v w.

Instance Fin_UAdjMatGG_adde':
  FiniteGraph (UAdjMatGG_adde').
Proof.
  unfold UAdjMatGG_adde'.
  unfold labeledgraph_add_edge.
  apply pregraph_add_edge_finite.
  apply Finite_UAdjMatGG.
Qed.

Instance SoundUAdjMat_adde':
  SoundUAdjMat UAdjMatGG_adde'.
Proof.
constructor; simpl. constructor; simpl.
+apply (size_representable g).
+apply (inf_representable g).
+apply (vvalid_meaning g).
+unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
  split; intros. destruct H. unfold equiv_dec; destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  apply (evalid_meaning g) in H. destruct H; split; lia. 
  subst e. unfold equiv_dec. destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  unfold complement, equiv in c; contradiction.
  unfold equiv_dec in H; destruct (E_EqDec (u,v)).
  hnf in e0; subst e. right; auto.
  left. apply (MathAdjMatGraph.evalid_meaning g). auto.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e);  destruct H.
 hnf in e0. subst e.
 apply add_edge_strong_evalid; trivial.
 hnf in e0. subst e.
 apply add_edge_strong_evalid; trivial.
 apply add_edge_preserves_strong_evalid; trivial.
 apply (evalid_strong_evalid g); trivial.
 hnf in c. exfalso. apply c. hnf. auto. 
+ split; intros; unfold update_elabel, equiv_dec in *; destruct (E_EqDec (u,v) e).
- exfalso. apply H. right. hnf in e0. auto.
- apply Decidable.not_or in H. destruct H.
  apply (invalid_edge_weight g); trivial.
- rewrite H in w_rep. lia.
- apply Classical_Prop.and_not_or.
  split. apply <- (invalid_edge_weight g); trivial.
  auto.
+ unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  apply (edge_src_fst g e).
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  apply (edge_dst_snd g e).
+apply Fin_UAdjMatGG_adde'.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
  destruct (E_EqDec (u,v) e). hnf in e0; subst e. trivial. 
  unfold complement, equiv in c. destruct H.
  apply (undirected_edge_rep g e); auto.
  exfalso. apply c.
  symmetry. trivial.
+ unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
  split; intros. destruct H. unfold equiv_dec; destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  apply (evalid_meaning g) in H. destruct H; split; lia. 
  subst e. unfold equiv_dec. destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  unfold complement, equiv in c; contradiction.
  unfold equiv_dec in H; destruct (E_EqDec (u,v)).
  hnf in e0; subst e. right; auto.
  left. apply (evalid_meaning g). auto.
Qed.

Definition UAdjMatGG_adde: UAdjMatGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
    UAdjMatGG_adde' (SoundUAdjMat_adde').

Lemma adde_vvalid:
  vvalid g v <-> vvalid UAdjMatGG_adde v.
Proof.
intros. simpl. split; auto.
Qed.

Lemma adde_evalid_or:
  forall e, evalid UAdjMatGG_adde e <-> (evalid g e \/ e = (u,v)).
Proof. unfold UAdjMatGG_adde; simpl; unfold addValidFunc. intros; split; auto. Qed.

(*all the Elist stuff are useless by themselves, because (@fin .. sound_matrx) clashes with Fin for some reason*)
Lemma adde_EList_new:
  ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList UAdjMatGG_adde).
Proof.
intros. apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
intros; split; intros. rewrite EList_evalid, adde_evalid_or. destruct H0.
right; symmetry; auto. left; rewrite EList_evalid in H0; auto.
rewrite EList_evalid, adde_evalid_or in H0. destruct H0. right; rewrite EList_evalid; auto. left; symmetry; auto.
Qed.

Lemma adde_EList_old:
  forall e, In e (EList g) -> In e (EList UAdjMatGG_adde).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
apply H1. rewrite adde_evalid_or. left; rewrite <- EList_evalid; apply H.
Qed.

Lemma adde_EList_rev:
  forall l, ~ evalid g (u,v) ->
    Permutation ((u,v)::l) (EList UAdjMatGG_adde) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList UAdjMatGG_adde)).
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

Lemma adde_src:
  forall e', evalid g e' -> src UAdjMatGG_adde e' = src g e'.
Proof.
  intros.
  pose proof (edge_src_fst g e').
  pose proof (edge_src_fst UAdjMatGG_adde e').
  replace (src g e') with (fst e') by trivial.
  replace (src UAdjMatGG_adde e') with (fst e') by trivial.
  reflexivity.
Qed.

Lemma adde_dst:
  forall e', evalid g e' -> dst UAdjMatGG_adde e' = dst g e'.
Proof.
  intros.
  pose proof (edge_dst_snd g e').
  pose proof (edge_dst_snd UAdjMatGG_adde e').
  replace (dst g e') with (snd e') by trivial.
  replace (dst UAdjMatGG_adde e') with (snd e') by trivial.
  reflexivity.
Qed.

Lemma adde_elabel_new:
  elabel UAdjMatGG_adde (u,v) = w.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec. auto.
unfold complement, equiv in c. contradiction.
Qed.

Lemma adde_elabel_old:
  forall e, e <> (u,v) -> elabel UAdjMatGG_adde e = elabel g e.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0; contradiction.
auto.
Qed.

Lemma adde_partial_graph:
  forall (g': UAdjMatGG), is_partial_graph g g' -> evalid g' (u,v) -> is_partial_graph UAdjMatGG_adde g'.
Proof.
intros. destruct H as [? [? [? ?]]].
split. intros. simpl. apply H. auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
apply H1; auto. subst e; auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H2. apply adde_src. auto. auto. rewrite adde_src in H5 by auto. simpl in H5; auto.
subst e. rewrite (edge_src_fst g').
rewrite (edge_src_fst UAdjMatGG_adde); auto.
intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H3. apply adde_dst. auto. auto. rewrite adde_dst in H5 by auto. simpl in H5; auto.
subst e. rewrite (edge_dst_snd g'), (edge_dst_snd UAdjMatGG_adde); auto.
Qed.

Lemma adde_partial_lgraph:
  forall (g': UAdjMatGG), is_partial_lgraph g g' -> evalid g' (u,v) -> w = elabel g' (u,v) -> is_partial_lgraph UAdjMatGG_adde g'.
Proof.
intros. split. apply adde_partial_graph. apply H. auto.
split. unfold preserve_vlabel; intros.
destruct vlabel. destruct vlabel. auto.
unfold preserve_elabel; intros.
destruct H. destruct H3. unfold preserve_elabel in H4.
destruct (E_EqDec e (u,v)).
unfold equiv in e0. subst e. rewrite adde_elabel_new. rewrite H1. auto.
unfold complement, equiv in c. apply add_edge_evalid_rev in H2. rewrite adde_elabel_old.
rewrite <- H4. all: auto.
Qed.

End ADD_EDGE_UADJMATGRAPH.

Section REMOVE_EDGE_UADJMATGRAPH.

Context {g: UAdjMatGG}.
Context {e: E} {evalid_e: evalid g e}.

Definition UAdjMatGG_eremove':=
  @Build_LabeledGraph V E V_EqDec E_EqDec unit Z unit (pregraph_remove_edge g e)
  (vlabel g)
  (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
  (glabel g).

Instance Fin_UAdjMatGG_eremove':
  FiniteGraph (UAdjMatGG_eremove').
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
(*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
(*case e already inside*)
exists (remove E_EqDec e (EList g)). split. apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff, EList_evalid; auto. split; auto.
Qed.

Instance SoundPrim_eremove':
  SoundUAdjMat UAdjMatGG_eremove'.
Proof.
constructor; simpl. constructor; simpl.
++apply (size_representable g).
++apply (inf_representable g).
++apply (vvalid_meaning g).
++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e).
  destruct H. hnf in e1. contradiction.
  apply (MathAdjMatGraph.evalid_meaning g). apply H.
  destruct H.
  exfalso; apply H0; trivial.
  split.
  apply (MathAdjMatGraph.evalid_meaning g). auto. auto.
++ intros. red in H. destruct H.
   apply remove_edge_preserves_strong_evalid; split; auto.
   apply (evalid_strong_evalid g); trivial.
++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e); trivial.
  ** apply Classical_Prop.not_and_or in H.
     destruct H.
     apply (invalid_edge_weight g); trivial.
     exfalso. apply H. apply c.
  ** apply Classical_Prop.or_not_and. right.
     unfold not. intro. apply H0. apply e1.
  ** apply Classical_Prop.or_not_and. left.
     apply <- (invalid_edge_weight g); trivial.
++apply (edge_src_fst g).
++apply (edge_dst_snd g).
++apply Fin_UAdjMatGG_eremove'.
++unfold removeValidFunc; intros. destruct H.
  apply (undirected_edge_rep g); trivial.
++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e).
  destruct H. hnf in e1. contradiction.
  apply (evalid_meaning g). apply H.
  destruct H.
  apply Zaux.Zgt_not_eq in H0; exfalso; apply H0; trivial.
  split.
  apply (evalid_meaning g). auto. auto.
Qed.

Definition UAdjMatGG_eremove: UAdjMatGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit SoundUAdjMat
    UAdjMatGG_eremove' (SoundPrim_eremove').

Lemma eremove_EList:
  forall l, Permutation (e::l) (EList g) -> Permutation l (EList UAdjMatGG_eremove).
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
  forall l, evalid g e -> Permutation l (EList (UAdjMatGG_eremove)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList UAdjMatGG_eremove)).
rewrite EList_evalid. simpl. unfold removeValidFunc, not; intros. destruct H1. contradiction.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList UAdjMatGG_eremove))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList UAdjMatGG_eremove))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid UAdjMatGG_eremove x).
simpl. unfold removeValidFunc. rewrite EList_evalid in H3. split; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList UAdjMatGG_eremove))). apply Permutation_sym; auto. apply H4.
Qed.

End REMOVE_EDGE_UADJMATGRAPH.

(**************MST****************)

Definition minimum_spanning_forest (t g: UAdjMatGG) :=
 labeled_spanning_uforest t g /\
  forall (t': UAdjMatGG), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

Lemma partial_lgraph_spanning_equiv:
forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
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
  intros. apply H. auto. apply (evalid_strong_evalid t1); auto.
  intros. apply H. auto. apply (evalid_strong_evalid t1); auto.
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
forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
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
forall (t1 t2 g: UAdjMatGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> minimum_spanning_forest t2 g -> minimum_spanning_forest t1 g.
Proof.
intros. split. auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t2 0) _ ).
apply Z.eq_le_incl. apply (partial_lgraph_spanning_sum_LE t1 t2 g); auto. apply H1.
apply H1; auto.
Qed.

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_DE_equiv:
  forall (g: UAdjMatGG) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

Lemma exists_labeled_spanning_uforest_pre:
forall (l: list E) (g: UAdjMatGG), Permutation l (EList g) -> exists (t: UAdjMatGG), labeled_spanning_uforest t g.
Proof.
induction l; intros.
(*nil case*)
exists (@edgeless_graph (inf_representable g) (size_representable g)).
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
pose proof (@edgeless_graph_disconnected (inf_representable g) (size_representable g) u v c).
contradiction.
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel. destruct vlabel. auto.
pose proof (@edgeless_graph_evalid (inf_representable g) (size_representable g) e).
contradiction.
(*inductive step*)
set (u:=src g a). set (v:=dst g a).
assert (connected g u v). apply adjacent_connected. exists a.
unfold u; unfold v; apply strong_evalid_adj_edge.
apply (evalid_strong_evalid g). rewrite <- EList_evalid, <- H. left; auto.
set (remove_a:=(@UAdjMatGG_eremove g a)).
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
unfold spanning in *. intros. rewrite <- H6. split; intros.
{(*---------->*)
destruct H7 as [p ?].
apply (connected_by_upath_exists_simple_upath) in H7. destruct H7 as [p' [? ?]]. clear p.
assert (exists l, fits_upath g l p'). apply (connected_exists_list_edges g p' u0 v0); auto.
destruct H9 as [l' ?]. destruct (in_dec E_EqDec a l').
**(*yes: split the path*)
assert (NoDup l'). apply (simple_upath_list_edges_NoDup g p' l'); auto.
apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. subst l'. fold u in H11. fold v in H11.
assert (~ In a l1). unfold not; intros.
apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14. apply H14.
apply in_or_app. left; left; auto.
assert (~ In a l2). unfold not; intros.
apply NoDup_app_r in H10. apply (NoDup_app_not_in E (a::nil) l2 H10 a).
left; auto. auto.
destruct H11; destruct H11.
****
apply (connected_trans _ u0 u). exists p1. split.
apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ u v). auto.
exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
****
apply (connected_trans _ u0 v). exists p1. split.
apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ v u). apply connected_symm; auto.
exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
**(*no: fits_upath_transfer*)
exists p'. split. apply (remove_edge_valid_upath _ a p' l'); auto. apply H7. apply H7.
} { (*<---*)
destruct H7 as [p [? ?]]. exists p. split.
apply remove_edge_unaffected in H7; auto. auto.
}
(*labels*)
apply Htg.
++
assert (vvalid g u /\ vvalid g v). apply connected_vvalid in H0; auto. destruct H3.
assert (u <= v). apply (undirected_edge_rep g). auto.
set (w:= elabel g a).
assert (Int.min_signed <= w < inf). unfold w. split.
pose proof (weight_representable g a). apply H6. apply (evalid_meaning g). auto.
rewrite vert_bound in H3, H4. rewrite <- (vert_bound t) in H3, H4.
assert (Ha: a = (u,v)). unfold u, v; apply evalid_form; auto. rewrite Ha in *.
set (adde_a:=@UAdjMatGG_adde t u v H3 H4 H5 w H6).
exists adde_a. split. split.
apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto.
split.
(*uforest*)
apply add_edge_uforest'; auto. apply H1.
unfold not; intros.
apply (is_partial_lgraph_connected t remove_a) in H7. contradiction.
split. apply H1. apply H1.
(*spanning*)
unfold spanning; intros. assert (Ht_uv: ~ evalid t (u,v)). unfold not; intros.
assert (evalid remove_a (u,v)). apply H1; auto.
simpl in H8. rewrite Ha in H8. unfold removeValidFunc in H8. destruct H8; contradiction.
split; intros.
{ (*-->*) destruct H7 as [p ?]. apply connected_by_upath_exists_simple_upath in H7.
destruct H7 as [p' [? ?]]. clear p.
assert (exists l', fits_upath g l' p'). apply connected_exists_list_edges in H7; auto.
destruct H9 as [l' ?]. assert (NoDup l'). apply simple_upath_list_edges_NoDup in H9; auto.
destruct (in_dec E_EqDec a l').
**
apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. fold u in H11. fold v in H11. subst l'.
assert (~ In a l1). unfold not; intros. apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14.
apply H14. apply in_or_app. left; left; auto.
assert (~ In a l2). unfold not; intros. apply NoDup_app_r in H10.
apply (NoDup_app_not_in E (a::nil) l2 H10 a). left; auto. auto.
destruct H11; destruct H11.
****
apply (connected_trans _ u0 u). apply add_edge_connected; auto.
apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ u v). apply adjacent_connected.
exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
apply add_edge_connected; auto. apply H1. exists p2. split.
apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
****
apply (connected_trans _ u0 v). apply add_edge_connected; auto.
apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ v u). apply adjacent_connected. apply adjacent_symm.
exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
apply add_edge_connected; auto. apply H1. exists p2. split.
apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
**
apply add_edge_connected; auto.
apply H1. exists p'. split. 2: apply H7.
apply (remove_edge_valid_upath g a p' l'); auto. apply H7.
} {
apply (is_partial_lgraph_connected adde_a g).
apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto. auto.
}
(*labels*)
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel; destruct vlabel; auto.
simpl. unfold update_elabel, equiv_dec.
destruct (E_EqDec (u,v) e). hnf in e0. subst e. unfold w; rewrite Ha; auto.
apply Htg. simpl in H7. unfold addValidFunc in H7. destruct H7. apply H7.
unfold complement, equiv in c. symmetry in H7; contradiction.
Qed.

Corollary exists_labeled_spanning_uforest:
forall (g: UAdjMatGG), exists (t: UAdjMatGG), labeled_spanning_uforest t g.
Proof.
intros. apply (exists_labeled_spanning_uforest_pre (EList g)). apply Permutation_refl.
Qed.

Lemma partial_graph_incl:
forall (t g: UAdjMatGG), is_partial_graph t g -> incl (EList t) (EList g).
Proof.
unfold incl; intros. rewrite EList_evalid in *. apply H; auto.
Qed.

Lemma exists_dec:
forall (g: UAdjMatGG) l, (exists (t: UAdjMatGG), labeled_spanning_uforest t g /\ Permutation l (EList t)) \/
  ~ (exists (t: UAdjMatGG), labeled_spanning_uforest t g /\ Permutation l (EList t)).
Proof.
intros. tauto.
Qed.

Lemma partial_lgraph_elabel_map:
forall (t g: UAdjMatGG) l, is_partial_lgraph t g -> incl l (EList t) ->
  map (elabel t) l = map (elabel g) l.
Proof.
induction l; intros. simpl; auto.
simpl. replace (elabel g a) with (elabel t a). rewrite IHl; auto.
apply incl_cons_inv in H0; destruct H0; auto.
apply H. rewrite <- EList_evalid. apply H0. left; auto.
Qed.

(* needs UAdjMatGG and NoDup_incl_ordered_powerlist, which means it should probably stay right here *) 
Lemma exists_msf:
forall {E_EqDec : EqDec E eq} (g: UAdjMatGG), exists (t: UAdjMatGG), minimum_spanning_forest t g.
Proof.
intros. pose proof (NoDup_incl_ordered_powerlist (EList g) (NoDup_EList g)).
destruct H as [L ?].
(*now what I need is the subset of L that exists t, labeled_spanning_uforest t g ...*)
destruct (list_decidable_prop_reduced_list
  (fun l' => NoDup l' /\ incl l' (EList g) /\ (forall x y, In x l' -> In y l' ->
      (find l' x 0 <= find l' y 0 <-> find (EList g) x 0 <= find (EList g) y 0)))
  (fun l => (exists (t: UAdjMatGG), labeled_spanning_uforest t g /\ Permutation l (EList t)))
  L
).
apply exists_dec.
intros; split; intros. rewrite <- H in H0. destruct H0 as [? [? ?]].
split. apply H0. split. apply H1. apply H2.
rewrite <- H. auto.
rename x into Lspan.
assert (Lspan <> nil). unfold not; intros. {
destruct (exists_labeled_spanning_uforest g) as [t ?].
destruct (test2 (EList t) (EList g)) as [lt ?]. apply NoDup_EList. apply NoDup_EList.
apply partial_graph_incl. apply H2. destruct H3.
assert (In lt Lspan). apply H0. split. split. apply (Permutation_NoDup (l:=EList t)).
apply Permutation_sym; auto. apply NoDup_EList.
split. unfold incl; intros. apply (Permutation_in (l':=EList t)) in H5; auto.
apply (partial_graph_incl t g) in H5; auto. apply H2. apply H4.
exists t. split; auto.
rewrite H1 in H5; contradiction.
}
pose proof (exists_Zmin Lspan (fun l => fold_left Z.add (map (elabel g) l) 0) H1).
destruct H2 as [lmin [? ?]].
apply H0 in H2. destruct H2. destruct H2 as [? [? ?]]. destruct H4 as [msf [? ?]].
exists msf. unfold minimum_spanning_forest. split. apply H4. intros.
destruct (test2 (EList t') (EList g)) as [lt' ?]. apply NoDup_EList. apply NoDup_EList.
apply partial_graph_incl. apply H8. destruct H9.
rewrite (sum_DE_equiv msf lmin). 2: apply Permutation_sym; auto.
rewrite (sum_DE_equiv t' lt'). 2: apply Permutation_sym; auto.
replace (map (elabel msf) lmin) with (map (elabel g) lmin).
replace (map (elabel t') lt') with (map (elabel g) lt').
apply H3. apply H0. split. split.
apply (Permutation_NoDup (l:=EList t')). apply Permutation_sym; auto. apply NoDup_EList.
split. unfold incl; intros. apply (Permutation_in (l':=EList t')) in H11; auto.
apply (partial_graph_incl t' g) in H11. auto. apply H8.
apply H10. exists t'. split; auto.
symmetry; apply partial_lgraph_elabel_map. split. apply H8. apply H8.
apply Permutation_incl; auto.
symmetry; apply partial_lgraph_elabel_map. split. apply H4. apply H4.
apply Permutation_incl; auto.
Qed.

Lemma msf_if_le_msf:
forall {E_EqDec : EqDec E eq} (t g: UAdjMatGG), labeled_spanning_uforest t g ->
  (forall t', minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
  minimum_spanning_forest t g.
Proof.
intros. unfold minimum_spanning_forest. split. auto.
intros. destruct (exists_msf g) as [msf ?].
apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
apply H2. auto.
Qed.

Corollary msf_if_le_msf':
forall {E_EqDec : EqDec E eq} (t t' g: UAdjMatGG), labeled_spanning_uforest t g ->
  minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
  minimum_spanning_forest t g.
Proof.
intros. apply msf_if_le_msf; auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
apply H0. apply H2.
Qed.

(*The following two could not be moved because they require a massage allowing in_dec
to be used as a bool, and I don't know what allows it*)
Lemma filter_list_Permutation:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A),
  NoDup l2 ->
  Permutation
    ((filter (fun x => in_dec EA x l1) l2) ++ (filter (fun x => negb (in_dec EA x l1)) l2))
    l2.
Proof.
intros. apply NoDup_Permutation.
apply NoDup_app_inv. apply NoDup_filter. auto. apply NoDup_filter. auto.
intros. rewrite filter_In in H0. rewrite filter_In. destruct H0.
unfold not; intros. destruct H2. destruct (in_dec EA x l1).
inversion H3. inversion H1. auto.
intros; split; intros.
apply in_app_or in H0; destruct H0; rewrite filter_In in H0; destruct H0; auto.
apply in_or_app. repeat rewrite filter_In.
destruct (in_dec EA x l1). left; split; auto. right; split; auto.
Qed.

Corollary path_partition_checkpoint2:
forall (g: UAdjMatGG) {fg: FiniteGraph g} (l: list V) p l' a b, In a l -> ~ In b l ->
  connected_by_path g p a b -> fits_upath g l' p ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l /\ ~ In v2 l /\ (exists e, adj_edge g e v1 v2 /\ In e l').
Proof.
intros.
apply (path_partition_checkpoint' g
  (filter (fun x => (in_dec V_EqDec x l)) (VList g))
  (filter (fun x => negb (in_dec V_EqDec x l)) (VList g)) p l' a b
) in H2.
2: { apply filter_list_Permutation. apply NoDup_VList. }
2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
      destruct (in_dec V_EqDec a l). auto. contradiction. }
2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
      destruct (In_dec V_EqDec b l). contradiction. auto. }
2: auto.
destruct H2 as [v1 [v2 [? [? [? [? ?]]]]]].
exists v1; exists v2. split. auto. split. auto.
split. rewrite filter_In in H4. destruct H4. destruct (in_dec V_EqDec v1 l). auto. inversion H7.
split. rewrite filter_In in H5. destruct H5. destruct (in_dec V_EqDec v2 l). inversion H7. auto.
auto.
Qed.

Lemma Zlt_Zmin:
forall x y, x < y -> Z.min x y = x.
Proof. intros. rewrite Zmin_spec. destruct (zlt x y); lia. Qed.

End Mathematical_Undirected_AdjMat_Model.
