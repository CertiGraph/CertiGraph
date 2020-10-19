Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Export CertiGraph.graph.MathUAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Section MathPrimGraph.

Context {size: Z} {inf: Z}.

Definition PrimGG := (@UAdjMatGG size inf).

(* Some handy coercions: *)
Identity Coercion UAdjMatGG_PrimGG: PrimGG >-> UAdjMatGG.

(* We can always drag out SoundUAdjMat *)
Definition SoundUAdjMat_PrimGG (g: PrimGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* Great! So now when we want to access an 
   AdjMat or UAdjMat plugin, we can simply use the 
   AdjMat or UAdjMat getter and pass it a PrimGG. 
   The coercion will be seamless. 
 *)

(* We often need to know that a PrimGG
   is a FiniteGraph *)
Instance Finite_PrimGG (g: PrimGG):
  FiniteGraph g.
Proof. apply (finGraph g). Qed.

Lemma vert_bound:
forall (g: PrimGG) v, vvalid g v <-> 0 <= v < size.
Proof.
intros. apply (vvalid_meaning g).
Qed.

Lemma PrimGG_VList:
  forall (g: PrimGG), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite vert_bound.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

Lemma evalid_form: (*useful for a = (u,v) etc*)
forall (g: PrimGG) e, evalid g e -> e = (src g e, dst g e).
Proof.
  intros.
  rewrite (edge_src_fst g).
  rewrite (edge_dst_snd g).
  destruct e; simpl; auto.
Qed.

Lemma evalid_vvalid:
forall (g: PrimGG) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply (evalid_strong_evalid g) in H. destruct H.
rewrite (edge_src_fst g), (edge_dst_snd g) in H0 by auto.
simpl in H0; auto.
Qed.

Lemma evalid_adjacent:
forall (g: PrimGG) u v, evalid g (u,v) -> adjacent g u v.
Proof.
intros. exists (u,v); split. apply (evalid_strong_evalid g); auto.
rewrite (edge_src_fst g), (edge_dst_snd g) by auto. left; simpl; auto.
Qed.

Lemma evalid_inf_iff:
forall (g: PrimGG) e, evalid g e <-> elabel g e < inf.
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
forall (g: PrimGG) e, Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
  intros. destruct (evalid_dec g e).
apply (evalid_meaning g e); auto.
rewrite (invalid_edge_weight g) in n.
replace (elabel g e) with inf in * by trivial.
pose proof (inf_representable g). rep_lia. 
Qed.

Lemma weight_inf_bound:
forall (g: PrimGG) e, elabel g e <= inf.
Proof.
intros. destruct (evalid_dec g e).
apply Z.lt_le_incl. apply (evalid_meaning  g e). auto.
apply (invalid_edge_weight g) in n.
replace (elabel g e) with inf in * by trivial. lia.
Qed.

Lemma adj_edge_form:
forall (g: PrimGG) u v a b, adj_edge g (u,v) a b -> a <= b -> (u = a /\ v = b).
Proof.
intros. destruct H. assert (src g (u,v) <= dst g (u,v)).
apply (undirected_edge_rep g). apply H.
rewrite (edge_src_fst g), (edge_dst_snd g) in *.
simpl in *. destruct H1. auto. destruct H1; subst u; subst v. lia.
all: apply H.
Qed.

Lemma eformat_evalid_vvalid:
forall (g: PrimGG) u v, evalid g (eformat (u,v)) -> vvalid g u /\ vvalid g v.
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

Lemma eformat_adj': forall (g : PrimGG) u v, evalid g (eformat (u,v)) -> adj_edge g (eformat (u,v)) u v.
Proof.
intros. split. apply (evalid_strong_evalid g); auto.
destruct (Z.le_ge_cases u v).
rewrite eformat1 in *. left. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
rewrite eformat2 in *. right. rewrite (edge_src_fst g), (edge_dst_snd g); auto. auto. auto.
Qed.

Lemma eformat_adj: forall (g: PrimGG) u v, adjacent g u v <-> evalid g (eformat (u,v)).
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

Corollary eformat_adj_elabel: forall (g: PrimGG) u v, adjacent g u v <-> elabel g (eformat (u,v)) < inf.
Proof.
intros. rewrite eformat_adj. apply evalid_inf_iff.
Qed.

(****************Edgeless graph*****************)

Section EDGELESS_MUGRAPH.

Context {inf_bound: 0 <= inf <= Int.max_signed}.
Context {size_bound: 0 < size <= Int.max_signed}.

Definition edgeless_lgraph : UAdjMatLG :=
  @Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
    (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
    (fun v => tt) (fun e => inf) tt. 

Instance SoundPrim_edgeless:
  (@SoundUAdjMat size inf) edgeless_lgraph.
Proof. 
constructor.
all: simpl; intros; try contradiction.
constructor. 
auto. auto. 
all: simpl; intros; try auto; try contradiction.
split; intros; auto.
split; intros. contradiction. destruct H.
apply Zaux.Zgt_not_eq in H0. contradiction.
split; intros; auto.
constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_graph: PrimGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG (@SoundUAdjMat size inf)
    edgeless_lgraph SoundPrim_edgeless.

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
  forall (g: PrimGG), is_partial_lgraph edgeless_graph g.
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

Section ADD_EDGE_MUGRAPH.

Context {g: PrimGG}.
Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
Context {w: Z} {w_rep: Int.min_signed <= w < inf}.

Definition PrimGG_adde':=
  labeledgraph_add_edge g (u,v) u v w.

Instance Fin_PrimGG_adde':
  FiniteGraph (PrimGG_adde').
Proof.
  unfold PrimGG_adde'.
  unfold labeledgraph_add_edge.
  apply pregraph_add_edge_finite.
  apply Finite_PrimGG.
Qed.

Instance SoundPrim_adde':
  (@SoundUAdjMat size inf) PrimGG_adde'.
Proof.
constructor; simpl. constructor; simpl.
+apply (size_representable g).
+apply (inf_representable g).
+apply (vvalid_meaning g).
+unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
  split; intros. destruct H. unfold equiv_dec; destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  apply (evalid_meaning g) in H. apply H.
  subst e. unfold equiv_dec. destruct E_EqDec.
  split. pose proof (inf_representable g); lia. lia.
  unfold complement, equiv in c; contradiction.
  unfold equiv_dec in H; destruct (E_EqDec (u,v)).
  hnf in e0; subst e. right; auto.
  left. apply (evalid_meaning g). auto.
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
+apply Fin_PrimGG_adde'.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
  destruct (E_EqDec (u,v) e). hnf in e0; subst e. trivial. 
  unfold complement, equiv in c. destruct H.
  apply (undirected_edge_rep g e); auto.
  exfalso. apply c.
  symmetry. trivial.
Qed.

Definition PrimGG_adde: PrimGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG SoundUAdjMat
    PrimGG_adde' (SoundPrim_adde').

Lemma adde_vvalid:
  vvalid g v <-> vvalid PrimGG_adde v.
Proof.
intros. simpl. split; auto.
Qed.

Lemma adde_evalid_or:
  forall e, evalid PrimGG_adde e <-> (evalid g e \/ e = (u,v)).
Proof. unfold PrimGG_adde; simpl; unfold addValidFunc. intros; split; auto. Qed.

(*all the Elist stuff are useless by themselves, because (@fin .. sound_matrx) clashes with Fin for some reason*)
Lemma adde_EList_new:
  ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList PrimGG_adde).
Proof.
intros. apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
intros; split; intros. rewrite EList_evalid, adde_evalid_or. destruct H0.
right; symmetry; auto. left; rewrite EList_evalid in H0; auto.
rewrite EList_evalid, adde_evalid_or in H0. destruct H0. right; rewrite EList_evalid; auto. left; symmetry; auto.
Qed.

Lemma adde_EList_old:
  forall e, In e (EList g) -> In e (EList PrimGG_adde).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
apply H1. rewrite adde_evalid_or. left; rewrite <- EList_evalid; apply H.
Qed.

Lemma adde_EList_rev:
  forall l, ~ evalid g (u,v) ->
    Permutation ((u,v)::l) (EList PrimGG_adde) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList PrimGG_adde)).
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
  forall e', evalid g e' -> src PrimGG_adde e' = src g e'.
Proof.
  intros.
  pose proof (edge_src_fst g e').
  pose proof (edge_src_fst PrimGG_adde e').
  replace (src g e') with (fst e') by trivial.
  replace (src PrimGG_adde e') with (fst e') by trivial.
  reflexivity.
Qed.

Lemma adde_dst:
  forall e', evalid g e' -> dst PrimGG_adde e' = dst g e'.
Proof.
  intros.
  pose proof (edge_dst_snd g e').
  pose proof (edge_dst_snd PrimGG_adde e').
  replace (dst g e') with (snd e') by trivial.
  replace (dst PrimGG_adde e') with (snd e') by trivial.
  reflexivity.
Qed.

Lemma adde_elabel_new:
  elabel PrimGG_adde (u,v) = w.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec. auto.
unfold complement, equiv in c. contradiction.
Qed.

Lemma adde_elabel_old:
  forall e, e <> (u,v) -> elabel PrimGG_adde e = elabel g e.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0; contradiction.
auto.
Qed.

Lemma adde_partial_graph:
  forall (g': PrimGG), is_partial_graph g g' -> evalid g' (u,v) -> is_partial_graph PrimGG_adde g'.
Proof.
intros. destruct H as [? [? [? ?]]].
split. intros. simpl. apply H. auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
apply H1; auto. subst e; auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H2. apply adde_src. auto. auto. rewrite adde_src in H5 by auto. simpl in H5; auto.
subst e. rewrite (edge_src_fst g').
rewrite (edge_src_fst PrimGG_adde); auto.
intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H3. apply adde_dst. auto. auto. rewrite adde_dst in H5 by auto. simpl in H5; auto.
subst e. rewrite (edge_dst_snd g'), (edge_dst_snd PrimGG_adde); auto.
Qed.

Lemma adde_partial_lgraph:
  forall (g': PrimGG), is_partial_lgraph g g' -> evalid g' (u,v) -> w = elabel g' (u,v) -> is_partial_lgraph PrimGG_adde g'.
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

End ADD_EDGE_MUGRAPH.

Section REMOVE_EDGE_MUGRAPH.

Context {g: PrimGG}.
Context {e: E} {evalid_e: evalid g e}.

Definition PrimGG_eremove':=
  @Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG (pregraph_remove_edge g e)
  (vlabel g)
  (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
  (glabel g).

Instance Fin_PrimGG_eremove':
  FiniteGraph (PrimGG_eremove').
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
  (@SoundUAdjMat size inf) PrimGG_eremove'.
Proof.
constructor; simpl. constructor; simpl.
++apply (size_representable g).
++apply (inf_representable g).
++apply (vvalid_meaning g).
++unfold removeValidFunc; split; intros; destruct (E_EqDec e0 e).
  destruct H. hnf in e1. contradiction.
  apply (evalid_meaning g). apply H.
  destruct H. apply Zaux.Zgt_not_eq in H0. contradiction.
  apply (evalid_meaning g) in H; auto.
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
++apply Fin_PrimGG_eremove'.
++unfold removeValidFunc; intros. destruct H.
apply (undirected_edge_rep g); trivial.
Qed.

Definition PrimGG_eremove: PrimGG :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG SoundUAdjMat
    PrimGG_eremove' (SoundPrim_eremove').

Lemma eremove_EList:
  forall l, Permutation (e::l) (EList g) -> Permutation l (EList PrimGG_eremove).
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
  forall l, evalid g e -> Permutation l (EList (PrimGG_eremove)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList PrimGG_eremove)).
rewrite EList_evalid. simpl. unfold removeValidFunc, not; intros. destruct H1. contradiction.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList PrimGG_eremove))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList PrimGG_eremove))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid PrimGG_eremove x).
simpl. unfold removeValidFunc. rewrite EList_evalid in H3. split; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList PrimGG_eremove))). apply Permutation_sym; auto. apply H4.
Qed.

End REMOVE_EDGE_MUGRAPH.

(**************MST****************)

Definition minimum_spanning_forest (t g: PrimGG) :=
 labeled_spanning_uforest t g /\
  forall (t': PrimGG), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

Lemma partial_lgraph_spanning_equiv:
forall (t1 t2 g: PrimGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
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
forall (t1 t2 g: PrimGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
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
forall (t1 t2 g: PrimGG), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> minimum_spanning_forest t2 g -> minimum_spanning_forest t1 g.
Proof.
intros. split. auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t2 0) _ ).
apply Z.eq_le_incl. apply (partial_lgraph_spanning_sum_LE t1 t2 g); auto. apply H1.
apply H1; auto.
Qed.

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_DE_equiv:
  forall (g: PrimGG) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

Lemma exists_labeled_spanning_uforest_pre:
forall (l: list E) (g: PrimGG), Permutation l (EList g) -> exists (t: PrimGG), labeled_spanning_uforest t g.
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
set (remove_a:=(@PrimGG_eremove g a)).
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
set (adde_a:=@PrimGG_adde t u v H3 H4 H5 w H6).
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
forall (g: PrimGG), exists (t: PrimGG), labeled_spanning_uforest t g.
Proof.
intros. apply (exists_labeled_spanning_uforest_pre (EList g)). apply Permutation_refl.
Qed.

Lemma partial_graph_incl:
forall (t g: PrimGG), is_partial_graph t g -> incl (EList t) (EList g).
Proof.
unfold incl; intros. rewrite EList_evalid in *. apply H; auto.
Qed.

Lemma exists_Zmin: (* TODO move this *)
  forall {A:Type} (l: list A) (f: A -> Z), l <> nil -> exists a, In a l /\ (forall b, In b l -> f a <= f b).
Proof.
induction l; intros. contradiction.
destruct l. exists a. split. left; auto. intros. destruct H0. subst b. lia. contradiction.
assert (exists a : A, In a (a0 :: l) /\ (forall b : A, In b (a0 :: l) -> f a <= f b)). apply IHl. unfold not; intros. inversion H0.
destruct H0 as [a' [? ?]].
destruct (Z.le_ge_cases (f a) (f a')).
exists a. split. left; auto. intros. destruct H3. subst a; lia. apply H1 in H3. lia.
exists a'. split. right; auto. intros. destruct H3. subst b; lia. apply H1 in H3; lia.
Qed.

Lemma exists_dec:
forall (g: PrimGG) l, (exists (t: PrimGG), labeled_spanning_uforest t g /\ Permutation l (EList t)) \/
  ~ (exists (t: PrimGG), labeled_spanning_uforest t g /\ Permutation l (EList t)).
Proof.
intros. tauto.
Qed.

Lemma partial_lgraph_elabel_map:
forall (t g: PrimGG) l, is_partial_lgraph t g -> incl l (EList t) ->
  map (elabel t) l = map (elabel g) l.
Proof.
induction l; intros. simpl; auto.
simpl. replace (elabel g a) with (elabel t a). rewrite IHl; auto.
apply incl_cons_inv in H0; auto.
apply H. rewrite <- EList_evalid. apply H0. left; auto.
Qed.

(* needs PrimGG and NoDup_incl_ordered_powerlist, which means it should probably stay right here *) 
Lemma exists_msf:
forall {E_EqDec : EqDec E eq} (g: PrimGG), exists (t: PrimGG), minimum_spanning_forest t g.
Proof.
intros. pose proof (NoDup_incl_ordered_powerlist (EList g) (NoDup_EList g)).
destruct H as [L ?].
(*now what I need is the subset of L that exists t, labeled_spanning_uforest t g ...*)
destruct (list_decidable_prop_reduced_list
  (fun l' => NoDup l' /\ incl l' (EList g) /\ (forall x y, In x l' -> In y l' ->
      (find l' x 0 <= find l' y 0 <-> find (EList g) x 0 <= find (EList g) y 0)))
  (fun l => (exists (t: PrimGG), labeled_spanning_uforest t g /\ Permutation l (EList t)))
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
forall {E_EqDec : EqDec E eq} (t g: PrimGG), labeled_spanning_uforest t g ->
  (forall t', minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
  minimum_spanning_forest t g.
Proof.
intros. unfold minimum_spanning_forest. split. auto.
intros. destruct (exists_msf g) as [msf ?].
apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
apply H2. auto.
Qed.

Corollary msf_if_le_msf':
forall {E_EqDec : EqDec E eq} (t t' g: PrimGG), labeled_spanning_uforest t g ->
  minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
  minimum_spanning_forest t g.
Proof.
intros. apply msf_if_le_msf; auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
apply H0. apply H2.
Qed.

(*MOVE TO APPROPRIATE PLACES*)

(*ideally generalise in_dec to any decidable function, and don't need NoDup*)
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

Lemma fold_left_Zadd_diff_accum:
forall (l: list Z) (x y: Z), x <= y -> fold_left Z.add l x <= fold_left Z.add l y.
Proof.
induction l; intros. simpl; auto.
apply IHl. lia.
Qed.

Lemma fold_left_accum_Zadd:
forall (l: list Z) (x y: Z), fold_left Z.add l (x+y) = (fold_left Z.add l x) + y.
Proof.
induction l; intros. simpl; auto.
simpl. replace (x + y + a) with ((x+a) + y) by lia. apply (IHl (x+a) y).
Qed.

Lemma fold_left_Zadd_comp:
forall (l1 l2: list Z), Zlength l1 = Zlength l2 -> (forall i, 0<=i<Zlength l1 -> Znth i l1 <= Znth i l2)
  -> (forall s, fold_left Z.add l1 s <= fold_left Z.add l2 s).
Proof.
induction l1; intros.
rewrite Zlength_nil in H. symmetry in H. apply Zlength_nil_inv in H. subst l2. lia.
destruct l2. rewrite Zlength_cons in H. rewrite Zlength_nil in H. pose proof (Zlength_nonneg l1). lia.
simpl. assert (a <= z). replace a with (Znth 0 (a::l1)). replace z with (Znth 0 (z::l2)).
apply H0. split. lia. rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia.
auto. auto.
apply (Z.le_trans _ (fold_left Z.add l1 (s + z)) _).
apply fold_left_Zadd_diff_accum. lia.
apply IHl1. do 2 rewrite Zlength_cons in H. lia.
intros. replace (Znth i l1) with (Znth (i+1) (a::l1)).
 replace (Znth i l2) with (Znth (i+1) (z::l2)). apply H0. rewrite Zlength_cons. lia.
all: rewrite (Znth_pos_cons (i+1)) by lia; rewrite Z.add_simpl_r; auto.
Qed.

Lemma fold_left_Zadd_map_remove:
forall {A: Type} {EA: EquivDec.EqDec A eq} l f b,
  In b l -> NoDup l ->
  fold_left Z.add (map f (remove EA b l)) 0 = (fold_left Z.add (map f l) 0) - f b.
Proof.
induction l; intros. contradiction.
simpl. rewrite fold_left_accum_Zadd.
replace (fold_left Z.add (map f l) 0 + f a - f b) with
  (fold_left Z.add (map f l) 0 - f b + f a) by lia.
destruct H; destruct (EA b a). 
++hnf in e. subst a. assert (~ In b l). apply NoDup_cons_2 in H0; auto.
rewrite remove_not_in by auto. rewrite Z.sub_add. auto.
++unfold RelationClasses.complement, Equivalence.equiv in c. subst a. contradiction.
++hnf in e; subst a. apply NoDup_cons_2 in H0. contradiction.
++simpl. rewrite fold_left_accum_Zadd. apply NoDup_cons_1 in H0. rewrite IHl; auto.
Qed.

Lemma path_partition_checkpoint':
forall (g: PrimGG) {fg: FiniteGraph g} (l1 l2: list V) p l a b, Permutation (l1++l2) (VList g) ->
  In a l1 -> In b l2 -> connected_by_path g p a b -> fits_upath g l p ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l1 /\ In v2 l2 /\ (exists e, adj_edge g e v1 v2 /\ In e l).
Proof.
  induction p; intros. destruct H2. destruct H4. inversion H4.
  destruct p. destruct H2. destruct H4. inversion H4; inversion H5; subst a. subst a0.
  assert (~ In b l2).
  apply (NoDup_app_not_in V l1). apply (Permutation_NoDup (l:=VList g)).
  apply Permutation_sym; auto. apply NoDup_VList. auto. contradiction.
  destruct l. simpl in H3; contradiction.
  destruct H2. destruct H4. destruct H2. inversion H4. subst a0.
  assert (In v (l1 ++ l2)). apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto.
  rewrite VList_vvalid. apply adjacent_requires_vvalid in H2; apply H2.
  apply in_app_or in H7; destruct H7.
  assert (exists v1 v2 : V, In v1 (v :: p) /\ In v2 (v :: p) /\
    In v1 l1 /\ In v2 l2 /\ (exists e, adj_edge g e v1 v2 /\ In e l)). apply (IHp l v b); auto.
  split. auto. split. simpl; auto. rewrite last_error_cons in H5. auto.
    unfold not; intros. assert (In v (v::p)). left; auto. rewrite H8 in H9. contradiction. auto. apply H3.
  destruct H8 as [v1 [v2 [? [? [? [? ?]]]]]]. exists v1; exists v2. split. right; auto. split. right; auto.
  split; auto. split; auto. destruct H12 as [e0 [? ?]]. exists e0. split. auto. right; auto.
  exists a; exists v. split. left; auto. split. right; left; auto. split; auto. split; auto.
  destruct H3. exists e. split; auto. left; auto.
Qed.

Lemma path_partition_checkpoint:
forall (g: PrimGG) {fg: FiniteGraph g} (l1 l2: list V) p a b, Permutation (l1++l2) (VList g) ->
  In a l1 -> In b l2 -> connected_by_path g p a b ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l1 /\ In v2 l2 /\ adjacent g v1 v2.
Proof.
intros. assert (exists l, fits_upath g l p). apply connected_exists_list_edges in H2; auto. destruct H3 as [l ?].
pose proof (path_partition_checkpoint' g l1 l2 p l a b H H0 H1 H2 H3). destruct H4 as [v1 [v2 [? [? [? [? ?]]]]]].
exists v1; exists v2. repeat split; auto. destruct H8 as [e [? ?]]. exists e; auto.
Qed.

Corollary path_partition_checkpoint2:
forall (g: PrimGG) {fg: FiniteGraph g} (l: list V) p l' a b, In a l -> ~ In b l ->
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

Lemma list_eq_Znth:
  forall {A:Type} {d: Inhabitant A} (l l': list A), Zlength l = Zlength l' ->
    (forall i, 0 <= i < Zlength l -> Znth i l = Znth i l') ->
    l = l'.
Proof.
induction l; intros. symmetry; apply Zlength_nil_inv. rewrite Zlength_nil in H; auto.
destruct l'. rewrite Zlength_cons, Zlength_nil in H.
pose proof (Zlength_nonneg (A:=A) l).
assert (Zlength l < Z.succ (Zlength l)) by lia. lia.
replace a with (Znth 0 (a::l)). 2: rewrite Znth_0_cons; auto.
replace a0 with (Znth 0 (a0::l)). 2: rewrite Znth_0_cons; auto.
rewrite (H0 0). 2: rewrite Zlength_cons; pose proof (Zlength_nonneg (A:=A) l); lia.
rewrite (IHl l'); auto.
apply Z.succ_inj. do 2 rewrite Zlength_cons in H. auto.
intros. replace (Znth i l) with (Znth (i+1) (a::l)).
replace (Znth i l') with (Znth (i+1) (a0::l')). apply H0. rewrite Zlength_cons. lia.
replace (Znth i l') with (Znth (i+1 - 1) l'). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
replace (Znth i l) with (Znth (i+1 - 1) l). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
Qed.

Lemma Zlt_Zmin:
forall x y, x < y -> Z.min x y = x.
Proof. intros. rewrite Zmin_spec. destruct (zlt x y); lia. Qed.

Lemma sublist_of_nil:
forall {A:Type} lo hi, sublist lo hi (nil (A:=A)) = nil.
Proof.
intros. unfold sublist. rewrite firstn_nil. rewrite skipn_nil. auto.
Qed.

Lemma sublist_overshoot:
forall {A:Type} (l: list A) lo hi, Zlength l <= lo -> sublist lo hi l = nil.
Proof.
intros. unfold sublist.
rewrite skipn_short; auto.
rewrite <- ZtoNat_Zlength.
rewrite Zlength_firstn.
destruct (Z.lt_trichotomy 0 hi). rewrite Z.max_r by lia.
destruct (Z.lt_trichotomy hi (Zlength l)). rewrite Z.min_l. lia. lia. destruct H1. 
subst hi. rewrite Z.min_id. lia. rewrite Z.min_r by lia. lia.
destruct H0. subst hi. rewrite Z.max_id. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
rewrite Z.max_l by lia. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
Qed.

Lemma sublist_same_overshoot:
forall {A:Type} (l: list A) hi, Zlength l <= hi -> sublist 0 hi l = l.
Proof.
intros. unfold sublist. rewrite skipn_0. rewrite firstn_same. auto.
rewrite <- ZtoNat_Zlength. lia.
Qed.

End MathPrimGraph.
