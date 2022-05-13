Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.zlist.sublist.
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

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(* Concretizing the EdgelistGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  |   unit  |  Z  | unit |  Finite   |
*)

Definition VType : Type := Z. (*0...V-1*)
Definition EType : Type := VType * VType.
Definition LE : Type := Z. (*weight*)
Definition LV: Type := unit. (*I don't think we need this*)
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec v v0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Definition WEdgeListGraph := LabeledGraph VType EType LV LE LG.

Class Fin (g: WEdgeListGraph) :=
  { fin: FiniteGraph g; }.

Definition FiniteWEdgeListGraph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

Definition FiniteWEdgeListGraph_WEdgeListGraph
           (g: FiniteWEdgeListGraph) : WEdgeListGraph := lg_gg g.
Local Coercion FiniteWEdgeListGraph_WEdgeListGraph: FiniteWEdgeListGraph >-> WEdgeListGraph.
Local Identity Coercion WEdgeListGraph_LabeledGraph: WEdgeListGraph >-> LabeledGraph.

Instance finGraph (g: FiniteWEdgeListGraph): FiniteGraph g := @fin g (@sound_gg _ _ _ _ _ _ _ _ g).
(* Nice. Now your definitions will be cleaner. *)

Definition vertex_valid (g: WEdgeListGraph): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> (vvalid g (src g e) /\ vvalid g (dst g e)).

Definition weight_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition src_edge (g : WEdgeListGraph): Prop :=
  forall e, evalid g e -> src g e = fst e.

Definition dst_edge (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> dst g e = snd e.

Definition sound_weighted_edge_graph (g: WEdgeListGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ weight_valid g /\ src_edge g /\ dst_edge g.

(*because it keeps appearing*)
Lemma sound_src:
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> fst e = src g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_dst:
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> snd e = dst g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_strong_evalid: (*literally the definition of edge_valid*)
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> strong_evalid g e.
Proof.
intros. split. auto. apply H. auto.
Qed.

Corollary sound_uv_vvalid:
  forall (g: WEdgeListGraph) u v, sound_weighted_edge_graph g -> evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply sound_strong_evalid in H0; auto. destruct H0.
destruct H as [? [? [? [? ?]]]].
rewrite H4, H5 in H1; auto.
Qed.

Definition numV (g: FiniteWEdgeListGraph) : Z := Zlength (VList g).
Definition numE (g: FiniteWEdgeListGraph) : Z := Zlength (EList g).

Lemma numE_pos: forall g, 0 <= numE g.
Proof. intros. unfold numE. apply Zlength_nonneg. Qed.

Definition edge_to_wedge (g: WEdgeListGraph) e : LE * EType := (elabel g e, e).

Definition graph_to_wedgelist (g: FiniteWEdgeListGraph) : list (LE * EType) :=
  map (edge_to_wedge g) (EList g).

Lemma g2wedgelist_numE:
  forall g, Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist. rewrite Zlength_map. trivial.
Qed.

Lemma NoDup_g2wedgelist:
  forall g, NoDup (graph_to_wedgelist g).
Proof.
intros. apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective; intros. inversion H. auto. apply NoDup_EList.
Qed.

Lemma g2wedgelist_evalid:
  forall g w, In w (graph_to_wedgelist g) -> evalid g (snd w).
Proof.
intros. apply list_in_map_inv in H. destruct H; destruct H.
apply EList_evalid in H0. unfold edge_to_wedge in H. inversion H. simpl. auto.
Qed.

Lemma sound_g2wedgelist_repable:
  forall g w, In w (graph_to_wedgelist g) -> sound_weighted_edge_graph g -> 
    Int.min_signed <= fst w <= Int.max_signed /\
    Int.min_signed <= fst (snd w) <= Int.max_signed /\
    Int.min_signed <= snd (snd w) <= Int.max_signed.
Proof.
intros. unfold graph_to_wedgelist in H.
apply list_in_map_inv in H. unfold edge_to_wedge in H. destruct H; destruct H.
destruct H0 as [? [? [? [? ?]]]].
subst w; simpl. split. apply H3. apply EList_evalid in H1; auto.
apply EList_evalid in H1. replace (fst x) with (src g x). replace (snd x) with (dst g x).
apply H2 in H1. destruct H1. unfold vertex_valid in H0. apply H0 in H. apply H0 in H1.
simpl. set (i:=Int.min_signed); compute in i; subst i.
split; lia.
apply H5; auto. apply H4; auto.
Qed.

(*******************SPECIFIC TYPES OF GRAPHS********************)
Definition empty_WEdgeListGraph : WEdgeListGraph :=
  (empty_labeledgraph (fun e => fst e) (fun e => snd e) (tt: LV) (0: LE) (tt: LG)).

Definition empty_WEdgeListGraph_finite:
  FiniteGraph empty_WEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Instance Fin_empty_WEdgeListGraph:
  Fin empty_WEdgeListGraph.
Proof.
  constructor.
  apply empty_WEdgeListGraph_finite.
Qed.

Definition empty_FiniteWEdgeListGraph : FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph empty_WEdgeListGraph) Fin_empty_WEdgeListGraph.

Definition empty_FiniteWEdgeListGraph_finite:
  FiniteGraph empty_FiniteWEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Lemma empty_WEdgeListGraph_sound:
  sound_weighted_edge_graph empty_WEdgeListGraph.
Proof.
  repeat split; contradiction.
Qed.

Lemma empty_WEdgeListGraph_VList: VList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold VList.
  destruct finiteV.
  destruct a.
  unfold proj1_sig.
  destruct x; [trivial | exfalso].
  assert (In v (v::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Lemma empty_WEdgeListGraph_EList: EList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold EList.
  destruct finiteE.
  destruct a.
  unfold proj1_sig. 
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Corollary empty_WEdgeListGraph_numV: numV empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numV. rewrite empty_WEdgeListGraph_VList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_numE: numE empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numE. rewrite empty_WEdgeListGraph_EList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_graph_to_wedgelist:
  graph_to_wedgelist empty_FiniteWEdgeListGraph = nil.
Proof.
unfold graph_to_wedgelist. rewrite empty_WEdgeListGraph_EList. reflexivity.
Qed.

(**********Edgeless graph with V vertices*************)
(*Built off empty WEdgelessGraph*)
(*Skipping an arbitrary list of vertices, because we need NoDup, and our design forbids the skipping of vertices anyway *)

Definition Zseq (z: Z) : list Z := map Z.of_nat (seq 0%nat (Z.to_nat z)).

Lemma Zseq_NoDup:
  forall z, NoDup (Zseq z).
Proof.
unfold Zseq; intros. destruct z; simpl; try apply NoDup_nil.
apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective. apply Nat2Z.inj.
apply seq_NoDup.
Qed.

Lemma Zseq_In:
  forall z x, In x (Zseq z) <-> 0 <= x < z.
Proof.
intros; unfold Zseq; simpl; split; intros.
+ destruct x; destruct z; try inversion H.
  lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H. rewrite in_seq in H0. lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H.
  assert (Z.neg p < 0) by (apply Pos2Z.neg_is_neg). assert (0 <= Z.of_nat x) by (apply Nat2Z.is_nonneg). lia.
+ destruct x; destruct z; try lia.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p))) 0%nat). rewrite in_seq.
  simpl. lia. rewrite <- positive_nat_Z.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p0))) (Pos.to_nat p)). rewrite in_seq. lia.
Qed.

Corollary Zseq_Zlength:
  forall z, 0 <= z -> Zlength (Zseq z) = z.
Proof.
intros. unfold Zseq. rewrite (Zlength_map nat Z Z.of_nat (seq 0 (Z.to_nat z))).
rewrite Zlength_correct. rewrite seq_length.
apply Z2Nat.id. lia.
Qed.

Definition edgeless_WEdgeLGraph (z: Z): WEdgeListGraph :=
@Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG
  (@Build_PreGraph VType EType V_EqDec E_EqDec (fun v => 0 <= v < z) (fun e => False) fst snd)
  (fun v => tt) (fun e => 0) tt.

Instance Fin_edgeless_WEdgeLGraph (z: Z):
  Fin (edgeless_WEdgeLGraph z).
Proof.
constructor. constructor; unfold EnumEnsembles.Enumerable.
exists (Zseq z); split. apply Zseq_NoDup.
unfold edgeless_WEdgeLGraph. simpl. intros. apply Zseq_In.
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_WEdgeGraph (z: Z): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (edgeless_WEdgeLGraph z)) (Fin_edgeless_WEdgeLGraph z).

Lemma edgeless_WEdgeGraph_vvalid:
  forall v k, 0 <= k < v <-> vvalid (edgeless_WEdgeGraph v) k.
Proof.
simpl. intros; split; intros; auto.
Qed.

Lemma edgeless_WEdgeGraph_Permutation:
  forall v, Permutation (VList (edgeless_WEdgeGraph v)) (Zseq v).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply Zseq_NoDup.
intros; rewrite Zseq_In. unfold VList; destruct finiteV; simpl.
destruct a. rewrite H0. rewrite edgeless_WEdgeGraph_vvalid. split; auto.
Qed.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Lemma edgeless_WEdgeGraph_numV:
  forall v, 0 <= v -> numV (edgeless_WEdgeGraph v) = v.
Proof.
unfold numV. intros.
assert (Zlength (VList (edgeless_WEdgeGraph v)) = Zlength (Zseq v)).
apply Permutation_Zlength. apply edgeless_WEdgeGraph_Permutation.
rewrite H0. rewrite Zseq_Zlength. auto. apply H.
Qed.

Lemma edgeless_WEdgeGraph_evalid:
  forall v e, ~ evalid (edgeless_WEdgeGraph v) e.
Proof.
intros. unfold edgeless_WEdgeGraph; simpl. auto.
Qed.

Lemma edgeless_WEdgeGraph_EList:
  forall v, EList (edgeless_WEdgeGraph v) = nil.
Proof.
  intros. unfold edgeless_WEdgeGraph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Corollary edgeless_WEdgeGraph_numE:
  forall v, numE (edgeless_WEdgeGraph v) = 0.
Proof.
unfold numE. intros. rewrite edgeless_WEdgeGraph_EList. apply Zlength_nil.
Qed.

Lemma edgeless_WEdgeGraph_sound:
  forall z, 0 <= z <= Int.max_signed -> sound_weighted_edge_graph (edgeless_WEdgeGraph z).
Proof.
intros. split. unfold vertex_valid; intros. apply edgeless_WEdgeGraph_vvalid in H0. lia.
split. unfold edge_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_WEdgeGraph_EList in H0. contradiction.
split. unfold weight_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_WEdgeGraph_EList in H0. contradiction.
split. unfold src_edge; intros. simpl; auto.
split.
Qed.

Corollary graph_to_wedgelist_edgeless_WEdgeGraph:
  forall v, graph_to_wedgelist (edgeless_WEdgeGraph v) = nil.
Proof.
unfold graph_to_wedgelist; intros. rewrite edgeless_WEdgeGraph_EList. auto.
Qed.

Lemma uforest'_edgeless_WEdgeGraph:
  forall z, uforest' (edgeless_WEdgeGraph z).
Proof.
split; intros.
(*no self-loops*)
apply edgeless_WEdgeGraph_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_WEdgeGraph_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_WEdgeGraph_evalid in H; contradiction.
(*main forest definition*)
unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

(***********ADDING A SINGLE EDGE************)

(**Adding is necessary for the kruskal algorithm**)
Definition WEdgeListGraph_adde (g: WEdgeListGraph) (e: EType) (w: LE):=
  labeledgraph_add_edge g e (fst e) (snd e) w.

Instance Fin_WEdgeListGraph_adde (g: FiniteWEdgeListGraph) (e: EType) (w: LE) :
  Fin (WEdgeListGraph_adde g e w).
Proof.
unfold WEdgeListGraph_adde. unfold labeledgraph_add_edge.
constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc. destruct (in_dec E_EqDec e (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists (e::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Definition FiniteWEdgeListGraph_adde (g: FiniteWEdgeListGraph) (e: EType) (w: LE): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (WEdgeListGraph_adde g e w))
    (Fin_WEdgeListGraph_adde g e w).

Corollary adde_numV:
  forall (g: FiniteWEdgeListGraph)  e w, numV (FiniteWEdgeListGraph_adde g e w) = numV g.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. unfold numV. simpl. unfold VList.
destruct finiteV. destruct finiteV. simpl. simpl in a.
destruct a. destruct a0. assert (Permutation x x0). apply NoDup_Permutation; auto.
intros. rewrite H0. rewrite H2. split; auto.
apply Permutation_Zlength. auto.
Qed.

(*should add an EList1 where e is already in g, but it's not necessary atm*)
Lemma adde_EList1_new:
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> Permutation (e::(EList g)) (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros.
unfold FiniteWEdgeListGraph_adde. simpl. unfold pregraph_add_edge.
set (l:=e::EList g). unfold EList. destruct finiteE. simpl.
destruct a. unfold addValidFunc in H1. simpl in H1.
apply NoDup_Permutation. unfold l. apply NoDup_cons. rewrite EList_evalid. auto. apply NoDup_EList. auto.
intros; split; intros. apply H1. destruct H2. right; auto. left. rewrite <- EList_evalid. apply H2.
apply H1 in H2. unfold l. destruct H2.
right. apply EList_evalid. auto.
left. auto.
Qed.

Lemma adde_EList2:
  forall (g: FiniteWEdgeListGraph) e w e', In e' (EList g) -> In e' (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
unfold FiniteWEdgeListGraph_adde in H1. simpl in H1. unfold addValidFunc in H1. apply H1.
left. apply EList_evalid in H. apply H.
Qed.

Lemma adde_elabel1:
  forall (g: FiniteWEdgeListGraph) e w, elabel (FiniteWEdgeListGraph_adde g e w) e = w.
Proof.
intros. simpl. unfold update_elabel. unfold equiv_dec. destruct E_EqDec. auto.
unfold complement in c. unfold equiv in c. contradiction.
Qed.

Lemma adde_evalid_or:
  forall (g: FiniteWEdgeListGraph) e w e', evalid (FiniteWEdgeListGraph_adde g e w) e' -> (evalid g e' \/ e' = e).
Proof. unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. apply H. Qed.

Lemma adde_EList_rev:
  forall (g: FiniteWEdgeListGraph) e w l, ~ evalid g e ->
    Permutation (e::l) (EList (FiniteWEdgeListGraph_adde g e w)) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList (FiniteWEdgeListGraph_adde g e w))).
apply (Permutation_in (l:=e::l)). auto. right; auto.
apply EList_evalid in H2. apply adde_evalid_or in H2. destruct H2.
rewrite EList_evalid; auto.
subst x. assert (NoDup (e::l)). apply NoDup_Perm_EList in H0; auto.
apply NoDup_cons_2 in H2. contradiction.
destruct (E_EqDec x e). unfold equiv in e0. subst x. apply EList_evalid in H1; contradiction.
unfold complement, equiv in c.
apply (adde_EList2 g e w) in H1.
apply (Permutation_in (l':=e::l)) in H1. destruct H1. symmetry in H1; contradiction. auto.
apply Permutation_sym; auto.
Qed.

Lemma adde_g2wedgelist_1:
  forall (g: FiniteWEdgeListGraph) e w, In (w, e) (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. unfold edge_to_wedge.
replace (w, e) with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e).
apply in_map. apply EList_evalid. apply add_edge_evalid.
unfold edge_to_wedge. rewrite adde_elabel1. auto.
Qed.

Corollary adde_g2wedgelist_2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> In (elabel g e', e') (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. replace (elabel g e', e') with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e').
apply in_map. apply EList_evalid. apply add_edge_preserves_evalid; auto.
unfold edge_to_wedge; simpl. unfold update_elabel.
unfold equiv_dec. destruct E_EqDec. contradiction. auto.
Qed.

Lemma adde_numE:
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> numE (FiniteWEdgeListGraph_adde g e w) = numE g + 1.
Proof.
intros. unfold numE.
pose proof (adde_EList1_new g e w H).
rewrite <- (Permutation_Zlength _ _ H0). apply Zlength_cons.
Qed.

Lemma adde_sound:
  forall (g: FiniteWEdgeListGraph) e w, sound_weighted_edge_graph g ->
    vvalid g (fst e) -> vvalid g (snd e) -> Int.min_signed <= w <= Int.max_signed ->
    sound_weighted_edge_graph (FiniteWEdgeListGraph_adde g e w).
Proof.
intros. split.
unfold vertex_valid; intros. apply H. simpl in H3. apply H3.
split. unfold edge_valid; intros. simpl in H3. destruct H3.
simpl. unfold updateEdgeFunc. unfold equiv_dec.
destruct E_EqDec; [split; auto | apply H; apply H3].
subst e0. simpl; unfold updateEdgeFunc.
unfold equiv_dec. destruct E_EqDec. split; auto. unfold complement, equiv in c; contradiction.
split. unfold weight_valid; intros. simpl in H3. unfold addValidFunc in H3.
simpl. unfold update_elabel. unfold equiv_dec.
destruct (E_EqDec e e0). apply H2.
destruct H3. apply H. apply H3. rewrite H3 in c. unfold complement in c.
assert (equiv e e). apply Equivalence.equiv_reflexive_obligation_1. contradiction.
split. unfold src_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H. unfold addValidFunc in H3. destruct H3. auto. unfold complement, equiv in c. subst e0; contradiction.
unfold dst_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H. unfold addValidFunc in H3. destruct H3. auto. unfold complement, equiv in c. subst e0; contradiction.
Qed.

(*****************************REMOVE EDGES****************************)

Definition WEdgeListGraph_eremove (g: WEdgeListGraph) (e: EType) :=
  @Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG (pregraph_remove_edge g e)
  (vlabel g)
  (*(fun e0 => if eq_dec e0 e then ? else elabel g e )*) (elabel g)
  (glabel g).

(*there is a clash with pregraph_remove_edge_finite*)
Instance Fin_WEdgeListGraph_eremove (g: FiniteWEdgeListGraph) (e: EType) :
  Fin (WEdgeListGraph_eremove g e).
Proof.
unfold WEdgeListGraph_eremove. unfold pregraph_remove_edge.
constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
destruct (in_dec E_EqDec e (EList g)).
(*case e already inside*)
exists (remove E_EqDec e (EList (g))). split.
apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff. rewrite EList_evalid. split; auto.
(*case e not inside*)
exists (EList g). split. apply NoDup_EList.
intros; split; intros. split. apply EList_evalid in H; auto.
unfold not; intros; subst x. contradiction.
destruct H. apply EList_evalid. auto.
Qed.

Definition FiniteWEdgeListGraph_eremove (g: FiniteWEdgeListGraph) (e: EType): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (WEdgeListGraph_eremove g e))
    (Fin_WEdgeListGraph_eremove g e).

Lemma eremove_vvalid:
  forall (g: FiniteWEdgeListGraph) (e: EType) v, vvalid (FiniteWEdgeListGraph_eremove g e) v <-> vvalid g v.
Proof.
simpl. intros; split; auto.
Qed.

(*Don't bother with defining what happens when e isn't inside*)
Lemma eremove_evalid1:
  forall (g: FiniteWEdgeListGraph) e, ~ evalid (FiniteWEdgeListGraph_eremove g e) e.
Proof.
simpl. unfold removeValidFunc, not; intros. destruct H. contradiction.
Qed.

Lemma eremove_sound:
  forall (g: FiniteWEdgeListGraph) e, sound_weighted_edge_graph g -> sound_weighted_edge_graph (FiniteWEdgeListGraph_eremove g e).
Proof.
intros. destruct H as [? [? [? [? ?]]]]. split. apply H.
split. unfold edge_valid; simpl; unfold removeValidFunc.
intros. destruct H4. apply H0; auto.
split. unfold weight_valid; simpl; unfold removeValidFunc. intros.
destruct H4. apply H1; auto.
split. unfold src_edge; simpl; unfold removeValidFunc. intros. apply H2. apply H4.
unfold dst_edge; simpl; unfold removeValidFunc. intros. apply H3. apply H4.
Qed.

Lemma eremove_EList_rev:
  forall (g: FiniteWEdgeListGraph) e l, evalid g e -> Permutation l (EList (FiniteWEdgeListGraph_eremove g e)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList (FiniteWEdgeListGraph_eremove g e))).
rewrite EList_evalid. apply eremove_evalid1.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList (FiniteWEdgeListGraph_eremove g e)))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList (FiniteWEdgeListGraph_eremove g e)))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid (FiniteWEdgeListGraph_eremove g e) x).
apply remove_edge_evalid. split. apply EList_evalid in H3; auto. auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList (FiniteWEdgeListGraph_eremove g e)))). apply Permutation_sym; auto. apply H4.
Qed.

(*****************************PARTIAL LGRAPH AND MSF**********************)
(*These should be abstracted, but we can deal with it after the kruskal proof is done*)

Lemma sound_fits_upath_transfer:
forall p l (g1 g2: FiniteWEdgeListGraph), sound_weighted_edge_graph g1 ->
sound_weighted_edge_graph g2 -> (forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) ->
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
intros. apply (fits_upath_transfer'' p l g1 g2); intros.
apply (valid_upath_vvalid g1 p) in H4. apply H1; auto. apply valid_upath_exists_list_edges'. exists l; auto.
apply H2; auto.
rewrite <- sound_src; auto. rewrite <- sound_src; auto. apply (fits_upath_evalid g1 p l); auto.
rewrite <- sound_dst; auto. rewrite <- sound_dst; auto. apply (fits_upath_evalid g1 p l); auto.
auto.
Qed.

(***********MST stuff***********)

Lemma fold_left_Zadd_diff_accum:
forall (l: list Z) (x y: Z), x <= y -> fold_left Z.add l x <= fold_left Z.add l y.
Proof.
induction l; intros. simpl; auto.
apply IHl. lia.
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

Definition sum_LE (g: FiniteWEdgeListGraph) : LE :=
  fold_left Z.add (DEList g) 0.

Lemma spanning_uforest_sound:
forall (t g: FiniteWEdgeListGraph), sound_weighted_edge_graph g ->
labeled_spanning_uforest t g -> sound_weighted_edge_graph t.
Proof.
intros.
split. unfold vertex_valid; intros. apply H. apply H0. auto.
assert (He: edge_valid t). unfold edge_valid; intros. apply H0; auto.
split. auto.
split. unfold weight_valid; intros.
destruct H0. destruct H0. destruct H2. rewrite H4 by auto. apply H. apply H0. auto.
destruct H as [? [? [? [? ?]]]]. 
split. unfold src_edge; intros. rewrite <- H3; apply H0; auto. apply He; auto.
unfold dst_edge; intros. rewrite <- H4; apply H0; auto. apply He; auto.
Qed.

Definition minimum_spanning_forest (t g: FiniteWEdgeListGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': FiniteWEdgeListGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv:
  forall (g: FiniteWEdgeListGraph) (l: list EType),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

(************SOME GENERAL LIST LEMMAS, SHOULD BE MOVED*********)
(*I can't induct directly on a graph or its EList (have to intros the graph), so relying on these*)

Lemma exists_element_list:
  forall {A B: Type} {A': Inhabitant A} {B': Inhabitant B} (P: A -> B -> Prop) (la: list A),
    (forall a, In a la -> exists b, P a b) ->
    (exists lb, Zlength lb = Zlength la /\ forall i, 0 <= i < Zlength la -> P (Znth i la) (Znth i lb)).
Proof.
induction la; intros. exists nil. split. auto. intros. rewrite Zlength_nil in H0; lia.
assert (forall a : A, In a la -> exists b : B, P a b). intros. apply H. right; auto.
apply IHla in H0. destruct H0 as [lb ?].
assert (exists b : B, P a b). apply H. left; auto. destruct H1 as [b ?].
exists (b::lb). split. do 2 rewrite Zlength_cons; lia.
intros. rewrite Zlength_cons in H2.
destruct (Z.lt_trichotomy 0 i).
do 2 rewrite Znth_pos_cons by lia. apply H0. lia.
destruct H3. subst i. do 2 rewrite Znth_0_cons. auto. lia.
Qed.

Lemma list_not_forall_exists:
  forall {A: Type} {A': Inhabitant A} (l: list A) (P: A -> Prop), l <> nil -> (forall a, P a \/ ~ P a) -> ~ (forall a, In a l -> P a) -> (exists a, In a l /\ ~ P a).
Proof.
induction l; intros.
contradiction.
destruct (H0 a).
assert (exists a0 : A, In a0 l /\ ~ P a0). apply IHl.
(*if l is nil, then (forall a, ... P a) holds*)
unfold not; intros. subst l. assert (forall a0, In a0 (a::nil) -> P a0). intros. destruct H3. subst a0. auto. contradiction. contradiction.
auto.
unfold not; intros.
assert (forall a0, In a0 (a::l) -> P a0). intros. destruct H4. subst a0. auto. apply H3. auto. contradiction.
destruct H3 as [a0 [? ?]]. exists a0. split. right; auto. auto.
exists a. split. left; auto. auto.
Qed.

(******Back to forests*****)

Lemma forest_bridge1:
  forall (g: FiniteWEdgeListGraph) u v, sound_weighted_edge_graph g -> uforest' g ->
    evalid g (u,v) -> bridge g (u,v) u v.
Proof.
unfold bridge; intros.
apply (forest_edge' p l g). auto. apply sound_strong_evalid; auto.
rewrite <- sound_src; auto. rewrite <- sound_dst; auto. auto.
Qed.

Lemma eremove_uforest':
  forall (g: FiniteWEdgeListGraph) e, sound_weighted_edge_graph g -> uforest' g -> evalid g e ->
    uforest' (FiniteWEdgeListGraph_eremove g e) /\ ~ connected (FiniteWEdgeListGraph_eremove g e) (src g e) (dst g e).
Proof.
intros.
destruct e as (u,v). rewrite <- sound_src; auto. rewrite <- sound_dst; auto.
pose proof (eremove_evalid1 g (u,v)). rename H2 into Huv.
assert (Hsound: sound_weighted_edge_graph (FiniteWEdgeListGraph_eremove g (u, v))). apply eremove_sound; auto.
assert (Hvvalid: forall v1 : VType, vvalid (FiniteWEdgeListGraph_eremove g (u, v)) v1 <-> vvalid g v1).
  simpl; intros; split; auto.
split.
{ split. intros. simpl. apply H0. apply H2.
split. intros. unfold adj_edge, strong_evalid in H2; simpl in H2. unfold removeValidFunc in H2. destruct H2. destruct H2. destruct H3.
  destruct H0. destruct H6. apply (H6 u0 v0).
  split; split.
  split. apply H2. apply H2. apply H4.
  split. apply H3. apply H3. apply H5.
split. intros. apply sound_strong_evalid; auto.
unfold unique_simple_upath; intros.
assert (exists l, fits_upath (FiniteWEdgeListGraph_eremove g (u, v)) l p1). apply valid_upath_exists_list_edges. apply H2.
destruct H6 as [l1 ?].
assert (exists l, fits_upath (FiniteWEdgeListGraph_eremove g (u, v)) l p2). apply valid_upath_exists_list_edges. apply H4.
destruct H7 as [l2 ?].
destruct (in_dec E_EqDec (u,v) l1).
apply (fits_upath_evalid (FiniteWEdgeListGraph_eremove g (u, v)) p1) in i; auto. contradiction.
destruct (in_dec E_EqDec (u,v) l2).
apply (fits_upath_evalid (FiniteWEdgeListGraph_eremove g (u, v)) p2) in i; auto. contradiction.
apply (sound_fits_upath_transfer p1 l1 _ g) in H6; auto.
apply (sound_fits_upath_transfer p2 l2 _ g) in H7; auto.
assert (valid_upath g p1). apply valid_upath_exists_list_edges'. exists l1. auto.
assert (valid_upath g p2). apply valid_upath_exists_list_edges'. exists l2. auto.
assert (unique_simple_upath g). apply H0. unfold unique_simple_upath in H10.
destruct H2. destruct H4. destruct H3. destruct H5.
apply (H10 u0 v0 p1 p2). split; auto. split; auto. split; auto. split; auto.
intros. apply (fits_upath_evalid _ _ _ _ H7) in H8. apply H8.
intros. apply (fits_upath_evalid _ _ _ _ H6) in H8. apply H8.
}
{
unfold not, connected; intros.
destruct H2 as [p ?].
assert (exists l, fits_upath (FiniteWEdgeListGraph_eremove g (u, v)) l p). apply valid_upath_exists_list_edges. apply H2.
destruct H3 as [l ?].
assert (fits_upath g l p). apply (sound_fits_upath_transfer p l (FiniteWEdgeListGraph_eremove g (u, v)) g); auto.
intros. apply (fits_upath_evalid _ _ _ _ H3) in H4. apply H4.
assert (connected_by_path g p u v). split.
apply valid_upath_exists_list_edges'. exists l; auto. destruct H2. auto.
pose proof (forest_bridge1 g u v H H0 H1).
assert (In (u,v) l). unfold bridge in H6. apply (H6 p l); auto.
apply (fits_upath_evalid _ _ _ _ H3) in H7. pose proof (eremove_evalid1 g (u,v)). contradiction.
}
Qed.

(******************SORTING****************)

(*Sigh, this is really silly, but I need a sort for this specific "struct"*)
Fixpoint insert (g:FiniteWEdgeListGraph) (i:EType) (l: list EType) :=
  match l with
  | nil => i::nil
  | h::t => if (elabel g i <=? elabel g h) then i::h::t else h :: insert g i t
 end.

Fixpoint sort (g: FiniteWEdgeListGraph) (l: list EType) :=
  match l with
  | nil => nil
  | h::t => insert g h (sort g t)
end.

Inductive sorted (g: FiniteWEdgeListGraph): list EType -> Prop := 
| sorted_nil:
    sorted g nil
| sorted_1: forall x,
    sorted g (x::nil)
| sorted_cons: forall x y l,
     (elabel g x) <= (elabel g y) -> sorted g (y::l) -> sorted g (x::y::l).

Lemma insert_perm: forall (g: FiniteWEdgeListGraph) x l, Permutation (x::l) (insert g x l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. destruct (Z.leb (elabel g x) (elabel g a)). apply Permutation_refl.
apply (Permutation_trans (l':=a::x::l)). apply perm_swap.
apply perm_skip. apply IHl.
Qed.

Theorem sort_perm: forall (g: FiniteWEdgeListGraph) l, Permutation l (sort g l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. apply (Permutation_trans (l':=a::(sort g l))).
apply perm_skip. apply IHl.
apply insert_perm.
Qed.

Lemma insert_sorted:
  forall g a l, sorted g l -> sorted g (insert g a l).
Proof.
intros. induction H.
simpl. apply sorted_1.
simpl. destruct (Z.leb (elabel g a) (elabel g x)) eqn:ax.
apply sorted_cons. apply Z.leb_le. auto. apply sorted_1.
apply Z.leb_gt in ax. apply sorted_cons. lia. apply sorted_1.
simpl.
destruct (Z.leb (elabel g a) (elabel g x)) eqn:ax.
apply sorted_cons. apply Z.leb_le. auto. apply sorted_cons; auto.
apply Z.leb_gt in ax. simpl in IHsorted. destruct (Z.leb (elabel g a) (elabel g y)) eqn:ay.
apply sorted_cons. lia. apply Z.leb_le in ay. apply sorted_cons; auto.
apply Z.leb_gt in ay. apply sorted_cons. lia. apply IHsorted.
Qed.

Theorem sort_sorted: forall (g:FiniteWEdgeListGraph) (l: list EType), sorted g (sort g l).
Proof.
induction l; intros. apply sorted_nil.
destruct l. simpl. apply sorted_1.
simpl in IHl. simpl. apply insert_sorted. auto.
Qed.

Definition sorted' (g: FiniteWEdgeListGraph) (l: list EType) :=
 forall i j, 0 <= i < j -> j < Zlength l -> Z.le (elabel g (Znth i l)) (elabel g (Znth j l)).

Lemma sorted_sorted':
  forall g l, sorted g l -> sorted' g l.
Proof.
intros. unfold sorted'. induction H.
intros. rewrite Zlength_nil in H0. lia.
intros. rewrite Zlength_cons, Zlength_nil in H0. lia.
intros. destruct (Z.lt_trichotomy i 0). lia. destruct H3.
subst i. rewrite Znth_0_cons. rewrite Znth_pos_cons by lia.
destruct (Z.lt_trichotomy (j-1) 0). lia. destruct H3.
rewrite H3. rewrite Znth_0_cons. auto.
specialize IHsorted with 0 (j-1). rewrite Znth_0_cons in IHsorted.
apply (Z.le_trans (elabel g x) (elabel g y)). auto. apply IHsorted. lia.
rewrite Zlength_cons in H2. lia.
rewrite (Znth_pos_cons i) by lia. rewrite (Znth_pos_cons j) by lia. apply IHsorted.
lia. rewrite Zlength_cons in H2. lia.
Qed.
