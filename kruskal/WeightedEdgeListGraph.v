(*Looted from msl_application/DijkstraArrayGraph*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
(*Require Import RamifyCoq.msl_application.ArrayGraph.*) (*I probably need this to transform this graph to the ArrayGraph?*)
Require Import RamifyCoq.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import RamifyCoq.graph.undirected_graph.

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

(* Later, we'll need ways to fish out the LG from the GG, 
   and we'll need to show that the specialized 
   LG you have is, at heart, an LG 
 *)
Definition FiniteWEdgeListGraph_WEdgeListGraph
           (g: FiniteWEdgeListGraph) : WEdgeListGraph := lg_gg g.
Local Coercion FiniteWEdgeListGraph_WEdgeListGraph: FiniteWEdgeListGraph >-> WEdgeListGraph.
Local Identity Coercion WEdgeListGraph_LabeledGraph: WEdgeListGraph >-> LabeledGraph.

(* This is the main thing you needed: an existing instance of 
   how to drag out FiniteGraph properties from your 
   existing GeneralGraph
 *)
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
(*Example of a WEdgeListGraph (returned by init_empty_graph*)
Definition empty_WEdgeListGraph : WEdgeListGraph :=
  (empty_labeledgraph (fun e => fst e) (fun e => snd e) (tt: LV) (0: LE) (tt: LG)).

(* Okay, so you have an empty LabeledGraph above. 
   Now we'll use that to construct a relevant 
   empty GeneralGraph.
 *)

(* First we need an instance to show that such an 
   empty LabeledGraph would satisfy the soundness condition
   of the GeneralGraph. 
 *)
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

(* Next we can build an empty GeneralGraph 
   using the two pieces above
 *)
Definition empty_FiniteWEdgeListGraph : FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
                      (WEdgeListGraph_LabeledGraph empty_WEdgeListGraph) Fin_empty_WEdgeListGraph.

(* and now a quick fact about the new GeneralGraph *)
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

(* Tada, these are all cleaner! *)
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
(*This is a really roundabout way...*)
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

Lemma adde_vvalid:
  forall (g: FiniteWEdgeListGraph)  e w v, vvalid g v <-> vvalid (FiniteWEdgeListGraph_adde g e w) v.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. split; auto.
Qed.

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

Lemma adde_evalid1:
  forall (g: FiniteWEdgeListGraph) e w, evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. right; auto.
Qed.

Lemma adde_evalid2:
  forall (g: FiniteWEdgeListGraph) e w e', evalid g e' -> evalid (FiniteWEdgeListGraph_adde g e w) e'.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. left; auto.
Qed.

Lemma adde_evalid2':
  forall (g: FiniteWEdgeListGraph) e w e', e' <> e -> evalid (FiniteWEdgeListGraph_adde g e w) e' -> evalid g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. destruct H0. auto. contradiction.
Qed.

Lemma adde_evalid_or:
  forall (g: FiniteWEdgeListGraph) e w e', evalid (FiniteWEdgeListGraph_adde g e w) e' -> (evalid g e' \/ e' = e).
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. apply H.
Qed.

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

Lemma adde_src1:
  forall (g: FiniteWEdgeListGraph) e w, src (FiniteWEdgeListGraph_adde g e w) e = fst e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Lemma adde_dst1:
  forall (g: FiniteWEdgeListGraph) e w, dst (FiniteWEdgeListGraph_adde g e w) e = snd e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Lemma adde_src2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> src (FiniteWEdgeListGraph_adde g e w) e' = src g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e0; contradiction. auto.
Qed.

Lemma adde_dst2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> dst (FiniteWEdgeListGraph_adde g e w) e' = dst g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e0; contradiction. auto.
Qed.

Corollary adde_strong_evalid1:
  forall (g: FiniteWEdgeListGraph) e w,
  vvalid g (fst e) -> vvalid g (snd e) ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. split. apply adde_evalid1.
split; apply adde_vvalid.
rewrite adde_src1. auto.
rewrite adde_dst1. auto.
Qed.

Lemma adde_strong_evalid2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' ->
  strong_evalid g e' ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e'.
Proof.
intros. split. apply adde_evalid2. apply H0.
do 2 rewrite <- adde_vvalid. split.
rewrite adde_src2. apply H0. auto.
rewrite adde_dst2. apply H0. auto.
Qed.

Lemma adde_strong_evalid_rev:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e' -> strong_evalid g e'.
Proof.
intros. destruct H0. destruct H1.
split. apply adde_evalid2' in H0; auto.
split. rewrite adde_src2 in H1; auto.
rewrite adde_dst2 in H2; auto.
Qed.

Lemma adde_g2wedgelist_1:
  forall (g: FiniteWEdgeListGraph) e w, In (w, e) (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. unfold edge_to_wedge.
replace (w, e) with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e).
apply in_map. apply EList_evalid. apply adde_evalid1.
unfold edge_to_wedge. rewrite adde_elabel1. auto.
Qed.

Corollary adde_g2wedgelist_2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> In (elabel g e', e') (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. replace (elabel g e', e') with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e').
apply in_map. apply EList_evalid. apply adde_evalid2. auto.
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

(*****************************CONNECTEDNESS*************************)

Lemma sound_adj_edge_form:
forall (g: FiniteWEdgeListGraph) e u v, sound_weighted_edge_graph g -> adj_edge g e u v -> (e = (u,v) \/ e = (v,u)).
Proof.
intros. destruct H0. rewrite <- sound_src in H1. rewrite <- sound_dst in H1.
rewrite (surjective_pairing e). destruct H1; destruct H1; subst u; subst v; auto.
auto. apply H0. auto. apply H0.
Qed.

Lemma adde_adj_edge1:
forall (g: FiniteWEdgeListGraph) e w, vvalid g (fst e) -> vvalid g (snd e) -> adj_edge (FiniteWEdgeListGraph_adde g e w) e (fst e) (snd e).
Proof.
unfold adj_edge; intros. split. apply adde_strong_evalid1; auto.
left. rewrite adde_src1, adde_dst1. auto.
Qed.

Lemma adde_adj_edge2:
forall (g: FiniteWEdgeListGraph) e w e' u v,
  e <> e' -> adj_edge g e' u v -> adj_edge (FiniteWEdgeListGraph_adde g e w) e' u v.
Proof.
unfold adj_edge; intros.
destruct H0. split.
apply adde_strong_evalid2; auto.
rewrite adde_src2; auto.
rewrite adde_dst2; auto.
Qed.

(*although sound_weighted_edge_graph is only needed for case e' = e,
  it's hard to remove in the case e already existed in g but was not pointing to fst and snd of itself
  It is possible to prove a form replacing sound... with ~ evalid g e
*)
Lemma sound_adde_adj_edge:
forall (g: FiniteWEdgeListGraph) e w e' u v,
  sound_weighted_edge_graph g ->
  adj_edge g e' u v -> adj_edge (FiniteWEdgeListGraph_adde g e w) e' u v.
Proof.
unfold adj_edge; intros. destruct (E_EqDec e e').
(*e=e'*)
unfold equiv in e0. subst e'. split.
apply adde_strong_evalid1.
replace (fst e) with (src g e). apply H0. apply H. apply H0.
replace (snd e) with (dst g e). apply H0. apply H. apply H0.
rewrite adde_src1.
rewrite adde_dst1.
destruct H0. destruct H0.
rewrite (sound_src g e); auto. rewrite (sound_dst g e); auto.
(*e<>e'*)
unfold complement, equiv in c. apply adde_adj_edge2; auto.
Qed.

Lemma adde_adj_edge_rev:
forall (g: FiniteWEdgeListGraph) e w e' u v,
  e <> e' ->
  adj_edge (FiniteWEdgeListGraph_adde g e w) e' u v -> adj_edge g e' u v .
Proof.
unfold adj_edge; intros. destruct H0.
split.
apply adde_strong_evalid_rev in H0; auto.
rewrite adde_src2 in H1; auto.
rewrite adde_dst2 in H1; auto.
Qed.

Lemma adde_valid_upath':
forall (g: FiniteWEdgeListGraph) e w p,
  ~ evalid g e ->
  valid_upath g p -> valid_upath (FiniteWEdgeListGraph_adde g e w) p.
Proof.
induction p; intros. auto.
destruct p. auto.
split. destruct H0. destruct H0. exists x.
apply adde_adj_edge2; auto. unfold not; intros; subst x.
destruct H0. destruct H0. contradiction.
apply IHp. auto. apply H0.
Qed.

Lemma adde_valid_upath:
forall (g: FiniteWEdgeListGraph) e w p,
  sound_weighted_edge_graph g ->
  valid_upath g p -> valid_upath (FiniteWEdgeListGraph_adde g e w) p.
Proof.
induction p; intros. auto.
destruct p. auto.
split. destruct H0. destruct H0. exists x.
apply sound_adde_adj_edge; auto.
apply IHp. auto. apply H0.
Qed.

Lemma adde_connected_by_path:
forall (g: FiniteWEdgeListGraph) e w p u v,
  sound_weighted_edge_graph g -> connected_by_path g p u v ->
  connected_by_path (FiniteWEdgeListGraph_adde g e w) p u v.
Proof.
unfold connected_by_path; intros.
split. apply adde_valid_upath. auto.
apply H0. apply H0.
Qed.

Corollary adde_connected:
forall (g: FiniteWEdgeListGraph) e w u v,
  sound_weighted_edge_graph g ->
  connected g u v -> connected (FiniteWEdgeListGraph_adde g e w) u v.
Proof.
intros. destruct H0 as [p ?]. exists p.
apply adde_connected_by_path; auto.
Qed.

Lemma adde_fits_upath:
forall (g: FiniteWEdgeListGraph) e w p l,
sound_weighted_edge_graph g ->
fits_upath g l p -> fits_upath (FiniteWEdgeListGraph_adde g e w) l p.
Proof.
induction p; intros. destruct l; auto.
destruct l. auto. destruct p. auto.
split. destruct H0. apply sound_adde_adj_edge; auto.
apply IHp. apply H. apply fits_upath_cons in H0. apply H0.
Qed.

Lemma adde_fits_upath_rev:
forall (g: FiniteWEdgeListGraph) e w p l,
fits_upath (FiniteWEdgeListGraph_adde g e w) l p -> ~ In e l -> fits_upath g l p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; auto.
destruct l. auto.
assert (Heq_e: e <> e0). unfold not; intros. apply H0. left; rewrite H1; auto.
assert (HIn_e: ~ In e l). unfold not; intros. apply H0. right; auto.
clear H0.
destruct H. split. destruct H. destruct H. split. split.
apply adde_evalid_or in H. destruct H. auto. symmetry in H; contradiction.
simpl in H2. unfold updateEdgeFunc in H2. unfold equiv_dec in H2. destruct (E_EqDec e e0).
unfold equiv in e1; contradiction. apply H2.
simpl in H1. unfold updateEdgeFunc in H1. unfold equiv_dec in H1. destruct (E_EqDec e e0).
unfold equiv in e1; contradiction. apply H1.
apply IHp; auto.
Qed.

Lemma adde_unaffected:
forall (g: FiniteWEdgeListGraph) e w p, valid_upath (FiniteWEdgeListGraph_adde g e w) p
  -> (exists l, fits_upath g l p /\ ~ In e l) -> valid_upath g p.
Proof.
intros. destruct H0 as [l ?].
apply valid_upath_exists_list_edges'.
exists l. destruct H0; auto.
Qed.

(*Try using this to simplify the below*)
Lemma adde_bridge':
forall (g: FiniteWEdgeListGraph) e w,
~ connected g (fst e) (snd e) -> bridge (FiniteWEdgeListGraph_adde g e w) e (fst e) (snd e).
Proof.
unfold bridge; intros. destruct (In_dec E_EqDec e l). auto.
exfalso; apply H. exists p. destruct H0. split; auto.
apply adde_unaffected in H0; auto.
apply adde_fits_upath_rev in H1; auto.
exists l; split; auto.
Qed.

Lemma adde_bridge:
forall (g: FiniteWEdgeListGraph) e w a b,
connected g a (fst e) -> connected g (snd e) b ->
~ connected g (fst e) (snd e) -> bridge (FiniteWEdgeListGraph_adde g e w) e a b.
Proof.
unfold bridge; intros. set (g':=FiniteWEdgeListGraph_adde g e w) in *.
destruct (In_dec E_EqDec e l). auto.
assert (connected g a b). { exists p. split. 2: apply H2.
apply (fits_upath_transfer'' p l g' g) in H3. apply valid_upath_exists_list_edges'. exists l; auto.
intros. apply (valid_upath_vvalid g' p v) in H4. simpl in H4; auto. apply H2.
intros. apply (adde_evalid2' g e w e0). unfold not; intros; subst e0; contradiction.
apply (fits_upath_evalid g' p l); auto.
intros. apply adde_src2. unfold not; intros; subst e0; contradiction.
intros. apply adde_dst2. unfold not; intros; subst e0; contradiction.
}
exfalso. apply H1. apply (connected_trans g (fst e) b). apply (connected_trans g (fst e) a).
apply connected_symm; auto. auto. apply connected_symm; auto.
Qed.

Lemma adde_connected_through_bridge1:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
connected g a u -> connected g v b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros.
assert (vvalid g u). apply (connected_vvalid g a u H0).
assert (vvalid g v). apply (connected_vvalid g v b H1).
apply (adde_connected g (u,v) w) in H0; auto. apply (adde_connected g (u,v) w) in H1; auto.
destruct H0 as [x [? [? ?]]]. destruct H1 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (adde_strong_evalid1 g (u,v) w); auto.
left. split. rewrite adde_src1; auto. rewrite adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma adde_connected_through_bridge2:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
connected g a v -> connected g u b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros.
assert (vvalid g v). apply (connected_vvalid g a v H0).
assert (vvalid g u). apply (connected_vvalid g u b H1).
apply (adde_connected g (u,v) w) in H0; auto. apply (adde_connected g (u,v) w) in H1; auto.
destruct H0 as [x [? [? ?]]]. destruct H1 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (adde_strong_evalid1 g (u,v) w); auto.
right. split. rewrite adde_src1; auto. rewrite adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

(*not possible to simplify with bridge after all, because bridge is "forward" while this is "backward"*)
Lemma cross_bridge_implies_endpoints:
forall (g: FiniteWEdgeListGraph) u v w p l a b,
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b ->
fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p -> In (u,v) l ->
((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
Proof.
induction p; intros. destruct H1. destruct H4. inversion H4.
assert (a = a0). destruct H1. destruct H4. inversion H4. auto. subst a0. (*that was weird*)
destruct l. contradiction.
destruct p. contradiction.
(*so we show that v0 is connected to one of them. By trans, a0 is connected to one*)
(*case where (u,v) is first in list. Then we show a = u or a = v*)
destruct H3. subst e.
destruct H2. destruct H2. destruct H2.
rewrite adde_src1 in *. rewrite adde_dst1 in *.
destruct H5. simpl in H5, H6.
assert (~ In (u,v) l).  unfold not; intros.
  destruct H4; destruct H4; subst a; subst v0; destruct H0.
  assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_src_In _ (v::p) l (u,v)); auto.
  rewrite adde_src1. auto. apply NoDup_cons_2 in H4. contradiction.
  assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_dst_In _ (u::p) l (u,v)); auto.
  rewrite adde_dst1. auto. apply NoDup_cons_2 in H4. contradiction.
destruct H4; destruct H4; subst a; subst v0.
left. split. apply connected_refl. auto. exists (v::p).
split. apply (adde_unaffected g (u,v) w). apply H0.
exists l. split. apply (adde_fits_upath_rev g (u,v) w). apply H3. auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
right. split. apply connected_refl. auto. exists (u::p).
split. apply (adde_unaffected g (u,v) w). apply H0.
exists l. split. apply (adde_fits_upath_rev g (u,v) w). apply H3. auto. auto.
split. simpl; auto. destruct H1. destruct H4. rewrite last_error_cons in H8; auto.
unfold not; intros; inversion H9.
(*Case where (u-v) is somewhere in the middle*)
assert (Hav0: connected g a v0). {
  apply adjacent_connected. destruct H2. destruct H2.
  assert ((u,v) <> e). unfold not; intros. subst e.
    rewrite adde_src1 in *; rewrite adde_dst1 in *.
    destruct H5; destruct H5; subst a; subst v0.
    assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
    apply (fits_upath_vertex_src_In _ (v::p) l (u,v)); auto.
    rewrite adde_src1. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
    assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
    apply (fits_upath_vertex_dst_In _ (u::p) l (u,v)); auto.
    rewrite adde_dst1. auto.
    destruct H0. apply NoDup_cons_2 in H6. contradiction.
  exists e. destruct H2. repeat rewrite <- adde_vvalid in H7.
  rewrite adde_src2 in H5, H7; auto. rewrite adde_dst2 in H5, H7; auto.
  apply (adde_evalid2' g (u,v) w) in H2; auto.
  split; auto. split; auto.
}
(*IHp on v0*)
assert (connected g v0 u /\ connected g v b \/ connected g v0 v /\ connected g u b).
apply (IHp l v0 b). auto. split. apply H0.
destruct H0. apply NoDup_cons_1 in H4. auto.
destruct H1. destruct H4. split. apply H0.
split. simpl; auto. rewrite last_error_cons in H5; auto. unfold not; intros; inversion H6.
apply H2. apply H3.
destruct H4; destruct H4. left. split.
apply (connected_trans g a v0 u); auto. auto.
right. split.
apply (connected_trans g a v0 v); auto. auto.
Qed.

Lemma adde_bridge_split1:
forall (g: FiniteWEdgeListGraph) u v w p a b,
connected g u a ->
connected g v b ->
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
(exists l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p /\ In (u,v) l) ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a u /\
    connected_by_path g p2 v b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l [? ?]].
destruct l. simpl in H5. contradiction.
destruct p. simpl in H3. contradiction.
assert (Hvvalid_g_u: vvalid g u). apply (connected_vvalid g u a0). auto.
assert (Hvvalid_g_v: vvalid g v). apply (connected_vvalid g v b). auto.
assert (a0 = a). destruct H4. destruct H6. simpl in H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite adde_src1 in H6. rewrite adde_dst1 in H6.
destruct H6; destruct H6. subst a; subst v0. exists (u::nil); exists (v::p).
split. auto. split. split; simpl; auto.
assert (~ In (u,v) l). unfold not; intros.
assert (In (src (FiniteWEdgeListGraph_adde g (u, v) w) (u, v)) (v :: p)).
apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)); auto.
rewrite adde_src1 in H7.
destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
split. apply (adde_unaffected g (u,v) w). apply H4. exists l. split.
apply (adde_fits_upath_rev g (u,v) w); auto. auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. rewrite <- H8. auto.
unfold not; intros. simpl in H9. inversion H9.
subst a. contradiction.
(*otherwise*)
assert (e <> (u,v)). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite adde_src1 in H7; rewrite adde_dst1 in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In (src (FiniteWEdgeListGraph_adde g (u, v) w) (u, v)) (v :: p)).
  apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)); auto.
  rewrite adde_src1 in H7. simpl in H7.
  destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
  assert (In (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u, v)) (u :: p)).
  apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)); auto.
  rewrite adde_dst1 in H7. simpl in H7.
  destruct H2. apply NoDup_cons_2 in H8. simpl in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3. destruct H3.
  split. apply (adde_strong_evalid_rev g (u,v) w e). auto. auto.
  rewrite adde_src2 in H8; auto. rewrite adde_dst2 in H8; auto.
assert (exists p1 p2 : list VType,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 u /\
        connected_by_path g p2 v b). apply (IHp v0 b); auto. (*<-------- WOW. If I use "apply IHp" instead of "apply (IHp v0 b)", universe inconsistency*)
apply (connected_trans g u a v0). auto.
apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 [? [? ?]]]].
exists (a::p1). exists p2. split. rewrite H7. simpl; auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

(*this is stupid*)
Lemma adde_bridge_split2:
forall (g: FiniteWEdgeListGraph) u v w p a b ,
connected g v a ->
connected g u b ->
~ connected g u v ->
simple_upath (FiniteWEdgeListGraph_adde g (u,v) w) p ->
(exists l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p /\ In (u,v) l) ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p a b
-> (exists p1 p2, p = p1++p2 /\
    connected_by_path g p1 a v /\
    connected_by_path g p2 u b).
Proof.
induction p; intros.
destruct H4. destruct H5. inversion H6.
destruct H3 as [l ?]. destruct H3.
destruct l. simpl in *. contradiction.
destruct p. simpl in H3. contradiction.
assert (Hvvalid_g_v: vvalid g v). apply (connected_vvalid g v a0). auto.
assert (Hvvalid_g_u: vvalid g u). apply (connected_vvalid g u b). auto.
assert (a0 = a). destruct H4. destruct H6. inversion H6. auto. subst a0.
destruct H5.
(*case where u-v is directly at the front*)
subst e. destruct H3. destruct H3.
rewrite adde_src1 in H6. rewrite adde_dst1 in H6.
destruct H6; destruct H6; subst a; subst v0. apply connected_symm in H. contradiction.
exists (v::nil); exists (u::p).
split. auto. split. split; simpl; auto.
assert (~ In (u,v) l). unfold not; intros.
assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)).
auto. auto. rewrite adde_dst1. auto.
destruct H2. apply NoDup_cons_2 in H8. contradiction.
split. apply (adde_unaffected g (u,v) w). apply H4. exists l. split.
apply (adde_fits_upath_rev g (u,v) w); auto. auto.
split. simpl; auto. destruct H4. destruct H7. rewrite last_error_cons in H8. auto.
unfold not; intros. inversion H9.
(*otherwise*)
assert (e <> (u,v)). unfold not; intros. subst e. destruct H3. destruct H3.
  rewrite adde_src1 in H7; rewrite adde_dst1 in H7.
  destruct H7; destruct H7; subst a; subst v0.
  assert (In u (v::p)). replace u with (src (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_src_In (FiniteWEdgeListGraph_adde g (u, v) w) (v::p) l (u,v)). auto. auto.
  rewrite adde_src1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
  assert (In v (u::p)). replace v with (dst (FiniteWEdgeListGraph_adde g (u, v) w) (u,v)).
  apply (fits_upath_vertex_dst_In (FiniteWEdgeListGraph_adde g (u, v) w) (u::p) l (u,v)). auto. auto.
  rewrite adde_dst1. auto.
  destruct H2. apply NoDup_cons_2 in H8. contradiction.
assert (Hav0: adjacent g a v0). exists e. destruct H3. destruct H3.
  split. apply (adde_strong_evalid_rev g (u,v) w e). auto. auto.
  rewrite adde_src2 in H8; auto. rewrite adde_dst2 in H8; auto.
assert (exists p1 p2 : list VType,
        v0 :: p = p1++ p2 /\
        connected_by_path g p1 v0 v /\
        connected_by_path g p2 u b). apply (IHp v0 b); auto.
apply (connected_trans g v a v0). auto. apply adjacent_connected. auto.
destruct H2. split. apply H2. apply NoDup_cons_1 in H7. auto.
exists l. split. destruct H3. apply H7. apply H5.
destruct H4. destruct H4. split. apply H8.
split. auto.
destruct H7. rewrite last_error_cons in H9. auto. unfold not; intros. inversion H10.
(*WHEW*)
destruct H7 as [p1 [p2 ?]]. destruct H7. destruct H8.
exists (a::p1). exists p2. split. rewrite H7. simpl. auto. split.
destruct H8. split. apply valid_upath_cons. apply H8.
destruct H10. rewrite H10. simpl. auto.
split. simpl; auto.
rewrite last_error_cons. apply H10.
destruct H10. unfold not; intros. subst p1. inversion H10.
auto.
Qed.

Lemma unique_simple_upath_adde:
forall (g: FiniteWEdgeListGraph) u v w, unique_simple_upath g -> ~ connected g u v ->
  unique_simple_upath (FiniteWEdgeListGraph_adde g (u,v) w).
Proof.
(*the forest definition*)
unfold unique_simple_upath; intros. rename u0 into a; rename v0 into b.
assert (exists l : list EType, fits_upath (FiniteWEdgeListGraph_adde g (u, v) w) l p1).
apply connected_exists_list_edges in H2; auto.
assert (exists l : list EType, fits_upath (FiniteWEdgeListGraph_adde g (u, v) w) l p2).
apply connected_exists_list_edges in H4; auto.
destruct H5 as [l1 ?]. destruct H6 as [l2 ?].
destruct (in_dec E_EqDec (u,v) l1); destruct (in_dec E_EqDec (u,v) l2).

+ assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p1 l1 a b); auto.
destruct H7; destruct H7.
(*case a-u and v-b*)
  apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a u /\
      connected_by_path g p1_b v b)).
  apply (adde_bridge_split1 g u v w p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a u /\
      connected_by_path g p2_b v b)).
  apply (adde_bridge_split1 g u v w p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  assert (p1_a = p2_a). apply (H a u p1_a p2_a).
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H v b p1_b p2_b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.
(*case a-v and u-b...*)
apply connected_symm in H7.
  assert (exists p1_a p1_b, (p1 = p1_a++p1_b /\
      connected_by_path g p1_a a v /\
      connected_by_path g p1_b u b)).
  apply (adde_bridge_split2 g u v w p1 a b); auto. exists l1; split; auto.
  destruct H9 as [p1_a [p1_b ?]]. destruct H9. destruct H10.
  assert (exists p2_a p2_b, (p2 = p2_a++p2_b /\
      connected_by_path g p2_a a v /\
      connected_by_path g p2_b u b)).
  apply (adde_bridge_split2 g u v w p2 a b); auto. exists l2; split; auto.
  destruct H12 as [p2_a [p2_b ?]]. destruct H12. destruct H13.
  rewrite H9 in H1; rewrite H12 in H3. destruct H1. destruct H3.
  (*by H, we have p1_a = p2_a*)
  assert (p1_a = p2_a). apply (H a v p1_a p2_a).         (*<--------- same issue here, I used "H a v" and let it infer the paths: universe inconsistency*)
  split. apply H10. apply (NoDup_app_l _ _ _ H15). auto.
  split. apply H13. apply (NoDup_app_l _ _ _ H16). auto.
  assert (p1_b = p2_b). apply (H u b p1_b p2_b).
  split. apply H11. apply (NoDup_app_r _ _ _ H15). auto.
  split. apply H14. apply (NoDup_app_r _ _ _ H16). auto.
  (*thus, rewrite*)
  rewrite H9; rewrite H12; rewrite H17; rewrite H18. auto.

+ (*In (u,v) l1, ~In (u,v) l2*)
(* Then p1 = p1_a++p1_b. p1_a connects a-u, p1_b connects v-b
Whereas p2 is valid in g, connected a b
p1_a does not contain u-v by simpleness, so it is unaffected and valid in g
Ditto p1_b
Thus, connected g u a, connected g v b, connected g a b. Thus, connected g u v. Contra
Repeat for a-v,b-u...
*)
apply adde_fits_upath_rev in H6; auto.
destruct H4. apply adde_unaffected in H4. 2: { exists l2. split; auto. }
assert (connected g a b). exists p2. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p1 l1 a b); auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.

+ (*~In (u,v) l1, In (u,v) l2*)
apply adde_fits_upath_rev in H5; auto.
destruct H2. apply adde_unaffected in H2. 2: { exists l1. split; auto. }
assert (connected g a b). exists p1. split; auto.
assert ((connected g a u /\ connected g v b) \/ (connected g a v /\ connected g u b)).
apply (cross_bridge_implies_endpoints g u v w p2 l2); auto.
assert (connected g u v).
destruct H9; destruct H9.
  apply (connected_trans g u a v). apply connected_symm; auto.
  apply (connected_trans g a b v). auto. apply connected_symm; auto.
  apply (connected_trans g u b v). auto.
  apply (connected_trans g b a v). apply connected_symm; auto. auto.
contradiction.

+ (*~In (u,v) l1, ~In (u,v) l2*)
(*then both p1 and p2 are valid in g*)
apply adde_fits_upath_rev in H5; auto. apply adde_fits_upath_rev in H6; auto.
destruct H2. apply adde_unaffected in H2.
destruct H4. apply adde_unaffected in H4.
apply (H a b).
split. apply H2. apply H1. split; auto.
split. apply H4. apply H3. split; auto.
exists l2. split; auto. exists l1. split; auto.
Qed.

Lemma uforest'_adde:
forall (g: FiniteWEdgeListGraph) u v w, sound_weighted_edge_graph g -> uforest' g -> vvalid g u -> vvalid g v -> Int.min_signed <= w <= Int.max_signed -> ~ connected g u v ->
  uforest' (FiniteWEdgeListGraph_adde g (u,v) w).
Proof.
intros.
(*first assert u <> v, as they're not connected*)
assert (Huv: u<>v). unfold not; intros; subst u. pose proof (connected_refl g v H1). auto.
split.
(*no self loop*)
intros.
destruct (E_EqDec e (u,v)).
unfold Equivalence.equiv in e0. subst e.
rewrite adde_src1. rewrite adde_dst1. simpl. unfold not; intros.
subst u. intros. pose proof (connected_refl g v H1). auto.
unfold RelationClasses.complement, Equivalence.equiv in c.
apply adde_evalid2' in H5. 2: auto.
rewrite adde_src2 by auto. rewrite adde_dst2 by auto. apply H0; auto.
(*not multigraph*)
split. intros. destruct H5.
assert (Hsound_adde: sound_weighted_edge_graph (FiniteWEdgeListGraph_adde g (u, v) w)).
apply adde_sound; auto.
pose proof (sound_adj_edge_form _ _ _ _ Hsound_adde H5).
pose proof (sound_adj_edge_form _ _ _ _ Hsound_adde H6).
assert (Huv': (u,v) <> (v,u)). unfold not; intros. inversion H9. auto.
destruct (E_EqDec (u0,v0) (u,v)). unfold Equivalence.equiv in e. inversion e. subst u0; subst v0.
destruct H7; destruct H8; subst e1; subst e2.
auto.
(*In all the (v,u) cases, (v,u) must be valid in g, thus connected g u v, contra*)
assert (connected g u v). apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
assert (connected g u v). apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
assert (connected g u v). apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
(*Repeat (u0,v0) - (v,u)*)
unfold RelationClasses.complement, Equivalence.equiv in c.
destruct (E_EqDec (u0,v0) (v,u)). unfold Equivalence.equiv in e. inversion e. subst u0; subst v0.
destruct H7; destruct H8; subst e1; subst e2.
assert (connected g u v). apply connected_symm. apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
assert (connected g u v). apply connected_symm. apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
assert (connected g u v). apply connected_symm. apply adjacent_connected. exists (v,u).
apply (adde_adj_edge_rev g (u,v) w); auto. contradiction.
auto.
(*So (u0,v0) is neither uv nor vu. Then it's not affected*)
unfold RelationClasses.complement, Equivalence.equiv in c0.
apply (adde_adj_edge_rev g (u,v) w) in H5; auto.
apply (adde_adj_edge_rev g (u,v) w) in H6; auto.
destruct H0. destruct H9. apply (H9 u0 v0). split; auto.
unfold not; intros; subst e2. destruct H8; symmetry in H8. contradiction.
inversion H8. assert ((u0, v0) = (v, u)). subst v0; subst u0. auto. contradiction.
unfold not; intros; subst e1. destruct H7; symmetry in H7. contradiction.
inversion H7. assert ((u0, v0) = (v, u)). subst v0; subst u0. auto. contradiction.
(*evalid -> strong_evalid*)
split. intros.
destruct (E_EqDec e (u,v)).
unfold Equivalence.equiv in e0. subst e.
apply adde_strong_evalid1; simpl; auto.
unfold RelationClasses.complement, Equivalence.equiv in c.
apply adde_strong_evalid2. auto.
apply adde_evalid2' in H5. 2: auto. apply H0. auto.
(*forest*)
apply unique_simple_upath_adde; auto. apply H0.
Qed.

(*****************************REMOVE EDGES****************************)

Definition WEdgeListGraph_eremove (g: WEdgeListGraph) (e: EType) :=
  @Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG (pregraph_remove_edge g e)
  (vlabel g)
  (*(fun e0 => if eq_dec e0 e then ? else elabel g e )*) (elabel g)
  (glabel g)
.

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

Lemma eremove_evalid2:
  forall (g: FiniteWEdgeListGraph) e e', e' <> e -> evalid g e' -> evalid (FiniteWEdgeListGraph_eremove g e) e'.
Proof. simpl. intros; split; auto. Qed.

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

(*Still need these functions even if with the general version in FiniteGraph. The coercion doesn't play well sometimes, even after simpl*)
Lemma eremove_EList:
  forall (g: FiniteWEdgeListGraph) e l, Permutation (e::l) (EList g) -> Permutation l (EList (FiniteWEdgeListGraph_eremove g e)).
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
assert (evalid (FiniteWEdgeListGraph_eremove g e) x). apply (eremove_evalid2 g e x). auto. apply EList_evalid in H3; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList (FiniteWEdgeListGraph_eremove g e)))). apply Permutation_sym; auto. apply H4.
Qed.

Lemma eremove_src2:
forall (g: FiniteWEdgeListGraph) e e', e' <> e -> src (FiniteWEdgeListGraph_eremove g e) e' = src g e'.
Proof. intros. simpl. auto. Qed.

Lemma eremove_dst2:
forall (g: FiniteWEdgeListGraph) e e', e' <> e -> dst (FiniteWEdgeListGraph_eremove g e) e' = dst g e'.
Proof. intros. simpl. auto. Qed.

(*****************************PARTIAL LGRAPH AND MSF**********************)
(*These should be abstracted, but we can deal with it after the kruskal proof is done*)

Lemma sound_fits_upath_transfer:
forall p l (g1 g2: FiniteWEdgeListGraph), sound_weighted_edge_graph g1 ->
sound_weighted_edge_graph g2 -> (forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) ->
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. apply H1. apply H3. simpl in H3. contradiction.
destruct p. simpl in H3. contradiction.
destruct H3. split.
+ (*adjacent edge*)
  destruct H3. destruct H3. destruct H6. assert (evalid g2 e). apply H2. left. auto.
  unfold adj_edge. unfold strong_evalid.
  replace (src g1 e) with (fst e) in *. 2: apply sound_src; auto.
  replace (src g2 e) with (fst e) in *. 2: apply sound_src; auto.
  replace (dst g1 e) with (snd e) in *. 2: apply sound_dst; auto.
  replace (dst g2 e) with (snd e) in *. 2: apply sound_dst; auto.
  split. split. apply H2. left; auto. split.
  apply H1; auto. apply H1; auto. apply H5.
+ apply (IHp l g1 g2); auto. intros. apply H2. right; auto.
Qed.

Lemma valid_upath_eremove:
forall (g: FiniteWEdgeListGraph) e p l, valid_upath g p
  -> fits_upath g l p -> ~ In e l -> valid_upath (FiniteWEdgeListGraph_eremove g e) p.
Proof.
intros. apply (remove_edge_valid_upath g e p l); auto.
Qed.

Lemma eremove_unaffected:
  forall (g: FiniteWEdgeListGraph) e p, valid_upath (FiniteWEdgeListGraph_eremove g e) p
  -> valid_upath g p.
Proof.
intros. apply (remove_edge_unaffected g e p); auto.
Qed.

(*****************)

(*Looks like the 10case scenario...
In addition, I need:
-strong_evalid_dec
-if e isn't strong_evalid, it can't be in a path (easy enough)
-fits_upath_transfer' is too strong atm, it was originally focused on partial graphs.
  Write a version that only cares about vertices/edges in p/l
  Then I may be able to avoid the 10-case business...
*)
Lemma connected_dec_pre:
  forall l (g: FiniteWEdgeListGraph) a b, Permutation l (EList g) -> connected g a b \/ ~ connected g a b.
Proof.
induction l; intros.
+
destruct (V_EqDec a b).
(*same vertex: check if vvalid*)
unfold equiv in e. subst b.
destruct (vvalid_dec g a). left. apply connected_refl. auto.
right. unfold not; intros. apply connected_vvalid in H1. destruct H1. auto.
(*not same vertex: no edges, so can't be connected*)
unfold complement, equiv in c.
right. unfold not; intros. assert (vvalid g a /\ vvalid g b). apply connected_vvalid; auto. destruct H1.
destruct H0 as [p [? [? ?]]]. destruct p. inversion H3. destruct p. simpl in H3, H4. inversion H3. inversion H4. subst a; subst b. contradiction.
destruct H0. destruct H0 as [e [? ?]]. destruct H0. rewrite <- EList_evalid in H0.
apply (Permutation_in (l':=nil)) in H0. contradiction. apply Permutation_sym. apply H.
+ (*inductive case*)
rename a into e. rename a0 into a.
set (g':=FiniteWEdgeListGraph_eremove g e).
assert (Permutation l (EList g')). apply eremove_EList; auto.
assert (connected g' a b \/ ~ connected g' a b). apply IHl; auto. destruct H1.
(*case they're connected even when e is removed*)
destruct H1 as [p ?].
left. exists p. split. apply (eremove_unaffected g e). apply H1. apply H1.
(*case they're not. Then, check if they're connected to the vertices of e*)
destruct (strong_evalid_dec g e).
(*case it is strong_evalid. Then get the vertices of e, split into cases
Seems like 10cases...
*) destruct H2. destruct H3.
set (u:=src g e). set (v:=dst g e).
admit.
(*case not strong_evalid: Then it remains unaffected*)
right. unfold not; intros. destruct H3 as [p ?].
assert (exists l, fits_upath g l p). apply (connected_exists_list_edges g p a b); auto. destruct H4 as [l' ?].
assert (connected g' a b). exists p. split.
apply (remove_edge_valid_upath g e p l'). apply H3. auto.
unfold not; intros. apply (fits_upath_strong_evalid g p l') in H5; auto.
apply H3.
contradiction.
Abort.

(*****************)

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
    Z.le (sum_DE Z.add g 0) (sum_DE Z.add g 0).

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
assert (Hvvalid: forall v1 : VType, vvalid (FiniteWEdgeListGraph_eremove g (u, v)) v1 <-> vvalid g v1). apply eremove_vvalid.
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

(*Sigh, this is really dumb*)
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

(*
Fixpoint insert {A:Type} (leb: A -> A -> bool) (i:A) (l: list A) :=
  match l with
  | nil => i::nil
  | h::t => if leb i h then i::h::t else h :: insert leb i t
 end.

Fixpoint sort {A: Type} (leb: A -> A -> bool) (l: list A) : list A :=
  match l with
  | nil => nil
  | h::t => insert leb h (sort leb t)
end.

Inductive sorted {A} (leb: A -> A -> bool): list A -> Prop := 
| sorted_nil:
    sorted leb nil
| sorted_1: forall x,
    sorted leb (x::nil)
| sorted_cons: forall x y l,
     is_true (leb x y) -> sorted leb (y::l) -> sorted leb (x::y::l).

Definition sorted' {A: Type} {d: Inhabitant A} (le: A -> A -> Prop) (l: list A) :=
 forall i j, i < j < Zlength l -> le (Znth i l) (Znth j l).

Lemma insert_perm: forall {A: Type} (leb: A -> A -> bool) x l, Permutation (x::l) (insert leb x l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. destruct (leb x a). apply Permutation_refl.
apply (Permutation_trans (l':=a::x::l)). apply perm_swap.
apply perm_skip. apply IHl.
Qed.

Theorem sort_perm: forall {A: Type} (leb: A->A->bool) l, Permutation l (sort leb l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. apply (Permutation_trans (l':=a::(sort leb l))).
apply perm_skip. apply IHl.
apply insert_perm.
Qed.

Lemma insert_sorted:
  forall {A: Type} (leb: A -> A -> bool) a l, sorted leb l -> sorted leb (insert leb a l).
Proof.
intros. induction H.
simpl. apply sorted_1.
simpl. destruct (leb a x) eqn:H. apply sorted_cons; auto. apply sorted_1.
assert (leb x a = true). admit. apply sorted_cons; auto. apply sorted_1.
simpl. destruct (leb a x) eqn:Hax. apply sorted_cons; auto.
destruct (leb a y) eqn:Hay. apply sorted_cons; auto.



induction l; intros. simpl. apply sorted_1.
simpl. destruct (leb a a0) eqn:H0. apply sorted_cons; auto.

destruct (insert leb a l). apply sorted_1.
clear H0. destruct (leb a0 a1) eqn:H0. apply sorted_cons; auto.


Theorem sort_sorted: forall {A: Type} (leb: A -> A -> bool) l, sorted leb (sort leb l).
Proof.
induction l; intros. apply sorted_nil.
destruct l. simpl. apply sorted_1.
simpl in IHl. simpl. destruct (leb a 
*)