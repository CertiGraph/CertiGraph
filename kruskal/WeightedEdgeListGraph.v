(*Looted from msl_application/DijkstraArrayGraph
Should try abstracting it if possible from an EdgeListGraph*)
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
Require Import RamifyCoq.kruskal.undirected_graph.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*
 Concretizing the EdgelistGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  |    ?    |  Z  | unit |  Finite   |
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

Lemma WEdgeListGraph_no_vlabel:
  forall (g: WEdgeListGraph) v, vlabel g v = tt.
Proof. intros. destruct vlabel. auto.
Qed.

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
  forall a b, evalid g (a,b) -> (vvalid g a /\ vvalid g b).

Definition weight_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition src_edge (g : WEdgeListGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g: WEdgeListGraph): Prop :=
  forall e, dst g e = snd e.

Definition sound_weighted_edge_graph (g: WEdgeListGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ weight_valid g /\ src_edge g /\ dst_edge g.

Definition numV (g: FiniteWEdgeListGraph) : Z := Zlength (VList g).
Definition numE (g: FiniteWEdgeListGraph) : Z := Zlength (EList g).

Lemma numE_pos: forall g, 0 <= numE g.
Proof.
  intros. unfold numE. apply Zlength_nonneg.
Qed.

Definition edge_to_wedge (g: WEdgeListGraph) e : LE * EType := (elabel g e, e).

(* from Graph to list of edges *)
Definition graph_to_wedgelist (g: FiniteWEdgeListGraph) : list (LE * EType) :=
  (*map (fun e => (elabel g e, e)) (EList g).*)
  map (edge_to_wedge g) (EList g).

Lemma g2wedgelist_numE:
  forall g,
    Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist.
  rewrite Zlength_map. trivial.
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
unfold edge_valid in H2. destruct x. specialize H2 with v v0.
apply EList_evalid in H1.
apply H2 in H1. destruct H1. unfold vertex_valid in H0. apply H0 in H. apply H0 in H1.
simpl. set (i:=Int.min_signed); compute in i; subst i.
split; lia.
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

Instance Sound_empty_WEdgeListGraph:
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
                      (WEdgeListGraph_LabeledGraph empty_WEdgeListGraph) Sound_empty_WEdgeListGraph.

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

Definition Zseq (z: Z) : list Z :=
map Z.of_nat (seq 0%nat (Z.to_nat z)).

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

Instance Sound_edgeless_WEdgeLGraph (z: Z):
  Fin (edgeless_WEdgeLGraph z).
Proof.
constructor. constructor; unfold EnumEnsembles.Enumerable.
exists (Zseq z); split. apply Zseq_NoDup.
unfold edgeless_WEdgeLGraph. simpl. intros. apply Zseq_In.
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_WEdgeGraph (z: Z): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (edgeless_WEdgeLGraph z)) (Sound_edgeless_WEdgeLGraph z).

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

Lemma uforest_edgeless_WEdgeGraph:
forall z, uforest (edgeless_WEdgeGraph z).
Proof.
unfold uforest; intros. destruct H0. destruct H3.
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2. destruct H5. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

(***********ADDING/REMOVING A SINGLE EDGE************)

(*Trivial lemmas to make life simple*)
(*These should probably be in FiniteGraph*)

(*These are specific here because it needs Z.eq_dec*)
Lemma VList_In_dec:
  forall (g: FiniteWEdgeListGraph) v, In v (VList g) \/ ~ In v (VList g).
Proof.
intros. destruct (in_dec Z.eq_dec v (VList g)); [left; auto | right; auto].
Qed.

Lemma EList_In_dec:
  forall (g: FiniteWEdgeListGraph) e, In e (EList g) \/ ~ In e (EList g).
Proof.
intros. destruct (in_dec E_EqDec e (EList g)); [left; auto | right; auto].
Qed.

Corollary FiniteWEdgeListGraph_vvalid_dec:
  forall (g: FiniteWEdgeListGraph) v, vvalid g v \/ ~ vvalid g v.
Proof.
  intros. destruct (VList_In_dec g v); [ left; rewrite <- VList_vvalid; apply H | right; rewrite <- VList_vvalid; apply H].
Qed.

Corollary FiniteWEdgeListGraph_evalid_dec:
  forall (g: FiniteWEdgeListGraph) e, evalid g e \/ ~ evalid g e.
Proof.
  intros. destruct (EList_In_dec g e); [ left; rewrite <- EList_evalid; apply H | right; rewrite <- EList_evalid; apply H].
Qed.

(**Adding is necessary for the kruskal algorithm**)
Definition WEdgeListGraph_adde (g: WEdgeListGraph) (e: EType) (w: LE):=
  labeledgraph_add_edge g e (fst e) (snd e) w.

Instance Sound_WEdgeListGraph_adde (g: FiniteWEdgeListGraph) (e: EType) (w: LE) :
  Fin (WEdgeListGraph_adde g e w).
Proof.
unfold WEdgeListGraph_adde. unfold labeledgraph_add_edge.
constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc.
destruct (in_dec E_EqDec e (EList g)).
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
    (Sound_WEdgeListGraph_adde g e w).

Lemma FiniteWEdgeListGraph_adde_vvalid:
  forall (g: FiniteWEdgeListGraph)  e w v, vvalid g v <-> vvalid (FiniteWEdgeListGraph_adde g e w) v.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. split; auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_numV:
  forall (g: FiniteWEdgeListGraph)  e w, numV (FiniteWEdgeListGraph_adde g e w) = numV g.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. unfold numV. simpl. unfold VList.
destruct finiteV. destruct finiteV. simpl. simpl in a.
destruct a. destruct a0. assert (Permutation x x0). apply NoDup_Permutation; auto.
intros. rewrite H0. rewrite H2. split; auto.
apply Permutation_Zlength. auto.
Qed.

(*should add an EList1 where e is already in g, but it's not necessary atm*)
Lemma FiniteWEdgeListGraph_adde_EList2:
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

Corollary FiniteWEdgeListGraph_adde_EList2':
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> Permutation ((EList g)+::e) (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. pose proof (FiniteWEdgeListGraph_adde_EList2 g e w).
apply (Permutation_trans (l:=EList g +:: e) (l':=e::EList g)).
apply Permutation_app_comm. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_EList_in:
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

Lemma adde_elabel2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> elabel (FiniteWEdgeListGraph_adde g e w) e' = elabel g e'.
Proof.
intros. simpl. unfold update_elabel. unfold equiv_dec. destruct E_EqDec.
contradiction. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid1:
  forall (g: FiniteWEdgeListGraph) e w, evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. right; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid2:
  forall (g: FiniteWEdgeListGraph) e w e', evalid g e' -> evalid (FiniteWEdgeListGraph_adde g e w) e'.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. left; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid_or:
  forall (g: FiniteWEdgeListGraph) e w e', evalid (FiniteWEdgeListGraph_adde g e w) e' -> (evalid g e' \/ e' = e).
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. apply H.
Qed.

Lemma FiniteWEdgeListGraph_adde_src1':
  forall (g: FiniteWEdgeListGraph) e w, src (FiniteWEdgeListGraph_adde g e w) e = fst e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Lemma FiniteWEdgeListGraph_adde_dst1':
  forall (g: FiniteWEdgeListGraph) e w, dst (FiniteWEdgeListGraph_adde g e w) e = snd e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Corollary FiniteWEdgeListGraph_adde_src1:
  forall (g: FiniteWEdgeListGraph) u v w, src (FiniteWEdgeListGraph_adde g (u,v) w) (u,v) = u.
Proof. intros. apply FiniteWEdgeListGraph_adde_src1'. Qed.

Lemma FiniteWEdgeListGraph_adde_dst1:
  forall (g: FiniteWEdgeListGraph) u v w, dst (FiniteWEdgeListGraph_adde g (u,v) w) (u,v) = v.
Proof. intros. apply FiniteWEdgeListGraph_adde_dst1'. Qed.

Corollary FiniteWEdgeListGraph_adde_strong_evalid1':
  forall (g: FiniteWEdgeListGraph) e w,
  vvalid g (fst e) -> vvalid g (snd e) ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. split. apply FiniteWEdgeListGraph_adde_evalid1.
split; apply FiniteWEdgeListGraph_adde_vvalid.
rewrite FiniteWEdgeListGraph_adde_src1'. auto.
rewrite FiniteWEdgeListGraph_adde_dst1'. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_strong_evalid1:
  forall (g: FiniteWEdgeListGraph) u v w,
  vvalid g u -> vvalid g v ->
  strong_evalid (FiniteWEdgeListGraph_adde g (u,v) w) (u,v).
Proof.
intros. apply FiniteWEdgeListGraph_adde_strong_evalid1'; simpl; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_g2wedgelist_1:
  forall (g: FiniteWEdgeListGraph) e w, In (w, e) (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. unfold edge_to_wedge.
replace (w, e) with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e).
apply in_map. apply EList_evalid. apply FiniteWEdgeListGraph_adde_evalid1.
unfold edge_to_wedge. rewrite adde_elabel1. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_e2w:
forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e' = edge_to_wedge g e'.
Proof.
intros. unfold edge_to_wedge; simpl. unfold update_elabel; simpl.
unfold equiv_dec. destruct E_EqDec. contradiction. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_g2wedgelist_2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> In (elabel g e', e') (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. replace (elabel g e', e') with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e').
apply in_map. apply EList_evalid. apply FiniteWEdgeListGraph_adde_evalid2. auto.
apply FiniteWEdgeListGraph_adde_e2w; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_numE:
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> numE (FiniteWEdgeListGraph_adde g e w) = numE g + 1.
Proof.
intros. unfold numE.
pose proof (FiniteWEdgeListGraph_adde_EList2 g e w H).
rewrite <- (Permutation_Zlength _ _ H0). apply Zlength_cons.
Qed.

Lemma FiniteWEdgeListGraph_adde_sound:
  forall (g: FiniteWEdgeListGraph) e w, sound_weighted_edge_graph g ->
    vvalid g (fst e) -> vvalid g (snd e) -> Int.min_signed <= w <= Int.max_signed ->
    sound_weighted_edge_graph (FiniteWEdgeListGraph_adde g e w).
Proof.
intros. split.
unfold vertex_valid; intros. apply H. simpl in H3. apply H3.
split. unfold edge_valid; intros. simpl in H3. destruct H3.
simpl. apply H. apply H3.
rewrite <- H3 in *. simpl in *. split. apply H0. apply H1.
split. unfold weight_valid; intros. simpl in H3. unfold addValidFunc in H3.
simpl. unfold update_elabel. unfold equiv_dec.
destruct (E_EqDec e e0). apply H2.
destruct H3. apply H. apply H3. rewrite H3 in c. unfold complement in c.
assert (equiv e e). apply Equivalence.equiv_reflexive_obligation_1. contradiction.
split. unfold src_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H.
unfold dst_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H.
Qed.

(*****************************CONNECTEDNESS*************************)

Lemma adde_valid_upath:
forall (g: FiniteWEdgeListGraph) e w p,
  sound_weighted_edge_graph g ->
  valid_upath g p -> valid_upath (FiniteWEdgeListGraph_adde g e w) p.
Proof.
induction p; intros. auto.
destruct p. auto.
assert (Hsrc: src_edge g). apply H. unfold src_edge in Hsrc.
assert (Hdst: dst_edge g). apply H. unfold dst_edge in Hdst.
split. destruct H0. destruct H0. exists x.
destruct (E_EqDec x e). unfold equiv in e0. rewrite e0.
rewrite e0 in H0. destruct H0. destruct H0.
split. split. apply FiniteWEdgeListGraph_adde_evalid1.
simpl. unfold updateEdgeFunc. unfold equiv_dec. destruct E_EqDec.
rewrite <- Hsrc. rewrite <- Hdst. apply H3.
unfold complement, equiv in c; contradiction.
simpl. unfold updateEdgeFunc. unfold equiv_dec; destruct E_EqDec.
rewrite <- Hsrc. rewrite <- Hdst. apply H2.
unfold complement, equiv in c; contradiction.
assert (x <> e) by (unfold complement, equiv in c; auto).
destruct H0. destruct H0. split. split.
apply FiniteWEdgeListGraph_adde_evalid2. apply H0.
simpl. unfold updateEdgeFunc. unfold equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0. contradiction. apply H4.
simpl. unfold updateEdgeFunc. unfold equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0. contradiction. apply H3.
apply IHp. auto. apply H0.
Qed.

Lemma adde_connected_by_path:
forall (g: FiniteWEdgeListGraph) e w p u v,
  sound_weighted_edge_graph g ->
  connected_by_path g p u v
  -> connected_by_path (FiniteWEdgeListGraph_adde g e w) p u v.
Proof.
unfold connected_by_path; intros.
split. apply adde_valid_upath. auto.
apply H0. apply H0.
Qed.

Corollary adde_connected:
forall (g: FiniteWEdgeListGraph) e w u v,
  sound_weighted_edge_graph g ->
  connected g u v
  -> connected (FiniteWEdgeListGraph_adde g e w) u v.
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
split.
destruct H0.
assert (Hsrc: src_edge g). apply H. unfold src_edge in Hsrc.
assert (Hdst: dst_edge g). apply H. unfold dst_edge in Hdst.
simpl. unfold pregraph_add_edge, addValidFunc, updateEdgeFunc.
split. split; simpl. left. apply H0.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e1.
rewrite e1. rewrite <- Hsrc; rewrite <- Hdst. apply H0.
apply H0.
simpl. unfold equiv_dec. destruct E_EqDec. unfold equiv in e1.
rewrite <- Hsrc; rewrite <- Hdst. rewrite e1. apply H0. apply H0.
apply IHp. apply H. apply fits_upath_cons in H0. apply H0.
Qed.

Lemma adde_connected_e:
forall (g:FiniteWEdgeListGraph) e w,
  sound_weighted_edge_graph g -> vvalid g (src g e) -> vvalid g (dst g e) ->
  connected (FiniteWEdgeListGraph_adde g e w) (src g e) (dst g e).
Proof.
intros. exists ((src g e)::(dst g e)::nil). split. 2: auto.
assert (src_edge g) by apply H.
assert (dst_edge g) by apply H.
split. exists e. split. split. apply FiniteWEdgeListGraph_adde_evalid1.
split; simpl; unfold updateEdgeFunc; unfold equiv_dec; destruct E_EqDec.
rewrite <- H2; auto. auto.
rewrite <- H3; auto. auto.
simpl; unfold updateEdgeFunc; unfold equiv_dec; destruct E_EqDec.
left; rewrite H2; rewrite H3; auto.
left; auto.
simpl. auto.
Qed.

Lemma adde_fits_upath':
forall (g: FiniteWEdgeListGraph) e w p l,
fits_upath (FiniteWEdgeListGraph_adde g e w) l p ->
~ In e l ->
fits_upath g l p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; auto.
destruct l. auto.
assert (Heq_e: e <> e0). unfold not; intros. assert (In e (e0::l)). left; rewrite H1; auto. contradiction.
assert (HIn_e: ~ In e l). unfold not; intros. assert (In e (e0::l)). right; auto. contradiction.
clear H0.
destruct H. split. destruct H. destruct H. split. split.
simpl in H. unfold addValidFunc in H. destruct H. apply H. symmetry in H. contradiction.
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
intros. apply (FiniteWEdgeListGraph_adde_vvalid g e w).
apply (valid_upath_vvalid _ _ v) in H. auto. auto.
exists l. destruct H0; auto.
Qed.

Lemma adde_bridge': (*anything that joins u v must contain (u,v)*)
forall (g: FiniteWEdgeListGraph) u v w p,
~ connected g u v ->
connected_by_path (FiniteWEdgeListGraph_adde g (u,v) w) p u v
-> forall l, fits_upath (FiniteWEdgeListGraph_adde g (u,v) w) l p ->
In (u,v) l.
Proof.
intros. destruct (in_dec E_EqDec (u,v) l). auto.
(*come to a contradiction that connected g u v*)
assert (connected g u v). exists p.
destruct H0. split. 2: auto.
apply (adde_unaffected g (u,v) w). apply H0.
exists l; split. apply (adde_fits_upath' g (u,v) w); auto. auto.
contradiction.
Qed.

Lemma adde_connected_through_bridge1:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
vvalid g u -> vvalid g v ->
connected g a u -> connected g v b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros. apply (adde_connected g (u,v) w) in H2; auto. apply (adde_connected g (u,v) w) in H3; auto.
destruct H2 as [x [? [? ?]]]. destruct H3 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (FiniteWEdgeListGraph_adde_strong_evalid1 g u v w); auto.
left. split. rewrite FiniteWEdgeListGraph_adde_src1; auto. rewrite FiniteWEdgeListGraph_adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma adde_connected_through_bridge2:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
vvalid g u -> vvalid g v ->
connected g a v -> connected g u b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros. apply (adde_connected g (u,v) w) in H2; auto. apply (adde_connected g (u,v) w) in H3; auto.
destruct H2 as [x [? [? ?]]]. destruct H3 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (FiniteWEdgeListGraph_adde_strong_evalid1 g u v w); auto.
right. split. rewrite FiniteWEdgeListGraph_adde_src1; auto. rewrite FiniteWEdgeListGraph_adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma fits_upath_vertex_src_In:
forall (g: FiniteWEdgeListGraph) p l e, fits_upath g l p -> In e l -> In (src g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1. left; symmetry; apply H1.
right. left. symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.

Lemma fits_upath_vertex_dst_In:
forall (g: FiniteWEdgeListGraph) p l e, fits_upath g l p -> In e l -> In (dst g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1.
right. left. symmetry; apply H1.
left; symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.
(*****************************SPANNING_UFOREST**********************)
(*These should be abstracted, but we can deal with it after the kruskal proof is done*)

Definition is_partial_lgraph
           (g1 g2: FiniteWEdgeListGraph) :=
  is_partial_graph g1 g2 /\
  (forall v, vvalid g1 v -> vlabel g1 v = vlabel g2 v) /\
  (forall e, evalid g1 e -> elabel g1 e = elabel g2 e).

Lemma is_partial_lgraph_refl: forall g,
    is_partial_lgraph g g.
Proof. intros. split; auto. apply is_partial_graph_refl. Qed.

Lemma is_partial_lgraph_trans: forall g1 g2 g3,
    is_partial_lgraph g1 g2 -> is_partial_lgraph g2 g3 -> is_partial_lgraph g1 g3.
Proof.
  intros. split. apply (is_partial_graph_trans g1 g2 g3). apply H. apply H0. split; intros.
  destruct H. destruct H2. rewrite H2. destruct H0. destruct H4. rewrite H4. auto.
  apply H. auto. auto.
  intros. destruct H. destruct H2. rewrite H3. destruct H0. destruct H4. rewrite H5. auto.
  apply H. auto. auto.
Qed.

Lemma is_partial_lgraph_adjacent:
forall g1 g2 u v, is_partial_lgraph g1 g2 -> adjacent g1 u v -> adjacent g2 u v.
Proof.
intros. destruct H0. destruct H0. destruct H0. destruct H2.
destruct H. destruct H4. destruct H. destruct H6. destruct H7.
exists x. split. split. apply H6; auto.
rewrite <- H7; auto. rewrite <- H8; auto.
rewrite <- H7; auto. rewrite <- H8; auto.
Qed.

Lemma is_partial_lgraph_valid_upath:
forall g1 g2 p, is_partial_lgraph g1 g2 -> valid_upath g1 p -> valid_upath g2 p.
Proof.
intros. induction p. auto. destruct p. simpl. simpl in H0. apply H. apply H0.
destruct H0. split. apply (is_partial_lgraph_adjacent g1 g2); auto. auto.
Qed.

Lemma is_partial_lgraph_connected:
forall g1 g2, is_partial_lgraph g1 g2 ->
forall u v, connected g1 u v -> connected g2 u v.
Proof.
intros. destruct H0 as [p ?]. destruct H0.
exists p. split.
apply (is_partial_lgraph_valid_upath g1 g2); auto. auto.
Qed.

(*
Lemma partial_lgraph_preservation:
forall (g t1: FiniteWEdgeListGraph), sound_weighted_edge_graph g ->
is_partial_lgraph t1 g -> sound_weighted_edge_graph t1.
Proof.
intros.
destruct H0. destruct H1. destruct H0. destruct H.
split. admit.
split. admit.
split. admit.
split. unfold src_edge; intros. destruct H4; destruct H6; destruct H7.
unfold src_edge in H7. rewrite <- H7. apply H3. auto. assert (edge_valid t1). admit.
apply H9 in H5. apply H5. apply H3. auto.
unfold dst_edge in H8. rewrite <- H8. apply H4. auto. assert (edge_valid t1). admit.
apply H9 in H5. apply H5. apply H3. auto.
*)
Lemma partial_lgraph_map:
forall g1 g2 l, is_partial_lgraph g1 g2 -> (forall e, In e l -> evalid g1 e) ->
  map (elabel g1) l = map (elabel g2) l.
Proof.
induction l; intros. simpl; auto.
rewrite map_cons. rewrite map_cons. replace (elabel g1 a) with (elabel g2 a).
replace (map (elabel g1) l) with (map (elabel g2) l). auto.
symmetry. apply IHl. auto. intros. apply H0. right; apply H1.
destruct H. destruct H1. symmetry. apply H2. apply H0. left; auto.
Qed.

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

(*NoDup is probably unnecessary, but convenient*)
Lemma list_same_diff:
forall {A: Type} {EA: EqDec A eq} (l1 l2: list A), NoDup l1 -> NoDup l2 ->
      exists lsame ldiff, NoDup lsame /\ NoDup ldiff /\ Permutation (lsame++ldiff) l1 /\
      incl lsame l2 /\ (forall e, In e ldiff -> ~ In e l2).
Proof.
induction l1; intros. exists nil. exists nil.
  rewrite app_nil_l. split. apply NoDup_nil. split. apply NoDup_nil. split. apply perm_nil.
  split. unfold incl; intros; contradiction. intros. unfold not; intros; contradiction.
  (*By NoDup, a can't already be in l1
  *)
  specialize IHl1 with l2. assert (NoDup l1). apply NoDup_cons_1 in H; auto.
  apply (IHl1 H1) in H0. destruct H0 as [lsame [ldiff [? [? ?]]]].
  destruct (in_dec EA a l2).
  (*yes, then a is in lsame*)
  exists (a::lsame). exists ldiff. split. simpl. apply NoDup_cons. unfold not; intros.
  assert (In a l1). apply (Permutation_in (l:=(lsame++ldiff))). apply H3.
  apply in_or_app. left; auto.
  apply NoDup_cons_2 in H. contradiction.
  auto. split. auto. split. simpl. apply perm_skip. apply H3.
  split. unfold incl; intros. destruct H4. subst a; auto. apply H3; auto. apply H3.
  (*no, then a is in ldiff*)
  exists lsame. exists (a::ldiff). split. auto. split. apply NoDup_cons.
  unfold not; intros. assert (In a l1).
  apply (Permutation_in (l:=(lsame++ldiff))). apply H3.
  apply in_or_app. right; auto.
  apply NoDup_cons_2 in H. contradiction.
  auto. split.
  apply (Permutation_trans (l:=lsame ++ a :: ldiff) (l':=a::ldiff++lsame)).
  apply Permutation_app_comm. apply perm_skip.
  apply (Permutation_trans (l':=lsame ++ ldiff) (l:=ldiff++lsame)).
  apply Permutation_app_comm. apply H3.
  split. apply H3. intros. destruct H4. subst a. auto. apply H3. auto.
Qed.

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

Definition spanning_uforest g t := is_partial_lgraph t g /\ uforest t /\ (forall u v, connected g u v <-> connected t u v).

Lemma spanning_uforest_preserves_vertices:
forall g t v, spanning_uforest g t -> (vvalid g v <-> vvalid t v).
Proof.
intros; split; intros; pose proof (connected_refl _ v H0);
apply H in H1; apply connected_vvalid in H1; apply H1.
Qed.

Definition DEList (g: FiniteWEdgeListGraph): list LE :=
  map (elabel g) (EList g).

Definition sum_LE g : LE :=
  fold_left Z.add (DEList g) 0.

Definition minimum_spanning_forest g t :=
  spanning_uforest g t /\
  forall t', spanning_uforest g t' ->
    Z.le (sum_LE t) (sum_LE t').

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv':
  forall (g: FiniteWEdgeListGraph) (l: list EType),
  Permutation (EList g) l -> sum_LE g = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

Lemma sum_LE_equiv:
  forall (g: FiniteWEdgeListGraph) (l: list (LE*EType)),
  Permutation (graph_to_wedgelist g) l -> sum_LE g = fold_left Z.add (map fst l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
replace (map (elabel g) (EList g)) with (map fst (graph_to_wedgelist g)).
apply Permutation_map. auto.
unfold graph_to_wedgelist. unfold edge_to_wedge.
rewrite map_map. simpl. auto.
Qed.