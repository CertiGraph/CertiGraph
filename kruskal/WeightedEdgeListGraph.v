(*Looted from msl_application/DijkstraArrayGraph
Should try abstracting it if possible from an EdgeListGraph*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
(*Require Import RamifyCoq.msl_application.ArrayGraph.*) (*I probably need this to transform this graph to the ArrayGraph?*)
Require Import RamifyCoq.graph.FiniteGraph.
Require Import Coq.Lists.List.
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
forall (g: FiniteWEdgeListGraph) e w P p u v,
  sound_weighted_edge_graph g ->
  connected_by_path g P p u v
  -> connected_by_path (FiniteWEdgeListGraph_adde g e w) P p u v.
Proof.
unfold connected_by_path; intros.
split. split. apply adde_valid_upath. auto.
apply H0. apply H0. apply H0.
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

Lemma VList_dec:
forall (g: FiniteWEdgeListGraph) v, In v (VList g) \/ ~ In v (VList g).
Proof.
intros. destruct (in_dec V_EqDec v (VList g)); auto.
Qed.

Lemma vvalid_dec:
forall (g: FiniteWEdgeListGraph) v, vvalid g v \/ ~ vvalid g v.
Proof.
intros. destruct (VList_dec g v); rewrite VList_vvalid in H; auto.
Qed.

Lemma EList_dec:
forall (g: FiniteWEdgeListGraph) e, In e (EList g) \/ ~ In e (EList g).
Proof.
intros. destruct (in_dec E_EqDec e (EList g)); auto.
Qed.

Lemma evalid_dec:
forall (g: FiniteWEdgeListGraph) e, evalid g e \/ ~ evalid g e.
Proof.
intros. destruct (EList_dec g e); rewrite EList_evalid in H; auto.
Qed.

Lemma connected_to_self:
forall (g: FiniteWEdgeListGraph) v, vvalid g v -> connected g v v.
Proof.
(* this proof causes universe inconsistency *)
(*
intros. exists (v::nil). split. split. simpl; auto. rewrite Forall_forall. auto. simpl; auto.
Qed.
 *)
(* but this proof works: *)
  intros. exists (v::nil).
  unfold connected_by_path; Coqlib2.split3; trivial.
  unfold good_upath; split; trivial.
  unfold upath_prop. rewrite Forall_forall.
  intros; trivial.
Qed.

Definition connected_dec (g:FiniteWEdgeListGraph):=
forall u v, connected g u v \/ ~ connected g u v.


Lemma edgeless_connected_dec:
forall x, connected_dec (edgeless_WEdgeGraph x).
Proof.
unfold connected_dec; intros. set (g:=edgeless_WEdgeGraph x).
destruct (vvalid_dec g u); destruct (vvalid_dec g v).
(*both are vvalid*)
destruct (V_EqDec u v).
(*u=v: trivially connected*)
unfold equiv in e; rewrite e. left; apply connected_to_self. auto.
(*u<>v: not connected*)
unfold complement, equiv in c. right; unfold not; intros. destruct H1 as [p ?]. destruct H1. destruct H2. destruct H1.
destruct p. inversion H2. destruct p. inversion H2; inversion H3. rewrite H6 in H7; contradiction.
destruct H1. destruct H1. destruct H1. destruct H1.
pose proof (edgeless_WEdgeGraph_evalid x x0). contradiction.
(*other cases; not connected*)
all: right; unfold not; intros; apply connected_vvalid in H1; destruct H1; contradiction.
Qed.

Lemma adde_connected_e:
forall (g:FiniteWEdgeListGraph) e w,
  sound_weighted_edge_graph g -> vvalid g (src g e) -> vvalid g (dst g e) ->
  connected (FiniteWEdgeListGraph_adde g e w) (src g e) (dst g e).
Proof. Admitted.
(* this proof causes universe inconsistency 
intros. exists ((src g e)::(dst g e)::nil). split. 2: auto.
split. 2: rewrite Forall_forall; auto.
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
*)
(*
Lemma adde_connected_dec:
forall (g:FiniteWEdgeListGraph) e w,
  sound_weighted_edge_graph g -> vvalid g (src g e) -> vvalid g (dst g e) ->
  connected_dec g ->
  connected_dec (FiniteWEdgeListGraph_adde g e w).
Proof.
unfold connected_dec; intros.
destruct (H2 u v). left. apply adde_connected; auto.

Fixpoint addedges (g:FiniteWEdgeListGraph) (l: list (LE*EType)):=
match l with
| nil => g
| a::l => addedges (FiniteWEdgeListGraph_adde g (snd a) (fst a)) l
end.

Lemma FiniteGraph_built_from_edgeless:
forall (g: FiniteWEdgeListGraph), g = addedges (edgeless_WEdgeGraph (numV g)) (graph_to_wedgelist g).
Proof.
intros.
Qed.
*)

(*
Definition wedgelist_to_graph (z: Z) (l: list (LE*EType)):=
@Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG
  (@Build_PreGraph VType EType V_EqDec E_EqDec (fun v => 0 <= v < z) (fun e => In (map snd l)) fst snd)
  (fun v => tt) (fun e => ) tt.
*)

(**Removing may be needed in the proof of minimality**)
