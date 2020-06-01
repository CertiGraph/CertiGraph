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
(*
Print Build_PreGraph.
Print Build_LabeledGraph.

Definition Build_WEdgeListGraph := Build_LabeledGraph LV LE LG.
*)
 
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


Definition src_edge (g : WEdgeListGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g: WEdgeListGraph): Prop :=
  forall e, dst g e = snd e.

Definition vertex_valid (g: WEdgeListGraph): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: WEdgeListGraph): Prop :=
  forall a b, evalid g (a,b) -> (vvalid g a /\ vvalid g b).

Definition weight_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition sound_weighted_edge_graph (g: WEdgeListGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g /\ weight_valid g.

Definition numV (g: FiniteWEdgeListGraph) : Z := Zlength (VList g).
Definition numE (g: FiniteWEdgeListGraph) : Z := Zlength (EList g).

(* from Graph to list of edges *)
Definition graph_to_wedgelist (g: FiniteWEdgeListGraph) : list (LE * EType) :=
  map (fun e => (elabel g e, e)) (EList g). (*ordering unknown*)

(* Moving on to Spatial Rep *)

Section SpatialWEdgeListGraph.
  
  Class SpatialWEdgeListGraphAssum (Pred : Type):= (*what is this?*)
    {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
    }.
  
  Class SpatialWEdgeListGraph (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list (LE*EType) -> Pred.

  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAGP: SpatialWEdgeListGraphAssum Pred}.
  Context {SAG: SpatialWEdgeListGraph Addr Pred}.
  
End SpatialWEdgeListGraph.


Lemma if_true_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = true -> (if b then a else c) = a.
Proof. intros. rewrite H. trivial. Qed.

Lemma if_false_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = false -> (if b then a else c) = c.
Proof. intros. rewrite H. trivial. Qed.


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
Definition WEdgeListGraph_add_edge (g: WEdgeListGraph) (e: EType) (w: LE):=
  labeledgraph_add_edge g e (fst e) (snd e) w.

Instance Sound_WEdgeListGraph_add_edge (g: FiniteWEdgeListGraph) (e: EType) (w: LE) :
  vvalid g (fst e) -> vvalid g (snd e) -> ~ In e (EList g) -> Fin (WEdgeListGraph_add_edge g e w).
Proof.
intros. constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
apply g.
exists (e::(EList g)). split. apply NoDup_cons. apply H1. apply NoDup_EList.
unfold addValidFunc.
simpl. intros; rewrite EList_evalid. split; intros; destruct H2; auto.
Qed.

(**Removing may be needed in the proof of minimality**)