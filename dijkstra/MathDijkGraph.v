Require Export VST.floyd.proofauto.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.

Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.FiniteGraph.

Require Import Coq.Classes.EquivDec.

(* This file is just one line: "Require Export priq.priq_arr_utils." 
   It can be inlined. 
   It is currently a separate file in case we want more constants stashed away *)
Require Export RamifyCoq.dijkstra.dijkstra_constants.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

(*
 Concretizing the DijkstraGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  | list DE |  Z  | unit |  Finite   | 
 *)

Definition VType : Type := Z.
Definition EType : Type := VType * VType.
Definition ElabelType : Type := Z. (* labels are in Z *)
Definition LE : Type := ElabelType.
Definition LV: Type := list LE.
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

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(* Here is the LabeledGraph *)
Definition DijkstraLabeledGraph := LabeledGraph VType EType LV LE LG.

(* The soundness condition (just one item for now) *)
Class Fin (g: DijkstraLabeledGraph) :=
  { fin: FiniteGraph g; }.

(* And the GeneralGraph that we will use *)
Definition DijkstraGeneralGraph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

Definition vertex_valid (g : DijkstraGeneralGraph): Prop :=
  forall v, vvalid g v <-> 0 <= v < SIZE.

Definition edge_valid (g : DijkstraGeneralGraph): Prop :=
  forall a b, evalid g (a,b) <->
            (vvalid g a /\ vvalid g b).

Definition src_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, dst g e = snd e.

Definition sound_dijk_graph (g : DijkstraGeneralGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g.
(* shouldn't this all go into soundess? *)


(* Moving on to Spatial Rep *)

Section SpaceDijkstraArrayGraph.
  
  Class SpatialDijkstraArrayGraphAssum (Pred : Type):=
    {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
    }.
  
  Class SpatialDijkstraArrayGraph (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list Z -> Pred.

  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAGP: SpatialDijkstraArrayGraphAssum Pred}.
  Context {SAG: SpatialDijkstraArrayGraph Addr Pred}.

  Definition vert_rep (g : DijkstraGeneralGraph) (v : VType) : list Z :=
    map (elabel g) (map (fun x => (v,x)) (nat_inc_list (Z.to_nat SIZE))).
  
  (* from Graph to list (list Z) *)
  Definition graph_to_mat (g : DijkstraGeneralGraph) : list (list Z) :=
    map (vert_rep g) (nat_inc_list (Z.to_nat SIZE)).
  
  (* spatial representation of the DijkstraGraph *)
  Definition graph_rep (g : DijkstraGeneralGraph) (a : Addr)  :=
    abstract_data_at a (concat (graph_to_mat g)).

End SpaceDijkstraArrayGraph.

Lemma graph_to_mat_Zlength: forall g, Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; auto. now vm_compute.
Qed.

Definition inrange_graph grph_contents :=
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
    Znth i (Znth j grph_contents) = inf.

Lemma elabel_Znth_graph_to_mat:
  forall g src dst,
    sound_dijk_graph g ->
    evalid (pg_lg g) (src, dst) ->
    elabel g (src, dst) =
    Znth dst (Znth src (graph_to_mat g)).
Proof.
  intros. 
  unfold graph_to_mat.
  destruct H as [? [? _]].
  red in H, H1.
  rewrite H1 in H0; destruct H0. 
  rewrite H in H0, H2.
  rewrite Znth_map, nat_inc_list_i.
  unfold vert_rep. rewrite Znth_map.
  rewrite Znth_map. rewrite nat_inc_list_i.
  reflexivity.
  3: rewrite Zlength_map.
  2, 3, 5: rewrite nat_inc_list_Zlength.
  all: rewrite Z2Nat.id; lia.
Qed.

Lemma vvalid2_evalid:
  forall g a b,
    sound_dijk_graph g ->
    vvalid g a ->
    vvalid g b ->
    evalid g (a,b).
Proof.
  intros. destruct H as [_ [? _]].
  red in H; rewrite H; split; trivial.
Qed.

Lemma vvalid_range:
  forall g a,
    sound_dijk_graph g ->
    vvalid g a <-> 0 <= a < SIZE.
Proof.
  intros. destruct H as [? _]. red in H. trivial.
Qed.

Lemma valid_path_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    evalid g (u,i) ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  assert (Hrem := H).
  destruct H as [? [? [? ?]]].
  simpl; split.
  1: rewrite H4; simpl; assumption.
  unfold strong_evalid.
  rewrite H4, H5; simpl.
  split; trivial.
  red in H3; rewrite H3 in H2; trivial.
Qed.

Lemma path_ends_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.
  split.
  + destruct H0; apply H0.
  + rewrite pfoot_last.
    destruct H as [_ [_ [_ ?]]].
    rewrite H; reflexivity.
Qed.

Lemma inrange_graph_cost_pos: forall g e,
    sound_dijk_graph g -> inrange_graph (graph_to_mat g) ->
    evalid g e -> 0 <= elabel g e.
Proof.
  intros. rewrite (surjective_pairing e) in *.
  rewrite elabel_Znth_graph_to_mat; auto. destruct H as [? [? _]].
  red in H, H2.
  rewrite (surjective_pairing e) in H1.
  rewrite H2 in H1. red in H0.
  rewrite (graph_to_mat_Zlength g) in H0.
  simpl in H1. destruct H1. rewrite H in H1, H3.
  specialize (H0 _ _ H3 H1). destruct H0.
  1: destruct H0; lia.
  rewrite H0. compute; inversion 1.
Qed.

Lemma step_in_range: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [? _]]].
  unfold vertex_valid in H.
  unfold src_edge in H2.
  assert (In_path g (fst x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| left]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
Qed.

Lemma step_in_range2: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [_ ?]]].
  unfold vertex_valid in H.
  unfold dst_edge in H2.
  assert (In_path g (snd x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| right]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
Qed.

