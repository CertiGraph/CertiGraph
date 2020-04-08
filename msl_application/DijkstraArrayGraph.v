Require Import Coq.ZArith.ZArith.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.msl_application.ArrayGraph.
 
Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.
Definition SIZE := 8.
Definition inf := Int.max_signed - Int.max_signed/SIZE.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).


(*
 Concretizing the DijkstraGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  | list DE |  Z  | unit |  Finite   | 
*)

Definition VType : Type := Z.
Definition EType : Type := VType * Z.
Definition LE : Type := Z.
Definition LV: Type := list LE.
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec z z0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Lemma nat_inc_list_Zlength:
  forall n, Zlength (nat_inc_list n) = Z.of_nat n.
Proof.
  intros. now rewrite Zlength_correct, nat_inc_list_length. Qed.

Lemma nat_inc_list_i: forall i n,
    0 <= i < Z.of_nat n ->
    Znth i (nat_inc_list n) = i.
Proof.
  intros. generalize dependent i. induction n.
  1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; omega.
  intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
  apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
  - rewrite app_Znth1. apply IHn. omega.
    now rewrite nat_inc_list_Zlength.
  - rewrite app_Znth2 by (rewrite nat_inc_list_Zlength; omega). 
    rewrite H0. rewrite nat_inc_list_Zlength. simpl. 
    replace (Z.of_nat n - Z.of_nat n) with 0 by omega.
    rewrite Znth_0_cons; trivial.
Qed.

Class Fin (g: LabeledGraph VType EType LV LE LG) :=
  { fin: FiniteGraph g; }.

Definition LGraph := LabeledGraph VType EType LV LE LG.
Definition Graph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

Definition vertex_valid (g: LGraph): Prop :=
  forall v, vvalid g v <-> 0 <= v < SIZE.

Definition edge_valid (g: LGraph): Prop :=
  forall e, evalid g e <->
            (vvalid g (fst e) /\ 0 <= snd e < SIZE).

Definition src_edge (g: LGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g: LGraph): Prop :=
  forall e, dst g e = snd e.

Definition sound_dijk_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g.

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

  Definition vert_rep (g: LGraph) (v : VType) : list Z :=
    map (elabel g) (map (fun x => (v,x)) (nat_inc_list (Z.to_nat SIZE))).
  
  (* from Graph to list (list Z) *)
  Definition graph_to_mat (g : LGraph) : list (list Z) :=
    map (vert_rep g) (nat_inc_list (Z.to_nat SIZE)).
  
  (* spatial representation of the DijkstraGraph *)
  Definition graph_rep (g : Graph) (a : Addr)  :=
    abstract_data_at a (concat (graph_to_mat g)).

  Definition careful_add (a b : Z) :=
    if (orb (Z.eqb a inf) (Z.eqb b inf)) then inf else a + b.

  Lemma careful_add_clean:
    forall a b,
      a <> inf ->
      b <> inf ->
      careful_add a b = a + b.
  Proof.
    intros. unfold careful_add.
    rewrite <- Z.eqb_neq in *.
    destruct (a =? inf); destruct (b =? inf);
      try discriminate; simpl; trivial.
  Qed.    
   
  Definition path_cost (g: LGraph) (path : @path VType EType) :=
    fold_left careful_add (map (elabel g) (snd path)) 0.
  
  Lemma path_cost_app_cons:
    forall g path i,
      elabel g i <> inf ->
      path_cost g path <> inf ->
      path_cost g (fst path, snd path +:: i) =
      path_cost g path + elabel g i.
  Proof.
    intros. unfold path_cost in *. simpl.
    rewrite map_app, fold_left_app. simpl.
    apply careful_add_clean; assumption.
  Qed. 

  Lemma elabel_Znth_graph_to_mat:
    forall g i,
      sound_dijk_graph g ->
      evalid (pg_lg g) i ->
      elabel g i =
      Znth (snd i) (Znth (fst i) (graph_to_mat g)).
  Proof.
    intros. destruct i as (src, dst); simpl.
    unfold graph_to_mat.
    destruct H as [? [? _]].
    unfold vertex_valid in H; unfold edge_valid in H1.
    rewrite H1 in H0; destruct H0. simpl in H0, H2.
    rewrite H in H0.
    rewrite Znth_map, nat_inc_list_i.
    unfold vert_rep. rewrite Znth_map.
    rewrite Znth_map. rewrite nat_inc_list_i.
    reflexivity.
    3: rewrite Zlength_map.
    2, 3, 5: rewrite nat_inc_list_Zlength.
    all: rewrite Z2Nat.id; omega.
Qed.
  
End SpaceDijkstraArrayGraph.

