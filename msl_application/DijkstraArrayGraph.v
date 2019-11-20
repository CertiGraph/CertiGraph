Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.ZArith.ZArith.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
Require Import RamifyCoq.msl_application.DijkstraGraph.
(* TODO: Narrow the above to be minimal *)

Local Open Scope logic.
Local Open Scope Z_scope.
Definition inf := Integers.Int.max_signed.
Definition SIZE := 8.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).


(* 
 Concretizing the DijkstraGraph with array-specific types.
 |  V  |  E  |    DV   |    DE    |  DG  | soundness |
 |-----|-----|---------|----------|------|-----------| 
 |  Z  |  Z  | list DE | option Z | unit |  Finite   |  
 *)

Definition VType : Type := Z.
Definition EType : Type := Z.
Definition LE : Type := option Z. (* not negative Zs. add to soundness?*)
Definition LV: Type := list LE.
Definition LG: Type := unit.
(*Record LG: Type := (* may be unnecessary? *)
  {
  vertices : list LV;
  size: nat;
  vertices_range: length vertices = size
  }. *)

Fixpoint Z_inc_list (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => Z_inc_list n' ++ (Z.of_nat n' :: nil)
  end.

Lemma Z_inc_list_length: forall n, Zlength (Z_inc_list n) = Z.of_nat n.
Proof.
  intros. induction n. trivial.
  simpl Z_inc_list. rewrite Zlength_app. rewrite IHn.
  rewrite Nat2Z.inj_succ. unfold Zlength. simpl. omega.
Qed.

Lemma Z_inc_list_eq: forall i len,
    0 <= i < (Z.of_nat len) -> i = Znth i (Z_inc_list len).
Proof.
  intros. generalize dependent i. induction len.
  1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; omega.
  intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
  apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
  - rewrite app_Znth1. apply IHlen. omega. now rewrite Z_inc_list_length.
  - rewrite app_Znth2 by (rewrite Z_inc_list_length; omega).
    rewrite H0 at 2. rewrite Z_inc_list_length. simpl.
    replace (Z.of_nat len - Z.of_nat len) with 0 by omega.
    rewrite Znth_0_cons; trivial.
Qed.


Class Fin (g: LabeledGraph VType EType LV LE LG) :=
  { fin: FiniteGraph g;
    (* pos: Z_inc_list (Z.to_nat SIZE) *)
  }.

Definition LGraph := LabeledGraph VType EType LV LE LG.
Definition Graph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).


(* Definition Graph := (@Graph VType EType _ _ LV LE LG). *)
(* Definition LGraph := (@LGraph VType EType _ _ LV LE LG). *)


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

  Fixpoint choose {A : Type} (l : list (option A)) : list A :=
    match l with
    | nil => nil
    | Some x :: tl => x :: choose tl
    | None :: tl => choose tl
    end.
  
  (* TODO: move this to vvalid of a Dijk path *)
  Definition allTrue {A : Type} (l : list (option A)) : bool :=
    fold_right (fun x acc => match x with Some _ => acc | _ => false end) true l.
  
  (* assuming that allTrue will be in the vvalid of path *)
  Definition path_cost (g: LGraph) (p : @path VType EType) : Z :=
    match p with
    | (v, nil) => 0
    | (v, edges) => fold_left Z.add (choose (map (elabel g) edges)) 0
    end.
  
  Definition vert_rep (g: LGraph) (v : LV) : list Z :=
    map (fun x => match x with Some x => x | None => inf end) v.
  
  (* from Graph to list (list Z) *)
  Definition graph_to_mat (g : LGraph) : list (list Z) :=
    map (vert_rep g) (map (vlabel g) (Z_inc_list (Z.to_nat SIZE))).
  
  Definition list_rep listaddr contents_mat index :=
    abstract_data_at listaddr (Znth index contents_mat).
  
  (* spatial representation of the DijkstraGraph *)
  Definition graph_rep (g : Graph) (a : Addr)  :=
    abstract_data_at a (concat (graph_to_mat g)).
  
(* But the above is a little annoying.
   I would prefer to make an iter_sepcon of the various list_reps.
   The issue right now is that I can't get the lists to calculate
   their own addresses. 
*)
  
End SpaceDijkstraArrayGraph.

