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

End SpaceDijkstraArrayGraph.
  
  Definition careful_add (a b : Z) :=
    if Z.eqb a 0 then b else
      if Z.eqb b 0 then a else
        if Z.leb inf (a + b) then inf else a + b.

  Lemma if_true_bool:
    forall (T : Type) (a : T) (b : bool) (c : T),
      b = true -> (if b then a else c) = a.
  Proof. intros. rewrite H. trivial. Qed.

    Lemma if_false_bool:
    forall (T : Type) (a : T) (b : bool) (c : T),
      b = false -> (if b then a else c) = c.
  Proof. intros. rewrite H. trivial. Qed.
  
  Lemma careful_add_comm:
    forall a b, careful_add a b = careful_add b a.
  Proof.
    intros. unfold careful_add.
    destruct (a =? 0) eqn:?; destruct (b =? 0) eqn:?; trivial.
    - try rewrite Z.eqb_eq in *. omega.
    - destruct (inf <=? a + b) eqn:?;
               rewrite Z.add_comm in Heqb2; rewrite Heqb2; omega.
  Qed.

  (* maybe I can lose the Hypos? *)  
  Lemma careful_add_assoc:
    forall a b c,
      0 <= a -> 0 <= b -> 0 <= c ->
      careful_add a (careful_add b c) =
      careful_add (careful_add a b) c.
  Proof.
    intros.
    unfold careful_add.
    destruct (a =? 0) eqn:?;
     destruct (b =? 0) eqn:?;
      destruct (c =? 0) eqn:?; trivial.
    - rewrite if_false_bool; trivial.
    - rewrite (if_false_bool _ _ (a =? 0)); trivial.
    - rewrite if_false_bool; trivial.
      rewrite (if_false_bool _ _ ((if inf <=? a + b then inf else a + b) =? 0)); trivial.
      destruct (inf <=? a + b) eqn:?.
      + trivial.
      + rewrite Z.eqb_neq in *. omega.
    - {
      rewrite Z.eqb_neq in *.
      assert ((inf =? 0) = false) by
          (rewrite Z.eqb_neq; compute; omega).
      destruct (inf <=? a) eqn:?.
    - rewrite Z.leb_le in Heqb3.
      destruct (inf <=? b + c) eqn:?.
      + rewrite H2.
        rewrite Z.leb_le in Heqb4.
        rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
        rewrite (if_true_bool _ _ (inf <=? a + b)) by (apply Zle_imp_le_bool; omega).
        rewrite H2.
        rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
        trivial.
      + rewrite if_false_bool by (rewrite Z.eqb_neq; omega).
        rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
        rewrite (if_true_bool _ _ (inf <=? a + b)) by (apply Zle_imp_le_bool; omega).
        rewrite H2.
        rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
        trivial.
    - destruct (inf <=? b + c) eqn:?.
      + rewrite Z.leb_le in Heqb4.
        rewrite H2.
        rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
        destruct (inf <=? a + b) eqn:?.
        * rewrite Z.leb_le in Heqb5.
          rewrite H2.
          rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
          trivial.
        * rewrite if_false_bool by
              (rewrite Z.eqb_neq; omega).
          rewrite if_true_bool by (apply Zle_imp_le_bool; omega).
          trivial.
      + repeat rewrite Z.add_assoc.
        destruct (inf <=? a + b + c) eqn:?.
        * rewrite if_false_bool by
              (rewrite Z.eqb_neq; omega).
          rewrite Z.leb_le in Heqb5.
          rewrite (if_false_bool _ _ ((if inf <=? a + b then inf else a + b) =? 0)).
          2: { destruct (inf <=? a + b).
               - compute. trivial.
               - rewrite Z.eqb_neq. omega.
          }
          destruct (inf <=? a + b) eqn:?;
                   rewrite if_true_bool by (apply Zle_imp_le_bool; omega);
            trivial.
        * rewrite if_false_bool by (rewrite Z.eqb_neq; omega).
          rewrite Z.leb_gt in Heqb5. 
          rewrite if_false_bool.
          2: { destruct (inf <=? a + b).
               - compute. trivial.
               - rewrite Z.eqb_neq. omega.
          }
          rewrite if_false_bool; rewrite if_false_bool;
            trivial; rewrite Z.leb_gt; omega.
      }
  Qed.
    
  Lemma careful_add_0:
    forall a, careful_add a 0 = a.
  Proof.
    intros. unfold careful_add.
    destruct (a =? 0) eqn:?; trivial.
    rewrite Z.eqb_eq in Heqb. omega.
  Qed.

  Lemma careful_add_clean:
    forall a b,
      a + b < inf ->
      careful_add a b = a + b.
  Proof.
    intros. unfold careful_add.
    destruct (a =? 0) eqn:?;
     destruct (b =? 0) eqn:?;
    try rewrite Z.eqb_eq in *;
      try rewrite Z.eqb_neq in *; subst; try omega.
    rewrite if_false_bool; trivial.
    rewrite Z.leb_gt; omega.
  Qed.
       
  Definition path_cost (g: LGraph) (path : @path VType EType) :=
    fold_left careful_add (map (elabel g) (snd path)) 0.
  
  Lemma path_cost_app_cons:
    forall g path i,
      elabel g i + path_cost g path < inf ->
      path_cost g (fst path, snd path +:: i) =
      path_cost g path + elabel g i.
  Proof.
    intros. unfold path_cost in *. simpl.
    rewrite map_app, fold_left_app. simpl. 
    apply careful_add_clean. omega. 
 Qed.
    
  Lemma path_cost_general:
    forall g p init,
      init < inf ->
      fold_left careful_add (map (elabel g) (snd p)) init = careful_add init (path_cost g p).
  Proof.
    intros. unfold path_cost.
    unfold LE in *.
    remember (map (elabel g) (snd p)) as l.
    remember careful_add as f.
    clear -H Heqf.
    induction l.
    - simpl. subst f. unfold careful_add.
      rewrite Z.add_0_r.
      destruct (init =? 0) eqn:?.
      1: rewrite Z.eqb_eq in Heqb; omega.
      trivial.
    - Abort.

  Lemma path_cost_with_init:
    forall l init,
      init < inf ->
      (* fold_left careful_add l 0 < inf -> *)
      fold_left careful_add l init =
      careful_add init (fold_left careful_add l 0).
  Proof.
    intros. induction l.
    - intros; simpl. unfold careful_add.
      destruct (init =? 0) eqn:?; trivial.
      rewrite Z.eqb_eq in Heqb; omega.
    - rewrite (List_Func_ext.monoid_fold_left_head 0).
      2: intro; rewrite careful_add_comm, careful_add_0.
      3: intro; rewrite careful_add_0.
      4: admit. (* will weaken assoc *)
      all: try apply Equivalence.equiv_reflexive_obligation_1.
      admit.

(*
      rewrite careful_add_assoc.
      rewrite (careful_add_comm init a).
      rewrite <- careful_add_assoc.
      rewrite <- (List_Func_ext.monoid_fold_left_head 0).
      simpl.
      replace (careful_add 0 init) with init.
      fold_left careful_add l (careful_add init a) =
  careful_add a (fold_left careful_add l init)
 *)
  Admitted.

      Lemma path_cost_path_glue:
    forall g p1 p2,
      path_cost g (path_glue p1 p2) = careful_add (path_cost g p1) (path_cost g p2).
  Proof.
    intros.
    unfold path_cost at 1, path_glue at 1.
    simpl. rewrite map_app.
    rewrite fold_left_app.
    unfold LE in *.
    unfold LE in *.
    assert ((fold_left careful_add (map (elabel g) (snd p1)) 0) = (path_cost g p1))
      by now unfold path_cost.
    Set Printing All. unfold LE in *. rewrite H. 
    unfold path_cost at 3.
    remember (map (elabel g) (snd p2)) as l2.
    unfold LE in *.
    rewrite <- Heql2.
    Unset Printing All.
    remember (path_cost g p1) as c1.
    rewrite path_cost_with_init; trivial.
    Admitted. (* the premises of path_cost_general
                 are a-changing *)      
 
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
  


(*
   Lemma path_cost_path_glue:
     forall g p1 p2,
       path_cost g (path_glue p1 p2) = careful_add (path_cost g p1) (path_cost g p2).
   Proof.
     intros.
     unfold path_glue, path_cost. simpl.
     rewrite map_app.
     remember (map (elabel g) (snd p1)) as m1.
     remember (map (elabel g) (snd p2)) as m2.
     rewrite List_Func_ext.monoid_fold_left_app; intros; trivial.
(*     - rewrite careful_add_l_0. apply Equivalence.equiv_reflexive_obligation_1.
     - rewrite careful_add_r_0. apply Equivalence.equiv_reflexive_obligation_1.
     - unfold careful_add.
       destruct (x =? inf) eqn:?;
                destruct (y =? inf) eqn:?;
                destruct (z =? inf) eqn:?; simpl;
         try apply Equivalence.equiv_reflexive_obligation_1.
       + destruct (x + y =? inf); simpl; apply Equivalence.equiv_reflexive_obligation_1.
 *)
   Admitted.
*)
