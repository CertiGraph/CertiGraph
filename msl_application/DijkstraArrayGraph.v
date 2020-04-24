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
Require Import Coq.Lists.List.


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
  forall a b, evalid g (a,b) <->
            (vvalid g a /\ vvalid g b).

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

Lemma if_true_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = true -> (if b then a else c) = a.
Proof. intros. rewrite H. trivial. Qed.

Lemma if_false_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = false -> (if b then a else c) = c.
Proof. intros. rewrite H. trivial. Qed.

Definition careful_add (a b : Z) :=
  if a =? 0 then b else
    if b =? 0 then a else
      if orb (a <? 0) (b <? 0) then -1 else
        if inf <=? (a + b) then inf else a + b.

Lemma careful_add_id:
  forall a, careful_add a 0 = a.
Proof.
  intros. unfold careful_add. simpl.
  destruct (a =? 0) eqn:?; trivial.
  rewrite Z.eqb_eq in Heqb. omega.
Qed.

Lemma careful_add_comm:
  forall a b, careful_add a b = careful_add b a.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0) eqn:?; destruct (b =? 0) eqn:?; trivial.
  1: try rewrite Z.eqb_eq in *; omega.
  destruct (a <? 0) eqn:?; destruct (b <? 0) eqn:?;
           simpl; trivial.
  destruct (inf <=? a + b) eqn:?;
           rewrite Z.add_comm in Heqb4; rewrite Heqb4; omega.
Qed.

Lemma careful_add_assoc:
  forall a b c,
    careful_add a (careful_add b c) =
    careful_add (careful_add a b) c.
Proof.
  intros.
  unfold careful_add.
  destruct (a =? 0) eqn:?;
           destruct (b =? 0) eqn:?;
           destruct (c =? 0) eqn:?;
           try rewrite Heqb0; try rewrite Heqb1;
    try rewrite Heqb2; trivial.
  - destruct (a <? 0) eqn:?;
             destruct (b <? 0) eqn:?;
             destruct (c <? 0) eqn:?; simpl; trivial.
    + destruct (inf <=? a + b) eqn:?.
      1: rewrite if_false_bool; trivial.
      rewrite if_false_bool; trivial.
      rewrite Z.eqb_neq, Z.ltb_nlt in *; omega.
    + destruct (inf <=? a + b) eqn:?.
      1: rewrite if_false_bool; trivial.
      destruct (a + b =? 0) eqn:?; trivial.
      rewrite Z.eqb_eq in *; omega.
  - destruct (a <? 0) eqn:?;
             destruct (b <? 0) eqn:?;
             destruct (c <? 0) eqn:?; simpl; trivial.
    + rewrite if_false_bool; trivial.
      destruct (inf <=? b + c) eqn:?.
      * compute; trivial.
      * rewrite Z.eqb_neq, Z.ltb_nlt in *; omega.
    + destruct (inf <=? a + b) eqn:?.
      * compute; trivial.
      * rewrite if_false_bool.
        2: rewrite Z.eqb_neq, Z.ltb_nlt in *; omega.
        rewrite Bool.orb_true_r; trivial.
    + rewrite Z.eqb_neq, Z.ltb_ge in *.
      rewrite if_false_bool.
      2: { destruct (inf <=? b + c).
           - compute; trivial.
           - rewrite Z.eqb_neq; omega. }
      destruct (inf <=? b + c) eqn:?.
      * rewrite if_false_bool by (compute; trivial).
        rewrite if_true_bool.
        2: rewrite Z.leb_le; omega.
        rewrite if_false_bool.
        2: { destruct (inf <=? a + b) eqn:?.
             - compute; trivial.
             - rewrite Z.eqb_neq; omega. }
        rewrite Bool.orb_false_r.
        rewrite if_false_bool.
        2: { destruct (inf <=? a + b) eqn:?.
             - compute; trivial.
             - rewrite Z.ltb_nlt; omega. }
        destruct (inf <=? a + b) eqn:?.
        -- rewrite if_true_bool; trivial.
           rewrite Z.leb_le; omega. 
        -- rewrite if_true_bool; trivial.
           rewrite Z.leb_le in *; omega. 
      * rewrite if_false_bool by (rewrite Z.ltb_nlt; omega).
        rewrite Z.add_assoc.
        destruct (inf <=? a + b + c) eqn:?.
        -- rewrite if_false_bool.
           2:  { destruct (inf <=? a + b) eqn:?.
                 - compute; trivial.
                 - rewrite Z.eqb_neq; omega. }
           rewrite Bool.orb_false_r.
           rewrite if_false_bool.
           2:  { destruct (inf <=? a + b) eqn:?.
                 - compute; trivial.
                 - rewrite Z.ltb_nlt; omega. }
           rewrite if_true_bool; trivial.
           destruct (inf <=? a + b) eqn:?; trivial.
           rewrite Z.leb_le. omega.
        -- rewrite if_false_bool.
           rewrite if_false_bool.
           rewrite if_false_bool.
           rewrite if_false_bool; trivial.
           all: rewrite Z.leb_gt in *.
           1: omega.
           1: { rewrite if_false_bool; trivial.
                rewrite Z.leb_gt in *; omega. }
           1: { rewrite Bool.orb_false_r.
                rewrite if_false_bool.
                rewrite Z.ltb_nlt; omega.
                rewrite Z.leb_gt; omega. }
           destruct (inf <=? a + b) eqn:?.
           ++ compute; trivial.
           ++ rewrite Z.eqb_neq; omega.
Qed.

Lemma careful_add_clean:
  forall a b,
    0 <= a -> 0 <= b -> a + b < inf ->
    careful_add a b = a + b.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0) eqn:?;
           destruct (b =? 0) eqn:?;
           try rewrite Z.eqb_eq in *;
    try rewrite Z.eqb_neq in *; subst; try omega.
  rewrite if_false_bool.
  rewrite if_false_bool; trivial.
  rewrite Z.leb_gt; trivial.
  rewrite Bool.orb_false_iff.
  split; rewrite Z.ltb_nlt; omega.
Qed.

Lemma careful_add_pos:
  forall a b,
    0 <= a -> 0 <= b -> 0 <= careful_add a b.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0); destruct (b =? 0); trivial.
  rewrite if_false_bool.
  2: { rewrite Bool.orb_false_iff; split;
       rewrite Z.ltb_nlt; omega. }
  destruct (inf <=? a + b); [now compute| omega].
Qed.

Lemma careful_add_inf:
  forall a,
    0 <= a -> careful_add a inf = inf.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0); trivial.
  rewrite if_false_bool by (now compute).
  rewrite if_false_bool.
  2: { rewrite Bool.orb_false_iff; split;
       rewrite Z.ltb_nlt; [omega | compute; inversion 1]. }
  rewrite if_true_bool; trivial. rewrite Z.leb_le. omega.
Qed.

Lemma careful_add_inf_clean:
  forall a b,
    0 <= a -> 0 <= b ->
    careful_add a b < inf ->
    a + b < inf.
Proof.
  intros.
  unfold careful_add in H1.
  destruct (a =? 0) eqn:?.
  - rewrite Z.eqb_eq in *. omega.
  - destruct (b =? 0) eqn:?.
    + rewrite Z.eqb_eq in *. omega.
    + rewrite Z.eqb_neq in *.
      destruct (a <? 0) eqn:?; destruct (b <? 0) eqn:?;
               try rewrite Z.ltb_lt in *; try omega.
      simpl in H1.
      destruct (inf <=? a + b); [inversion H1 | trivial].
Qed.

Definition path_cost (g: LGraph) (path : @path VType EType) :=
  fold_left careful_add (map (elabel g) (snd path)) 0.

Definition inrange_graph grph_contents :=
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
    Znth i (Znth j grph_contents) = inf.

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
  red in H, H1.
  rewrite H1 in H0; destruct H0. 
  rewrite H in H0, H2.
  rewrite Znth_map, nat_inc_list_i.
  unfold vert_rep. rewrite Znth_map.
  rewrite Znth_map. rewrite nat_inc_list_i.
  reflexivity.
  3: rewrite Zlength_map.
  2, 3, 5: rewrite nat_inc_list_Zlength.
  all: rewrite Z2Nat.id; omega.
Qed.

