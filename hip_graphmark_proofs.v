Require Import ZArith.
Require Import hip_graphmark.
Require Import graph.
Require Import List.

Module GraphMark <: Mgraphmark.
  Definition formula : Type := Prop.
  Definition valid (F : formula) : Prop := F.

  Definition and (F1 F2 : formula) : formula := F1 /\ F2.
  Definition imp (F1 F2 : formula) : formula := F1 -> F2.
  Definition not (F : formula) : formula := ~F.
  
  Definition node : Type := Z.
  Definition null_node : node := 0%Z.
  
  Definition eq (n1 n2 : node) : formula := n1 = n2.
  Definition neq (z1 z2 : Z) : formula := z1 <> z2.
  
  Instance node_eq_dec : EqDec node.
  Proof. constructor. unfold node. apply Z_eq_dec. Qed.
  
  (* This needs to be though through some more... *)
  Definition valid_node (n : node) : Prop := n <> null_node.

  Definition A : Type := @PreGraph node node node_eq_dec valid_node.
  
  Definition lookup (g : A) (n : node) (d : Z) (l r : node) : formula :=
    @node_label _ _ _ _ g n = d /\
    @edge_func _ _ _ _ g n = l :: r :: nil.
  
  Definition update (g : A) (n : node) (d : Z) (l r : node) (g' : A) : formula :=
    (forall n', n <> n' -> 
      (@node_label _ _ _ _ g n' = @node_label _ _ _ _ g' n' /\
       @edge_func _ _ _ _ g n' = @edge_func _ _ _ _ g' n')) /\
    @node_label _ _ _ _ g' n = d /\
    @edge_func _ _ _ _ g' n = l :: r :: nil.
  
  Definition marked (g : A) (d : Z) : formula :=
    d = 1%Z.
  
  Lemma lookup_update_mark1: forall g n d l r g',
    lookup g n d l r ->
    update g n (1%Z) l r g' ->
    mark1 _ _ _ _ (marked g') g n g'.
  Proof.
    intros. split. 
    red. intros. split. tauto.
    destruct H as [? ?]. destruct H0 as [? [? ?]].
    case (t_eq_dec v n). intros. subst n. unfold node in *. rewrite H1,H3. apply eq_as_set_refl.
    intro. destruct (H0 v). auto.
    unfold node in *. rewrite H5. apply eq_as_set_refl.
    split. red. admit. (* need valid proof *)
    split. red. red. 
    destruct H0 as [? [? ?]]. apply H1.
    intros. destruct H0 as [? [? ?]].
    destruct (H0 n'); auto.
  Qed.
 rewrite H1. reflexivity.

 trivial.

 unfold node_label. hnf. 
 apply sublist_refl.
    

 trivial.
    spec H0 v.

; auto.

    unfold lookup in H. destruct H. rewrite H1.
    destruct H0. destruct H2.

 intro.

apply sublist_refl. intro. 
    split.  intro. red. red. 

(* SL, empty for now *) 
  Definition star (F1 F2 : formula) : formula := True.
  Definition mwand (F1 F2 : formula) : formula := True.
  Definition union (F1 F2 : formula) : formula := True.
  Definition ptto_node (n : node) (d : Z) (l r : node) : formula := True.
  Definition graph (n : node) (g : A) : formula := True.
(* end SL *)
End GraphMark.


Module Type Mgraphmark.
  Parameter mark : A -> node -> A -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Axiom axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G2 l G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_2 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G2 r G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_3 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G1 l G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_4 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G1 r G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_5 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 r G2) (mark G2 l G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_6 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 l G2) (mark G2 r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_7 : forall v G x G1 y v1 l r, valid (imp (and (mark G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (lookup G1 y v1 l r)))).
  Axiom axiom_8 : forall G x G1, valid (imp (mark G x G1) (and (subset_reach G x G1) (eq_notreach G x G1))).
  Axiom axiom_9 : forall l r x G, valid (imp (lookup G x 1 l r) (mark G x G)).
  Axiom axiom_10 : forall G, valid (mark G null_node G).
  Axiom lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_pttoupdate : forall v1 G1 G x v l r, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (lookup G x v l r)) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
End Mgraphmark.
