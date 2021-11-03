(** * Demo: Traversing Imperative Structures *) 

(** A brief demo on how to use the CertiGraph library.

Consider the following C program: 

<<
#include <stdlib.h>

/* demonstrate traversal of a read-only tree */

struct tree {
  unsigned int n;
  struct tree *left, *right;
};


unsigned int sum (struct tree *t) {
  if (t==NULL)
    return 0;
  else return t->n + sum(t->left) + sum (t->right);
}
>>

*) 

Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import TR.treeread.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.

(** The Coq representation of a tree is a nested tuple of three values. *) 
Compute (reptype t_struct_tree). 

(** ** The Functional Model 

Our functional model contains
-  a data structure of trees, where a tree is either a leaf [E] or a binary node [T n tl tr] with a label [n], left subtree [tl], and right subtree [tr]
- the function [sum] which adds up all labels in a tree.
 *) 
Inductive tree : Type :=
 | E: tree
 | T: int -> tree -> tree -> tree.

Fixpoint sum (t : tree) : int :=
  match t with
  | E => Int.zero
  | T n tl tr => Int.add n (Int.add (sum tl) (sum tr))
  end.


(** ** Simplified model

  We start with a simplified model which highlights the general localization tactics.
*) 

Module SimplifiedModel.

(** In this simplified model, a graph is a list of the addresses and representations of trees. *) 
Definition graph := list (val * reptype t_struct_tree).

(** A graph representation separates all trees. *)
Definition graph_rep (g: graph) : mpred :=
  iter_sepcon (fun p => data_at Ews t_struct_tree (snd p) (fst p)) g.

(** An inductive predicate stating that a tree is present in a graph.
    Note that this is a purely propositional predicate.
 *) 
Inductive tree_in_graph (g: graph) : tree -> val -> Prop :=
| TIG_E: tree_in_graph g E nullval (** The empty tree corresponds to the null value. *) 
| TIG_T: (** Definition of a leaf *)
    forall (p : val) (n : int) tl (pl : val) tr (pr: val),
    In (p, (Vint n, (pl, pr))) g ->
    tree_in_graph g tl pl ->
    tree_in_graph g tr pr ->
    tree_in_graph g (T n tl tr) p.

(** The VST specification of [sum] contains of a spatial and a propositional part: 
 - In the spatial part, we declare the spatial graph representation of [g].
 - In the propositional part, we state that graph [g] contains a representation of tree [t] at position [p].
*) 
Definition sum_spec :=
 DECLARE _sum
 WITH g: graph, t: tree, p: val
  PRE  [ tptr t_struct_tree ]
       PROP(tree_in_graph g t p)
       PARAMS (p)
       SEP (graph_rep g)
  POST [ tuint ]
    PROP()
    LOCAL(temp ret_temp (Vint (sum t)))
    SEP (graph_rep g).

Definition Gprog : funspecs := [ sum_spec ]. 

(** We require several intermediate facts, which will later be provided automatically by the CertiGraph library. *)  

(** Predicate needed for the localization *) 
Lemma graph_rep_In (g : graph) (n: reptype t_struct_tree) p: 
  In (p, n) g -> graph_rep g = (data_at Ews t_struct_tree n p * (data_at Ews t_struct_tree n p -* graph_rep g))%logic. 
Proof.
  intros. apply pred_ext. 
  - induction g; simpl in *. 
    + inversion H. 
    + destruct H as [|]; subst.
      * simpl. entailer!. apply wand_sepcon_adjoint. entailer!. 
      * specialize (IHg H). sep_apply IHg. entailer. cancel.
        rewrite <- wand_sepcon_adjoint.
        cancel. rewrite sepcon_comm. apply modus_ponens_wand. 
  - sep_apply modus_ponens_wand. entailer.
Qed.

(** We will require local facts for  [tree_in_graph]. *)

Lemma graph_rep_In_valid p v g: 
  In (p, v) g -> graph_rep g |-- valid_pointer p. 
Proof.
  intros H. rewrite (graph_rep_In _ _ _ H). entailer!.
Qed.
 
Lemma valid_pointer_tree g t p: 
tree_in_graph g t p -> graph_rep g |-- valid_pointer p. 
Proof. 
  induction 1. 
  - entailer!. 
  - entailer!. eauto using graph_rep_In_valid.
Qed.

Hint Resolve valid_pointer_tree : valid_pointer.

Lemma graph_rep_local_facts p v g: 
  In (p, v) g -> graph_rep g |-- !!(isptr p). 
Proof.
  intros H. rewrite (graph_rep_In _ _ _ H). entailer!.
Qed.

Lemma treerep_local_facts g: 
graph_rep g |-- !!(forall t p, tree_in_graph g t p ->  is_pointer_or_null p). 
Proof.
  rewrite prop_forall. apply allp_right. intros t.
  rewrite prop_forall. apply allp_right. intros v. 
  rewrite prop_impl. apply imp_andp_adjoint. entailer.
  induction H.
   - entailer!.
   - entailer. sep_apply (graph_rep_local_facts p (Vint n, (pl, pr))). entailer!. 
Qed.

Hint Resolve treerep_local_facts : saturate_local.

(** Inversion predicates for tree representations *)
Lemma tree_in_graph_null g t:
  tree_in_graph g t nullval -> graph_rep g |-- !!(t = E). 
Proof.
  intros H. 
  inversion H; subst.
  - entailer!.
  - sep_apply (graph_rep_In _ _ _ H0). entailer!.
Qed.

Lemma tree_in_graph_nonnull: forall g t p,
  p <> nullval -> tree_in_graph g t p ->
  graph_rep g |--
    EX pl pr: val, EX n : int, EX tl tr : tree,
      graph_rep g && !! (In (p, (Vint n, (pl, pr))) g /\ t = T n tl tr /\ tree_in_graph g tl pl /\ tree_in_graph g tr pr). 
Proof.
  intros. inversion H0; subst. 
  - congruence. 
  - Exists pl pr n tl tr. entailer!. 
Qed.


(** *** The main theorem *) 
Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward_if. 
  { sep_apply (valid_pointer_tree _ _ _ H). entailer!. }
  - subst. sep_apply (tree_in_graph_null _ _ H). 
    forward.
  - sep_apply (tree_in_graph_nonnull _ _ _ H0 H).  
    Intros pl pr n tl tr. subst. 

    assert_PROP (is_pointer_or_null pl). { entailer!. eauto. }
    assert_PROP (is_pointer_or_null pr). { entailer!. eauto. }
    
    (** Here, the localization tactic is used to single out the representation of one node. *)                                    
    localize [data_at Ews t_struct_tree (Vint n, (pl, pr)) p].
    (* unfold abbreviate in RamL. 
    unfold abbreviate in RamG. *)
    forward.
    (** We can undo the localization. *) 
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. } 

    forward_call (g, tl, pl). 

    localize [data_at Ews t_struct_tree (Vint n, (pl, pr)) p]. 
    forward.
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. } 

    forward_call (g, tr, pr). 

    localize [data_at Ews t_struct_tree (Vint n, (pl, pr)) p]. 
    forward.
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. } 

    forward. entailer!.
    now rewrite Int.add_assoc.
Qed.

End SimplifiedModel.



(** ** Part 2: In CertiGraph *) 

Require Import CertiGraph. (* TODO *) 

Definition graph : Type := (* TODO *).

Inductive tree_in_graph (g: graph) : tree -> val -> Prop :=
| TIG_E: tree_in_graph g E nullval (** The empty tree corresponds to the null value. *) 
| TIG_T: (** Definition of a leaf *)
    forall (p : val) (n : int) tl (pl : val) tr (pr: val),
(*     graph_has_v (p, (Vint n, (pl, pr))) g ->
       replace with a suitable predicate.
 *)
    tree_in_graph g tl pl ->
    tree_in_graph g tr pr ->
    tree_in_graph g (T n tl tr) p.


(** An inductive predicate corresponding to ... *) 

Definition sum_spec :=
 DECLARE _sum
 WITH g: graph, t: tree, p: val, sh: wshare, x : addr
  PRE  [ tptr t_struct_tree ]
       PROP(tree_in_graph g t p)
       PARAMS (p)
       SEP (graph_rep sh x g)
       (* The term "g" has type "graph" while it is expected to have type "LabeledGraph addr (addr * LR) bool unit unit". *) 
  POST [ tuint ]
    PROP()
    LOCAL(temp ret_temp (Vint (sum t)))
    SEP (graph_rep g).


Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
 (* TODO *) 
Admitted.


(** Related Work: 


*) 
