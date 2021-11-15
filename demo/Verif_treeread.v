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

#[local] Hint Resolve valid_pointer_tree : valid_pointer.

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

#[local] Hint Resolve treerep_local_facts : saturate_local.

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

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.msl_application.Graph.

Section CertiGraphModel.

(* With the help of the CertiGraph library, we can treat the data in
   the heap as a graph and reason about it. *)

(* Every graph must have a type called PreGraph. *)

Print PreGraph.

(* To declare a PreGraph, we need to provide the types of the vertices
   and edges, also with the proofs which say their equliaties are
   decidable.

   In our case, we can simply define val in VST as the vertex
   type. The definition of the edge type could be (val * LR) where LR
   is an inductive type indicating left or right, because what we have
   is a binary tree here. *)

Definition VType : Type := val.

Inductive LR := L | R.

Definition EType : Type := val * LR.

#[local] Instance V_EqDec: EquivDec.EqDec VType eq.
Proof. repeat intro. apply Val.eq. Defined.

#[local] Instance E_EqDec: EquivDec.EqDec EType eq.
Proof.
  intros [x lx] [y ly]. destruct (Val.eq x y).
  - subst. destruct lx, ly; [left | right ..| left]; easy.
  - right. destruct lx, ly; congruence.
Defined.

(* V_EqDec and E_EqDec would be maximally inserted. *)

Check (PreGraph VType EType).

(* When we declared a type like above, we assume we have all the four
   components of PreGraph: two predicates (vvalid and evalid) and two
   functions (src and dst). Please refer to the section 4.1 in [1] for
   more information. *)

(* PreGraph just describes the topological layout of a graph. The
   graph used in concrete programs usually carry more information. The
   CertiGraph library provides LabeledGraph, which allows us to
   represent any type of "labels" attached to vertices or/and edges,
   or even the whole graph. *)

(* In this case, each node carries an unsigned integer which can be
   represented by type int. We specify the unit type for labels of edges
   and the whole graph. *)

Definition graph: Type := (LabeledGraph VType EType int unit unit).

(* Even after defining the LabeledGraph, there are still too many
   possibilities for our graphs. The graph in our case is very
   special: it is a binary tree. So we can define a predicate to show
   this: *)

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Inductive tree_in_graph (g: graph) : tree -> val -> Prop :=
| TIG_E: tree_in_graph g E nullval (** The empty tree corresponds to the null value. *)
| TIG_T: (** Definition of a leaf *)
  forall (p : val) tl tr,
    vvalid g p ->
    tree_in_graph g tl (dst g (p, L)) ->
    tree_in_graph g tr (dst g (p, R)) ->
    tree_in_graph g (T (vlabel g p) tl tr) p.

(* So far, all these definitions are pure mathematical. The next step
   is connecting the pure mathematical graph and its spatial
   representation. The CertiGraph library provides some helper
   definitions for such connections. All we need to do is to
   implementing some classes. *)

(* This is just a wrapper for the decidable equality of vertices and edges *)

#[local] Instance PGBA_VST: PointwiseGraphBasicAssum val (val * LR).
Proof. constructor; apply _. Defined.

(* The following two classes together form the spatial representation
   of a single vertex, the first maps a vertex to a intermediate type,
   the second maps the intermediate value to the spatial predicate. *)

#[local] Instance PGC_VST: PointwiseGraphConstructor val (val * LR) int unit unit (int * val * val) unit.
Proof. constructor. exact (fun g v => (vlabel g v, dst g (v, L), dst g (v, R))). exact (fun _ _ => tt). Defined.

#[local] Instance PGP_VST: PointwiseGraphPred VType EType (int * val * val) unit mpred.
Proof.
  constructor. exact (fun p dlr => match dlr with | (d, l, r) => data_at Ews t_struct_tree (Vint d, (l, r)) p end).
  exact (fun _ _ => emp).
Defined.

(* This is just a wrapper for various VST classes *)

#[local] Instance PGA_VST: PointwiseGraphAssum PGP_VST.
Proof. refine (Build_PointwiseGraphAssum _ _ _ _ _ _ _ _ _ _ _). Defined.

(* Now we can define the spatial representation of our
   graph. Basically it iteratively separates all valid vertex
   representations. *)

Definition graph_rep (g: graph) := full_vertices_at g.

(* The following 4 lines coerce the type graph to the type
   PointwiseGraph, so that we can use terms like "vgamma g p" without
   writing conversion function explicitly. *)

Definition SGraph := PointwiseGraph val (val * LR) (int * val * val) unit.
Definition graph_SGraph (G: graph): SGraph := Graph_PointwiseGraph G.
Local Coercion graph_SGraph: graph >-> SGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.

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

(* Here we use the lemma vertices_at_ramif_1_stable the CertiGraph
   library to establish graph_rep_In. *)

Lemma graph_rep_In (g : graph) p:
  vvalid g p -> graph_rep g = (vertex_at p (vgamma g p) * (vertex_at p (vgamma g p) -* graph_rep g))%logic.
Proof.
  intros. apply pred_ext.
  - apply (@vertices_at_ramif_1_stable _ _ _ _ PGBA_VST mpred PGP_VST PGA_VST); auto.
  - sep_apply modus_ponens_wand. entailer.
Qed.

(* The rest proofs are almost the same. *)

Lemma valid_pointer_tree g t p:
  tree_in_graph g t p -> graph_rep g |-- valid_pointer p.
Proof.
  intros. inversion H; subst.
  - entailer !.
  - rewrite (graph_rep_In g p); auto. simpl vertex_at. entailer !.
Qed.

#[local] Hint Resolve valid_pointer_tree : valid_pointer.

Lemma treerep_local_facts g:
  graph_rep g |-- !!(forall t p, tree_in_graph g t p ->  is_pointer_or_null p).
Proof.
  do 2 (rewrite prop_forall; apply allp_right; intros).
  rewrite prop_impl. apply imp_andp_adjoint. entailer.
  inversion H.
  - entailer!.
  - entailer. rewrite (graph_rep_In _ _ H0). simpl vertex_at. entailer!.
Qed.

#[local] Hint Resolve treerep_local_facts : saturate_local.

Lemma tree_in_graph_null g t:
  tree_in_graph g t nullval -> graph_rep g |-- !!(t = E).
Proof.
  intros H.
  inversion H; subst.
  - entailer!.
  - sep_apply (graph_rep_In _ _ H0). simpl vertex_at. entailer !.
Qed.

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward_if.
  { sep_apply (valid_pointer_tree _ _ _ H). entailer !. }
  - subst. sep_apply (tree_in_graph_null _ _ H). forward.
  - inversion H; subst. 1: now exfalso.
    assert_PROP (is_pointer_or_null (dst g (p, L))). { entailer!. eauto. }
    assert_PROP (is_pointer_or_null (dst g (p, R))). { entailer!. eauto. }

    (** Here, the localization tactic is used to single out the representation of one node. *)
    localize [vertex_at p (vgamma g p)].
    simpl vertex_at.
    forward.
    (** We can undo the localization. *)
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. }

    forward_call (g, tl, (dst g (p, L))).

    localize [vertex_at p (vgamma g p)].
    simpl vertex_at.
    forward.
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. }

    forward_call (g, tr, (dst g (p, R))).

    localize [vertex_at p (vgamma g p)].
    simpl vertex_at.
    forward.
    unlocalize [graph_rep g].
    { rewrite <- graph_rep_In; auto. }

    forward. entailer!.
    now rewrite Int.add_assoc.
Qed.

End CertiGraphModel.


(** Related Work:

[1] Certifying Graph-Manipulating C Programs via Localizations within Data Structures (OOPSLA 2019)

*)
