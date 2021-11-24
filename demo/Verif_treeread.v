(** * CertiGraph Demo: Traversing Imperative Structures *)
(** This tutorial written by Shengyi Wang, Kathrin Stark, Andrew W. Appel *)

(**   Separation Logic is based on the separating conjunction P*Q
   in which assertions P and Q describe disjoint parts of memory,
  but _graphs_  (directed cyclic graphs, directed acyclic graphs)
  are pointer data structures in which the subgraphs reachable
  from the different out-edges of a node may _overlap_ -- they
  are not disjoint.
 
  The purpose of the CertiGraph library is to allow reasoning about
  graphs in VST -- a separation-logic-based proof system --
  even though graphs require _sharing_ and not pure separation.

  This demo has three parts:
   0.   Traversing a tree-as-tree, using separation logic.  That's in
            Module TreeModel of this file.            But what
            if the tree is represented in the C program's memory with
            shared pointers to subtrees?  That is, what if the tree is
            really represented as a DAG?  The same treeread.c program
            will still work, but the tree-as-tree proof is inapplicable,
            because its precondition is violated.
   1.  Traversing a tree-as-DAG, using the _principles_ of CertiGraph,
           but without actually using CertiGraph.  That's in
            Module SimplifiedModel of this file.  This proof works
            (its precondition is satisfied) whether or not there is 
            structure-sharing in the representation of the tree.
   2.  Traversing the tree-as-DAG, using those same principles, but
           this time using the CertiGraph library.  That's in 
            Module CertiGraphModel of this file. 
   3.  Depth-first search of a DAG or a cyclic graph, using CertiGraph.
           That's in a different directory, ../mark/verif_mark_bi.v.

Consider the following C program:

<<
/* treeread.c */
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

We will show two similar verifications of this program in VST,
in modules SimplifiedModel and CertiGraphModel respectively.

Both verifications need to import VST itself as well as 
  treeread.v which is the AST of the treeread program.
*)

Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import TR.treeread.

(* The next two lines are standard VST boilerplate, useful
  in both verifications *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* We continue with definitions that will be useful in both
  versions of the verification *)

Definition t_struct_tree := Tstruct _tree noattr.

(** The Coq representation of a tree-node is a nested tuple of three values. *)
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

(** ** Tree model *)

Module TreeModel.

(* A standard proof in VST's natural style.  The reader is expected
   to be familiar with this kind of proof, so we don't explain much here.
*)

Fixpoint tree_rep (t: tree) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T v a b =>
    EX pa:val, EX pb:val,
    data_at Ews t_struct_tree (Vint v,(pa,pb)) p * tree_rep a pa * tree_rep b pb
 end.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
  intros.
  destruct t; simpl; Intros; try Intros x y; subst; auto with valid_pointer.
Qed.
#[local] Hint Resolve tree_rep_valid_pointer : valid_pointer.

Lemma tree_rep_local_facts:
  forall t p, tree_rep t p |-- !! (is_pointer_or_null p  /\ (p=nullval <-> t=E)).
Proof.
  intros.
  destruct t; simpl; Intros; try Intros x y; subst; entailer!.
  + split; auto.
  + destruct H as [? _].
     split; intro. subst. contradiction H. inversion H1. 
Qed.
#[local] Hint Resolve tree_rep_local_facts : saturate_local.

Definition sum_spec :=
 DECLARE _sum
 WITH t: tree, p: val
  PRE  [ tptr t_struct_tree ]
       PROP()
       PARAMS (p)
       SEP (tree_rep t p)
  POST [ tuint ]
    PROP()
    LOCAL(temp ret_temp (Vint (sum t)))
    SEP (tree_rep t p).

Definition Gprog : funspecs := [ sum_spec ].

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward_if.
  - (* then clause *)
   forward. entailer!. rewrite (proj1 H0) by auto. reflexivity.
  - (* else clause *)
   destruct t.
   + assert_PROP False. entailer!. rewrite (proj2 H0) in H by auto. contradiction. contradiction. 
   + 
   unfold tree_rep; fold tree_rep.
   Intros pa pb.
   forward. forward_call. forward. forward_call. forward. forward.
   entailer!.
   * simpl. rewrite Int.add_assoc. auto.
   * unfold tree_rep at 3; fold tree_rep.
      Exists pa pb. cancel.
Qed.

(* That's all simple enough.  But what if the logical tree is,
    T(1,T(2,E,E),T(3,T(2,E,E),T(2,E,E)))
    where all three occurrences of T(2,E,E) are represented by
    the same address in memory?   Then the program will 
    still compute sum(p)=1+2+3+2+2=10.   But we can't use this
    specification TreeModel.sum_spec to prove it, because
    that data structure does not satisfy the separation requirements
    implied by our tree_rep specification.  So this data structure
    does not satisfy the precondition of sum_spec.

    The next two verifications of this same program,  treeread.c,
    show how to prove it correct for more general,  graph-based
    precondition.
*)

End TreeModel.

(** ** Simplified model *)

(**  We start with a simplified model which highlights the general localization tactics.
    It uses the same principles and techniques as CertiGraph, but we 
    re-derive them so that the reader can see the principles.
   Note!  CertiGraph has many other powerful features that are not
   demonstrated by this example.
*)

Module SimplifiedModel.

(** In this simplified model, a graph is a list of nodes, where each node
   has an _address_ (of type [val]) and _contents_ (the three fields of struct_tree,
   that is, number and two out-edges.  The out-edges are addresses of the
   successor nodes. *)
Definition graph := list (val * reptype t_struct_tree).

(** [graph_rep] is a separation-logic predicate that defines the embedding
    of a graph in memory.  It's very simple, just the interated separating 
     conjunction of all the nodes. *)
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

(* We can demonstrate using the tree-in-DAG example above: a three-node DAG
   that represents a five-node tree. *)

Module ExampleGraph.
Definition p1 := Vptr 1%positive Ptrofs.zero.
Definition p2 := Vptr 2%positive Ptrofs.zero.
Definition p3 := Vptr 3%positive Ptrofs.zero.

Definition graph1 : graph  := [
        (p1, (Vint (Int.repr 2), (nullval,nullval))); 
        (p2, (Vint (Int.repr 3), (p1,p1)));
        (p3, (Vint (Int.repr 1), (p1,p2))) ].

Definition tree1 : tree := 
   T (Int.repr 1) (T (Int.repr 2) E E)
                        (T (Int.repr 3) (T (Int.repr 2) E E) (T (Int.repr 2) E E)).

Lemma tree1_in_graph1:  tree_in_graph graph1 tree1 p3.
Proof.
eapply TIG_T; [repeat ((left; reflexivity) || right)| | ].
eapply TIG_T; [repeat ((left; reflexivity) || right)| | ].
apply TIG_E.
apply TIG_E.
eapply TIG_T; [repeat ((left; reflexivity) || right)| | ].
eapply TIG_T; [repeat ((left; reflexivity) || right)| | ].
apply TIG_E.
apply TIG_E.
eapply TIG_T; [repeat ((left; reflexivity) || right)| | ].
apply TIG_E.
apply TIG_E.
Qed.

End ExampleGraph.


(** The VST specification of [sum] contains of a spatial and a propositional part:
 - In the spatial part (SEP), we declare the spatial graph representation of [g].
 - In the propositional part (PROP), we state that graph [g] contains a 
                 representation of tree [t] at position [p].
  As the [sum] function recursively traverses the tree-in-DAG, the tree [t] and
  focused node [p] vary with the recursion, but the graph [g] stays the same, 
  and the SEP clause continues to hold the _entire_ graph.
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

(** As the [sum] function traverses the tree-in-DAG, to access the fields of the
   "current root node" it will need to _separate_ that node from the rest of the
   graph.  We use the word _separate_ in the sense of "separation logic".

    The CertiGraph library provides lemmas and typeclasses to assist in
    focusing on nodes.  But in this Module SimplifiedModel we show how
    these are constructed.
*)

(** Lemma:  if node p (with fields n) is in graph g, then (data_at n p) can be 
   separated from the rest of the graph.  "The rest" is described as usual in
   separation logic -- by magic wand. *)
Lemma graph_rep_In (g : graph) (n: reptype t_struct_tree) p:
  In (p, n) g -> 
  graph_rep g = (data_at Ews t_struct_tree n p * (data_at Ews t_struct_tree n p -* graph_rep g))%logic.
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

(**  As usual in VST, when you define a new SEP predicate, as we have done
    here for [graph_rep], you should prove lemmas to add to the Hint databases
    for valid_pointer and saturate_local.
*)

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
#[local] Hint Resolve graph_rep_In_valid valid_pointer_tree : valid_pointer.

Lemma graph_rep_local_facts g:
graph_rep g |-- !!( (forall p v, In (p,v) g -> isptr p) /\
                              (forall t p, tree_in_graph g t p ->  is_pointer_or_null p)).
Proof.
rewrite prop_and_mpred.
apply andp_right.
-
   rewrite prop_forall; apply allp_right; intros p.
   rewrite prop_forall; apply allp_right; intros v.
   rewrite prop_impl.
   apply imp_andp_adjoint.
   Intros.
   rewrite  (graph_rep_In _ _ _ H).  entailer!.
-
  rewrite prop_forall. apply allp_right. intros t.
  rewrite prop_forall. apply allp_right. intros v.
  rewrite prop_impl. apply imp_andp_adjoint. entailer.
  induction H.
  + entailer!.
  + rewrite  (graph_rep_In _ _ _ H).  entailer!.
Qed.
#[local] Hint Resolve graph_rep_local_facts : saturate_local.

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
  eauto with valid_pointer.
  - subst. sep_apply (tree_in_graph_null _ _ H).
    forward.
  - sep_apply (tree_in_graph_nonnull _ _ _ H0 H).
    Intros pl pr n tl tr. subst.

    Fail forward.  
   (** Can't do [forward] because node at address p is not isolated
        from the (graph_rep g), into its own SEP conjunct. So let's do that now. *)

    assert_PROP (is_pointer_or_null pl). { entailer!. eauto. }
    assert_PROP (is_pointer_or_null pr). { entailer!. eauto. }

    (** Here, the localization tactic is used to single out the representation of one node. *)
    localize [data_at Ews t_struct_tree (Vint n, (pl, pr)) p].
    (** The [FRZR RamL RamG] in the SEP clause now is basically a magic wand
         lifted up to _lists_ of conjuncts,   (RamL -* RamG).  *)
    (* Uncomment these lines to see what is in the freezer.
    unfold abbreviate in RamL. 
               (* RamL := [data_at Ews t_struct_tree (Vint n, (pl, pr))  p]*)
    unfold abbreviate in RamG. 
               (* RamG := [graph_rep g]  *)
   *)
    (** So therefore, the SEP clause has the localized [data_at], and a magic
        wand that says, if you put that data_at back in, you'll rebuild [graph_rep g].

     The point of this is that, with the [data_at] now in the SEP clause,
     we can go forward through [ _t->_left ].   *)
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

(** We import the basic definitions of graphs, including PreGraph, LabeledGraph,
     and GeneralGraph. *)
Require Import CertiGraph.graph.graph_model.

(**  We import spatial definitions which connect the mathematical definitions of
    graphs and their spatial representations, such as "full_vertices_at" below. *)
Require Import CertiGraph.msl_application.Graph.

Module CertiGraphModel.

(** With the help of the CertiGraph library, we can treat the data in
    the heap as a graph and reason about it. *)

(** Every graph must have a type called PreGraph. *)

Print PreGraph.

(** To declare a PreGraph, we need to provide the types of the vertices and
     edges, also with the proofs which say their equalities are decidable.

    In our case, we can simply define val in VST as the vertex type. The 
    definition of the edge type could be (val * LR) where LR is an inductive
    type indicating left or right, because what we have is a binary tree here. *)

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

(** The following two types are the same, because V_EqDec and E_EqDec
     are automatically inferred typeclass instances: *)
Check (PreGraph VType EType).
Check (@PreGraph VType EType V_EqDec E_EqDec).

(**  Any instance of this Type will have four components:
     two predicates (vvalid and evalid) and two functions (src and dst). 
     Please refer to the section 4.1 in [1] for more information. *)

(** PreGraph just describes the topological layout of a graph. The  graphs used
    in concrete programs usually carry more information. CertiGraph provides
    LabeledGraph, which allows us to represent any type of "labels" attached to
    vertices or edges, or even the whole graph.

    In this case, each node carries an unsigned integer which can be represented
    by type int. We specify the unit type for labels of edges and the whole graph. *)

Definition graph: Type := (LabeledGraph VType EType int unit unit).
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

(** Even after defining the LabeledGraph, there are still too many possibilities for
    our graphs. The graph in our case is very special: there is a binary tree 
    embedded in it. So we can define a predicate to show this: *)

Inductive tree_in_graph (g: graph) : tree -> val -> Prop :=
| TIG_E: tree_in_graph g E nullval (** The empty tree corresponds to the null value. *)
| TIG_T: (** Definition of an internal node of the tree *)
  forall (p : val) tl tr,
    vvalid g p ->
    tree_in_graph g tl (dst g (p, L)) ->
    tree_in_graph g tr (dst g (p, R)) ->
    tree_in_graph g (T (vlabel g p) tl tr) p.

(** The CertiGraph library actually provides another type called
    GeneralGraph, which contains a LabeledGraph g and a predicate
    describing the properties g must obey. In this case, we can define
    the GeneralGraph by putting the graph and tree_in_graph
    together. For simplicity, we omit this definition. We put
    tree_in_graph in the precondition instead. For more information
    about GeneralGraph, please refer to section 4.1 and 4.2 in [1]. *)

(** So far, all these definitions are purely mathematical. The next step is
    connecting the pure mathematical graph and its spatial representation. 
    CertiGraph provides some helper definitions for such connections. 
    All we need to do is to implement some classes. *)

(** PGBA_VST is just a wrapper for decidable equality of vertices and edges *)

#[local] Instance PGBA_VST: PointwiseGraphBasicAssum val (val * LR).
Proof. constructor; apply _. Defined.

(** The following two classes together form the spatial representation of a
    single vertex.  The first maps a vertex to an intermediate type, the second
    maps the intermediate value to the spatial predicate. *)

#[local] Instance PGC_VST: PointwiseGraphConstructor val (val * LR) int unit unit (int * val * val) unit.
Proof. constructor. exact (fun g v => (vlabel g v, dst g (v, L), dst g (v, R))). exact (fun _ _ => tt). Defined.

#[local] Instance PGP_VST: PointwiseGraphPred VType EType (int * val * val) unit mpred.
Proof.
  constructor. exact (fun p dlr => match dlr with | (d, l, r) => data_at Ews t_struct_tree (Vint d, (l, r)) p end).
  exact (fun _ _ => emp).
Defined.

(** This is just a wrapper for various VST classes.  We will be using the *)
#[local] Instance PGA_VST: PointwiseGraphAssum PGP_VST.
Proof. refine (Build_PointwiseGraphAssum _ _ _ _ _ _ _ _ _ _ _). Defined.

(** Now we can define the spatial representation of our  graph. Like 
    SimplifiedModel.graph_rep, it is the iterated separating conjunction of
    all representations of (valid) vertices.  See also: section 5 of [1]. *)

Definition graph_rep (g: graph) := full_vertices_at g.

(** The following 4 lines coerce the type [graph] to the type [PointwiseGraph],
    so we can use terms like [vgamma g p] without writing an explicit
    conversion function. *)

Definition SGraph := PointwiseGraph val (val * LR) (int * val * val) unit.
Definition graph_SGraph (G: graph): SGraph := Graph_PointwiseGraph G.
Local Coercion graph_SGraph: graph >-> SGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.

(** This funspec for [_sum] is just like SimplifiedModel.sum_spec, but
    with CertiGraph-derived definitions for graph, graph_rep, etc. *)
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

(** Let's review:
  - graph   is   [LabeledGraph VType EType int unit unit],  that is, a graph
        with vertices of type [val], edges of type (val*LR), and node-labels of type [int].
  - tree is  the same inductive type that we used in SimplifiedModel.
  - tree_in_graph  is an inductive predicate that relates trees to graphs.
  - graph_rep is  [full_vertices_at], a CertiGraph predicate that's the 
                separating conjunction of all the valid vertices of the graph. *)

Print SimplifiedModel.graph. (*
     = list (val * reptype t_struct_tree) : Type *)

Print graph. (* 
     = LabeledGraph VType EType int unit unit : Type *)
Print LabeledGraph.  (* . . . lots of stuff *)
(** Our graph type here has a lot more information than SimplifiedModel.graph,
  but from it we can still derive the list of nodes with their node-representations,
  the [graph_rep].  *)

Definition Gprog : funspecs := [ sum_spec ].

(** Just like in the SimpleModel proof, we need a graph_rep_In lemma.
   Here we use vertices_at_ramif_1_stable  to prove it. *)

Check vertices_at_ramif_1_stable. (*
     : forall   (g : PointwiseGraph val (val * LR) (int * val * val) unit)
         (P : val -> Prop) (x : val) (d : int * val * val),
       vgamma g x = d ->
       P x ->
       vertices_at P g |-- vertex_at x d * (vertex_at x d -* vertices_at P g)
*)

Lemma graph_rep_In (g : graph) p:
  vvalid g p -> graph_rep g = (vertex_at p (vgamma g p) * (vertex_at p (vgamma g p) -* graph_rep g))%logic.
Proof.
  intros. apply pred_ext.
  - apply (@vertices_at_ramif_1_stable _ _ _ _ PGBA_VST mpred PGP_VST PGA_VST); auto.
  - apply modus_ponens_wand.
Qed.

(** The remaining proofs are almost the same as in section SimplifiedModel above. *)

(** As usual in any VST proof, if you define a new mpred such as graph_rep,
   it's useful to define Hints for valid_pointer and saturate_local Hint databases. *)
Lemma valid_pointer_tree g t p:
  tree_in_graph g t p -> graph_rep g |-- valid_pointer p.
Proof.
  intros. inversion H; subst.
  - entailer !.
  - rewrite (graph_rep_In g p); auto. simpl vertex_at. auto with valid_pointer.
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
  - sep_apply (graph_rep_In _ _ H0). simpl vertex_at. entailer!.
Qed.

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward_if.
  eauto with valid_pointer.
  - subst. sep_apply (tree_in_graph_null _ _ H). forward.
  - inversion H; subst. now exfalso.
    assert_PROP (is_pointer_or_null (dst g (p, L))). { entailer!. eauto. }
    assert_PROP (is_pointer_or_null (dst g (p, R))). { entailer!. eauto. }

    (** Here, the localization tactic is used to single out the
        representation of one node. For more details about this
        localize/unlocalize pair, please refer to section 7.1 of  [1]. *)
    localize [vertex_at p (vgamma g p)].
    (** FRZR RamL RamG is basically a magic wand,   RamL -* RamG. *)

    (* Uncomment these lines to see what is in the freezer.
    unfold abbreviate in RamL. 
               (* RamL := [vertex_at p (vgamma (graph_SGraph g) p)] *)
    unfold abbreviate in RamG. 
               (* RamG := [graph_rep g]  *)
   *)
    (** So therefore, the SEP clause has the localized [vertex_at], and a magic
        wand that says, if you put that data_at back in, you'll rebuild [graph_rep g]. *)
    simpl vertex_at.  (* unfolds vertex_at into a data_at, giving access to _t->_left *)
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

(** For a more subtle example, please refer to ../mark/verif_mark_bi.v
    which verifies a graph-marking program. *)

(** Related Work:

[1] Certifying Graph-Manipulating C Programs via Localizations within Data Structures,
    by Shengyi Wang, Qinxiang Cao, Anshuman Mohan, and Aquinas Hobor,
    OOPSLA 2019, https://dl.acm.org/doi/10.1145/3360597

*)
