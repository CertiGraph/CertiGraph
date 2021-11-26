(** *Demo: A Graph-Marking Program *)

(** The following command imports a mark program in Coq form:
<<

struct Node {
  int m;
  struct Node * l;
  struct Node * r;
};

void mark(struct Node * x) {
  struct Node * l, * r;
  int root_mark;
  if (x == 0)
    return;
  root_mark = x -> m;
  if (root_mark == 1)
    return;
  l = x -> l;
  r = x -> r;
  x -> m = 1;
  mark(l);
  mark(r);
}

>>
 *)
Require Import Demo.env_mark_bin.

(** Besides PreGraph, LabeledGraph and GeneralGraph, this module 
    also contains the definition of predicates such as "structurally
    identical". *)
Require Import CertiGraph.graph.graph_model.

(** This module contains the predicate "mark x g1 g2" which says a
    graph g1 is marked to become g2 in some sense, starting from
    vertex x. The name "weak" indicates that it is a weak version,
    which does not require the structure of g2 is the same as g1. *)
Require Import CertiGraph.graph.weak_mark_lemmas.

(** This module contains various spatial definitions which connect the
    mathematical definitions of graphs and their spatial
    representations, such as "reachable_vertices_at" below. *)
Require Import CertiGraph.msl_application.Graph.

(** This module defines the complete mark predicate in our case, which
    requires that g1 and g2 are structurally identical. Some spatial
    lemmas are also proved in it. They are general to any graphs which
    need to be marked. *)
Require Import CertiGraph.msl_application.Graph_Mark.

(** This module specializes the PreGraph, LabeledGraph and
    GeneralGraph we used in this case. It captures the key properties
    of our graph: 1. Every node contains two out edges. 2. The edge
    can points to a special "null" node. 3. The number of vertices and
    edges is finite. *)
Require Import CertiGraph.msl_application.GraphBin.

(** This module combines the two orthogonal definitons to prove the
    spatial lemmas we need in the following proofs. They are essentially
    the specializations of lemmas proved in Graph_Mark and GraphBi. *)
Require Import CertiGraph.msl_application.GraphBin_Mark.
Require Import CertiGraph.floyd_ext.share.

(** This module instantiate classes in modules above to connect VST
    and the CertiGraph library. *)
Require Import Demo.spatial_graph_bin_mark.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

(** The spatial representation of the graph, specialized with instances *)
Notation graph sh x g := 
  (@reachable_vertices_at _ _ _ _ _ _ unit unit _ mpred
        (@SGP pSGG_VST bool unit (sSGG_VST sh)) 
        (SGA_VST sh) x g).

(** The definition of graph. *)
Notation Graph := (@Graph pSGG_VST bool unit unit).
Existing Instances MGS binGraph maGraph finGraph RGF.

(** The key in this spec is the predicate "mark x g g'". This is a
    rather subtle definition:

    mark x g g' := WeakMarkGraph.mark x g g' /\ g ~=~ g'

    Here g ~=~ g' means they are structurally identical.

    WeakMarkGraph.mark root g1 g2 : Prop :=
      let PV := reachable_by g1 root (unmarked g1) in
      (predicate_partialgraph g1 (Complement _ PV)) ~=~
      (predicate_partialgraph g2 (Complement _ PV)) /\
      (forall n, marked g2 n <-> (marked g1 n \/ PV n)). *)

(** The second clause is easy to understand: every node marked in g2
    is either already marked in g1 or is reachable through an unmarked
    path from root.

    The first clause requires the unreachable partial graph of g1 and
    g2 to be structurally identical. It means the program does not touch
    those parts.

    It is not defined naively: every node in g1 is unmarked and
    every node in g2 is marked because what we have is a graph. The
    "root", "left branch" and "right branch" may overlap. When the
    spec is used in the recursive calls, the mark predicate must be
    weak enough to be provable and strong enough to indicate the final
    conclusion. *)

(** Now, you can see that the funspec is quite simple!  All the
     interesting mathematics is within the [mark] relation. *)
Definition mark_spec :=
 DECLARE _mark
  WITH sh: wshare, g: Graph, x: pointer_val
  PRE [tptr (Tstruct _Node noattr)]
          PROP  (weak_valid g x)
          PARAMS (pointer_val_val x)
          GLOBALS ()
          SEP (graph sh x g)
  POST [ Tvoid ]
        EX g': Graph,
        PROP (mark x g g')
        LOCAL ()
        SEP   (graph sh x g').

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := [mark_spec ; main_spec].

Lemma graph_local_facts: forall sh x (g: Graph), weak_valid g x -> @derives mpred Nveric (graph sh x g) (valid_pointer (pointer_val_val x)).
Proof.
  intros. destruct H.
  - simpl in H. subst x. entailer!.
  - eapply derives_trans.
    + apply (@va_reachable_root_stable_ramify pSGG_VST _ _ _ (sSGG_VST sh) g x (vgamma g x)); auto.
    + simpl.
      entailer!.
Qed.

Opaque pSGG_VST sSGG_VST.

Lemma body_mark: semax_body Vprog Gprog f_mark mark_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.
  forward_if.
  - apply denote_tc_test_eq_split. 2: entailer!. apply graph_local_facts; auto.
  - forward.
    (* return. *)
    (** null case*)
    Exists g. entailer!. destruct x. 1: simpl in H; inversion H.
    apply (mark_null_refl g).
  - assert (vvalid g x) as gx_vvalid. {
      destruct H_weak_valid; [| auto].
      unfold is_null_SGBA in H0; simpl in H0; subst x.
      exfalso. apply H. auto.
    } assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i). {
      destruct x. 2: exfalso; apply H; reflexivity. split; simpl; auto.
      exists b, i. reflexivity.
    } destruct H0 as [? [b [i ?]]]. clear H0 H_weak_valid.
    (* root_mark = x -> m; *)
    localize [data_at sh node_type (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)].
    forward.
    unlocalize [graph sh x g].
    1: apply (@root_stable_ramify _ (sSGG_VST sh) g x _ H_GAMMA_g); auto.
    (* if (root_mark == 1) *)
    forward_if.
    + (* return *)
      (** if root is already marked, we return the unchanged graph *)
      forward. Exists g. entailer!.
      eapply (mark_vgamma_true_refl g); eauto.
      clear - H0; destruct d; [auto | inversion H0].
    + assert (d = false) by (destruct d; congruence). subst d.
      (* l = x -> l; *)
      localize [data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r)) (pointer_val_val x)].
      forward. 1: entailer!; destruct l; simpl; auto.
      forward. 1: entailer!; destruct r; simpl; auto.
      (** Now root is marked. *)
      forward.
      (** We even know the graph we get is (Graph_vgen g x true). *)
      unlocalize [graph sh x (Graph_vgen g x true)].
      1: apply (@root_update_ramify _ (sSGG_VST sh) g x _ (false, l, r) (true, l, r)); auto;
      eapply Graph_vgen_vgamma; eauto.
      pose proof Graph_vgen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
      forget (Graph_vgen g x true) as g1.
      assert (weak_valid g1 l) by (eapply left_weak_valid; eauto).
      (* mark (l); *)
      localize [graph sh l g1].
      (** Mark the left part to get g2 from g1. *)
      forward_call (sh, g1, l).
      Intros g2.
      unlocalize [graph sh x g2] using g2 assuming H4.
      1: subst; eapply (@graph_ramify_left _ (sSGG_VST sh) g); eauto.
      assert (weak_valid g2 r) by (eapply right_weak_valid; eauto).
      (* mark (r); *)
      localize [graph sh r g2].
      (** Mark the right part to get g3 from g2. *)
      forward_call (sh, g2, r).
      Intros g3.
      unlocalize [graph sh x g3] using g3 assuming H6.
      1: subst; eapply (@graph_ramify_right _ (sSGG_VST sh) g); eauto.
      (* return; *)
      Exists g3. entailer!.
      (** The key theorem to show we really finished the marking procedure. *)
      apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
Qed.

(* Print Assumptions body_mark. *)
