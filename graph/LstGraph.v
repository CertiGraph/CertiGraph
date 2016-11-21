Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.GraphAsList.
Require Import RamifyCoq.graph.MathGraph.
(* Require Import RamifyCoq.graph.graph_gen. *)
(* Require Import RamifyCoq.graph.FiniteGraph. *)

Section MathValidVertexAccessible.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.
  Context {is_null: DecidablePred Vertex}.

  Variable (g: PreGraph Vertex Edge).
  Context {MA: MathGraph g is_null}.

  Instance MA_vva: ValidVertexAccessible g.
  Proof.
    apply (Build_ValidVertexAccessible _ (fun l => filter (fun e => if (projT2 is_null) (dst g e) then false else true) l)).
    intros. destruct is_null as [is_nullP ?]. simpl. destruct MA. simpl in *.
    rewrite filter_In. intuition.
    - destruct (s (dst g e)). inversion H2. specialize (valid_not_null (dst g e)). rewrite Forall_forall in H. specialize (H _ H1). apply valid_graph in H.
      destruct H. destruct H0; intuition.
    - destruct (s (dst g e)); auto. specialize (valid_not_null (dst g e)). exfalso; apply valid_not_null; auto.
  Qed.

End MathValidVertexAccessible.
