Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.SpaceUAdjMatGraph3.
Require Import CertiGraph.prim.MathPrimGraph.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Section SpacePrimGraph3.

Context {size : Z}.
Context {inf : Z}.
Context {size_rep': 0 < size <= Int.max_signed}.
Context {inf_rep: 0 <= inf <= Int.max_signed}.
  
Definition G := @PrimGG size inf.
Identity Coercion PrimGG_G: G >-> PrimGG.
Definition edgeless_graph' := @edgeless_graph size inf inf_rep size_rep'.
Definition adde := @PrimGG_adde size inf.
Definition eremove := @PrimGG_eremove size inf.

Lemma edgeless_vert_rep:
  forall v,
    0 <= v < size ->
    (@vert_to_list size edgeless_graph' eformat v) =
    list_repeat (Z.to_nat size) inf.
Proof.
  intros. simpl. auto.
  (*should try to find a better scalable way*)
Admitted.

Lemma edgeless_to_symm_mat:
  (@graph_to_symm_mat size edgeless_graph') =
  list_repeat (Z.to_nat size) (list_repeat (Z.to_nat size) inf).
Proof.
  simpl. repeat rewrite edgeless_vert_rep; simpl. auto.
Admitted.

End SpacePrimGraph3.
