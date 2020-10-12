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
  unfold vert_to_list; intros. rewrite map_map. apply list_eq_Znth.
+rewrite Zlength_map, nat_inc_list_Zlength, Zlength_list_repeat'; auto.
+intros. rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id in H0. 2: lia.
rewrite Znth_list_repeat_inrange by auto.
rewrite Znth_map, nat_inc_list_i. simpl; auto.
rewrite Z2Nat.id; lia.
rewrite nat_inc_list_Zlength.
rewrite Z2Nat.id; lia.
Qed.

Lemma edgeless_to_symm_mat:
  (@graph_to_symm_mat size edgeless_graph') =
  list_repeat (Z.to_nat size) (list_repeat (Z.to_nat size) inf).
Proof.
  unfold graph_to_symm_mat, graph_to_mat. apply list_eq_Znth.
+rewrite Zlength_map, nat_inc_list_Zlength, Zlength_list_repeat'; auto.
+intros. rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id in H by lia.
rewrite Znth_list_repeat_inrange by lia.
rewrite Znth_map. rewrite nat_inc_list_i. apply edgeless_vert_rep; lia.
rewrite Z2Nat.id by lia; lia.
rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
Qed.

End SpacePrimGraph3.
