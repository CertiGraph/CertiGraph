Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.exportclight.Clightdefs.

Require Import VST.veric.expr.
Require Import VST.veric.mpred.
Require Import VST.floyd.forward.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.
Require Import VST.floyd.coqlib3.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.seplog.

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.MathAdjMatGraph.

Section Spatial_AdjMat_Model_2.
  (* Model 2 is for a stack-allocated graph,
     where the graph is declared on the stack
     as a single-dimension array of size "size^2". 
     Access to graph[u][v] is via graph[size*u + v].
   *)

  Context {size : Z}. 
  Context {CompSpecs : compspecs}.
  Context {V_EqDec : EquivDec.EqDec V eq}. 
  Context {E_EqDec: EquivDec.EqDec E eq}.
  
  (* SPATIAL REPRESENTATION *)

  (* Assumption: 
     (v,0), (v,1) ... (v, size-1) are edges.
   
   Action: 
    Makes a list containing each edge's elabel.
    The argument f is an opportunity to tweak the edges as needed
   *)  
  Definition vert_to_list (g: AdjMatLG) (f : E -> E) (v : V) :=
    map (elabel g)
        (map (fun x => f (v,x))
             (nat_inc_list (Z.to_nat size))).

  (* Assumptions: 
     1. 0, 1, ... (size-1) are vertices
     2. for any vertex v,
          (v,0), (v,1) ... (v, size-1) are edges.
          
     Action:
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
   *)
  Definition graph_to_mat (g: AdjMatLG) (f : E -> E) : list (list Z) :=
    map (vert_to_list g f)
        (nat_inc_list (Z.to_nat size)).

  Lemma graph_to_mat_Zlength:
    forall g (f : E -> E),
      0 <= size ->
      Zlength (graph_to_mat g f) = size.
  Proof.
    intros. unfold graph_to_mat.
    rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; trivial.
  Qed.

  Lemma elabel_Znth_graph_to_mat:
    forall (g: AdjMatLG) (f: E -> E) src dst,
      0 <= size ->
      0 <= src < size ->
      0 <= dst < size ->
      elabel g (f (src, dst)) =
      Znth dst (Znth src (graph_to_mat g f)).
  Proof.
    intros. 
    unfold graph_to_mat.
    rewrite Znth_map, nat_inc_list_i.
    unfold vert_to_list. rewrite Znth_map.
    rewrite Znth_map. rewrite nat_inc_list_i.
    reflexivity.
    3: rewrite Zlength_map.
    2, 3, 5: rewrite nat_inc_list_Zlength.
    all: rewrite Z2Nat.id; trivial.
  Qed.

  Definition graph_to_list (g: AdjMatLG) (f : E -> E) : list Z :=
    (concat (graph_to_mat g f)).

   Lemma Zlength_concat:
   forall size n f,
     0 <= n ->
     Forall (fun list : list Z => Zlength list = n)
            (map f (nat_inc_list size)) ->
     Zlength (concat (map f (nat_inc_list size))) =
     Z.of_nat size * n.
 Proof.
   intros.
   clear H. induction size0.
   1: simpl; apply Zlength_nil.
   rewrite Nat2Z.inj_succ, Z.mul_succ_l.
   simpl. rewrite map_app, concat_app, Zlength_app.
   simpl. rewrite app_nil_r.
   f_equal.
   - apply IHsize0.
     rewrite Forall_forall in H0 |- *.
     intros. apply H0.
     simpl. rewrite map_app.
     apply in_or_app; left; trivial.
   - rewrite Forall_forall in H0. apply H0.
     apply in_map. rewrite nat_inc_list_in_iff. lia.
 Qed.

 Lemma graph_to_list_Zlength:
    forall g (f : E -> E) n,
      0 <= size ->
      0 <= n ->
      Forall (fun list => Zlength list = n) (graph_to_mat g f) ->
      Zlength (graph_to_list g f) = size * n.
  Proof.
    intros.
    rewrite <- (Z2Nat.id size); trivial.
    unfold graph_to_list, graph_to_mat in *.
    apply Zlength_concat; trivial.
  Qed.

  Lemma graph_to_list_to_mat:
    forall g (f : E -> E) u i,
      0 <= u < size ->
      0 <= i < size ->
      0 < size ->
      Forall (fun list => Zlength list = size)
             (graph_to_mat g f) ->
      Znth (u * size + i) (graph_to_list g f) =
      Znth i (Znth u (graph_to_mat g f)).
  Proof.
    intros.
    assert (Htemp: 0 <= size) by lia.
    clear Htemp.
    unfold graph_to_list, graph_to_mat in *.
    rewrite <- (Z2Nat.id size) in H by lia.
    generalize dependent u.
    induction (Z.to_nat size).
    1: intros; lia.
    intros. simpl.
    rewrite map_app, concat_app.
    assert (Forall (fun list : list Z => Zlength list = size)
                   (map (vert_to_list g f) (nat_inc_list n))). {
      rewrite Forall_forall in H2 |- *.
      intros. apply H2. simpl. rewrite map_app.
      apply in_or_app. left; trivial.
    }
    specialize (IHn H3).
    destruct H.
    rewrite Nat2Z.inj_succ in H4.
    apply Z.lt_succ_r in H4.
    rewrite Z.le_lteq in H4. destruct H4.
    - repeat rewrite app_Znth1.
      + apply IHn; trivial; lia.
      + rewrite Zlength_map, nat_inc_list_Zlength; lia.
      + rewrite (Zlength_concat _ size); trivial; [|lia].
        rewrite <- (Z.succ_pred (Z.of_nat n)).
        rewrite Z.mul_succ_l.
        apply Z.add_le_lt_mono; try lia.
        apply Zorder.Zmult_le_compat_r; lia.
    - clear IHn. repeat rewrite app_Znth2.
      + rewrite (Zlength_concat _ size); trivial; [|lia].
        replace (u * size + i - Z.of_nat n * size)
          with
            (u * size - Z.of_nat n * size  + i) by lia.
        replace (u * size - Z.of_nat n * size)
          with
            ((u - Z.of_nat n) * size) by lia.
        rewrite Zlength_map, nat_inc_list_Zlength.
        simpl. rewrite app_nil_r.
        replace (u - Z.of_nat n) with 0 by lia.
        rewrite Znth_0_cons.
        replace (0 * size + i) with i by lia.
        reflexivity.
      + rewrite Zlength_map, nat_inc_list_Zlength; lia.
      + rewrite (Zlength_concat _ size); trivial; lia.
  Qed.

  Definition SpaceAdjMatGraph' sh g_contents gaddr : mpred :=
    data_at sh (tarray tint (size * size))
            (map Vint (map Int.repr g_contents))
            gaddr.

  Definition SpaceAdjMatGraph sh (f : E -> E) g gaddr : mpred :=
    SpaceAdjMatGraph' sh (graph_to_list g f) gaddr.

End Spatial_AdjMat_Model_2.

